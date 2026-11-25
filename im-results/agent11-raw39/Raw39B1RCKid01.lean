import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid01_part1 : Audit := .cycle 0 9 true (0)
theorem kid01_part1_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (kid01_part1) = true := by rfl

def kid01_part2 : Audit := .cycle 1 8 true (1)
theorem kid01_part2_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,1⟩)) (kid01_part2) = true := by rfl

def kid01_part3 : Audit := .cycle 17 1 false (1)
theorem kid01_part3_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (kid01_part3) = true := by rfl

def kid01_part4 : Audit := .cycle 19 1 false (1)
theorem kid01_part4_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,3⟩)) (kid01_part4) = true := by rfl

def kid01_part6 : Audit := .cycle 0 19 false (3)
theorem kid01_part6_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part6) = true := by rfl

def kid01_part7 : Audit := .cycle 10 9 false (0)
theorem kid01_part7_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part7) = true := by rfl

def kid01_part8 : Audit := .cycle 21 1 false (-1)
theorem kid01_part8_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part8) = true := by rfl

def kid01_part9 : Audit := .cycle 0 11 true (0)
theorem kid01_part9_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part9) = true := by rfl

def kid01_part10 : Audit := .split 10 (4,true) (byMove [
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
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 23 (5,true),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 22 1 false (0),
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
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 22 1 false (2),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
]),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 22 1 false (0),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
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
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 9 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid01_part10_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part10) = true := by rfl

def kid01_part12 : Audit := .cycle 0 11 false (3)
theorem kid01_part12_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part12) = true := by rfl

def kid01_part13 : Audit := .split 20 (5,false) (byMove [
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
.last 23 (4,true),
.cycle 17 5 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 18 14 false (2),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 12 12 true (-2),
.cycle 9 12 false (1),
.cycle 20 1 true (-2)
])
theorem kid01_part13_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part13) = true := by rfl

def kid01_part14 : Audit := .cycle 12 1 false (0)
theorem kid01_part14_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part14) = true := by rfl

def kid01_part15 : Audit := .cycle 11 1 false (-1)
theorem kid01_part15_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part15) = true := by rfl

def kid01_part16 : Audit := .split 12 (5,false) (byMove [
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
.last 15 (4,true),
.cycle 11 5 false (-1),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 24 (4,true),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 11 12 true (-2),
.cycle 9 4 false (1),
.cycle 12 1 true (-2)
])
theorem kid01_part16_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part16) = true := by rfl

def kid01_part17 : Audit := .split 11 (5,false) (byMove [
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
.last 14 (4,true),
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
theorem kid01_part17_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part17) = true := by rfl

def kid01_part18 : Audit := .cycle 0 11 true (0)
theorem kid01_part18_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part18) = true := by rfl

def kid01_part19 : Audit := .split 20 (5,false) (byMove [
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
.last 23 (4,true),
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
theorem kid01_part19_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part19) = true := by rfl

def kid01_part20 : Audit := .cycle 12 1 false (2)
theorem kid01_part20_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part20) = true := by rfl

def kid01_part21 : Audit := .cycle 11 1 false (1)
theorem kid01_part21_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part21) = true := by rfl

def kid01_part22 : Audit := .split 12 (5,false) (byMove [
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
.last 15 (4,true),
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
theorem kid01_part22_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part22) = true := by rfl

def kid01_part23 : Audit := .split 11 (5,false) (byMove [
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
.last 14 (4,true),
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
theorem kid01_part23_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part23) = true := by rfl

def kid01_part24 : Audit := .split 13 (4,true) (byMove [
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
.cycle 11 3 false (0),
.last 18 (5,false),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 29 (5,false),
.cycle 1 13 false (3),
.last 22 (5,false),
.last 25 (5,false),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid01_part24_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part24) = true := by rfl

def kid01_part25 : Audit := .split 15 (5,false) (byMove [
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
.last 18 (4,true),
.cycle 11 5 false (0),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 34 (4,true),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 12 12 true (-3),
.cycle 9 7 false (1),
.cycle 15 1 true (-3)
])
theorem kid01_part25_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part25) = true := by rfl

def kid01_part26 : Audit := .cycle 0 13 true (-1)
theorem kid01_part26_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part26) = true := by rfl

def kid01_part27 : Audit := .cycle 11 1 false (-1)
theorem kid01_part27_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part27) = true := by rfl

def kid01_part28 : Audit := .split 12 (5,false) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M0.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M0.never m hm),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.cycle 14 10 true (-3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.last 15 (4,true),
.cycle 11 5 false (-1),
.last 17 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-2),
.cycle 13 12 true (-3),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid01_part28_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part28) = true := by rfl

def kid01_part29 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 22 true (-1),
.cycle 12 10 true (-2),
.cycle 24 1 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.cycle 0 26 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.last 13 (4,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid01_part29_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part29) = true := by rfl

def kid01_part30 : Audit := .cycle 0 11 true (0)
theorem kid01_part30_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part30) = true := by rfl

def kid01_part31 : Audit := .cycle 1 10 true (0)
theorem kid01_part31_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part31) = true := by rfl

def kid01_part32 : Audit := .split 19 (5,false) (byMove [
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
.last 22 (4,true),
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
theorem kid01_part32_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part32) = true := by rfl

def kid01_part33 : Audit := .split 22 (5,false) (byMove [
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
.last 25 (4,true),
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
theorem kid01_part33_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part33) = true := by rfl

def kid01_part34 : Audit := .cycle 9 2 true (0)
theorem kid01_part34_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part34) = true := by rfl

def kid01_part35 : Audit := .split 11 (5,false) (byMove [
.cycle 0 22 false (3),
.cycle 12 10 false (0),
.cycle 24 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.last 19 (4,true),
.cycle 12 5 false (0),
.cycle 0 16 true (-1),
.cycle 23 1 false (-1),
.last 12 (4,true),
.cycle 10 3 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 12 true (1),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
theorem kid01_part35_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part35) = true := by rfl

def kid01_part11 : Audit := .split 10 (5,true) (byMove [(kid01_part12),(kid01_part13),(kid01_part14),(kid01_part15),(kid01_part16),(kid01_part17),(kid01_part18),(kid01_part19),(kid01_part20),(kid01_part21),(kid01_part22),(kid01_part23),(kid01_part24),(kid01_part25),(kid01_part26),(kid01_part27),(kid01_part28),(kid01_part29),(kid01_part30),(kid01_part31),(kid01_part32),(kid01_part33),(kid01_part34),(kid01_part35)])

theorem kid01_part11_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part11) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part12),(kid01_part13),(kid01_part14),(kid01_part15),(kid01_part16),(kid01_part17),(kid01_part18),(kid01_part19),(kid01_part20),(kid01_part21),(kid01_part22),(kid01_part23),(kid01_part24),(kid01_part25),(kid01_part26),(kid01_part27),(kid01_part28),(kid01_part29),(kid01_part30),(kid01_part31),(kid01_part32),(kid01_part33),(kid01_part34),(kid01_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part12_checked

  · exact kid01_part18_checked

  · exact kid01_part24_checked

  · exact kid01_part30_checked

  · exact kid01_part13_checked

  · exact kid01_part19_checked

  · exact kid01_part25_checked

  · exact kid01_part31_checked

  · exact kid01_part14_checked

  · exact kid01_part20_checked

  · exact kid01_part26_checked

  · exact kid01_part32_checked

  · exact kid01_part15_checked

  · exact kid01_part21_checked

  · exact kid01_part27_checked

  · exact kid01_part33_checked

  · exact kid01_part16_checked

  · exact kid01_part22_checked

  · exact kid01_part28_checked

  · exact kid01_part34_checked

  · exact kid01_part17_checked

  · exact kid01_part23_checked

  · exact kid01_part29_checked

  · exact kid01_part35_checked

def kid01_part36 : Audit := .cycle 0 10 true (0)
theorem kid01_part36_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part36) = true := by rfl

def kid01_part37 : Audit := .cycle 1 9 true (1)
theorem kid01_part37_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part37) = true := by rfl

def kid01_part38 : Audit := .cycle 20 1 false (2)
theorem kid01_part38_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part38) = true := by rfl

def kid01_part39 : Audit := .cycle 17 1 false (1)
theorem kid01_part39_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part39) = true := by rfl

def kid01_part40 : Audit := .cycle 9 1 true (1)
theorem kid01_part40_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part40) = true := by rfl

def kid01_part41 : Audit := .split 10 (5,false) (byMove [
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
.last 15 (4,true),
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
.split 13 (4,true) (byMove [
.cycle 0 27 false (3),
.cycle 14 13 false (0),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 9 5 true (1),
.cycle 10 4 true (1),
.cycle 19 3 false (0),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.cycle 28 1 false (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 9 5 true (1),
.cycle 17 9 false (1)
]),
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
.cycle 13 3 false (1),
.cycle 15 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 23 5 false (3),
.cycle 9 6 true (0),
.cycle 16 5 false (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 9 4 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 9 4 true (1),
.cycle 10 3 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.last 17 (4,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.last 13 (4,true),
.cycle 15 1 false (3),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.last 16 (4,true),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.last 13 (4,true),
.cycle 13 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid01_part41_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part41) = true := by rfl

def kid01_part42 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 17 1 true (-3),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 15 15 false (1),
.cycle 1 17 false (3),
.cycle 10 12 false (1),
.cycle 10 15 false (1),
.cycle 9 9 false (1),
.cycle 17 1 true (-3)
]),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 17 1 false (-1),
.cycle 0 18 true (-2),
.cycle 10 13 true (-2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 13 5 true (-2),
.cycle 17 1 true (-1),
.cycle 14 4 true (-2),
.cycle 11 8 false (1),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 17 1 false (-1),
.cycle 15 15 true (-2),
.cycle 1 17 false (3),
.cycle 10 12 true (-2),
.cycle 10 15 true (-2),
.cycle 9 9 false (1),
.cycle 17 1 true (-1)
]),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.split 17 (5,false) (byMove [
.cycle 15 6 false (-1),
.last 38 (5,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 10 13 false (1),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 19 false (3),
.cycle 16 2 true (-3),
.last 18 (5,true),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 10 15 false (1),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 2 17 false (3),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.cycle 6 23 false (3),
.last 19 (5,true),
.last 18 (5,true)
]),
.cycle 15 14 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.split 17 (5,false) (byMove [
.cycle 10 13 false (1),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 19 false (3),
.cycle 16 2 true (-2),
.last 18 (5,true),
.cycle 6 22 false (3),
.cycle 10 13 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 13 5 true (-2),
.cycle 17 1 true (-1),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.cycle 7 72 false (3),
.cycle 10 14 true (-2),
.last 19 (5,true),
.last 18 (5,true),
.cycle 15 15 true (-2),
.cycle 15 14 true (-2),
.cycle 2 16 false (3),
.cycle 10 15 true (-2),
.cycle 15 6 true (-2),
.cycle 17 1 true (-1)
])
])
theorem kid01_part42_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part42) = true := by rfl

def kid01_part43 : Audit := .cycle 10 4 false (0)
theorem kid01_part43_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part43) = true := by rfl

def kid01_part44 : Audit := .cycle 0 14 true (-1)
theorem kid01_part44_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part44) = true := by rfl

def kid01_part45 : Audit := .cycle 20 1 false (0)
theorem kid01_part45_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part45) = true := by rfl

def kid01_part46 : Audit := .split 10 (4,true) (byMove [
.cycle 0 16 false (3),
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
.cycle 0 16 true (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 13 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 15 (5,true),
.cycle 1 16 false (3),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 19 1 false (1),
.cycle 12 1 false (0),
.cycle 20 1 false (0),
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
.last 15 (5,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 19 1 false (1),
.cycle 22 1 false (2),
.cycle 9 3 true (0),
.last 12 (5,false)
]),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 21 1 false (1),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.cycle 24 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 2 16 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 5 20 false (3),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 2 10 true (0),
.cycle 1 12 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 9 3 true (0),
.split 11 (5,true) (byMove [
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 8 16 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 17 (5,false),
.last 12 (5,false),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 27 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
])
theorem kid01_part46_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part46) = true := by rfl

def kid01_part48 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.last 25 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 17 (5,false),
.last 16 (5,false),
.cycle 0 16 true (-1),
.last 25 (5,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 17 (5,false),
.last 16 (5,false),
.cycle 14 3 false (0),
.last 20 (5,false),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 17 (5,false),
.last 16 (5,false),
.cycle 0 30 true (-1),
.cycle 1 15 false (3),
.last 24 (5,false),
.last 27 (5,false),
.cycle 9 7 false (1),
.last 16 (5,false)
])
theorem kid01_part48_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part48) = true := by rfl

def kid01_part49 : Audit := .cycle 0 14 true (-1)
theorem kid01_part49_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part49) = true := by rfl

def kid01_part50 : Audit := .cycle 12 1 false (0)
theorem kid01_part50_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part50) = true := by rfl

def kid01_part51 : Audit := .cycle 11 1 false (-1)
theorem kid01_part51_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part51) = true := by rfl

def kid01_part52 : Audit := .split 12 (5,false) (byMove [
.last 17 (4,true),
.last 18 (4,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-2),
.cycle 11 3 false (-1),
.cycle 11 11 false (0),
.last 16 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.cycle 11 5 false (-1),
.cycle 13 20 true (-3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-2),
.last 14 (4,true),
.cycle 11 4 false (-1),
.last 16 (4,true),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid01_part52_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part52) = true := by rfl

def kid01_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.last 29 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 14 (4,true),
.cycle 14 3 false (0),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 14 1 true (0),
.last 14 (4,true),
.cycle 11 5 false (-1),
.last 16 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 9 3 false (1),
.cycle 16 1 true (-2)
])
theorem kid01_part53_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part53) = true := by rfl

def kid01_part54 : Audit := .split 20 (5,false) (byMove [
.last 25 (4,true),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 11 10 true (0),
.cycle 18 3 false (2),
.cycle 12 11 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 0 22 true (0),
.last 23 (4,true),
.cycle 17 5 false (3),
.cycle 11 12 true (-1),
.cycle 21 1 false (-1),
.cycle 19 2 false (1),
.cycle 20 1 false (0),
.cycle 2 20 true (0),
.last 22 (4,true),
.cycle 17 4 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 0 22 true (0)
])
theorem kid01_part54_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part54) = true := by rfl

def kid01_part55 : Audit := .split 13 (5,false) (byMove [
.last 18 (4,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 10 true (-1),
.cycle 11 3 false (1),
.cycle 11 11 false (1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 11 11 true (-1),
.last 16 (4,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 2 13 false (3),
.last 15 (4,true),
.cycle 11 4 false (1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 11 11 true (-1)
])
theorem kid01_part55_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part55) = true := by rfl

def kid01_part56 : Audit := .split 21 (5,false) (byMove [
.last 26 (4,true),
.cycle 0 25 true (-2),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 20 2 false (0),
.cycle 21 1 false (-1),
.cycle 13 10 true (-1),
.cycle 19 3 false (1),
.cycle 11 11 false (2),
.cycle 0 23 true (-1),
.last 22 (4,true),
.cycle 24 1 false (2),
.last 24 (4,true),
.cycle 18 5 false (2),
.cycle 13 12 true (-2),
.cycle 22 1 false (-2),
.cycle 20 2 false (0),
.cycle 21 1 false (-1),
.cycle 2 21 false (3),
.last 23 (4,true),
.cycle 18 4 false (2),
.cycle 0 23 true (-1),
.last 22 (4,true),
.cycle 14 11 false (2)
])
theorem kid01_part56_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part56) = true := by rfl

def kid01_part57 : Audit := .cycle 0 12 true (0)
theorem kid01_part57_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part57) = true := by rfl

def kid01_part58 : Audit := .split 11 (4,true) (byMove [
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
.cycle 11 3 false (1),
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
theorem kid01_part58_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part58) = true := by rfl

def kid01_part59 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 0 13 true (0),
.cycle 20 3 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.last 15 (4,true),
.cycle 12 1 true (2),
.last 15 (4,true),
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
theorem kid01_part59_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part59) = true := by rfl

def kid01_part60 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.last 23 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 17 true (-1),
.last 18 (5,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.cycle 11 3 false (0),
.last 18 (5,false),
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 15 20 true (-1),
.cycle 1 17 false (3),
.cycle 0 16 true (-1),
.last 20 (5,false),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid01_part60_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part60) = true := by rfl

def kid01_part61 : Audit := .split 15 (5,false) (byMove [
.last 20 (4,true),
.last 23 (4,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 10 true (-3),
.cycle 13 3 false (-1),
.cycle 12 11 false (0),
.last 21 (4,true),
.last 16 (4,true),
.cycle 10 6 false (0),
.last 18 (4,true),
.cycle 11 5 false (0),
.cycle 12 12 true (-4),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 2 15 false (3),
.last 17 (4,true),
.cycle 12 4 false (0),
.last 21 (4,true),
.last 16 (4,true),
.cycle 13 4 false (-1)
])
theorem kid01_part61_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part61) = true := by rfl

def kid01_part62 : Audit := .split 22 (5,false) (byMove [
.last 27 (4,true),
.cycle 0 26 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 13 10 true (0),
.cycle 20 3 false (2),
.cycle 14 11 false (3),
.cycle 0 24 true (-1),
.last 23 (4,true),
.cycle 0 26 true (-1),
.last 25 (4,true),
.cycle 19 5 false (3),
.cycle 11 12 true (-1),
.cycle 23 1 false (-1),
.cycle 21 2 false (1),
.cycle 22 1 false (0),
.cycle 2 22 true (-1),
.last 24 (4,true),
.cycle 19 4 false (3),
.cycle 0 24 true (-1),
.last 23 (4,true),
.cycle 0 28 true (-1)
])
theorem kid01_part62_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part62) = true := by rfl

def kid01_part63 : Audit := .cycle 11 1 false (-1)
theorem kid01_part63_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part63) = true := by rfl

def kid01_part64 : Audit := .split 12 (5,false) (byMove [
.last 17 (4,true),
.last 31 (4,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 13 10 true (-3),
.cycle 11 3 false (-1),
.cycle 1 38 false (3),
.cycle 0 20 true (-2),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.cycle 11 5 false (-1),
.cycle 14 12 true (-4),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.last 14 (4,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid01_part64_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part64) = true := by rfl

def kid01_part65 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 28 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 12 10 true (-2),
.cycle 11 3 false (0),
.cycle 0 16 true (-1),
.cycle 0 24 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.cycle 13 12 true (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 13 (4,true),
.cycle 11 4 false (0),
.cycle 0 24 true (-1),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid01_part65_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part65) = true := by rfl

def kid01_part66 : Audit := .cycle 2 10 true (0)
theorem kid01_part66_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part66) = true := by rfl

def kid01_part67 : Audit := .split 12 (4,true) (byMove [
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
.cycle 11 3 false (1),
.last 17 (5,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 21 (5,false),
.last 24 (5,false),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid01_part67_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part67) = true := by rfl

def kid01_part68 : Audit := .split 14 (5,false) (byMove [
.last 19 (4,true),
.last 43 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 10 true (-2),
.cycle 12 3 false (0),
.cycle 11 11 false (1),
.cycle 0 16 true (-2),
.last 15 (4,true),
.cycle 11 10 true (-2),
.last 17 (4,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 2 14 false (3),
.last 16 (4,true),
.cycle 11 4 false (1),
.cycle 7 20 false (3),
.last 15 (4,true),
.cycle 2 14 false (3)
])
theorem kid01_part68_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part68) = true := by rfl

def kid01_part69 : Audit := .cycle 0 12 true (0)
theorem kid01_part69_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part69) = true := by rfl

def kid01_part70 : Audit := .split 11 (4,true) (byMove [
.last 21 (5,false),
.last 14 (5,false),
.last 22 (5,false),
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
.last 14 (5,false),
.cycle 0 16 true (-1),
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
theorem kid01_part70_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part70) = true := by rfl

def kid01_part71 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (0),
.last 14 (4,true),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 8 15 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 15 (4,true),
.cycle 12 1 true (2),
.last 16 (4,true),
.last 14 (4,true),
.cycle 13 12 true (-3),
.cycle 30 1 false (-2),
.last 13 (4,true),
.cycle 10 3 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 26 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (2)
])
theorem kid01_part71_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part71) = true := by rfl

def kid01_part47 : Audit := .split 10 (5,true) (byMove [(kid01_part48),(kid01_part49),(kid01_part50),(kid01_part51),(kid01_part52),(kid01_part53),(kid01_part54),(kid01_part55),(kid01_part56),(kid01_part57),(kid01_part58),(kid01_part59),(kid01_part60),(kid01_part61),(kid01_part62),(kid01_part63),(kid01_part64),(kid01_part65),(kid01_part66),(kid01_part67),(kid01_part68),(kid01_part69),(kid01_part70),(kid01_part71)])

theorem kid01_part47_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part47) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part48),(kid01_part49),(kid01_part50),(kid01_part51),(kid01_part52),(kid01_part53),(kid01_part54),(kid01_part55),(kid01_part56),(kid01_part57),(kid01_part58),(kid01_part59),(kid01_part60),(kid01_part61),(kid01_part62),(kid01_part63),(kid01_part64),(kid01_part65),(kid01_part66),(kid01_part67),(kid01_part68),(kid01_part69),(kid01_part70),(kid01_part71)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part48_checked

  · exact kid01_part54_checked

  · exact kid01_part60_checked

  · exact kid01_part66_checked

  · exact kid01_part49_checked

  · exact kid01_part55_checked

  · exact kid01_part61_checked

  · exact kid01_part67_checked

  · exact kid01_part50_checked

  · exact kid01_part56_checked

  · exact kid01_part62_checked

  · exact kid01_part68_checked

  · exact kid01_part51_checked

  · exact kid01_part57_checked

  · exact kid01_part63_checked

  · exact kid01_part69_checked

  · exact kid01_part52_checked

  · exact kid01_part58_checked

  · exact kid01_part64_checked

  · exact kid01_part70_checked

  · exact kid01_part53_checked

  · exact kid01_part59_checked

  · exact kid01_part65_checked

  · exact kid01_part71_checked

def kid01_part72 : Audit := .cycle 0 10 true (0)
theorem kid01_part72_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part72) = true := by rfl

def kid01_part73 : Audit := .cycle 1 9 true (1)
theorem kid01_part73_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part73) = true := by rfl

def kid01_part74 : Audit := .cycle 2 8 true (1)
theorem kid01_part74_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part74) = true := by rfl

def kid01_part75 : Audit := .cycle 2 11 true (1)
theorem kid01_part75_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part75) = true := by rfl

def kid01_part76 : Audit := .cycle 9 1 true (1)
theorem kid01_part76_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part76) = true := by rfl

def kid01_part78 : Audit := .cycle 2 10 true (1)
theorem kid01_part78_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part78) = true := by rfl

def kid01_part79 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 21 3 false (-1),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 3 false (2),
.cycle 21 3 false (1),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 22 3 false (2),
.cycle 9 4 true (0),
.cycle 13 3 false (1)
])
theorem kid01_part79_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part79) = true := by rfl

def kid01_part80 : Audit := .cycle 11 11 false (1)
theorem kid01_part80_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part80) = true := by rfl

def kid01_part81 : Audit := .cycle 0 12 true (0)
theorem kid01_part81_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part81) = true := by rfl

def kid01_part82 : Audit := .split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 9 4 true (1),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid01_part82_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part82) = true := by rfl

def kid01_part83 : Audit := .split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 15 1 false (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid01_part83_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part83) = true := by rfl

def kid01_part84 : Audit := .cycle 0 11 true (0)
theorem kid01_part84_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part84) = true := by rfl

def kid01_part85 : Audit := .cycle 1 10 true (1)
theorem kid01_part85_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part85) = true := by rfl

def kid01_part86 : Audit := .cycle 0 23 true (0)
theorem kid01_part86_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part86) = true := by rfl

def kid01_part87 : Audit := .cycle 3 8 true (1)
theorem kid01_part87_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part87) = true := by rfl

def kid01_part88 : Audit := .cycle 9 2 true (1)
theorem kid01_part88_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part88) = true := by rfl

def kid01_part89 : Audit := .cycle 10 1 true (2)
theorem kid01_part89_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part89) = true := by rfl

def kid01_part90 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.cycle 13 4 false (1),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 5 false (2),
.cycle 13 4 true (0),
.cycle 13 3 false (1),
.cycle 16 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 13 4 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 22 5 false (3),
.cycle 9 6 true (0),
.cycle 15 5 false (1)
])
theorem kid01_part90_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part90) = true := by rfl

def kid01_part91 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 16 3 false (-2),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 14 (5,true),
.cycle 16 3 false (0),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.cycle 16 3 false (-2),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.last 14 (5,true),
.cycle 13 3 false (1)
])
theorem kid01_part91_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part91) = true := by rfl

def kid01_part92 : Audit := .split 21 (4,true) (byMove [
.cycle 7 26 false (3),
.cycle 0 36 true (-2),
.cycle 11 17 false (2),
.cycle 3 53 false (3),
.cycle 0 28 true (-2),
.cycle 0 25 true (-2),
.cycle 0 22 true (-2),
.cycle 0 36 true (-2),
.cycle 0 137 true (-3),
.cycle 11 17 false (2),
.cycle 0 28 true (-2),
.cycle 0 25 true (-2),
.cycle 67 3 false (-3),
.cycle 7 16 false (3),
.cycle 0 24 true (-2),
.cycle 11 15 false (2),
.last 23 (5,true),
.cycle 0 39 true (-2),
.cycle 20 19 true (1),
.cycle 1 21 true (-2),
.cycle 0 35 true (-2),
.cycle 0 38 true (-2),
.cycle 9 13 true (-2),
.cycle 0 27 true (-2)
])
theorem kid01_part92_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part92) = true := by rfl

def kid01_part93 : Audit := .cycle 2 11 true (1)
theorem kid01_part93_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part93) = true := by rfl

def kid01_part94 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 36 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 12 (5,true),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 13 true (1),
.cycle 20 5 false (2),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 12 (5,true)
])
theorem kid01_part94_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part94) = true := by rfl

def kid01_part95 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 25 1 false (-1),
.last 15 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 20 1 false (4),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (1)
])
theorem kid01_part95_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part95) = true := by rfl

def kid01_part96 : Audit := .cycle 0 11 true (0)
theorem kid01_part96_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part96) = true := by rfl

def kid01_part97 : Audit := .cycle 1 10 true (1)
theorem kid01_part97_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part97) = true := by rfl

def kid01_part98 : Audit := .cycle 2 9 true (1)
theorem kid01_part98_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part98) = true := by rfl

def kid01_part99 : Audit := .cycle 2 12 true (1)
theorem kid01_part99_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part99) = true := by rfl

def kid01_part100 : Audit := .cycle 9 2 true (1)
theorem kid01_part100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part100) = true := by rfl

def kid01_part101 : Audit := .cycle 10 1 true (2)
theorem kid01_part101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part101) = true := by rfl

def kid01_part77 : Audit := .split 10 (5,false) (byMove [(kid01_part78),(kid01_part79),(kid01_part80),(kid01_part81),(kid01_part82),(kid01_part83),(kid01_part84),(kid01_part85),(kid01_part86),(kid01_part87),(kid01_part88),(kid01_part89),(kid01_part90),(kid01_part91),(kid01_part92),(kid01_part93),(kid01_part94),(kid01_part95),(kid01_part96),(kid01_part97),(kid01_part98),(kid01_part99),(kid01_part100),(kid01_part101)])

theorem kid01_part77_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part77) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part78),(kid01_part79),(kid01_part80),(kid01_part81),(kid01_part82),(kid01_part83),(kid01_part84),(kid01_part85),(kid01_part86),(kid01_part87),(kid01_part88),(kid01_part89),(kid01_part90),(kid01_part91),(kid01_part92),(kid01_part93),(kid01_part94),(kid01_part95),(kid01_part96),(kid01_part97),(kid01_part98),(kid01_part99),(kid01_part100),(kid01_part101)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part78_checked

  · exact kid01_part84_checked

  · exact kid01_part90_checked

  · exact kid01_part96_checked

  · exact kid01_part79_checked

  · exact kid01_part85_checked

  · exact kid01_part91_checked

  · exact kid01_part97_checked

  · exact kid01_part80_checked

  · exact kid01_part86_checked

  · exact kid01_part92_checked

  · exact kid01_part98_checked

  · exact kid01_part81_checked

  · exact kid01_part87_checked

  · exact kid01_part93_checked

  · exact kid01_part99_checked

  · exact kid01_part82_checked

  · exact kid01_part88_checked

  · exact kid01_part94_checked

  · exact kid01_part100_checked

  · exact kid01_part83_checked

  · exact kid01_part89_checked

  · exact kid01_part95_checked

  · exact kid01_part101_checked

def kid01_part5 : Audit := .split 9 (4,false) (byMove [(kid01_part6),(kid01_part7),(kid01_part8),(kid01_part9),(kid01_part10),(kid01_part11),(kid01_part36),(kid01_part37),(kid01_part38),(kid01_part39),(kid01_part40),(kid01_part41),(kid01_part42),(kid01_part43),(kid01_part44),(kid01_part45),(kid01_part46),(kid01_part47),(kid01_part72),(kid01_part73),(kid01_part74),(kid01_part75),(kid01_part76),(kid01_part77)])

theorem kid01_part5_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (kid01_part5) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid01_part6),(kid01_part7),(kid01_part8),(kid01_part9),(kid01_part10),(kid01_part11),(kid01_part36),(kid01_part37),(kid01_part38),(kid01_part39),(kid01_part40),(kid01_part41),(kid01_part42),(kid01_part43),(kid01_part44),(kid01_part45),(kid01_part46),(kid01_part47),(kid01_part72),(kid01_part73),(kid01_part74),(kid01_part75),(kid01_part76),(kid01_part77)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part6_checked

  · exact kid01_part36_checked

  · exact kid01_part42_checked

  · exact kid01_part72_checked

  · exact kid01_part7_checked

  · exact kid01_part37_checked

  · exact kid01_part43_checked

  · exact kid01_part73_checked

  · exact kid01_part8_checked

  · exact kid01_part38_checked

  · exact kid01_part44_checked

  · exact kid01_part74_checked

  · exact kid01_part9_checked

  · exact kid01_part39_checked

  · exact kid01_part45_checked

  · exact kid01_part75_checked

  · exact kid01_part10_checked

  · exact kid01_part40_checked

  · exact kid01_part46_checked

  · exact kid01_part76_checked

  · exact kid01_part11_checked

  · exact kid01_part41_checked

  · exact kid01_part47_checked

  · exact kid01_part77_checked

def kid01_part103 : Audit := .cycle 0 19 false (3)
theorem kid01_part103_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part103) = true := by rfl

def kid01_part104 : Audit := .cycle 10 9 false (0)
theorem kid01_part104_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part104) = true := by rfl

def kid01_part105 : Audit := .cycle 21 1 false (-1)
theorem kid01_part105_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part105) = true := by rfl

def kid01_part106 : Audit := .cycle 0 11 true (0)
theorem kid01_part106_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part106) = true := by rfl

def kid01_part108 : Audit := .cycle 0 11 false (3)
theorem kid01_part108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part108) = true := by rfl

def kid01_part109 : Audit := .split 20 (4,false) (byMove [
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
.last 23 (5,true),
.cycle 17 5 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 18 14 false (2),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 12 12 true (-2),
.cycle 20 1 true (-2),
.cycle 9 12 false (1)
])
theorem kid01_part109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part109) = true := by rfl

def kid01_part110 : Audit := .cycle 12 1 false (0)
theorem kid01_part110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part110) = true := by rfl

def kid01_part111 : Audit := .cycle 11 1 false (-1)
theorem kid01_part111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part111) = true := by rfl

def kid01_part112 : Audit := .split 11 (4,false) (byMove [
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
.last 14 (5,true),
.cycle 11 5 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 10 13 false (3),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 11 12 true (-1),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
])
theorem kid01_part112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part112) = true := by rfl

def kid01_part113 : Audit := .split 12 (4,false) (byMove [
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
.last 15 (5,true),
.cycle 11 5 false (-1),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 24 (5,true),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 11 12 true (-2),
.cycle 12 1 true (-2),
.cycle 9 4 false (1)
])
theorem kid01_part113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part113) = true := by rfl

def kid01_part114 : Audit := .cycle 0 11 true (0)
theorem kid01_part114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part114) = true := by rfl

def kid01_part115 : Audit := .split 20 (4,false) (byMove [
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
.last 23 (5,true),
.cycle 17 5 false (3),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 12 9 false (3),
.cycle 12 12 true (0),
.cycle 20 1 true (0),
.cycle 9 12 true (0)
])
theorem kid01_part115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part115) = true := by rfl

def kid01_part116 : Audit := .cycle 12 1 false (2)
theorem kid01_part116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part116) = true := by rfl

def kid01_part117 : Audit := .cycle 11 1 false (1)
theorem kid01_part117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part117) = true := by rfl

def kid01_part118 : Audit := .split 11 (4,false) (byMove [
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
.last 14 (5,true),
.cycle 11 5 false (1),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 11 9 false (3),
.cycle 11 12 true (1),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid01_part118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part118) = true := by rfl

def kid01_part119 : Audit := .split 12 (4,false) (byMove [
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
.last 15 (5,true),
.cycle 11 5 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 11 9 false (2),
.cycle 11 12 true (0),
.cycle 12 1 true (0),
.cycle 9 4 true (0)
])
theorem kid01_part119_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part119) = true := by rfl

def kid01_part120 : Audit := .split 13 (5,true) (byMove [
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
.cycle 11 3 false (0),
.last 18 (4,false),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 29 (4,false),
.cycle 1 13 false (3),
.last 22 (4,false),
.last 25 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid01_part120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part120) = true := by rfl

def kid01_part121 : Audit := .split 15 (4,false) (byMove [
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
.last 18 (5,true),
.cycle 11 5 false (0),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 34 (5,true),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 12 12 true (-3),
.cycle 15 1 true (-3),
.cycle 9 7 false (1)
])
theorem kid01_part121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part121) = true := by rfl

def kid01_part122 : Audit := .cycle 0 13 true (-1)
theorem kid01_part122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part122) = true := by rfl

def kid01_part123 : Audit := .cycle 11 1 false (-1)
theorem kid01_part123_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part123) = true := by rfl

def kid01_part124 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 22 true (-1),
.cycle 12 10 true (-2),
.cycle 24 1 false (0),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.cycle 0 26 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 2 11 false (3),
.last 13 (5,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid01_part124_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part124) = true := by rfl

def kid01_part125 : Audit := .split 12 (4,false) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M1.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M1.never m hm),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 14 10 true (-3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.last 15 (5,true),
.cycle 11 5 false (-1),
.last 17 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (-2),
.cycle 13 12 true (-3),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid01_part125_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part125) = true := by rfl

def kid01_part126 : Audit := .cycle 0 11 true (0)
theorem kid01_part126_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part126) = true := by rfl

def kid01_part127 : Audit := .cycle 1 10 true (0)
theorem kid01_part127_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part127) = true := by rfl

def kid01_part128 : Audit := .split 19 (4,false) (byMove [
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
.last 22 (5,true),
.cycle 16 5 false (2),
.cycle 0 22 true (-2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 2 false (0),
.cycle 2 29 false (3),
.cycle 1 19 false (3),
.cycle 11 9 false (2),
.cycle 11 12 true (-1),
.cycle 19 1 true (-1),
.cycle 9 11 false (2)
])
theorem kid01_part128_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part128) = true := by rfl

def kid01_part129 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 14 10 false (3),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 0 23 true (0),
.cycle 14 10 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 true (0),
.cycle 21 2 true (0),
.last 25 (5,true),
.cycle 19 5 false (3),
.cycle 0 25 true (-1),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 14 9 false (3),
.cycle 11 12 true (0),
.cycle 22 1 true (0),
.cycle 9 14 true (0)
])
theorem kid01_part129_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part129) = true := by rfl

def kid01_part130 : Audit := .split 11 (4,false) (byMove [
.cycle 0 22 false (3),
.cycle 12 10 false (0),
.cycle 24 1 false (-2),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.last 19 (5,true),
.cycle 12 5 false (0),
.cycle 0 16 true (-1),
.cycle 23 1 false (-1),
.cycle 10 3 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 12 true (1),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid01_part130_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part130) = true := by rfl

def kid01_part131 : Audit := .cycle 9 2 true (0)
theorem kid01_part131_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part131) = true := by rfl

def kid01_part107 : Audit := .split 10 (4,true) (byMove [(kid01_part108),(kid01_part109),(kid01_part110),(kid01_part111),(kid01_part112),(kid01_part113),(kid01_part114),(kid01_part115),(kid01_part116),(kid01_part117),(kid01_part118),(kid01_part119),(kid01_part120),(kid01_part121),(kid01_part122),(kid01_part123),(kid01_part124),(kid01_part125),(kid01_part126),(kid01_part127),(kid01_part128),(kid01_part129),(kid01_part130),(kid01_part131)])

theorem kid01_part107_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part107) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part108),(kid01_part109),(kid01_part110),(kid01_part111),(kid01_part112),(kid01_part113),(kid01_part114),(kid01_part115),(kid01_part116),(kid01_part117),(kid01_part118),(kid01_part119),(kid01_part120),(kid01_part121),(kid01_part122),(kid01_part123),(kid01_part124),(kid01_part125),(kid01_part126),(kid01_part127),(kid01_part128),(kid01_part129),(kid01_part130),(kid01_part131)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part108_checked

  · exact kid01_part114_checked

  · exact kid01_part120_checked

  · exact kid01_part126_checked

  · exact kid01_part109_checked

  · exact kid01_part115_checked

  · exact kid01_part121_checked

  · exact kid01_part127_checked

  · exact kid01_part110_checked

  · exact kid01_part116_checked

  · exact kid01_part122_checked

  · exact kid01_part128_checked

  · exact kid01_part111_checked

  · exact kid01_part117_checked

  · exact kid01_part123_checked

  · exact kid01_part129_checked

  · exact kid01_part112_checked

  · exact kid01_part118_checked

  · exact kid01_part124_checked

  · exact kid01_part130_checked

  · exact kid01_part113_checked

  · exact kid01_part119_checked

  · exact kid01_part125_checked

  · exact kid01_part131_checked

def kid01_part132 : Audit := .split 10 (5,true) (byMove [
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
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 23 (4,true),
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
.cycle 10 4 true (0),
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
.cycle 10 3 false (0),
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
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 22 1 false (0),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 2 11 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.split 11 (4,false) (byMove [
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
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
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 9 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid01_part132_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part132) = true := by rfl

def kid01_part133 : Audit := .cycle 0 10 true (0)
theorem kid01_part133_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part133) = true := by rfl

def kid01_part134 : Audit := .cycle 1 9 true (1)
theorem kid01_part134_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part134) = true := by rfl

def kid01_part135 : Audit := .cycle 20 1 false (2)
theorem kid01_part135_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part135) = true := by rfl

def kid01_part136 : Audit := .cycle 17 1 false (1)
theorem kid01_part136_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part136) = true := by rfl

def kid01_part137 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
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
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (1),
.split 13 (5,true) (byMove [
.cycle 0 27 false (3),
.cycle 14 13 false (0),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 14 5 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 10 4 true (1),
.cycle 9 5 true (1),
.cycle 19 3 false (0),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.cycle 28 1 false (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 17 9 false (1),
.cycle 9 5 true (1)
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
.cycle 13 3 false (1),
.cycle 15 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 23 5 false (3),
.cycle 16 5 false (0),
.cycle 9 6 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.last 17 (5,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.cycle 15 1 false (3),
.last 13 (5,true),
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.cycle 13 3 true (1),
.last 13 (5,true)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 14 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 9 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid01_part137_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part137) = true := by rfl

def kid01_part138 : Audit := .cycle 9 1 true (1)
theorem kid01_part138_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part138) = true := by rfl

def kid01_part139 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
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
.cycle 15 15 false (1),
.cycle 1 17 false (3),
.cycle 10 12 false (1),
.cycle 10 15 false (1),
.cycle 17 1 true (-3),
.cycle 9 9 false (1)
]),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 13 5 false (-1),
.cycle 0 18 true (-2),
.cycle 10 13 true (-2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 true (-1),
.cycle 13 5 true (-2),
.cycle 14 4 true (-2),
.cycle 11 8 false (1),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 13 5 false (-1),
.cycle 15 15 true (-2),
.cycle 1 17 false (3),
.cycle 10 12 true (-2),
.cycle 10 15 true (-2),
.cycle 17 1 true (-1),
.cycle 9 9 false (1)
]),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 15 6 false (-1),
.last 38 (4,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 10 13 false (1),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 16 2 true (-3),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 10 15 false (1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 2 17 false (3),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.cycle 6 23 false (3),
.last 18 (4,true),
.last 19 (4,true)
]),
.cycle 13 4 false (-1),
.cycle 15 14 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.split 17 (4,false) (byMove [
.cycle 10 13 false (1),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 16 2 true (-2),
.cycle 6 22 false (3),
.cycle 10 13 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 17 1 true (-1),
.cycle 13 5 true (-2),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.cycle 7 72 false (3),
.cycle 10 14 true (-2),
.last 18 (4,true),
.last 19 (4,true),
.cycle 15 15 true (-2),
.cycle 15 14 true (-2),
.cycle 2 16 false (3),
.cycle 10 15 true (-2),
.cycle 17 1 true (-1),
.cycle 15 6 true (-2)
]),
.cycle 9 8 false (1)
])
theorem kid01_part139_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part139) = true := by rfl

def kid01_part140 : Audit := .cycle 10 4 false (0)
theorem kid01_part140_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part140) = true := by rfl

def kid01_part141 : Audit := .cycle 0 14 true (-1)
theorem kid01_part141_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part141) = true := by rfl

def kid01_part142 : Audit := .cycle 20 1 false (0)
theorem kid01_part142_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part142) = true := by rfl

def kid01_part144 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 false (3),
.last 25 (4,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.last 17 (4,false),
.cycle 0 16 true (-1),
.last 25 (4,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 17 (4,false),
.cycle 14 3 false (0),
.last 20 (4,false),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.last 17 (4,false),
.cycle 0 30 true (-1),
.cycle 1 15 false (3),
.last 24 (4,false),
.last 27 (4,false),
.last 16 (4,false),
.cycle 9 7 false (1)
])
theorem kid01_part144_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part144) = true := by rfl

def kid01_part145 : Audit := .cycle 0 14 true (-1)
theorem kid01_part145_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part145) = true := by rfl

def kid01_part146 : Audit := .cycle 12 1 false (0)
theorem kid01_part146_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part146) = true := by rfl

def kid01_part147 : Audit := .cycle 11 1 false (-1)
theorem kid01_part147_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part147) = true := by rfl

def kid01_part148 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.last 29 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (5,true),
.cycle 14 3 false (0),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 14 1 true (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 16 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 16 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid01_part148_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part148) = true := by rfl

def kid01_part149 : Audit := .split 12 (4,false) (byMove [
.last 17 (5,true),
.last 18 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 16 true (-2),
.cycle 11 3 false (-1),
.cycle 11 11 false (0),
.last 16 (5,true),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 15 (5,true),
.cycle 11 5 false (-1),
.cycle 13 20 true (-3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 16 true (-2),
.last 14 (5,true),
.cycle 11 4 false (-1),
.last 16 (5,true),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid01_part149_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part149) = true := by rfl

def kid01_part150 : Audit := .split 20 (4,false) (byMove [
.last 25 (5,true),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 11 10 true (0),
.cycle 18 3 false (2),
.cycle 12 11 false (3),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.last 21 (5,true),
.last 23 (5,true),
.cycle 17 5 false (3),
.cycle 11 12 true (-1),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 2 20 true (0),
.last 22 (5,true),
.cycle 17 4 false (3),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.last 21 (5,true)
])
theorem kid01_part150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part150) = true := by rfl

def kid01_part151 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 10 true (-1),
.cycle 11 3 false (1),
.cycle 11 11 false (1),
.cycle 0 15 true (-1),
.cycle 11 11 true (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 2 13 false (3),
.last 15 (5,true),
.cycle 11 4 false (1),
.cycle 0 15 true (-1),
.cycle 11 11 true (-1),
.last 14 (5,true)
])
theorem kid01_part151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part151) = true := by rfl

def kid01_part152 : Audit := .split 21 (4,false) (byMove [
.last 26 (5,true),
.cycle 0 25 true (-2),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 20 2 false (0),
.cycle 13 10 true (-1),
.cycle 19 3 false (1),
.cycle 11 11 false (2),
.cycle 0 23 true (-1),
.cycle 24 1 false (2),
.last 22 (5,true),
.last 24 (5,true),
.cycle 18 5 false (2),
.cycle 13 12 true (-2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 20 2 false (0),
.cycle 2 21 false (3),
.last 23 (5,true),
.cycle 18 4 false (2),
.cycle 0 23 true (-1),
.cycle 14 11 false (2),
.last 22 (5,true)
])
theorem kid01_part152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part152) = true := by rfl

def kid01_part153 : Audit := .cycle 0 12 true (0)
theorem kid01_part153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part153) = true := by rfl

def kid01_part154 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 20 3 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 12 1 true (2),
.last 15 (5,true),
.last 15 (5,true),
.cycle 12 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (4),
.cycle 0 26 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid01_part154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part154) = true := by rfl

def kid01_part155 : Audit := .split 11 (5,true) (byMove [
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
.cycle 11 3 false (1),
.last 16 (4,false),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 20 (4,false),
.last 23 (4,false),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid01_part155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part155) = true := by rfl

def kid01_part156 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (-2),
.last 23 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 17 true (-1),
.last 18 (4,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.cycle 11 3 false (0),
.last 18 (4,false),
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 15 20 true (-1),
.cycle 1 17 false (3),
.cycle 0 16 true (-1),
.last 20 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid01_part156_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part156) = true := by rfl

def kid01_part157 : Audit := .split 15 (4,false) (byMove [
.last 20 (5,true),
.last 23 (5,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 10 true (-3),
.cycle 13 3 false (-1),
.cycle 12 11 false (0),
.last 21 (5,true),
.cycle 10 6 false (0),
.last 16 (5,true),
.last 18 (5,true),
.cycle 11 5 false (0),
.cycle 12 12 true (-4),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 2 15 false (3),
.last 17 (5,true),
.cycle 12 4 false (0),
.last 21 (5,true),
.cycle 13 4 false (-1),
.last 16 (5,true)
])
theorem kid01_part157_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part157) = true := by rfl

def kid01_part158 : Audit := .split 22 (4,false) (byMove [
.last 27 (5,true),
.cycle 0 26 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 13 10 true (0),
.cycle 20 3 false (2),
.cycle 14 11 false (3),
.cycle 0 24 true (-1),
.cycle 0 26 true (-1),
.last 23 (5,true),
.last 25 (5,true),
.cycle 19 5 false (3),
.cycle 11 12 true (-1),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 2 22 true (-1),
.last 24 (5,true),
.cycle 19 4 false (3),
.cycle 0 24 true (-1),
.cycle 0 28 true (-1),
.last 23 (5,true)
])
theorem kid01_part158_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part158) = true := by rfl

def kid01_part159 : Audit := .cycle 11 1 false (-1)
theorem kid01_part159_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part159) = true := by rfl

def kid01_part160 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 28 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 12 10 true (-2),
.cycle 11 3 false (0),
.cycle 0 16 true (-1),
.cycle 0 24 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.cycle 13 12 true (-3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 11 4 false (0),
.cycle 0 24 true (-1),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid01_part160_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part160) = true := by rfl

def kid01_part161 : Audit := .split 12 (4,false) (byMove [
.last 17 (5,true),
.last 31 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 13 10 true (-3),
.cycle 11 3 false (-1),
.cycle 1 38 false (3),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 15 (5,true),
.cycle 11 5 false (-1),
.cycle 14 12 true (-4),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid01_part161_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part161) = true := by rfl

def kid01_part162 : Audit := .cycle 2 10 true (0)
theorem kid01_part162_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part162) = true := by rfl

def kid01_part163 : Audit := .split 12 (5,true) (byMove [
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
.cycle 11 3 false (1),
.last 17 (4,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 21 (4,false),
.last 24 (4,false),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid01_part163_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part163) = true := by rfl

def kid01_part164 : Audit := .split 14 (4,false) (byMove [
.last 19 (5,true),
.last 43 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 10 true (-2),
.cycle 12 3 false (0),
.cycle 11 11 false (1),
.cycle 0 16 true (-2),
.cycle 11 10 true (-2),
.last 15 (5,true),
.last 17 (5,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 2 14 false (3),
.last 16 (5,true),
.cycle 11 4 false (1),
.cycle 7 20 false (3),
.cycle 2 14 false (3),
.last 15 (5,true)
])
theorem kid01_part164_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part164) = true := by rfl

def kid01_part165 : Audit := .cycle 0 12 true (0)
theorem kid01_part165_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part165) = true := by rfl

def kid01_part166 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (0),
.last 14 (5,true),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 8 15 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 12 1 true (2),
.last 15 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 13 12 true (-3),
.cycle 30 1 false (-2),
.cycle 10 3 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 26 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid01_part166_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part166) = true := by rfl

def kid01_part167 : Audit := .split 11 (5,true) (byMove [
.last 21 (4,false),
.last 14 (4,false),
.last 22 (4,false),
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
.last 14 (4,false),
.cycle 0 16 true (-1),
.last 22 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.last 23 (4,false),
.last 12 (4,false),
.cycle 9 3 true (0)
])
theorem kid01_part167_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part167) = true := by rfl

def kid01_part143 : Audit := .split 10 (4,true) (byMove [(kid01_part144),(kid01_part145),(kid01_part146),(kid01_part147),(kid01_part148),(kid01_part149),(kid01_part150),(kid01_part151),(kid01_part152),(kid01_part153),(kid01_part154),(kid01_part155),(kid01_part156),(kid01_part157),(kid01_part158),(kid01_part159),(kid01_part160),(kid01_part161),(kid01_part162),(kid01_part163),(kid01_part164),(kid01_part165),(kid01_part166),(kid01_part167)])

theorem kid01_part143_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part143) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part144),(kid01_part145),(kid01_part146),(kid01_part147),(kid01_part148),(kid01_part149),(kid01_part150),(kid01_part151),(kid01_part152),(kid01_part153),(kid01_part154),(kid01_part155),(kid01_part156),(kid01_part157),(kid01_part158),(kid01_part159),(kid01_part160),(kid01_part161),(kid01_part162),(kid01_part163),(kid01_part164),(kid01_part165),(kid01_part166),(kid01_part167)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part144_checked

  · exact kid01_part150_checked

  · exact kid01_part156_checked

  · exact kid01_part162_checked

  · exact kid01_part145_checked

  · exact kid01_part151_checked

  · exact kid01_part157_checked

  · exact kid01_part163_checked

  · exact kid01_part146_checked

  · exact kid01_part152_checked

  · exact kid01_part158_checked

  · exact kid01_part164_checked

  · exact kid01_part147_checked

  · exact kid01_part153_checked

  · exact kid01_part159_checked

  · exact kid01_part165_checked

  · exact kid01_part148_checked

  · exact kid01_part154_checked

  · exact kid01_part160_checked

  · exact kid01_part166_checked

  · exact kid01_part149_checked

  · exact kid01_part155_checked

  · exact kid01_part161_checked

  · exact kid01_part167_checked

def kid01_part168 : Audit := .split 10 (5,true) (byMove [
.cycle 0 16 false (3),
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
.cycle 0 16 true (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 1 false (0),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.cycle 1 16 false (3),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 19 1 false (1),
.cycle 12 1 false (0),
.cycle 20 1 false (0),
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
.last 15 (4,false),
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
]),
.cycle 12 1 false (2),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 21 1 false (1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.cycle 24 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 2 16 false (3),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 5 20 false (3),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 2 10 true (0),
.cycle 1 12 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 8 16 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 12 (4,false),
.last 17 (4,false),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.last 13 (4,false),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 27 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 9 3 true (0)
])
theorem kid01_part168_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part168) = true := by rfl

def kid01_part169 : Audit := .cycle 0 10 true (0)
theorem kid01_part169_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part169) = true := by rfl

def kid01_part170 : Audit := .cycle 1 9 true (1)
theorem kid01_part170_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part170) = true := by rfl

def kid01_part171 : Audit := .cycle 2 8 true (1)
theorem kid01_part171_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part171) = true := by rfl

def kid01_part172 : Audit := .cycle 2 11 true (1)
theorem kid01_part172_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part172) = true := by rfl

def kid01_part174 : Audit := .cycle 2 10 true (1)
theorem kid01_part174_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part174) = true := by rfl

def kid01_part175 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 3 false (-1),
.cycle 13 3 false (0),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 21 3 false (1),
.cycle 13 3 false (2),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 22 3 false (2),
.cycle 13 3 false (1),
.cycle 9 4 true (0)
])
theorem kid01_part175_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part175) = true := by rfl

def kid01_part176 : Audit := .cycle 11 11 false (1)
theorem kid01_part176_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part176) = true := by rfl

def kid01_part177 : Audit := .cycle 0 12 true (0)
theorem kid01_part177_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part177) = true := by rfl

def kid01_part178 : Audit := .split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 9 3 true (1),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid01_part178_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part178) = true := by rfl

def kid01_part179 : Audit := .split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (1),
.cycle 9 3 true (1),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
])
theorem kid01_part179_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part179) = true := by rfl

def kid01_part180 : Audit := .cycle 0 11 true (0)
theorem kid01_part180_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part180) = true := by rfl

def kid01_part181 : Audit := .cycle 1 10 true (1)
theorem kid01_part181_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part181) = true := by rfl

def kid01_part182 : Audit := .cycle 0 23 true (0)
theorem kid01_part182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part182) = true := by rfl

def kid01_part183 : Audit := .cycle 3 8 true (1)
theorem kid01_part183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part183) = true := by rfl

def kid01_part184 : Audit := .cycle 10 1 true (2)
theorem kid01_part184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part184) = true := by rfl

def kid01_part185 : Audit := .cycle 9 2 true (1)
theorem kid01_part185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part185) = true := by rfl

def kid01_part186 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 4 false (1),
.cycle 15 5 false (0),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 13 4 true (0),
.cycle 15 5 false (2),
.cycle 13 3 false (1),
.cycle 16 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 4 false (1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 22 5 false (3),
.cycle 15 5 false (1),
.cycle 9 6 true (0)
])
theorem kid01_part186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part186) = true := by rfl

def kid01_part187 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 3 false (-2),
.cycle 13 3 false (0),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 3 false (0),
.last 14 (4,true),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.cycle 16 3 false (-2),
.last 14 (4,true),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.cycle 13 3 false (1),
.last 14 (4,true)
])
theorem kid01_part187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part187) = true := by rfl

def kid01_part188 : Audit := .split 21 (5,true) (byMove [
.cycle 7 26 false (3),
.cycle 0 36 true (-2),
.cycle 11 17 false (2),
.cycle 3 53 false (3),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.cycle 0 22 true (-2),
.cycle 0 36 true (-2),
.cycle 0 137 true (-3),
.cycle 11 17 false (2),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.cycle 67 3 false (-3),
.cycle 7 16 false (3),
.cycle 0 24 true (-2),
.cycle 11 15 false (2),
.cycle 0 39 true (-2),
.last 23 (4,true),
.cycle 20 19 true (1),
.cycle 1 21 true (-2),
.cycle 0 35 true (-2),
.cycle 0 38 true (-2),
.cycle 0 27 true (-2),
.cycle 9 13 true (-2)
])
theorem kid01_part188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part188) = true := by rfl

def kid01_part189 : Audit := .cycle 2 11 true (1)
theorem kid01_part189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part189) = true := by rfl

def kid01_part190 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 25 1 false (-1),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.last 12 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 10 3 true (1),
.last 12 (5,true)
])
theorem kid01_part190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part190) = true := by rfl

def kid01_part191 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 36 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (1),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 2 11 true (1),
.cycle 1 13 true (1),
.cycle 20 5 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (1)
])
theorem kid01_part191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part191) = true := by rfl

def kid01_part192 : Audit := .cycle 0 11 true (0)
theorem kid01_part192_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part192) = true := by rfl

def kid01_part193 : Audit := .cycle 1 10 true (1)
theorem kid01_part193_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part193) = true := by rfl

def kid01_part194 : Audit := .cycle 2 9 true (1)
theorem kid01_part194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part194) = true := by rfl

def kid01_part195 : Audit := .cycle 2 12 true (1)
theorem kid01_part195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part195) = true := by rfl

def kid01_part196 : Audit := .cycle 10 1 true (2)
theorem kid01_part196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part196) = true := by rfl

def kid01_part197 : Audit := .cycle 9 2 true (1)
theorem kid01_part197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part197) = true := by rfl

def kid01_part173 : Audit := .split 10 (4,false) (byMove [(kid01_part174),(kid01_part175),(kid01_part176),(kid01_part177),(kid01_part178),(kid01_part179),(kid01_part180),(kid01_part181),(kid01_part182),(kid01_part183),(kid01_part184),(kid01_part185),(kid01_part186),(kid01_part187),(kid01_part188),(kid01_part189),(kid01_part190),(kid01_part191),(kid01_part192),(kid01_part193),(kid01_part194),(kid01_part195),(kid01_part196),(kid01_part197)])

theorem kid01_part173_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part173) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid01_part174),(kid01_part175),(kid01_part176),(kid01_part177),(kid01_part178),(kid01_part179),(kid01_part180),(kid01_part181),(kid01_part182),(kid01_part183),(kid01_part184),(kid01_part185),(kid01_part186),(kid01_part187),(kid01_part188),(kid01_part189),(kid01_part190),(kid01_part191),(kid01_part192),(kid01_part193),(kid01_part194),(kid01_part195),(kid01_part196),(kid01_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part174_checked

  · exact kid01_part180_checked

  · exact kid01_part186_checked

  · exact kid01_part192_checked

  · exact kid01_part175_checked

  · exact kid01_part181_checked

  · exact kid01_part187_checked

  · exact kid01_part193_checked

  · exact kid01_part176_checked

  · exact kid01_part182_checked

  · exact kid01_part188_checked

  · exact kid01_part194_checked

  · exact kid01_part177_checked

  · exact kid01_part183_checked

  · exact kid01_part189_checked

  · exact kid01_part195_checked

  · exact kid01_part178_checked

  · exact kid01_part184_checked

  · exact kid01_part190_checked

  · exact kid01_part196_checked

  · exact kid01_part179_checked

  · exact kid01_part185_checked

  · exact kid01_part191_checked

  · exact kid01_part197_checked

def kid01_part198 : Audit := .cycle 9 1 true (1)
theorem kid01_part198_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part198) = true := by rfl

def kid01_part102 : Audit := .split 9 (5,false) (byMove [(kid01_part103),(kid01_part104),(kid01_part105),(kid01_part106),(kid01_part107),(kid01_part132),(kid01_part133),(kid01_part134),(kid01_part135),(kid01_part136),(kid01_part137),(kid01_part138),(kid01_part139),(kid01_part140),(kid01_part141),(kid01_part142),(kid01_part143),(kid01_part168),(kid01_part169),(kid01_part170),(kid01_part171),(kid01_part172),(kid01_part173),(kid01_part198)])

theorem kid01_part102_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (kid01_part102) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid01_part103),(kid01_part104),(kid01_part105),(kid01_part106),(kid01_part107),(kid01_part132),(kid01_part133),(kid01_part134),(kid01_part135),(kid01_part136),(kid01_part137),(kid01_part138),(kid01_part139),(kid01_part140),(kid01_part141),(kid01_part142),(kid01_part143),(kid01_part168),(kid01_part169),(kid01_part170),(kid01_part171),(kid01_part172),(kid01_part173),(kid01_part198)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part103_checked

  · exact kid01_part133_checked

  · exact kid01_part139_checked

  · exact kid01_part169_checked

  · exact kid01_part104_checked

  · exact kid01_part134_checked

  · exact kid01_part140_checked

  · exact kid01_part170_checked

  · exact kid01_part105_checked

  · exact kid01_part135_checked

  · exact kid01_part141_checked

  · exact kid01_part171_checked

  · exact kid01_part106_checked

  · exact kid01_part136_checked

  · exact kid01_part142_checked

  · exact kid01_part172_checked

  · exact kid01_part107_checked

  · exact kid01_part137_checked

  · exact kid01_part143_checked

  · exact kid01_part173_checked

  · exact kid01_part132_checked

  · exact kid01_part138_checked

  · exact kid01_part168_checked

  · exact kid01_part198_checked

def kid01_part199 : Audit := .cycle 0 9 true (0)
theorem kid01_part199_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,0⟩)) (kid01_part199) = true := by rfl

def kid01_part200 : Audit := .cycle 1 8 true (1)
theorem kid01_part200_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,1⟩)) (kid01_part200) = true := by rfl

def kid01_part201 : Audit := .cycle 29 1 false (7)
theorem kid01_part201_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,2⟩)) (kid01_part201) = true := by rfl

def kid01_part202 : Audit := .cycle 16 1 false (2)
theorem kid01_part202_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,3⟩)) (kid01_part202) = true := by rfl

def kid01_part204 : Audit := .cycle 0 10 true (0)
theorem kid01_part204_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part204) = true := by rfl

def kid01_part205 : Audit := .cycle 1 9 true (1)
theorem kid01_part205_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part205) = true := by rfl

def kid01_part206 : Audit := .cycle 20 1 false (2)
theorem kid01_part206_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part206) = true := by rfl

def kid01_part207 : Audit := .cycle 17 1 false (1)
theorem kid01_part207_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part207) = true := by rfl

def kid01_part208 : Audit := .split 12 (4,true) (byMove [
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
.cycle 10 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 27 (5,true),
.cycle 1 13 false (3),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
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
.cycle 10 6 true (0),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 21 1 false (3),
.cycle 24 1 false (4),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
]),
.cycle 10 5 false (2),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 10 8 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 23 1 false (1),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 21 1 false (-1),
.cycle 17 1 false (-1),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 2 13 false (3),
.cycle 10 5 false (2),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 11 2 true (0),
.split 13 (5,false) (byMove [
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 23 1 false (1),
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
.cycle 12 3 true (0),
.cycle 0 18 true (-1),
.cycle 23 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 9 16 true (0),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
])
])
theorem kid01_part208_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part208) = true := by rfl

def kid01_part209 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
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
.last 17 (4,true),
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
.cycle 11 5 false (1),
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
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 9 2 true (2),
.cycle 10 1 true (2),
.cycle 17 9 false (2),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 24 5 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 24 5 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 5 false (2),
.cycle 18 5 false (2),
.cycle 13 6 true (0),
.cycle 18 5 false (1),
.cycle 0 20 true (0),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 23 5 false (3),
.cycle 26 5 false (4),
.last 19 (5,true),
.cycle 15 3 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 17 (4,true),
.cycle 16 2 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 17 (4,true),
.cycle 16 2 false (0),
.last 19 (4,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.cycle 11 2 true (0),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.cycle 11 7 false (1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.last 13 (4,true),
.cycle 15 1 false (3),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 2 18 true (0),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.last 13 (4,true),
.cycle 13 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
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
.cycle 21 13 false (2),
.last 21 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.cycle 10 3 true (2)
]),
.cycle 10 1 true (2)
])
theorem kid01_part209_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part209) = true := by rfl

def kid01_part210 : Audit := .cycle 0 10 true (0)
theorem kid01_part210_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part210) = true := by rfl

def kid01_part211 : Audit := .cycle 1 9 true (1)
theorem kid01_part211_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part211) = true := by rfl

def kid01_part212 : Audit := .cycle 0 91 true (0)
theorem kid01_part212_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part212) = true := by rfl

def kid01_part213 : Audit := .cycle 29 1 false (7)
theorem kid01_part213_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part213) = true := by rfl

def kid01_part214 : Audit := .cycle 9 1 true (3)
theorem kid01_part214_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part214) = true := by rfl

def kid01_part216 : Audit := .cycle 0 11 true (0)
theorem kid01_part216_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part216) = true := by rfl

def kid01_part217 : Audit := .cycle 1 10 true (1)
theorem kid01_part217_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part217) = true := by rfl

def kid01_part218 : Audit := .split 21 (5,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (7),
.cycle 26 1 false (6),
.cycle 34 1 false (6),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 25 1 false (5),
.last 24 (4,true),
.cycle 33 1 false (5),
.cycle 35 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 24 1 false (2),
.cycle 2 21 true (0),
.cycle 1 34 true (0),
.cycle 27 1 false (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 29 1 false (5)
])
theorem kid01_part218_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part218) = true := by rfl

def kid01_part219 : Audit := .split 19 (5,true) (byMove [
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
.cycle 32 1 false (4),
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
theorem kid01_part219_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part219) = true := by rfl

def kid01_part220 : Audit := .cycle 9 2 true (3)
theorem kid01_part220_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part220) = true := by rfl

def kid01_part221 : Audit := .split 14 (5,true) (byMove [
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
.cycle 11 7 false (3),
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
theorem kid01_part221_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part221) = true := by rfl

def kid01_part222 : Audit := .cycle 0 11 true (0)
theorem kid01_part222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part222) = true := by rfl

def kid01_part223 : Audit := .cycle 1 10 true (1)
theorem kid01_part223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part223) = true := by rfl

def kid01_part224 : Audit := .split 23 (5,true) (byMove [
.cycle 0 54 true (0),
.cycle 0 127 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 66 25 true (6),
.cycle 33 1 false (9),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 62 23 true (6),
.cycle 31 1 false (9),
.last 24 (4,true),
.cycle 29 1 false (9),
.last 26 (4,true),
.cycle 45 1 false (9),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 22 2 true (2),
.cycle 0 141 true (0),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 33 1 false (9),
.cycle 5 19 true (0),
.last 24 (4,true),
.cycle 26 11 true (6)
])
theorem kid01_part224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part224) = true := by rfl

def kid01_part225 : Audit := .split 21 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 91 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.cycle 27 1 false (7),
.last 23 (4,true),
.cycle 0 26 true (0),
.cycle 33 1 false (9),
.last 22 (4,true),
.cycle 25 1 false (7),
.last 24 (4,true),
.cycle 37 1 false (7),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 29 1 false (7),
.cycle 2 36 true (0),
.last 23 (4,true),
.cycle 35 1 false (9),
.cycle 5 40 true (0),
.last 22 (4,true),
.cycle 3 22 true (0)
])
theorem kid01_part225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part225) = true := by rfl

def kid01_part226 : Audit := .cycle 9 2 true (3)
theorem kid01_part226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part226) = true := by rfl

def kid01_part227 : Audit := .cycle 10 1 true (4)
theorem kid01_part227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part227) = true := by rfl

def kid01_part228 : Audit := .cycle 8 4 true (2)
theorem kid01_part228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part228) = true := by rfl

def kid01_part229 : Audit := .cycle 7 5 true (2)
theorem kid01_part229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part229) = true := by rfl

def kid01_part230 : Audit := .cycle 0 13 true (0)
theorem kid01_part230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part230) = true := by rfl

def kid01_part231 : Audit := .split 19 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 30 1 false (6),
.cycle 23 1 false (5),
.cycle 31 1 false (5),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 22 1 false (4),
.last 22 (4,true),
.cycle 30 1 false (4),
.cycle 32 1 false (6),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 21 1 false (1),
.cycle 2 19 true (0),
.cycle 1 30 true (0),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 19 24 true (3)
])
theorem kid01_part231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part231) = true := by rfl

def kid01_part232 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 9 4 true (3),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 64 25 true (6),
.cycle 37 1 false (9),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 11 2 true (3),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.last 14 (4,true)
])
theorem kid01_part232_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part232) = true := by rfl

def kid01_part233 : Audit := .split 14 (5,true) (byMove [
.cycle 0 27 true (-1),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 29 1 false (7),
.last 16 (4,true),
.cycle 14 37 true (0),
.cycle 21 1 false (5),
.last 15 (4,true),
.cycle 19 1 false (5),
.last 17 (4,true),
.cycle 39 1 false (5),
.cycle 33 1 false (7),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 2 19 true (0),
.last 16 (4,true),
.cycle 31 1 false (7),
.cycle 14 32 true (0),
.last 15 (4,true),
.cycle 17 3 true (3)
])
theorem kid01_part233_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part233) = true := by rfl

def kid01_part234 : Audit := .cycle 0 11 true (0)
theorem kid01_part234_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part234) = true := by rfl

def kid01_part235 : Audit := .cycle 1 10 true (1)
theorem kid01_part235_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part235) = true := by rfl

def kid01_part236 : Audit := .cycle 2 9 true (1)
theorem kid01_part236_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part236) = true := by rfl

def kid01_part237 : Audit := .cycle 2 12 true (1)
theorem kid01_part237_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part237) = true := by rfl

def kid01_part238 : Audit := .cycle 9 2 true (3)
theorem kid01_part238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part238) = true := by rfl

def kid01_part239 : Audit := .cycle 10 1 true (4)
theorem kid01_part239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part239) = true := by rfl

def kid01_part215 : Audit := .split 10 (5,false) (byMove [(kid01_part216),(kid01_part217),(kid01_part218),(kid01_part219),(kid01_part220),(kid01_part221),(kid01_part222),(kid01_part223),(kid01_part224),(kid01_part225),(kid01_part226),(kid01_part227),(kid01_part228),(kid01_part229),(kid01_part230),(kid01_part231),(kid01_part232),(kid01_part233),(kid01_part234),(kid01_part235),(kid01_part236),(kid01_part237),(kid01_part238),(kid01_part239)])

theorem kid01_part215_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part215) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part216),(kid01_part217),(kid01_part218),(kid01_part219),(kid01_part220),(kid01_part221),(kid01_part222),(kid01_part223),(kid01_part224),(kid01_part225),(kid01_part226),(kid01_part227),(kid01_part228),(kid01_part229),(kid01_part230),(kid01_part231),(kid01_part232),(kid01_part233),(kid01_part234),(kid01_part235),(kid01_part236),(kid01_part237),(kid01_part238),(kid01_part239)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part216_checked

  · exact kid01_part222_checked

  · exact kid01_part228_checked

  · exact kid01_part234_checked

  · exact kid01_part217_checked

  · exact kid01_part223_checked

  · exact kid01_part229_checked

  · exact kid01_part235_checked

  · exact kid01_part218_checked

  · exact kid01_part224_checked

  · exact kid01_part230_checked

  · exact kid01_part236_checked

  · exact kid01_part219_checked

  · exact kid01_part225_checked

  · exact kid01_part231_checked

  · exact kid01_part237_checked

  · exact kid01_part220_checked

  · exact kid01_part226_checked

  · exact kid01_part232_checked

  · exact kid01_part238_checked

  · exact kid01_part221_checked

  · exact kid01_part227_checked

  · exact kid01_part233_checked

  · exact kid01_part239_checked

def kid01_part240 : Audit := .cycle 8 3 true (2)
theorem kid01_part240_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part240) = true := by rfl

def kid01_part241 : Audit := .cycle 7 4 true (2)
theorem kid01_part241_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part241) = true := by rfl

def kid01_part242 : Audit := .cycle 0 12 true (0)
theorem kid01_part242_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part242) = true := by rfl

def kid01_part243 : Audit := .cycle 17 1 false (1)
theorem kid01_part243_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part243) = true := by rfl

def kid01_part244 : Audit := .split 12 (4,true) (byMove [
.cycle 10 7 false (2),
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
.cycle 0 28 true (-1),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 15 (5,true),
.cycle 10 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 40 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 23 (5,true),
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.cycle 11 3 false (1),
.last 15 (5,true)
]),
.cycle 16 1 false (2),
.cycle 16 1 false (4),
.cycle 26 12 true (0),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.split 13 (5,true) (byMove [
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (3),
.last 16 (5,false),
.cycle 0 18 true (0),
.cycle 23 1 false (5),
.cycle 16 1 false (4),
.last 16 (5,false),
.last 27 (5,false),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 2 20 true (0),
.last 16 (5,false),
.cycle 16 1 false (2),
.cycle 5 24 true (0),
.cycle 14 3 true (2),
.last 16 (5,false)
]),
.cycle 36 1 false (0),
.cycle 16 1 false (0),
.cycle 18 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 10 8 false (2),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 24 1 false (4),
.cycle 9 13 false (3),
.cycle 18 1 false (2),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 21 1 false (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.last 27 (5,true),
.cycle 16 1 false (0),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 10 6 true (0),
.cycle 1 20 true (0),
.cycle 15 1 false (1),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.split 13 (5,true) (byMove [
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 23 1 false (1),
.last 18 (5,false),
.last 15 (5,false),
.last 15 (5,false),
.cycle 6 8 true (0),
.last 16 (5,false),
.cycle 0 18 true (0),
.cycle 24 10 true (0),
.last 21 (5,false),
.last 16 (5,false),
.cycle 17 1 false (1),
.last 22 (5,false),
.cycle 9 13 false (3),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.last 15 (5,false),
.cycle 2 20 true (0),
.last 16 (5,false),
.cycle 10 6 true (0),
.cycle 5 24 true (0),
.cycle 14 3 true (2),
.last 16 (5,false)
])
])
theorem kid01_part244_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part244) = true := by rfl

def kid01_part246 : Audit := .cycle 0 20 true (0)
theorem kid01_part246_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part246) = true := by rfl

def kid01_part247 : Audit := .cycle 0 14 true (0)
theorem kid01_part247_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part247) = true := by rfl

def kid01_part248 : Audit := .cycle 21 1 false (1)
theorem kid01_part248_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part248) = true := by rfl

def kid01_part249 : Audit := .cycle 0 16 true (0)
theorem kid01_part249_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part249) = true := by rfl

def kid01_part250 : Audit := .split 12 (5,true) (byMove [
.last 19 (4,true),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.cycle 14 2 false (2),
.cycle 22 2 false (2),
.last 18 (4,true),
.last 13 (4,true),
.cycle 14 2 false (2),
.last 15 (4,true),
.cycle 16 2 false (0),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 16 (4,true),
.cycle 15 2 false (1),
.last 18 (4,true),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid01_part250_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part250) = true := by rfl

def kid01_part251 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 5 true (1),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 11 5 false (1),
.cycle 17 1 false (-1),
.cycle 18 7 true (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 16 5 true (1),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.last 15 (4,true),
.cycle 11 2 true (0)
])
theorem kid01_part251_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part251) = true := by rfl

def kid01_part252 : Audit := .cycle 2 10 true (1)
theorem kid01_part252_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part252) = true := by rfl

def kid01_part253 : Audit := .cycle 8 3 true (2)
theorem kid01_part253_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part253) = true := by rfl

def kid01_part254 : Audit := .cycle 1 11 true (1)
theorem kid01_part254_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part254) = true := by rfl

def kid01_part255 : Audit := .cycle 0 12 true (0)
theorem kid01_part255_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part255) = true := by rfl

def kid01_part256 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 9 4 true (2),
.cycle 8 5 true (2),
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
.cycle 9 4 true (2)
])
theorem kid01_part256_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part256) = true := by rfl

def kid01_part257 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 3 false (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 12 1 true (4)
])
theorem kid01_part257_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part257) = true := by rfl

def kid01_part258 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 32 true (0),
.cycle 0 27 true (0),
.cycle 9 5 true (1),
.last 27 (5,true),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 1, 64],[1, 1, 2, 1, 1, 64, 64],64⟩,
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 6 9 true (1)
])
theorem kid01_part258_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part258) = true := by rfl

def kid01_part259 : Audit := .split 17 (4,true) (byMove [
.cycle 11 8 true (0),
.cycle 32 20 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 19 5 false (3),
.cycle 26 5 false (6),
.cycle 0 22 true (0),
.cycle 25 5 false (5),
.cycle 20 5 false (4),
.last 18 (5,true),
.cycle 19 9 true (1),
.cycle 18 5 false (1),
.cycle 21 5 false (3),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 2 24 true (0),
.cycle 1 19 true (0),
.cycle 18 5 false (2),
.cycle 5 36 true (0),
.last 21 (5,true),
.last 18 (5,true)
])
theorem kid01_part259_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part259) = true := by rfl

def kid01_part260 : Audit := .cycle 2 12 true (1)
theorem kid01_part260_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part260) = true := by rfl

def kid01_part261 : Audit := .cycle 18 1 false (0)
theorem kid01_part261_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part261) = true := by rfl

def kid01_part262 : Audit := .split 12 (5,true) (byMove [
.last 19 (4,true),
.last 23 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 14 (4,true),
.last 42 (4,true),
.cycle 17 2 false (3),
.last 13 (4,true),
.cycle 16 2 false (4),
.last 15 (4,true),
.cycle 16 2 false (0),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (4,true),
.last 14 (4,true),
.cycle 15 2 false (1),
.cycle 5 8 true (0),
.last 13 (4,true),
.last 17 (4,true)
])
theorem kid01_part262_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part262) = true := by rfl

def kid01_part263 : Audit := .split 12 (5,true) (byMove [
.cycle 11 7 false (1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 14 (4,true),
.cycle 27 12 true (0),
.cycle 18 1 false (2),
.last 13 (4,true),
.cycle 16 1 false (4),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 6 true (0),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 5 8 true (0),
.last 13 (4,true),
.cycle 14 3 true (2)
])
theorem kid01_part263_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part263) = true := by rfl

def kid01_part264 : Audit := .cycle 2 10 true (1)
theorem kid01_part264_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part264) = true := by rfl

def kid01_part265 : Audit := .cycle 8 3 true (2)
theorem kid01_part265_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part265) = true := by rfl

def kid01_part266 : Audit := .cycle 7 4 true (2)
theorem kid01_part266_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part266) = true := by rfl

def kid01_part267 : Audit := .cycle 0 12 true (0)
theorem kid01_part267_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part267) = true := by rfl

def kid01_part268 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid01_part268_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part268) = true := by rfl

def kid01_part269 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 12 1 true (4)
])
theorem kid01_part269_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part269) = true := by rfl

def kid01_part245 : Audit := .split 10 (5,false) (byMove [(kid01_part246),(kid01_part247),(kid01_part248),(kid01_part249),(kid01_part250),(kid01_part251),(kid01_part252),(kid01_part253),(kid01_part254),(kid01_part255),(kid01_part256),(kid01_part257),(kid01_part258),(kid01_part259),(kid01_part260),(kid01_part261),(kid01_part262),(kid01_part263),(kid01_part264),(kid01_part265),(kid01_part266),(kid01_part267),(kid01_part268),(kid01_part269)])

theorem kid01_part245_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part245) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid01_part246),(kid01_part247),(kid01_part248),(kid01_part249),(kid01_part250),(kid01_part251),(kid01_part252),(kid01_part253),(kid01_part254),(kid01_part255),(kid01_part256),(kid01_part257),(kid01_part258),(kid01_part259),(kid01_part260),(kid01_part261),(kid01_part262),(kid01_part263),(kid01_part264),(kid01_part265),(kid01_part266),(kid01_part267),(kid01_part268),(kid01_part269)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part246_checked

  · exact kid01_part252_checked

  · exact kid01_part258_checked

  · exact kid01_part264_checked

  · exact kid01_part247_checked

  · exact kid01_part253_checked

  · exact kid01_part259_checked

  · exact kid01_part265_checked

  · exact kid01_part248_checked

  · exact kid01_part254_checked

  · exact kid01_part260_checked

  · exact kid01_part266_checked

  · exact kid01_part249_checked

  · exact kid01_part255_checked

  · exact kid01_part261_checked

  · exact kid01_part267_checked

  · exact kid01_part250_checked

  · exact kid01_part256_checked

  · exact kid01_part262_checked

  · exact kid01_part268_checked

  · exact kid01_part251_checked

  · exact kid01_part257_checked

  · exact kid01_part263_checked

  · exact kid01_part269_checked

def kid01_part270 : Audit := .cycle 0 10 true (0)
theorem kid01_part270_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part270) = true := by rfl

def kid01_part271 : Audit := .cycle 1 9 true (1)
theorem kid01_part271_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part271) = true := by rfl

def kid01_part272 : Audit := .cycle 2 8 true (1)
theorem kid01_part272_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part272) = true := by rfl

def kid01_part273 : Audit := .cycle 2 11 true (1)
theorem kid01_part273_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part273) = true := by rfl

def kid01_part274 : Audit := .cycle 9 1 true (3)
theorem kid01_part274_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part274) = true := by rfl

def kid01_part275 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 1 11 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
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
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 35 1 false (3),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 9 3 true (3),
.cycle 17 1 false (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 32 1 false (4),
.last 14 (4,true),
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
.cycle 8 13 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 39 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 4, 64],[4, 16, 40, 1, 64, 32, 64],64⟩,
.cycle 6 15 true (2),
.last 22 (4,true),
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.last 21 (4,true),
.cycle 0 27 true (0),
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
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 9 4 true (3),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 7 8 true (2),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.last 14 (5,true),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 15 true (0),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true),
.cycle 8 8 true (2),
.last 16 (5,true),
.cycle 2 13 true (1),
.last 19 (5,true),
.last 13 (5,true),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true)
]),
.split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 46 1 false (4),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 24 1 false (6),
.last 14 (4,true),
.last 18 (4,true),
.cycle 2 13 true (1),
.cycle 27 1 false (3),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid01_part275_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part275) = true := by rfl

def kid01_part203 : Audit := .split 9 (4,false) (byMove [(kid01_part204),(kid01_part205),(kid01_part206),(kid01_part207),(kid01_part208),(kid01_part209),(kid01_part210),(kid01_part211),(kid01_part212),(kid01_part213),(kid01_part214),(kid01_part215),(kid01_part240),(kid01_part241),(kid01_part242),(kid01_part243),(kid01_part244),(kid01_part245),(kid01_part270),(kid01_part271),(kid01_part272),(kid01_part273),(kid01_part274),(kid01_part275)])

theorem kid01_part203_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (kid01_part203) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid01_part204),(kid01_part205),(kid01_part206),(kid01_part207),(kid01_part208),(kid01_part209),(kid01_part210),(kid01_part211),(kid01_part212),(kid01_part213),(kid01_part214),(kid01_part215),(kid01_part240),(kid01_part241),(kid01_part242),(kid01_part243),(kid01_part244),(kid01_part245),(kid01_part270),(kid01_part271),(kid01_part272),(kid01_part273),(kid01_part274),(kid01_part275)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part204_checked

  · exact kid01_part210_checked

  · exact kid01_part240_checked

  · exact kid01_part270_checked

  · exact kid01_part205_checked

  · exact kid01_part211_checked

  · exact kid01_part241_checked

  · exact kid01_part271_checked

  · exact kid01_part206_checked

  · exact kid01_part212_checked

  · exact kid01_part242_checked

  · exact kid01_part272_checked

  · exact kid01_part207_checked

  · exact kid01_part213_checked

  · exact kid01_part243_checked

  · exact kid01_part273_checked

  · exact kid01_part208_checked

  · exact kid01_part214_checked

  · exact kid01_part244_checked

  · exact kid01_part274_checked

  · exact kid01_part209_checked

  · exact kid01_part215_checked

  · exact kid01_part245_checked

  · exact kid01_part275_checked

def kid01_part277 : Audit := .cycle 0 10 true (0)
theorem kid01_part277_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part277) = true := by rfl

def kid01_part278 : Audit := .cycle 1 9 true (1)
theorem kid01_part278_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part278) = true := by rfl

def kid01_part279 : Audit := .cycle 20 1 false (2)
theorem kid01_part279_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part279) = true := by rfl

def kid01_part280 : Audit := .cycle 17 1 false (1)
theorem kid01_part280_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part280) = true := by rfl

def kid01_part281 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
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
.cycle 11 5 false (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 24 1 false (2),
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
.last 17 (5,true),
.cycle 16 2 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 2 false (2),
.cycle 23 2 false (3),
.last 14 (5,true),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (2),
.cycle 17 9 false (2),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 24 5 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 24 5 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 5 false (2),
.cycle 18 5 false (2),
.cycle 13 6 true (0),
.cycle 18 5 false (1),
.cycle 0 20 true (0),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 23 5 false (3),
.cycle 26 5 false (4),
.cycle 15 3 true (0),
.last 19 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.cycle 11 7 false (1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.cycle 15 1 false (3),
.last 13 (5,true),
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 2 18 true (0),
.last 14 (5,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
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
.last 17 (5,true),
.cycle 16 2 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 17 (5,true),
.cycle 16 2 false (0),
.last 19 (5,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 17 (5,true),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.last 14 (5,true),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 16 3 false (0),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 10 3 true (2),
.cycle 9 4 true (2),
.cycle 21 13 false (2),
.last 21 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (2),
.cycle 11 2 true (2)
])
])
theorem kid01_part281_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part281) = true := by rfl

def kid01_part282 : Audit := .split 12 (5,true) (byMove [
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
.cycle 10 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 27 (4,true),
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
.cycle 10 6 true (0),
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
.cycle 10 5 false (2),
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
.cycle 15 1 false (1),
.cycle 23 1 false (1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 21 1 false (-1),
.cycle 17 1 false (-1),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 2 13 false (3),
.cycle 10 5 false (2),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.split 13 (4,false) (byMove [
.cycle 22 1 false (2),
.cycle 15 1 false (1),
.cycle 23 1 false (1),
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
.cycle 12 3 true (0),
.cycle 0 18 true (-1),
.cycle 23 1 false (3),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 9 16 true (0),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
]),
.cycle 11 2 true (0)
])
theorem kid01_part282_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part282) = true := by rfl

def kid01_part283 : Audit := .cycle 0 10 true (0)
theorem kid01_part283_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part283) = true := by rfl

def kid01_part284 : Audit := .cycle 1 9 true (1)
theorem kid01_part284_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part284) = true := by rfl

def kid01_part285 : Audit := .cycle 0 91 true (0)
theorem kid01_part285_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part285) = true := by rfl

def kid01_part286 : Audit := .cycle 29 1 false (7)
theorem kid01_part286_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part286) = true := by rfl

def kid01_part288 : Audit := .cycle 0 11 true (0)
theorem kid01_part288_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part288) = true := by rfl

def kid01_part289 : Audit := .cycle 1 10 true (1)
theorem kid01_part289_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part289) = true := by rfl

def kid01_part290 : Audit := .split 21 (4,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (3),
.cycle 33 1 false (7),
.cycle 26 1 false (6),
.cycle 34 1 false (6),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.last 22 (5,true),
.last 24 (5,true),
.cycle 33 1 false (5),
.cycle 35 1 false (7),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 20 2 true (2),
.cycle 2 21 true (0),
.cycle 1 34 true (0),
.cycle 27 1 false (5),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.last 22 (5,true)
])
theorem kid01_part290_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part290) = true := by rfl

def kid01_part291 : Audit := .split 19 (4,true) (byMove [
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
.cycle 32 1 false (4),
.cycle 25 1 false (3),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 32 1 false (6),
.cycle 0 22 true (0),
.cycle 34 1 false (6)
])
theorem kid01_part291_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part291) = true := by rfl

def kid01_part292 : Audit := .split 14 (4,true) (byMove [
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
.cycle 11 7 false (3),
.cycle 19 1 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 26 1 false (4),
.cycle 13 2 true (0),
.cycle 12 4 true (0)
])
theorem kid01_part292_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part292) = true := by rfl

def kid01_part293 : Audit := .cycle 9 2 true (3)
theorem kid01_part293_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part293) = true := by rfl

def kid01_part294 : Audit := .cycle 0 11 true (0)
theorem kid01_part294_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part294) = true := by rfl

def kid01_part295 : Audit := .cycle 1 10 true (1)
theorem kid01_part295_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part295) = true := by rfl

def kid01_part296 : Audit := .split 23 (4,true) (byMove [
.cycle 0 54 true (0),
.cycle 0 127 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.cycle 66 25 true (6),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 62 23 true (6),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.last 24 (5,true),
.last 26 (5,true),
.cycle 45 1 false (9),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 0 141 true (0),
.cycle 22 2 true (2),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 33 1 false (9),
.cycle 5 19 true (0),
.cycle 26 11 true (6),
.last 24 (5,true)
])
theorem kid01_part296_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part296) = true := by rfl

def kid01_part297 : Audit := .split 21 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 91 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 35 1 false (9),
.cycle 27 1 false (7),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 33 1 false (9),
.cycle 25 1 false (7),
.last 22 (5,true),
.last 24 (5,true),
.cycle 37 1 false (7),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 29 1 false (7),
.cycle 20 2 true (2),
.cycle 2 36 true (0),
.last 23 (5,true),
.cycle 35 1 false (9),
.cycle 5 40 true (0),
.cycle 3 22 true (0),
.last 22 (5,true)
])
theorem kid01_part297_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part297) = true := by rfl

def kid01_part298 : Audit := .cycle 10 1 true (4)
theorem kid01_part298_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part298) = true := by rfl

def kid01_part299 : Audit := .cycle 9 2 true (3)
theorem kid01_part299_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part299) = true := by rfl

def kid01_part300 : Audit := .cycle 8 4 true (2)
theorem kid01_part300_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part300) = true := by rfl

def kid01_part301 : Audit := .cycle 7 5 true (2)
theorem kid01_part301_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part301) = true := by rfl

def kid01_part302 : Audit := .cycle 0 13 true (0)
theorem kid01_part302_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part302) = true := by rfl

def kid01_part303 : Audit := .split 19 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 30 1 false (6),
.cycle 23 1 false (5),
.cycle 31 1 false (5),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.last 20 (5,true),
.last 22 (5,true),
.cycle 30 1 false (4),
.cycle 32 1 false (6),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 2 19 true (0),
.cycle 1 30 true (0),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.cycle 19 24 true (3),
.last 20 (5,true)
])
theorem kid01_part303_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part303) = true := by rfl

def kid01_part304 : Audit := .split 14 (4,true) (byMove [
.cycle 0 27 true (-1),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 29 1 false (7),
.last 16 (5,true),
.cycle 14 37 true (0),
.cycle 21 1 false (5),
.cycle 19 1 false (5),
.last 15 (5,true),
.last 17 (5,true),
.cycle 39 1 false (5),
.cycle 33 1 false (7),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 2 19 true (0),
.last 16 (5,true),
.cycle 31 1 false (7),
.cycle 14 32 true (0),
.cycle 17 3 true (3),
.last 15 (5,true)
])
theorem kid01_part304_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part304) = true := by rfl

def kid01_part305 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 64 25 true (6),
.cycle 37 1 false (9),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.last 20 (5,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 9 4 true (3)
])
theorem kid01_part305_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part305) = true := by rfl

def kid01_part306 : Audit := .cycle 0 11 true (0)
theorem kid01_part306_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part306) = true := by rfl

def kid01_part307 : Audit := .cycle 1 10 true (1)
theorem kid01_part307_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part307) = true := by rfl

def kid01_part308 : Audit := .cycle 2 9 true (1)
theorem kid01_part308_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part308) = true := by rfl

def kid01_part309 : Audit := .cycle 2 12 true (1)
theorem kid01_part309_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part309) = true := by rfl

def kid01_part310 : Audit := .cycle 10 1 true (4)
theorem kid01_part310_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part310) = true := by rfl

def kid01_part311 : Audit := .cycle 9 2 true (3)
theorem kid01_part311_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part311) = true := by rfl

def kid01_part287 : Audit := .split 10 (4,false) (byMove [(kid01_part288),(kid01_part289),(kid01_part290),(kid01_part291),(kid01_part292),(kid01_part293),(kid01_part294),(kid01_part295),(kid01_part296),(kid01_part297),(kid01_part298),(kid01_part299),(kid01_part300),(kid01_part301),(kid01_part302),(kid01_part303),(kid01_part304),(kid01_part305),(kid01_part306),(kid01_part307),(kid01_part308),(kid01_part309),(kid01_part310),(kid01_part311)])

theorem kid01_part287_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part287) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid01_part288),(kid01_part289),(kid01_part290),(kid01_part291),(kid01_part292),(kid01_part293),(kid01_part294),(kid01_part295),(kid01_part296),(kid01_part297),(kid01_part298),(kid01_part299),(kid01_part300),(kid01_part301),(kid01_part302),(kid01_part303),(kid01_part304),(kid01_part305),(kid01_part306),(kid01_part307),(kid01_part308),(kid01_part309),(kid01_part310),(kid01_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part288_checked

  · exact kid01_part294_checked

  · exact kid01_part300_checked

  · exact kid01_part306_checked

  · exact kid01_part289_checked

  · exact kid01_part295_checked

  · exact kid01_part301_checked

  · exact kid01_part307_checked

  · exact kid01_part290_checked

  · exact kid01_part296_checked

  · exact kid01_part302_checked

  · exact kid01_part308_checked

  · exact kid01_part291_checked

  · exact kid01_part297_checked

  · exact kid01_part303_checked

  · exact kid01_part309_checked

  · exact kid01_part292_checked

  · exact kid01_part298_checked

  · exact kid01_part304_checked

  · exact kid01_part310_checked

  · exact kid01_part293_checked

  · exact kid01_part299_checked

  · exact kid01_part305_checked

  · exact kid01_part311_checked

def kid01_part312 : Audit := .cycle 9 1 true (3)
theorem kid01_part312_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part312) = true := by rfl

def kid01_part313 : Audit := .cycle 8 3 true (2)
theorem kid01_part313_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part313) = true := by rfl

def kid01_part314 : Audit := .cycle 7 4 true (2)
theorem kid01_part314_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part314) = true := by rfl

def kid01_part315 : Audit := .cycle 0 12 true (0)
theorem kid01_part315_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part315) = true := by rfl

def kid01_part316 : Audit := .cycle 17 1 false (1)
theorem kid01_part316_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part316) = true := by rfl

def kid01_part318 : Audit := .cycle 0 20 true (0)
theorem kid01_part318_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part318) = true := by rfl

def kid01_part319 : Audit := .cycle 0 14 true (0)
theorem kid01_part319_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part319) = true := by rfl

def kid01_part320 : Audit := .cycle 21 1 false (1)
theorem kid01_part320_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part320) = true := by rfl

def kid01_part321 : Audit := .cycle 0 16 true (0)
theorem kid01_part321_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part321) = true := by rfl

def kid01_part322 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 16 5 true (1),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 11 5 false (1),
.cycle 17 1 false (-1),
.cycle 18 7 true (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 16 5 true (1),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.last 15 (5,true)
])
theorem kid01_part322_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part322) = true := by rfl

def kid01_part323 : Audit := .split 12 (4,true) (byMove [
.last 19 (5,true),
.last 20 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.cycle 14 2 false (2),
.cycle 22 2 false (2),
.last 18 (5,true),
.cycle 14 2 false (2),
.last 13 (5,true),
.last 15 (5,true),
.cycle 16 2 false (0),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 16 true (0),
.last 16 (5,true),
.cycle 15 2 false (1),
.last 18 (5,true),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid01_part323_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part323) = true := by rfl

def kid01_part324 : Audit := .cycle 2 10 true (1)
theorem kid01_part324_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part324) = true := by rfl

def kid01_part325 : Audit := .cycle 8 3 true (2)
theorem kid01_part325_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part325) = true := by rfl

def kid01_part326 : Audit := .cycle 1 11 true (1)
theorem kid01_part326_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part326) = true := by rfl

def kid01_part327 : Audit := .cycle 0 12 true (0)
theorem kid01_part327_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part327) = true := by rfl

def kid01_part328 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.last 14 (5,true)
])
theorem kid01_part328_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part328) = true := by rfl

def kid01_part329 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 4 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 9 4 true (2),
.cycle 9 3 true (2),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 4 true (2),
.last 13 (4,true)
])
theorem kid01_part329_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part329) = true := by rfl

def kid01_part330 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 19 9 false (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 32 true (0),
.cycle 0 27 true (0),
.last 27 (4,true),
.cycle 9 5 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 1, 16, 64],[1, 1, 2, 1, 64, 1, 64],64⟩,
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 19 9 false (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (1),
.last 15 (4,true)
])
theorem kid01_part330_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part330) = true := by rfl

def kid01_part331 : Audit := .split 17 (5,true) (byMove [
.cycle 11 8 true (0),
.cycle 32 20 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 19 5 false (3),
.cycle 26 5 false (6),
.cycle 0 22 true (0),
.cycle 25 5 false (5),
.last 18 (4,true),
.cycle 20 5 false (4),
.cycle 19 9 true (1),
.cycle 18 5 false (1),
.cycle 21 5 false (3),
.cycle 18 1 false (0),
.cycle 18 5 false (0),
.cycle 18 5 false (0),
.cycle 2 24 true (0),
.cycle 1 19 true (0),
.cycle 18 5 false (2),
.cycle 5 36 true (0),
.last 18 (4,true),
.last 21 (4,true)
])
theorem kid01_part331_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part331) = true := by rfl

def kid01_part332 : Audit := .cycle 2 12 true (1)
theorem kid01_part332_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part332) = true := by rfl

def kid01_part333 : Audit := .cycle 18 1 false (0)
theorem kid01_part333_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part333) = true := by rfl

def kid01_part334 : Audit := .split 12 (4,true) (byMove [
.cycle 11 7 false (1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.last 14 (5,true),
.cycle 27 12 true (0),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.last 13 (5,true),
.last 15 (5,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 true (0),
.last 14 (5,true),
.cycle 16 1 false (0),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.last 13 (5,true)
])
theorem kid01_part334_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part334) = true := by rfl

def kid01_part335 : Audit := .split 12 (4,true) (byMove [
.last 19 (5,true),
.last 23 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 14 (5,true),
.last 42 (5,true),
.cycle 17 2 false (3),
.cycle 16 2 false (4),
.last 13 (5,true),
.last 15 (5,true),
.cycle 16 2 false (0),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 15 2 false (1),
.cycle 5 8 true (0),
.last 17 (5,true),
.last 13 (5,true)
])
theorem kid01_part335_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part335) = true := by rfl

def kid01_part336 : Audit := .cycle 2 10 true (1)
theorem kid01_part336_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part336) = true := by rfl

def kid01_part337 : Audit := .cycle 8 3 true (2)
theorem kid01_part337_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part337) = true := by rfl

def kid01_part338 : Audit := .cycle 7 4 true (2)
theorem kid01_part338_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part338) = true := by rfl

def kid01_part339 : Audit := .cycle 0 12 true (0)
theorem kid01_part339_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part339) = true := by rfl

def kid01_part340 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 15 3 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.last 14 (5,true)
])
theorem kid01_part340_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part340) = true := by rfl

def kid01_part341 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.last 13 (4,true)
])
theorem kid01_part341_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part341) = true := by rfl

def kid01_part317 : Audit := .split 10 (4,false) (byMove [(kid01_part318),(kid01_part319),(kid01_part320),(kid01_part321),(kid01_part322),(kid01_part323),(kid01_part324),(kid01_part325),(kid01_part326),(kid01_part327),(kid01_part328),(kid01_part329),(kid01_part330),(kid01_part331),(kid01_part332),(kid01_part333),(kid01_part334),(kid01_part335),(kid01_part336),(kid01_part337),(kid01_part338),(kid01_part339),(kid01_part340),(kid01_part341)])

theorem kid01_part317_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part317) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid01_part318),(kid01_part319),(kid01_part320),(kid01_part321),(kid01_part322),(kid01_part323),(kid01_part324),(kid01_part325),(kid01_part326),(kid01_part327),(kid01_part328),(kid01_part329),(kid01_part330),(kid01_part331),(kid01_part332),(kid01_part333),(kid01_part334),(kid01_part335),(kid01_part336),(kid01_part337),(kid01_part338),(kid01_part339),(kid01_part340),(kid01_part341)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part318_checked

  · exact kid01_part324_checked

  · exact kid01_part330_checked

  · exact kid01_part336_checked

  · exact kid01_part319_checked

  · exact kid01_part325_checked

  · exact kid01_part331_checked

  · exact kid01_part337_checked

  · exact kid01_part320_checked

  · exact kid01_part326_checked

  · exact kid01_part332_checked

  · exact kid01_part338_checked

  · exact kid01_part321_checked

  · exact kid01_part327_checked

  · exact kid01_part333_checked

  · exact kid01_part339_checked

  · exact kid01_part322_checked

  · exact kid01_part328_checked

  · exact kid01_part334_checked

  · exact kid01_part340_checked

  · exact kid01_part323_checked

  · exact kid01_part329_checked

  · exact kid01_part335_checked

  · exact kid01_part341_checked

def kid01_part342 : Audit := .split 12 (5,true) (byMove [
.cycle 10 7 false (2),
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
.cycle 0 28 true (-1),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 14 1 false (0),
.cycle 10 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 40 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 23 (4,true),
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.last 15 (4,true),
.cycle 11 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.cycle 16 1 false (4),
.cycle 26 12 true (0),
.cycle 17 1 false (3),
.split 13 (4,true) (byMove [
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.last 16 (4,false),
.cycle 0 18 true (0),
.cycle 23 1 false (5),
.last 16 (4,false),
.cycle 16 1 false (4),
.last 27 (4,false),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 2 20 true (0),
.last 16 (4,false),
.cycle 16 1 false (2),
.cycle 5 24 true (0),
.last 16 (4,false),
.cycle 14 3 true (2)
]),
.cycle 16 1 false (4),
.cycle 36 1 false (0),
.cycle 16 1 false (0),
.cycle 18 1 false (2),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 10 8 false (2),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 24 1 false (4),
.cycle 9 13 false (3),
.cycle 18 1 false (2),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 21 1 false (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 10 7 false (2),
.last 27 (4,true),
.cycle 16 1 false (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 10 6 true (0),
.cycle 1 20 true (0),
.cycle 15 1 false (1),
.cycle 5 8 true (0),
.split 13 (4,true) (byMove [
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 23 1 false (1),
.last 18 (4,false),
.last 15 (4,false),
.last 15 (4,false),
.cycle 6 8 true (0),
.last 16 (4,false),
.cycle 0 18 true (0),
.cycle 24 10 true (0),
.last 16 (4,false),
.last 21 (4,false),
.cycle 17 1 false (1),
.last 22 (4,false),
.cycle 9 13 false (3),
.cycle 18 1 false (2),
.last 15 (4,false),
.cycle 12 2 true (0),
.cycle 2 20 true (0),
.last 16 (4,false),
.cycle 10 6 true (0),
.cycle 5 24 true (0),
.last 16 (4,false),
.cycle 14 3 true (2)
]),
.cycle 14 3 true (2)
])
theorem kid01_part342_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part342) = true := by rfl

def kid01_part343 : Audit := .cycle 0 10 true (0)
theorem kid01_part343_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part343) = true := by rfl

def kid01_part344 : Audit := .cycle 1 9 true (1)
theorem kid01_part344_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part344) = true := by rfl

def kid01_part345 : Audit := .cycle 2 8 true (1)
theorem kid01_part345_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part345) = true := by rfl

def kid01_part346 : Audit := .cycle 2 11 true (1)
theorem kid01_part346_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part346) = true := by rfl

def kid01_part347 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 1 11 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 35 1 false (3),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 17 1 false (1),
.cycle 9 3 true (3),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 32 1 false (4),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.split 11 (5,true) (byMove [
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
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 2 20 true (1),
.cycle 8 13 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 39 1 false (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 4, 16, 64],[4, 32, 24, 1, 16, 64, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.last 22 (5,true),
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.cycle 0 27 true (0),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
]),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 6 5 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 7 8 true (2),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 7 8 true (2),
.cycle 9 4 true (3),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
]),
.cycle 0 15 true (0),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 46 1 false (4),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.last 12 (5,true),
.last 14 (5,true),
.last 18 (5,true),
.cycle 2 13 true (1),
.cycle 27 1 false (3),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.last 12 (5,true)
]),
.split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 18 3 false (0),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3),
.cycle 8 8 true (2),
.last 16 (4,true),
.cycle 2 13 true (1),
.last 19 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid01_part347_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part347) = true := by rfl

def kid01_part348 : Audit := .cycle 9 1 true (3)
theorem kid01_part348_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part348) = true := by rfl

def kid01_part276 : Audit := .split 9 (5,false) (byMove [(kid01_part277),(kid01_part278),(kid01_part279),(kid01_part280),(kid01_part281),(kid01_part282),(kid01_part283),(kid01_part284),(kid01_part285),(kid01_part286),(kid01_part287),(kid01_part312),(kid01_part313),(kid01_part314),(kid01_part315),(kid01_part316),(kid01_part317),(kid01_part342),(kid01_part343),(kid01_part344),(kid01_part345),(kid01_part346),(kid01_part347),(kid01_part348)])

theorem kid01_part276_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (kid01_part276) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part277),(kid01_part278),(kid01_part279),(kid01_part280),(kid01_part281),(kid01_part282),(kid01_part283),(kid01_part284),(kid01_part285),(kid01_part286),(kid01_part287),(kid01_part312),(kid01_part313),(kid01_part314),(kid01_part315),(kid01_part316),(kid01_part317),(kid01_part342),(kid01_part343),(kid01_part344),(kid01_part345),(kid01_part346),(kid01_part347),(kid01_part348)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part277_checked

  · exact kid01_part283_checked

  · exact kid01_part313_checked

  · exact kid01_part343_checked

  · exact kid01_part278_checked

  · exact kid01_part284_checked

  · exact kid01_part314_checked

  · exact kid01_part344_checked

  · exact kid01_part279_checked

  · exact kid01_part285_checked

  · exact kid01_part315_checked

  · exact kid01_part345_checked

  · exact kid01_part280_checked

  · exact kid01_part286_checked

  · exact kid01_part316_checked

  · exact kid01_part346_checked

  · exact kid01_part281_checked

  · exact kid01_part287_checked

  · exact kid01_part317_checked

  · exact kid01_part347_checked

  · exact kid01_part282_checked

  · exact kid01_part312_checked

  · exact kid01_part342_checked

  · exact kid01_part348_checked

def kid01_part349 : Audit := .cycle 13 5 false (1)
theorem kid01_part349_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (kid01_part349) = true := by rfl

def kid01_part350 : Audit := .cycle 12 3 false (0)
theorem kid01_part350_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (kid01_part350) = true := by rfl

def kid01_part351 : Audit := .cycle 0 11 true (0)
theorem kid01_part351_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (kid01_part351) = true := by rfl

def kid01_part352 : Audit := .cycle 14 1 false (0)
theorem kid01_part352_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,3⟩)) (kid01_part352) = true := by rfl

def kid01_part354 : Audit := .cycle 0 13 true (0)
theorem kid01_part354_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part354) = true := by rfl

def kid01_part355 : Audit := .split 17 (4,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.cycle 16 15 false (2),
.cycle 1 18 false (3),
.split 18 (5,false) (byMove [
.cycle 0 23 true (-2),
.cycle 1 18 false (3),
.cycle 16 17 false (2),
.cycle 10 18 true (-2),
.last 51 (5,true),
.last 20 (5,true),
.cycle 15 4 true (0),
.cycle 0 26 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.cycle 0 23 true (-2),
.last 20 (5,true),
.last 22 (5,true),
.cycle 16 18 false (2),
.cycle 13 6 true (-1),
.cycle 16 15 false (2),
.cycle 9 10 false (2),
.last 20 (5,true),
.last 22 (5,true),
.last 28 (5,true),
.cycle 0 21 true (-2),
.cycle 0 28 true (-2),
.cycle 8 12 false (2),
.last 20 (5,true)
]),
.cycle 0 30 true (-2),
.cycle 0 23 true (-2),
.cycle 0 31 true (-2),
.cycle 0 19 true (-2),
.cycle 0 32 true (-2),
.split 18 (5,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 10 17 false (2),
.cycle 10 15 false (2),
.cycle 0 32 true (-2),
.last 19 (5,false),
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 32 64 true (-2),
.cycle 0 117 true (-3),
.cycle 0 32 true (-2),
.last 19 (5,false),
.cycle 15 4 true (1),
.cycle 0 26 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.cycle 0 23 true (-2),
.last 19 (5,false),
.cycle 15 17 true (1),
.cycle 1 18 true (-2),
.cycle 0 30 true (-2),
.cycle 0 33 true (-2),
.cycle 0 25 true (-2),
.last 19 (5,false)
]),
.cycle 10 16 false (2),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.cycle 10 13 false (2),
.cycle 0 34 true (-2),
.split 18 (5,false) (byMove [
.last 24 (5,true),
.cycle 0 34 true (-2),
.cycle 10 15 false (2),
.cycle 0 36 true (-2),
.cycle 16 12 false (2),
.last 20 (5,true),
.cycle 0 26 true (-2),
.cycle 0 36 true (-2),
.cycle 0 23 true (-2),
.cycle 0 32 true (-2),
.cycle 17 2 true (0),
.last 19 (5,true),
.last 22 (5,true),
.cycle 10 16 false (2),
.cycle 0 28 true (-2),
.cycle 10 13 false (2),
.cycle 9 10 false (2),
.last 20 (5,true),
.last 28 (5,true),
.last 24 (5,true),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.last 20 (5,true),
.last 19 (5,true)
]),
.cycle 2 17 true (-2),
.cycle 16 2 true (1),
.cycle 0 24 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 10, 64, 64],[4, 1, 10, 1, 8, 64, 64],96⟩,
.cycle 16 4 true (1),
.split 18 (5,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 24 true (-2),
.cycle 0 32 true (-2),
.cycle 0 20 true (-2),
.last 20 (5,false),
.last 20 (5,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 10, 64, 64],[4, 1, 10, 1, 32, 1, 64],96⟩,
.cycle 0 31 true (-2),
.cycle 10 16 true (-2),
.cycle 0 29 true (-2),
.cycle 1 19 true (-2),
.last 19 (5,false),
.cycle 0 26 true (-2),
.cycle 0 36 true (-2),
.cycle 0 23 true (-2),
.cycle 0 32 true (-2),
.cycle 17 2 true (1),
.last 20 (5,false),
.cycle 15 17 true (1),
.cycle 16 17 true (1),
.cycle 2 17 true (-2),
.cycle 0 33 true (-2),
.cycle 16 4 true (1),
.last 19 (5,false)
])
])
theorem kid01_part355_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part355) = true := by rfl

def kid01_part356 : Audit := .cycle 21 1 false (-1)
theorem kid01_part356_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part356) = true := by rfl

def kid01_part357 : Audit := .split 13 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 0 19 true (-1),
.cycle 24 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 11 4 true (0),
.cycle 19 1 false (-1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.last 16 (5,true),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 10 6 true (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.last 18 (5,true),
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 9 6 true (0),
.last 16 (5,true)
]),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 24 1 false (0),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 24 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.last 15 (5,false),
.cycle 11 4 true (1),
.cycle 19 1 false (-1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (1),
.cycle 26 1 false (2),
.cycle 0 17 true (0),
.last 15 (5,false)
]),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 25 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 12 6 false (2),
.cycle 34 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 13 2 true (0),
.last 15 (5,true),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 12 5 false (2),
.cycle 12 3 false (2),
.cycle 18 1 false (-2),
.cycle 0 30 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.split 14 (5,true) (byMove [
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 25 1 false (-1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 0 29 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 27 1 false (1),
.last 15 (5,false),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 13 2 true (1),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 31 true (0),
.cycle 0 17 true (0),
.last 15 (5,false)
])
])
theorem kid01_part357_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part357) = true := by rfl

def kid01_part358 : Audit := .split 10 (4,true) (byMove [
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
.cycle 15 4 true (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 14 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 6 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 17 (5,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.last 14 (5,true)
]),
.cycle 22 1 false (2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 11 1 false (1),
.split 11 (5,false) (byMove [
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.last 12 (5,true),
.last 15 (5,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.last 14 (5,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 12 (5,true)
]),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 26 1 false (2),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.last 34 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 26 1 false (2),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.last 29 (5,true),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 2 13 true (0),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 16 1 false (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.last 16 (5,true),
.cycle 10 2 true (0),
.last 12 (5,true),
.last 27 (5,true),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 12 4 true (2),
.last 12 (5,true),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 38 (5,true),
.cycle 16 1 false (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 2 11 true (0),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 12 (5,true)
])
])
theorem kid01_part358_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part358) = true := by rfl

def kid01_part360 : Audit := .cycle 0 15 true (-1)
theorem kid01_part360_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part360) = true := by rfl

def kid01_part361 : Audit := .split 20 (5,false) (byMove [
.last 27 (4,true),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 23 (4,true),
.cycle 17 5 false (1),
.last 25 (4,true),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 10 12 true (-2),
.last 23 (4,true),
.cycle 17 5 false (1),
.last 25 (4,true),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 23 (4,true),
.last 24 (4,true),
.last 25 (4,true),
.cycle 14 7 false (1),
.cycle 9 12 false (1),
.last 24 (4,true)
])
theorem kid01_part361_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part361) = true := by rfl

def kid01_part362 : Audit := .cycle 12 1 false (0)
theorem kid01_part362_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part362) = true := by rfl

def kid01_part363 : Audit := .cycle 11 1 false (-1)
theorem kid01_part363_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part363) = true := by rfl

def kid01_part364 : Audit := .split 12 (5,false) (byMove [
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
.last 15 (4,true),
.cycle 11 5 false (-1),
.last 40 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 28 (4,true),
.cycle 18 7 false (1),
.cycle 9 4 false (1),
.last 17 (4,true)
])
theorem kid01_part364_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part364) = true := by rfl

def kid01_part365 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 15 1 true (1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.last 18 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.last 25 (4,true),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.cycle 18 1 true (-2)
])
theorem kid01_part365_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part365) = true := by rfl

def kid01_part366 : Audit := .split 13 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 23 (5,false),
.last 16 (5,false),
.last 24 (5,false),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 11 3 false (2),
.last 18 (5,false),
.last 25 (5,false),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 0 15 true (0)
])
theorem kid01_part366_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part366) = true := by rfl

def kid01_part367 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 18 (4,true),
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 14 2 true (-1),
.cycle 12 12 true (-1),
.last 18 (4,true),
.cycle 11 5 false (2),
.last 20 (4,true),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 9 7 false (2),
.cycle 12 12 true (-1)
])
theorem kid01_part367_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part367) = true := by rfl

def kid01_part368 : Audit := .cycle 0 13 true (0)
theorem kid01_part368_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part368) = true := by rfl

def kid01_part369 : Audit := .cycle 11 1 false (1)
theorem kid01_part369_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part369) = true := by rfl

def kid01_part370 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 15 (4,true),
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.cycle 16 1 true (2),
.last 15 (4,true),
.cycle 11 5 false (1),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 9 4 true (0),
.cycle 16 1 true (2)
])
theorem kid01_part370_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part370) = true := by rfl

def kid01_part371 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.last 24 (4,true),
.cycle 12 5 false (2),
.cycle 0 25 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3),
.last 14 (4,true),
.cycle 11 5 false (1),
.last 28 (4,true),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.last 13 (4,true),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3)
])
theorem kid01_part371_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part371) = true := by rfl

def kid01_part372 : Audit := .split 13 (4,true) (byMove [
.cycle 12 5 false (0),
.cycle 0 23 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 17 true (-1),
.last 16 (5,false),
.last 24 (5,false),
.cycle 0 19 true (-1),
.last 16 (5,false),
.cycle 10 4 true (-1),
.cycle 11 3 false (0),
.last 18 (5,false),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 17 true (-1),
.cycle 12 2 true (-1),
.last 17 (5,false),
.cycle 0 19 true (-1),
.last 21 (5,false),
.last 19 (5,false)
])
theorem kid01_part372_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part372) = true := by rfl

def kid01_part373 : Audit := .split 15 (5,false) (byMove [
.last 24 (4,true),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 18 (4,true),
.cycle 11 5 false (0),
.last 22 (4,true),
.cycle 16 1 false (-2),
.cycle 14 2 true (-3),
.cycle 10 7 false (0),
.last 18 (4,true),
.cycle 11 5 false (0),
.last 20 (4,true),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 18 (4,true),
.last 19 (4,true),
.last 22 (4,true),
.cycle 12 7 false (0),
.cycle 9 7 false (1),
.last 19 (4,true)
])
theorem kid01_part373_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part373) = true := by rfl

def kid01_part374 : Audit := .split 15 (4,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 17 (5,false),
.last 16 (5,false),
.last 25 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.cycle 0 17 true (-1),
.last 18 (5,false),
.cycle 0 19 true (-1),
.cycle 13 3 false (2),
.last 20 (5,false),
.last 27 (5,false),
.cycle 16 1 false (0),
.last 17 (5,false),
.last 16 (5,false),
.cycle 2 15 true (-1),
.cycle 14 2 true (1),
.last 19 (5,false),
.cycle 0 17 true (-1),
.cycle 0 23 true (-1),
.cycle 0 21 true (-1)
])
theorem kid01_part374_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part374) = true := by rfl

def kid01_part375 : Audit := .cycle 11 1 false (-1)
theorem kid01_part375_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part375) = true := by rfl

def kid01_part376 : Audit := .split 12 (5,false) (byMove [
.last 19 (4,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.cycle 11 5 false (0),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.last 15 (4,true),
.cycle 11 5 false (-1),
.last 17 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.cycle 11 7 false (0),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid01_part376_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part376) = true := by rfl

def kid01_part377 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.cycle 12 5 false (0),
.last 27 (4,true),
.last 15 (4,true),
.last 12 (4,true),
.cycle 10 2 true (-1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 13 (4,true),
.last 22 (4,true),
.last 15 (4,true),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid01_part377_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part377) = true := by rfl

def kid01_part378 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 16 (5,false),
.last 24 (5,false),
.cycle 18 1 false (0),
.last 16 (5,false),
.cycle 10 4 true (0),
.last 23 (5,false),
.cycle 8 6 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 15 true (0),
.last 18 (5,false),
.last 16 (5,false),
.last 27 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.last 20 (5,false),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 0 15 true (0)
])
theorem kid01_part378_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part378) = true := by rfl

def kid01_part379 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.last 24 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 1 15 true (0),
.cycle 13 3 false (1),
.last 19 (5,false),
.last 26 (5,false),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.last 18 (5,false),
.cycle 0 16 true (0),
.cycle 1 17 true (0),
.cycle 1 15 true (0)
])
theorem kid01_part379_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part379) = true := by rfl

def kid01_part380 : Audit := .cycle 0 13 true (0)
theorem kid01_part380_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part380) = true := by rfl

def kid01_part381 : Audit := .split 17 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 20 (4,true),
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 11 14 true (-1),
.last 20 (4,true),
.cycle 14 5 false (2),
.last 22 (4,true),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 9 9 false (2),
.cycle 11 14 true (-1)
])
theorem kid01_part381_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part381) = true := by rfl

def kid01_part382 : Audit := .cycle 9 2 true (0)
theorem kid01_part382_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part382) = true := by rfl

def kid01_part383 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 12 10 false (0),
.cycle 24 1 false (-2),
.last 15 (4,true),
.last 12 (4,true),
.cycle 10 2 true (0),
.last 24 (4,true),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3),
.last 19 (4,true),
.cycle 12 5 false (0),
.last 30 (4,true),
.cycle 18 1 false (-2),
.last 12 (4,true),
.cycle 13 3 true (1),
.cycle 2 11 true (0),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (3)
])
theorem kid01_part383_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part383) = true := by rfl

def kid01_part359 : Audit := .split 10 (5,true) (byMove [(kid01_part360),(kid01_part361),(kid01_part362),(kid01_part363),(kid01_part364),(kid01_part365),(kid01_part366),(kid01_part367),(kid01_part368),(kid01_part369),(kid01_part370),(kid01_part371),(kid01_part372),(kid01_part373),(kid01_part374),(kid01_part375),(kid01_part376),(kid01_part377),(kid01_part378),(kid01_part379),(kid01_part380),(kid01_part381),(kid01_part382),(kid01_part383)])

theorem kid01_part359_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part359) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part360),(kid01_part361),(kid01_part362),(kid01_part363),(kid01_part364),(kid01_part365),(kid01_part366),(kid01_part367),(kid01_part368),(kid01_part369),(kid01_part370),(kid01_part371),(kid01_part372),(kid01_part373),(kid01_part374),(kid01_part375),(kid01_part376),(kid01_part377),(kid01_part378),(kid01_part379),(kid01_part380),(kid01_part381),(kid01_part382),(kid01_part383)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part360_checked

  · exact kid01_part366_checked

  · exact kid01_part372_checked

  · exact kid01_part378_checked

  · exact kid01_part361_checked

  · exact kid01_part367_checked

  · exact kid01_part373_checked

  · exact kid01_part379_checked

  · exact kid01_part362_checked

  · exact kid01_part368_checked

  · exact kid01_part374_checked

  · exact kid01_part380_checked

  · exact kid01_part363_checked

  · exact kid01_part369_checked

  · exact kid01_part375_checked

  · exact kid01_part381_checked

  · exact kid01_part364_checked

  · exact kid01_part370_checked

  · exact kid01_part376_checked

  · exact kid01_part382_checked

  · exact kid01_part365_checked

  · exact kid01_part371_checked

  · exact kid01_part377_checked

  · exact kid01_part383_checked

def kid01_part384 : Audit := .cycle 2 9 true (1)
theorem kid01_part384_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part384) = true := by rfl

def kid01_part385 : Audit := .cycle 8 2 true (1)
theorem kid01_part385_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part385) = true := by rfl

def kid01_part386 : Audit := .cycle 1 10 true (1)
theorem kid01_part386_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part386) = true := by rfl

def kid01_part387 : Audit := .cycle 0 11 true (0)
theorem kid01_part387_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part387) = true := by rfl

def kid01_part388 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 11 1 true (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 true (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1),
.cycle 16 4 false (0),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
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
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 15 (5,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 40 true (-2),
.cycle 25 1 false (-1),
.cycle 17 1 false (-1),
.cycle 12 4 true (-2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 16 4 false (0),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 15 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid01_part388_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part388) = true := by rfl

def kid01_part390 : Audit := .cycle 0 11 true (0)
theorem kid01_part390_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part390) = true := by rfl

def kid01_part391 : Audit := .cycle 1 10 true (1)
theorem kid01_part391_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part391) = true := by rfl

def kid01_part392 : Audit := .cycle 21 1 false (1)
theorem kid01_part392_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part392) = true := by rfl

def kid01_part393 : Audit := .cycle 23 1 false (1)
theorem kid01_part393_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part393) = true := by rfl

def kid01_part394 : Audit := .split 12 (5,false) (byMove [
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
.last 15 (4,true),
.last 16 (4,true),
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
theorem kid01_part394_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part394) = true := by rfl

def kid01_part395 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1)
])
theorem kid01_part395_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part395) = true := by rfl

def kid01_part396 : Audit := .cycle 0 11 true (0)
theorem kid01_part396_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part396) = true := by rfl

def kid01_part397 : Audit := .cycle 1 10 true (1)
theorem kid01_part397_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part397) = true := by rfl

def kid01_part398 : Audit := .cycle 35 1 false (7)
theorem kid01_part398_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part398) = true := by rfl

def kid01_part399 : Audit := .cycle 20 1 false (2)
theorem kid01_part399_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part399) = true := by rfl

def kid01_part400 : Audit := .split 12 (5,false) (byMove [
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
.last 15 (4,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 24 (4,true),
.cycle 9 4 true (1),
.last 17 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid01_part400_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part400) = true := by rfl

def kid01_part401 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (2),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 14 (4,true),
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
theorem kid01_part401_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part401) = true := by rfl

def kid01_part402 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 29 true (-2),
.cycle 29 1 false (-1),
.cycle 18 1 false (0),
.last 16 (5,false),
.last 18 (5,false),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 10 4 true (1),
.cycle 19 3 false (0),
.cycle 14 8 false (0),
.cycle 16 15 true (0),
.cycle 23 1 false (-1),
.cycle 14 5 false (0),
.last 18 (5,false),
.cycle 2 13 true (1),
.cycle 12 2 true (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 17 9 false (1)
])
theorem kid01_part402_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part402) = true := by rfl

def kid01_part403 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 21 5 false (3),
.cycle 15 5 false (1),
.cycle 22 5 false (2),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 15 5 false (1),
.cycle 13 3 false (1),
.cycle 15 5 false (0),
.cycle 23 5 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 16 5 false (0)
])
theorem kid01_part403_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part403) = true := by rfl

def kid01_part404 : Audit := .cycle 0 13 true (0)
theorem kid01_part404_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part404) = true := by rfl

def kid01_part405 : Audit := .cycle 18 1 false (0)
theorem kid01_part405_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part405) = true := by rfl

def kid01_part406 : Audit := .cycle 9 2 true (1)
theorem kid01_part406_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part406) = true := by rfl

def kid01_part407 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 25 1 false (-1),
.last 15 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid01_part407_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part407) = true := by rfl

def kid01_part408 : Audit := .cycle 0 11 true (0)
theorem kid01_part408_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part408) = true := by rfl

def kid01_part409 : Audit := .cycle 1 10 true (1)
theorem kid01_part409_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part409) = true := by rfl

def kid01_part410 : Audit := .cycle 2 9 true (1)
theorem kid01_part410_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part410) = true := by rfl

def kid01_part411 : Audit := .cycle 2 12 true (1)
theorem kid01_part411_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part411) = true := by rfl

def kid01_part412 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 9 13 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid01_part412_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part412) = true := by rfl

def kid01_part413 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 18 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid01_part413_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part413) = true := by rfl

def kid01_part389 : Audit := .split 10 (5,true) (byMove [(kid01_part390),(kid01_part391),(kid01_part392),(kid01_part393),(kid01_part394),(kid01_part395),(kid01_part396),(kid01_part397),(kid01_part398),(kid01_part399),(kid01_part400),(kid01_part401),(kid01_part402),(kid01_part403),(kid01_part404),(kid01_part405),(kid01_part406),(kid01_part407),(kid01_part408),(kid01_part409),(kid01_part410),(kid01_part411),(kid01_part412),(kid01_part413)])

theorem kid01_part389_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part389) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part390),(kid01_part391),(kid01_part392),(kid01_part393),(kid01_part394),(kid01_part395),(kid01_part396),(kid01_part397),(kid01_part398),(kid01_part399),(kid01_part400),(kid01_part401),(kid01_part402),(kid01_part403),(kid01_part404),(kid01_part405),(kid01_part406),(kid01_part407),(kid01_part408),(kid01_part409),(kid01_part410),(kid01_part411),(kid01_part412),(kid01_part413)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part390_checked

  · exact kid01_part396_checked

  · exact kid01_part402_checked

  · exact kid01_part408_checked

  · exact kid01_part391_checked

  · exact kid01_part397_checked

  · exact kid01_part403_checked

  · exact kid01_part409_checked

  · exact kid01_part392_checked

  · exact kid01_part398_checked

  · exact kid01_part404_checked

  · exact kid01_part410_checked

  · exact kid01_part393_checked

  · exact kid01_part399_checked

  · exact kid01_part405_checked

  · exact kid01_part411_checked

  · exact kid01_part394_checked

  · exact kid01_part400_checked

  · exact kid01_part406_checked

  · exact kid01_part412_checked

  · exact kid01_part395_checked

  · exact kid01_part401_checked

  · exact kid01_part407_checked

  · exact kid01_part413_checked

def kid01_part414 : Audit := .split 16 (4,true) (byMove [
.cycle 15 5 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 15, 64, 64],96⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.split 17 (5,false) (byMove [
.last 42 (5,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.last 40 (5,true),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.last 19 (5,true),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 21 (5,true),
.cycle 15 5 false (-1),
.last 40 (5,true),
.cycle 10 10 false (1),
.cycle 9 9 false (1),
.last 19 (5,true)
]),
.cycle 10 7 false (1),
.cycle 12 5 false (0),
.cycle 0 41 true (-2),
.cycle 0 21 true (-2),
.cycle 23 5 true (1),
.split 17 (5,true) (byMove [
.cycle 0 24 false (3),
.cycle 0 41 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.last 18 (5,false),
.cycle 0 21 true (-2),
.cycle 12 6 true (-2),
.cycle 10 14 true (-2),
.cycle 23 1 false (3),
.last 19 (5,false),
.last 19 (5,false),
.cycle 14 4 true (-2),
.cycle 11 8 false (1),
.cycle 0 23 true (-2),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.last 18 (5,false),
.cycle 0 21 true (-2),
.cycle 1 25 true (-2),
.cycle 11 7 false (1),
.cycle 28 38 true (1),
.last 19 (5,false),
.last 19 (5,false)
]),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.split 17 (5,false) (byMove [
.cycle 15 6 false (-1),
.last 28 (5,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.last 42 (5,true),
.cycle 10 9 false (1),
.cycle 16 2 true (-3),
.last 18 (5,true),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 10 10 false (1),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 15 5 false (-1),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.cycle 5 13 false (3),
.last 19 (5,true),
.last 18 (5,true)
]),
.cycle 2 20 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 17 6 true (-1),
.split 17 (5,true) (byMove [
.cycle 0 41 true (-2),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 31 true (-2),
.last 19 (5,false),
.last 19 (5,false),
.cycle 0 21 true (-2),
.cycle 8 10 false (2),
.cycle 1 18 false (3),
.cycle 0 35 true (-2),
.last 19 (5,false),
.last 19 (5,false),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 32, 15, 64],96⟩,
.cycle 10 9 false (1),
.cycle 16 2 true (-2),
.last 19 (5,false),
.cycle 0 21 true (-2),
.cycle 18 19 true (-1),
.cycle 2 20 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[4, 15, 15, 1, 32, 8, 64],96⟩,
.last 19 (5,false),
.last 19 (5,false)
])
])
theorem kid01_part414_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part414) = true := by rfl

def kid01_part415 : Audit := .cycle 10 4 false (0)
theorem kid01_part415_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part415) = true := by rfl

def kid01_part416 : Audit := .cycle 12 11 true (0)
theorem kid01_part416_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part416) = true := by rfl

def kid01_part417 : Audit := .cycle 15 1 false (-1)
theorem kid01_part417_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part417) = true := by rfl

def kid01_part418 : Audit := .split 10 (4,true) (byMove [
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 28 (5,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 4 true (-1),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 13 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 10 6 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 15 (5,true),
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 14 1 false (0),
.cycle 12 1 false (0),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.split 11 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 2 11 true (0),
.cycle 1 14 true (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false)
]),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.cycle 9 10 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 25 11 false (2),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 5 7 false (3),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 2 14 true (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 5 18 true (0),
.cycle 11 3 true (1),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 18 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 6 18 true (0),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 25 11 false (2),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 2 11 true (0),
.cycle 1 14 true (0),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false)
])
])
theorem kid01_part418_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part418) = true := by rfl

def kid01_part420 : Audit := .split 15 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 17 (5,false),
.last 16 (5,false),
.cycle 0 19 true (-1),
.last 18 (5,false),
.last 26 (5,false),
.cycle 0 21 true (-1),
.last 18 (5,false),
.cycle 0 21 true (-1),
.cycle 14 3 false (0),
.last 20 (5,false),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.last 17 (5,false),
.last 16 (5,false),
.cycle 0 19 true (-1),
.cycle 14 2 true (-1),
.last 19 (5,false),
.cycle 0 21 true (-1),
.last 31 (5,false),
.last 26 (5,false)
])
theorem kid01_part420_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part420) = true := by rfl

def kid01_part421 : Audit := .split 23 (5,false) (byMove [
.last 28 (4,true),
.cycle 11 13 true (-1),
.cycle 34 1 false (-2),
.cycle 12 15 true (-1),
.last 31 (4,true),
.cycle 35 1 false (-3),
.cycle 6 23 false (4),
.cycle 24 11 false (2),
.cycle 0 28 true (-1),
.cycle 13 11 true (1),
.last 24 (4,true),
.cycle 0 28 true (-1),
.last 26 (4,true),
.last 27 (4,true),
.cycle 24 9 false (3),
.cycle 31 1 false (-3),
.last 34 (4,true),
.cycle 24 9 false (2),
.last 27 (4,true),
.last 25 (4,true),
.cycle 0 34 true (-2),
.cycle 13 11 true (1),
.last 24 (4,true),
.cycle 0 34 true (-2)
])
theorem kid01_part421_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part421) = true := by rfl

def kid01_part422 : Audit := .cycle 12 1 false (0)
theorem kid01_part422_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part422) = true := by rfl

def kid01_part423 : Audit := .cycle 11 1 false (-1)
theorem kid01_part423_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part423) = true := by rfl

def kid01_part424 : Audit := .split 12 (5,false) (byMove [
.last 17 (4,true),
.last 18 (4,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 6 25 false (4),
.cycle 11 3 false (-1),
.last 30 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.cycle 11 5 false (-1),
.cycle 28 9 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 29 (4,true),
.last 14 (4,true),
.cycle 11 4 false (-1),
.last 16 (4,true),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid01_part424_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part424) = true := by rfl

def kid01_part425 : Audit := .split 11 (5,false) (byMove [
.last 30 (4,true),
.cycle 26 13 true (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 14 (4,true),
.cycle 14 3 false (0),
.cycle 0 28 true (-1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 17 1 true (1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.last 16 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 34 true (-2),
.cycle 0 23 true (-2),
.cycle 9 3 false (1),
.cycle 25 1 true (-3)
])
theorem kid01_part425_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part425) = true := by rfl

def kid01_part426 : Audit := .split 15 (5,false) (byMove [
.last 20 (4,true),
.cycle 11 13 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.cycle 13 3 false (1),
.cycle 0 20 true (-1),
.cycle 11 11 true (-1),
.last 16 (4,true),
.cycle 11 11 true (-1),
.last 18 (4,true),
.cycle 12 5 false (2),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.last 17 (4,true),
.cycle 12 4 false (2),
.cycle 11 11 true (-1),
.last 16 (4,true),
.cycle 11 11 true (-1)
])
theorem kid01_part426_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part426) = true := by rfl

def kid01_part427 : Audit := .split 13 (5,false) (byMove [
.last 18 (4,true),
.cycle 29 13 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 3 false (1),
.cycle 0 32 true (-1),
.cycle 14 11 true (-1),
.last 14 (4,true),
.cycle 10 4 true (-1),
.last 16 (4,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 15 (4,true),
.cycle 11 4 false (1),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 8 7 false (2)
])
theorem kid01_part427_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part427) = true := by rfl

def kid01_part428 : Audit := .cycle 0 15 true (0)
theorem kid01_part428_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part428) = true := by rfl

def kid01_part429 : Audit := .split 21 (5,false) (byMove [
.last 26 (4,true),
.cycle 11 13 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.cycle 17 5 false (4),
.cycle 19 3 false (3),
.cycle 0 26 true (0),
.cycle 11 11 true (1),
.last 22 (4,true),
.cycle 0 24 true (0),
.last 24 (4,true),
.cycle 18 5 false (4),
.cycle 16 7 false (4),
.cycle 22 1 false (0),
.cycle 20 2 false (2),
.cycle 21 1 false (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 18 4 false (4),
.cycle 11 11 true (1),
.last 22 (4,true),
.cycle 0 24 true (0)
])
theorem kid01_part429_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part429) = true := by rfl

def kid01_part430 : Audit := .split 11 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.last 21 (5,false),
.last 14 (5,false),
.last 22 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 11 3 false (1),
.last 16 (5,false),
.last 23 (5,false),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 2 11 true (0),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 14 (5,false)
])
theorem kid01_part430_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part430) = true := by rfl

def kid01_part431 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 15 13 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 2 false (3),
.cycle 13 1 false (3),
.cycle 0 14 true (0),
.cycle 21 3 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.last 16 (4,true),
.cycle 13 1 true (3),
.last 16 (4,true),
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
theorem kid01_part431_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part431) = true := by rfl

def kid01_part432 : Audit := .split 13 (4,true) (byMove [
.cycle 12 5 false (0),
.last 21 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.last 16 (5,false),
.last 27 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.cycle 10 4 true (-1),
.cycle 11 3 false (0),
.last 18 (5,false),
.last 20 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 21 true (-1),
.cycle 12 2 true (-1),
.last 17 (5,false),
.cycle 5 9 false (3),
.last 37 (5,false),
.last 19 (5,false)
])
theorem kid01_part432_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part432) = true := by rfl

def kid01_part433 : Audit := .split 15 (5,false) (byMove [
.last 20 (4,true),
.cycle 20 13 true (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 5 false (0),
.cycle 13 3 false (-1),
.last 22 (4,true),
.cycle 19 11 true (1),
.last 16 (4,true),
.cycle 10 6 false (0),
.last 18 (4,true),
.cycle 11 5 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.last 17 (4,true),
.cycle 12 4 false (0),
.cycle 19 11 true (1),
.last 16 (4,true),
.cycle 13 4 false (-1)
])
theorem kid01_part433_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part433) = true := by rfl

def kid01_part434 : Audit := .split 17 (5,false) (byMove [
.last 22 (4,true),
.cycle 12 13 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.cycle 15 3 false (1),
.cycle 0 22 true (-1),
.cycle 12 11 true (-1),
.last 18 (4,true),
.cycle 12 13 true (-1),
.last 20 (4,true),
.cycle 14 5 false (2),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 14 4 false (2),
.cycle 12 11 true (-1),
.last 18 (4,true),
.cycle 12 15 true (-2)
])
theorem kid01_part434_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part434) = true := by rfl

def kid01_part435 : Audit := .cycle 11 1 false (-1)
theorem kid01_part435_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part435) = true := by rfl

def kid01_part436 : Audit := .split 12 (5,false) (byMove [
.last 17 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M11.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M11.never m hm),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 3 false (-1),
.cycle 0 26 true (-2),
.cycle 0 23 true (-2),
.last 13 (4,true),
.cycle 10 3 false (0),
.last 15 (4,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.last 14 (4,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid01_part436_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part436) = true := by rfl

def kid01_part437 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 27 13 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 3 false (0),
.cycle 0 30 true (-1),
.cycle 12 11 true (-1),
.last 12 (4,true),
.cycle 10 2 true (-1),
.last 14 (4,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 13 (4,true),
.cycle 11 4 false (0),
.cycle 5 7 false (3),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid01_part437_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part437) = true := by rfl

def kid01_part438 : Audit := .split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.last 24 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 13 3 false (1),
.last 19 (5,false),
.last 26 (5,false),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.last 18 (5,false),
.cycle 0 16 true (0),
.cycle 2 17 true (0),
.cycle 0 16 true (0)
])
theorem kid01_part438_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part438) = true := by rfl

def kid01_part439 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.last 25 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 15 (5,false),
.cycle 0 17 true (0),
.last 23 (5,false),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 11 3 false (1),
.last 17 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 2 16 true (0),
.cycle 11 2 true (0),
.last 16 (5,false),
.last 23 (5,false),
.cycle 13 5 true (1),
.cycle 1 16 true (0)
])
theorem kid01_part439_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part439) = true := by rfl

def kid01_part440 : Audit := .split 14 (5,false) (byMove [
.last 19 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M12.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M12.never m hm),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (1),
.cycle 12 3 false (0),
.last 21 (4,true),
.cycle 0 19 true (-2),
.last 15 (4,true),
.cycle 10 5 false (1),
.last 17 (4,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.last 16 (4,true),
.cycle 11 4 false (1),
.cycle 0 19 true (-2),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid01_part440_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part440) = true := by rfl

def kid01_part441 : Audit := .split 21 (5,false) (byMove [
.last 39 (4,true),
.cycle 29 13 true (1),
.cycle 34 1 false (-2),
.last 25 (4,true),
.last 22 (4,true),
.cycle 29 1 false (-1),
.cycle 6 16 true (0),
.cycle 5 20 true (0),
.cycle 0 26 true (0),
.cycle 11 11 true (1),
.last 22 (4,true),
.cycle 0 24 true (0),
.last 29 (4,true),
.cycle 22 5 false (0),
.cycle 16 9 false (4),
.cycle 28 1 false (-2),
.last 22 (4,true),
.cycle 5 18 true (0),
.last 25 (4,true),
.last 23 (4,true),
.last 24 (4,true),
.cycle 11 11 true (1),
.last 22 (4,true),
.cycle 0 24 true (0)
])
theorem kid01_part441_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part441) = true := by rfl

def kid01_part442 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 14 (5,false),
.last 22 (5,false),
.cycle 16 1 false (0),
.last 14 (5,false),
.cycle 9 4 true (0),
.last 21 (5,false),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 14 (5,false),
.last 25 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 2 11 true (0),
.cycle 11 2 true (1),
.last 18 (5,false),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.last 16 (5,false)
])
theorem kid01_part442_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part442) = true := by rfl

def kid01_part443 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 10 17 true (0),
.cycle 1 27 true (0),
.cycle 3 11 true (0),
.last 16 (4,true),
.cycle 13 1 true (3),
.last 17 (4,true),
.last 15 (4,true),
.last 16 (4,true),
.cycle 5 29 true (0),
.last 14 (4,true),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 11 true (3),
.cycle 11 4 true (1),
.cycle 13 1 true (3)
])
theorem kid01_part443_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part443) = true := by rfl

def kid01_part419 : Audit := .split 10 (5,true) (byMove [(kid01_part420),(kid01_part421),(kid01_part422),(kid01_part423),(kid01_part424),(kid01_part425),(kid01_part426),(kid01_part427),(kid01_part428),(kid01_part429),(kid01_part430),(kid01_part431),(kid01_part432),(kid01_part433),(kid01_part434),(kid01_part435),(kid01_part436),(kid01_part437),(kid01_part438),(kid01_part439),(kid01_part440),(kid01_part441),(kid01_part442),(kid01_part443)])

theorem kid01_part419_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part419) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part420),(kid01_part421),(kid01_part422),(kid01_part423),(kid01_part424),(kid01_part425),(kid01_part426),(kid01_part427),(kid01_part428),(kid01_part429),(kid01_part430),(kid01_part431),(kid01_part432),(kid01_part433),(kid01_part434),(kid01_part435),(kid01_part436),(kid01_part437),(kid01_part438),(kid01_part439),(kid01_part440),(kid01_part441),(kid01_part442),(kid01_part443)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part420_checked

  · exact kid01_part426_checked

  · exact kid01_part432_checked

  · exact kid01_part438_checked

  · exact kid01_part421_checked

  · exact kid01_part427_checked

  · exact kid01_part433_checked

  · exact kid01_part439_checked

  · exact kid01_part422_checked

  · exact kid01_part428_checked

  · exact kid01_part434_checked

  · exact kid01_part440_checked

  · exact kid01_part423_checked

  · exact kid01_part429_checked

  · exact kid01_part435_checked

  · exact kid01_part441_checked

  · exact kid01_part424_checked

  · exact kid01_part430_checked

  · exact kid01_part436_checked

  · exact kid01_part442_checked

  · exact kid01_part425_checked

  · exact kid01_part431_checked

  · exact kid01_part437_checked

  · exact kid01_part443_checked

def kid01_part444 : Audit := .cycle 2 9 true (1)
theorem kid01_part444_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part444) = true := by rfl

def kid01_part445 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 17 true (-1),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.last 13 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 16 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 18 (5,false),
.cycle 13 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.cycle 10 4 true (0),
.last 17 (5,false),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 9 4 true (0),
.last 13 (5,false)
]),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 10 4 true (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 13 true (1),
.last 13 (5,false)
]),
.cycle 16 3 false (0),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.split 12 (5,true) (byMove [
.last 18 (5,false),
.last 27 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 17 (5,false),
.cycle 0 17 true (0),
.last 25 (5,false),
.last 14 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 25 (5,false),
.cycle 11 2 true (0),
.last 15 (5,false)
]),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 5 false (1),
.cycle 13 13 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 15 7 false (1),
.cycle 13 5 false (1),
.cycle 0 31 true (-2),
.cycle 2 13 true (1),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 13 true (1),
.last 13 (5,false)
])
])
theorem kid01_part445_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part445) = true := by rfl

def kid01_part446 : Audit := .split 12 (4,true) (byMove [
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 20 3 false (0),
.cycle 13 1 false (-1),
.cycle 11 4 true (-1),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.last 15 (5,true),
.cycle 11 4 false (1),
.cycle 15 3 false (-1),
.cycle 11 6 true (-2),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.last 17 (5,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 9 5 false (2),
.last 15 (5,true)
]),
.cycle 19 3 false (3),
.cycle 13 3 false (1),
.cycle 20 3 false (2),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 20 3 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 20 3 false (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 20 3 false (4),
.last 14 (5,false),
.cycle 11 4 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 3 false (3),
.cycle 22 3 false (4),
.cycle 2 13 true (0),
.last 14 (5,false)
]),
.cycle 11 3 false (1),
.cycle 14 3 false (0),
.cycle 21 3 false (3),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 7 22 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 7 22 false (3),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.cycle 12 2 true (-1),
.last 14 (5,true),
.cycle 11 4 false (1),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.cycle 11 3 false (1),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 2 12 true (0),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 2 13 true (0),
.split 13 (5,true) (byMove [
.cycle 20 3 false (2),
.cycle 14 3 false (0),
.cycle 21 3 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 7 16 true (0),
.last 14 (5,false),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.cycle 12 2 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 18 true (0),
.cycle 2 13 true (0),
.last 14 (5,false)
])
])
theorem kid01_part446_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part446) = true := by rfl

def kid01_part447 : Audit := .cycle 0 11 true (0)
theorem kid01_part447_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part447) = true := by rfl

def kid01_part448 : Audit := .split 10 (4,true) (byMove [
.cycle 2 10 true (1),
.cycle 0 16 true (-1),
.cycle 11 11 false (1),
.cycle 0 12 true (0),
.cycle 13 1 true (-1),
.split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.last 21 (5,false),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
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
.cycle 2 13 true (1),
.cycle 12 1 true (2),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.cycle 13 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 38 true (-2),
.cycle 2 11 true (1),
.cycle 11 3 false (1),
.split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 22 (5,false),
.cycle 25 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.last 13 (5,false),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.last 21 (5,false),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 13 (5,false),
.cycle 2 11 true (1),
.last 17 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 16 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid01_part448_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part448) = true := by rfl

def kid01_part450 : Audit := .cycle 2 10 true (1)
theorem kid01_part450_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part450) = true := by rfl

def kid01_part451 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 20 3 false (2),
.cycle 13 3 false (1),
.cycle 21 3 false (1),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 21 3 false (1),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 22 3 false (2),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 2 12 true (0),
.cycle 11 2 true (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 13 3 false (1)
])
theorem kid01_part451_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part451) = true := by rfl

def kid01_part452 : Audit := .cycle 11 11 false (1)
theorem kid01_part452_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part452) = true := by rfl

def kid01_part453 : Audit := .cycle 0 12 true (0)
theorem kid01_part453_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part453) = true := by rfl

def kid01_part454 : Audit := .split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid01_part454_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part454) = true := by rfl

def kid01_part455 : Audit := .split 13 (5,false) (byMove [
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
.last 16 (4,true),
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
theorem kid01_part455_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part455) = true := by rfl

def kid01_part456 : Audit := .cycle 0 11 true (0)
theorem kid01_part456_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part456) = true := by rfl

def kid01_part457 : Audit := .cycle 1 10 true (1)
theorem kid01_part457_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part457) = true := by rfl

def kid01_part458 : Audit := .cycle 0 23 true (0)
theorem kid01_part458_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part458) = true := by rfl

def kid01_part459 : Audit := .cycle 3 8 true (1)
theorem kid01_part459_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part459) = true := by rfl

def kid01_part460 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 1 13 true (1),
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
.last 16 (4,true),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid01_part460_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part460) = true := by rfl

def kid01_part461 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 14 (4,true),
.last 15 (4,true),
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
theorem kid01_part461_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part461) = true := by rfl

def kid01_part462 : Audit := .split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 20 5 false (3),
.cycle 15 5 false (1),
.cycle 21 5 false (2),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 13 4 true (0),
.cycle 13 3 false (1),
.cycle 16 5 false (0),
.cycle 22 5 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 15 5 false (1)
])
theorem kid01_part462_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part462) = true := by rfl

def kid01_part463 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 26 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 3 false (1),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.cycle 21 3 false (3),
.last 16 (5,false),
.cycle 16 3 false (0),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 2 16 true (0),
.cycle 11 2 true (0),
.cycle 14 3 false (0),
.cycle 5 24 true (0),
.last 16 (5,false),
.cycle 13 3 false (1)
])
theorem kid01_part463_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part463) = true := by rfl

def kid01_part464 : Audit := .split 21 (4,true) (byMove [
.cycle 0 35 true (-2),
.cycle 0 25 true (-2),
.cycle 11 17 false (2),
.cycle 20 17 false (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 0 36 true (-2),
.cycle 0 29 true (-2),
.cycle 0 37 true (-2),
.cycle 0 23 true (-2),
.last 24 (5,false),
.cycle 0 25 true (-2),
.cycle 11 18 false (2),
.cycle 7 16 false (3),
.cycle 0 38 true (-2),
.cycle 11 15 false (2),
.cycle 0 42 true (-2),
.last 22 (5,false),
.cycle 2 21 true (-2),
.cycle 20 2 true (1),
.cycle 0 30 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 32, 64, 64],[4, 1, 10, 1, 8, 1, 64],112⟩,
.last 24 (5,false),
.cycle 0 27 true (-2)
])
theorem kid01_part464_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part464) = true := by rfl

def kid01_part465 : Audit := .cycle 2 11 true (1)
theorem kid01_part465_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part465) = true := by rfl

def kid01_part466 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.last 14 (5,false),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 9 4 true (1),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 11 2 true (1),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.last 14 (5,false),
.cycle 10 2 true (1)
])
theorem kid01_part466_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part466) = true := by rfl

def kid01_part467 : Audit := .split 13 (5,false) (byMove [
.last 18 (4,true),
.cycle 33 15 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 11 5 false (1),
.cycle 0 34 true (-1),
.cycle 14 13 true (-1),
.last 14 (4,true),
.cycle 12 2 true (-1),
.last 16 (4,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 15 (4,true),
.cycle 11 6 false (1),
.cycle 5 9 false (3),
.last 14 (4,true),
.cycle 11 3 false (1)
])
theorem kid01_part467_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part467) = true := by rfl

def kid01_part468 : Audit := .cycle 0 11 true (0)
theorem kid01_part468_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part468) = true := by rfl

def kid01_part469 : Audit := .cycle 1 10 true (1)
theorem kid01_part469_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part469) = true := by rfl

def kid01_part470 : Audit := .cycle 2 9 true (1)
theorem kid01_part470_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part470) = true := by rfl

def kid01_part471 : Audit := .cycle 2 12 true (1)
theorem kid01_part471_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part471) = true := by rfl

def kid01_part472 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 14 (4,true),
.last 15 (4,true),
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
.last 14 (4,true),
.last 15 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid01_part472_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part472) = true := by rfl

def kid01_part473 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.last 15 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3)
])
theorem kid01_part473_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part473) = true := by rfl

def kid01_part449 : Audit := .split 10 (5,true) (byMove [(kid01_part450),(kid01_part451),(kid01_part452),(kid01_part453),(kid01_part454),(kid01_part455),(kid01_part456),(kid01_part457),(kid01_part458),(kid01_part459),(kid01_part460),(kid01_part461),(kid01_part462),(kid01_part463),(kid01_part464),(kid01_part465),(kid01_part466),(kid01_part467),(kid01_part468),(kid01_part469),(kid01_part470),(kid01_part471),(kid01_part472),(kid01_part473)])

theorem kid01_part449_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part449) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part450),(kid01_part451),(kid01_part452),(kid01_part453),(kid01_part454),(kid01_part455),(kid01_part456),(kid01_part457),(kid01_part458),(kid01_part459),(kid01_part460),(kid01_part461),(kid01_part462),(kid01_part463),(kid01_part464),(kid01_part465),(kid01_part466),(kid01_part467),(kid01_part468),(kid01_part469),(kid01_part470),(kid01_part471),(kid01_part472),(kid01_part473)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part450_checked

  · exact kid01_part456_checked

  · exact kid01_part462_checked

  · exact kid01_part468_checked

  · exact kid01_part451_checked

  · exact kid01_part457_checked

  · exact kid01_part463_checked

  · exact kid01_part469_checked

  · exact kid01_part452_checked

  · exact kid01_part458_checked

  · exact kid01_part464_checked

  · exact kid01_part470_checked

  · exact kid01_part453_checked

  · exact kid01_part459_checked

  · exact kid01_part465_checked

  · exact kid01_part471_checked

  · exact kid01_part454_checked

  · exact kid01_part460_checked

  · exact kid01_part466_checked

  · exact kid01_part472_checked

  · exact kid01_part455_checked

  · exact kid01_part461_checked

  · exact kid01_part467_checked

  · exact kid01_part473_checked

def kid01_part353 : Audit := .split 9 (4,false) (byMove [(kid01_part354),(kid01_part355),(kid01_part356),(kid01_part357),(kid01_part358),(kid01_part359),(kid01_part384),(kid01_part385),(kid01_part386),(kid01_part387),(kid01_part388),(kid01_part389),(kid01_part414),(kid01_part415),(kid01_part416),(kid01_part417),(kid01_part418),(kid01_part419),(kid01_part444),(kid01_part445),(kid01_part446),(kid01_part447),(kid01_part448),(kid01_part449)])

theorem kid01_part353_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (kid01_part353) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid01_part354),(kid01_part355),(kid01_part356),(kid01_part357),(kid01_part358),(kid01_part359),(kid01_part384),(kid01_part385),(kid01_part386),(kid01_part387),(kid01_part388),(kid01_part389),(kid01_part414),(kid01_part415),(kid01_part416),(kid01_part417),(kid01_part418),(kid01_part419),(kid01_part444),(kid01_part445),(kid01_part446),(kid01_part447),(kid01_part448),(kid01_part449)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part354_checked

  · exact kid01_part384_checked

  · exact kid01_part414_checked

  · exact kid01_part444_checked

  · exact kid01_part355_checked

  · exact kid01_part385_checked

  · exact kid01_part415_checked

  · exact kid01_part445_checked

  · exact kid01_part356_checked

  · exact kid01_part386_checked

  · exact kid01_part416_checked

  · exact kid01_part446_checked

  · exact kid01_part357_checked

  · exact kid01_part387_checked

  · exact kid01_part417_checked

  · exact kid01_part447_checked

  · exact kid01_part358_checked

  · exact kid01_part388_checked

  · exact kid01_part418_checked

  · exact kid01_part448_checked

  · exact kid01_part359_checked

  · exact kid01_part389_checked

  · exact kid01_part419_checked

  · exact kid01_part449_checked

def kid01_part475 : Audit := .cycle 0 13 true (0)
theorem kid01_part475_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part475) = true := by rfl

def kid01_part476 : Audit := .split 17 (5,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.cycle 16 15 false (2),
.split 18 (4,false) (byMove [
.cycle 0 23 true (-2),
.cycle 1 18 false (3),
.cycle 16 17 false (2),
.cycle 10 18 true (-2),
.last 20 (4,true),
.last 51 (4,true),
.cycle 15 4 true (0),
.cycle 0 26 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.last 20 (4,true),
.cycle 0 23 true (-2),
.last 22 (4,true),
.cycle 16 18 false (2),
.cycle 13 6 true (-1),
.cycle 16 15 false (2),
.last 20 (4,true),
.cycle 9 10 false (2),
.last 22 (4,true),
.last 28 (4,true),
.cycle 0 21 true (-2),
.cycle 0 28 true (-2),
.last 20 (4,true),
.cycle 8 12 false (2)
]),
.cycle 1 18 false (3),
.cycle 0 30 true (-2),
.cycle 0 23 true (-2),
.cycle 0 31 true (-2),
.cycle 0 19 true (-2),
.split 18 (4,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 10 17 false (2),
.cycle 10 15 false (2),
.last 19 (4,false),
.cycle 0 32 true (-2),
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 32 64 true (-2),
.cycle 0 117 true (-3),
.last 19 (4,false),
.cycle 0 32 true (-2),
.cycle 15 4 true (1),
.cycle 0 26 true (-2),
.cycle 0 21 true (-2),
.cycle 10 15 false (2),
.last 19 (4,false),
.cycle 0 23 true (-2),
.cycle 15 17 true (1),
.cycle 1 18 true (-2),
.cycle 0 30 true (-2),
.cycle 0 33 true (-2),
.last 19 (4,false),
.cycle 0 25 true (-2)
]),
.cycle 0 32 true (-2),
.cycle 10 16 false (2),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.cycle 10 13 false (2),
.split 18 (4,false) (byMove [
.last 24 (4,true),
.cycle 0 34 true (-2),
.cycle 10 15 false (2),
.cycle 0 36 true (-2),
.last 20 (4,true),
.cycle 16 12 false (2),
.cycle 0 26 true (-2),
.cycle 0 36 true (-2),
.cycle 0 23 true (-2),
.cycle 0 32 true (-2),
.last 19 (4,true),
.cycle 17 2 true (0),
.last 22 (4,true),
.cycle 10 16 false (2),
.cycle 0 28 true (-2),
.cycle 10 13 false (2),
.last 20 (4,true),
.cycle 9 10 false (2),
.last 28 (4,true),
.last 24 (4,true),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.last 19 (4,true),
.last 20 (4,true)
]),
.cycle 0 34 true (-2),
.cycle 2 17 true (-2),
.cycle 16 2 true (1),
.cycle 0 24 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 10, 64],[4, 1, 10, 1, 64, 8, 64],80⟩,
.split 18 (4,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 24 true (-2),
.cycle 0 32 true (-2),
.cycle 0 20 true (-2),
.last 20 (4,false),
.last 20 (4,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 10, 64],[4, 1, 10, 1, 1, 16, 64],80⟩,
.cycle 0 31 true (-2),
.cycle 10 16 true (-2),
.cycle 0 29 true (-2),
.last 19 (4,false),
.cycle 1 19 true (-2),
.cycle 0 26 true (-2),
.cycle 0 36 true (-2),
.cycle 0 23 true (-2),
.cycle 0 32 true (-2),
.last 20 (4,false),
.cycle 17 2 true (1),
.cycle 15 17 true (1),
.cycle 16 17 true (1),
.cycle 2 17 true (-2),
.cycle 0 33 true (-2),
.last 19 (4,false),
.cycle 16 4 true (1)
]),
.cycle 16 4 true (1)
])
theorem kid01_part476_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part476) = true := by rfl

def kid01_part477 : Audit := .cycle 21 1 false (-1)
theorem kid01_part477_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part477) = true := by rfl

def kid01_part478 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
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
.last 16 (4,true),
.cycle 16 1 false (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 10 6 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.last 18 (4,true),
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.last 16 (4,true),
.cycle 9 6 true (0)
]),
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 24 1 false (0),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 24 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.last 15 (4,false),
.cycle 16 1 false (2),
.cycle 11 4 true (1),
.cycle 19 1 false (-1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (1),
.cycle 26 1 false (2),
.last 15 (4,false),
.cycle 0 17 true (0)
]),
.cycle 16 1 false (2),
.cycle 11 3 false (2),
.cycle 18 1 false (-2),
.cycle 25 1 false (1),
.cycle 14 1 false (0),
.split 14 (4,false) (byMove [
.cycle 12 6 false (2),
.cycle 34 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.last 15 (4,true),
.cycle 13 2 true (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 12 5 false (2),
.cycle 12 3 false (2),
.cycle 18 1 false (-2),
.cycle 0 30 true (0),
.last 15 (4,true),
.last 16 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 25 1 false (-1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false),
.cycle 0 15 true (0),
.cycle 0 29 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.last 15 (4,false),
.cycle 27 1 false (1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.last 16 (4,false),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 31 true (0),
.last 15 (4,false),
.cycle 0 17 true (0)
]),
.cycle 0 17 true (0)
])
theorem kid01_part478_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part478) = true := by rfl

def kid01_part480 : Audit := .cycle 0 15 true (-1)
theorem kid01_part480_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part480) = true := by rfl

def kid01_part481 : Audit := .split 20 (4,false) (byMove [
.last 27 (5,true),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 23 (5,true),
.cycle 17 5 false (1),
.last 25 (5,true),
.cycle 21 1 false (-1),
.cycle 10 12 true (-2),
.cycle 19 2 true (-2),
.last 23 (5,true),
.cycle 17 5 false (1),
.last 25 (5,true),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 23 (5,true),
.last 24 (5,true),
.last 25 (5,true),
.cycle 14 7 false (1),
.last 24 (5,true),
.cycle 9 12 false (1)
])
theorem kid01_part481_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part481) = true := by rfl

def kid01_part482 : Audit := .cycle 12 1 false (0)
theorem kid01_part482_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part482) = true := by rfl

def kid01_part483 : Audit := .cycle 11 1 false (-1)
theorem kid01_part483_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part483) = true := by rfl

def kid01_part484 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 true (1),
.cycle 11 2 true (-1),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 18 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 0 15 true (-1),
.last 25 (5,true),
.cycle 0 17 true (-1),
.cycle 18 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid01_part484_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part484) = true := by rfl

def kid01_part485 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.cycle 19 5 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 true (0),
.cycle 11 2 true (-2),
.last 15 (5,true),
.cycle 11 5 false (-1),
.last 40 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 28 (5,true),
.cycle 18 7 false (1),
.last 17 (5,true),
.cycle 9 4 false (1)
])
theorem kid01_part485_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part485) = true := by rfl

def kid01_part486 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 23 (4,false),
.last 16 (4,false),
.last 24 (4,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 16 (4,false),
.cycle 11 3 false (2),
.last 18 (4,false),
.last 25 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.cycle 0 17 true (0)
])
theorem kid01_part486_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part486) = true := by rfl

def kid01_part487 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 18 (5,true),
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 12 12 true (-1),
.cycle 14 2 true (-1),
.last 18 (5,true),
.cycle 11 5 false (2),
.last 20 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 18 (5,true),
.last 19 (5,true),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 12 12 true (-1),
.cycle 9 7 false (2)
])
theorem kid01_part487_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part487) = true := by rfl

def kid01_part488 : Audit := .cycle 0 13 true (0)
theorem kid01_part488_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part488) = true := by rfl

def kid01_part489 : Audit := .cycle 11 1 false (1)
theorem kid01_part489_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part489) = true := by rfl

def kid01_part490 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.last 24 (5,true),
.cycle 12 5 false (2),
.cycle 0 25 true (0),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true),
.last 14 (5,true),
.cycle 11 5 false (1),
.last 28 (5,true),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 2 11 true (0),
.last 13 (5,true),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true)
])
theorem kid01_part490_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part490) = true := by rfl

def kid01_part491 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 15 (5,true),
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 1 true (2),
.cycle 11 2 true (0),
.last 15 (5,true),
.cycle 11 5 false (1),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 16 1 true (2),
.cycle 9 4 true (0)
])
theorem kid01_part491_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part491) = true := by rfl

def kid01_part492 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (0),
.cycle 0 23 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 17 true (-1),
.last 16 (4,false),
.last 24 (4,false),
.cycle 0 19 true (-1),
.cycle 10 4 true (-1),
.last 16 (4,false),
.cycle 11 3 false (0),
.last 18 (4,false),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 17 true (-1),
.cycle 12 2 true (-1),
.last 17 (4,false),
.cycle 0 19 true (-1),
.last 19 (4,false),
.last 21 (4,false)
])
theorem kid01_part492_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part492) = true := by rfl

def kid01_part493 : Audit := .split 15 (4,false) (byMove [
.last 24 (5,true),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 18 (5,true),
.cycle 11 5 false (0),
.last 22 (5,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 14 2 true (-3),
.last 18 (5,true),
.cycle 11 5 false (0),
.last 20 (5,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 18 (5,true),
.last 19 (5,true),
.last 22 (5,true),
.cycle 12 7 false (0),
.last 19 (5,true),
.cycle 9 7 false (1)
])
theorem kid01_part493_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part493) = true := by rfl

def kid01_part494 : Audit := .split 15 (5,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.last 18 (4,false),
.last 26 (4,false),
.cycle 0 17 true (-1),
.cycle 0 19 true (-1),
.last 18 (4,false),
.cycle 13 3 false (2),
.last 20 (4,false),
.last 27 (4,false),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 17 (4,false),
.cycle 2 15 true (-1),
.cycle 14 2 true (1),
.last 19 (4,false),
.cycle 0 17 true (-1),
.cycle 0 21 true (-1),
.cycle 0 23 true (-1)
])
theorem kid01_part494_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part494) = true := by rfl

def kid01_part495 : Audit := .cycle 11 1 false (-1)
theorem kid01_part495_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part495) = true := by rfl

def kid01_part496 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 15 true (-1),
.cycle 12 5 false (0),
.last 27 (5,true),
.last 15 (5,true),
.cycle 10 2 true (-1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 15 true (-1),
.last 13 (5,true),
.last 22 (5,true),
.last 15 (5,true),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid01_part496_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part496) = true := by rfl

def kid01_part497 : Audit := .split 12 (4,false) (byMove [
.last 19 (5,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 11 5 false (0),
.last 17 (5,true),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.last 15 (5,true),
.cycle 11 5 false (-1),
.last 17 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 11 7 false (0),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid01_part497_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part497) = true := by rfl

def kid01_part498 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 16 (4,false),
.last 24 (4,false),
.cycle 18 1 false (0),
.cycle 10 4 true (0),
.last 16 (4,false),
.last 23 (4,false),
.cycle 8 6 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 16 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.last 27 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.cycle 2 13 true (0),
.cycle 12 2 true (1),
.last 20 (4,false),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.cycle 0 17 true (0)
])
theorem kid01_part498_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part498) = true := by rfl

def kid01_part499 : Audit := .split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 17 (4,false),
.cycle 13 3 false (1),
.last 19 (4,false),
.last 26 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.last 18 (4,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 1 17 true (0)
])
theorem kid01_part499_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part499) = true := by rfl

def kid01_part500 : Audit := .cycle 0 13 true (0)
theorem kid01_part500_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part500) = true := by rfl

def kid01_part501 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 20 (5,true),
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 11 14 true (-1),
.cycle 16 2 true (-1),
.last 20 (5,true),
.cycle 14 5 false (2),
.last 22 (5,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 20 (5,true),
.last 21 (5,true),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 11 14 true (-1),
.cycle 9 9 false (2)
])
theorem kid01_part501_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part501) = true := by rfl

def kid01_part502 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 12 10 false (0),
.cycle 24 1 false (-2),
.last 15 (5,true),
.cycle 10 2 true (0),
.last 12 (5,true),
.last 24 (5,true),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true),
.last 19 (5,true),
.cycle 12 5 false (0),
.last 30 (5,true),
.cycle 18 1 false (-2),
.cycle 13 3 true (1),
.last 12 (5,true),
.cycle 2 11 true (0),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.last 12 (5,true)
])
theorem kid01_part502_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part502) = true := by rfl

def kid01_part503 : Audit := .cycle 9 2 true (0)
theorem kid01_part503_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part503) = true := by rfl

def kid01_part479 : Audit := .split 10 (4,true) (byMove [(kid01_part480),(kid01_part481),(kid01_part482),(kid01_part483),(kid01_part484),(kid01_part485),(kid01_part486),(kid01_part487),(kid01_part488),(kid01_part489),(kid01_part490),(kid01_part491),(kid01_part492),(kid01_part493),(kid01_part494),(kid01_part495),(kid01_part496),(kid01_part497),(kid01_part498),(kid01_part499),(kid01_part500),(kid01_part501),(kid01_part502),(kid01_part503)])

theorem kid01_part479_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part479) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part480),(kid01_part481),(kid01_part482),(kid01_part483),(kid01_part484),(kid01_part485),(kid01_part486),(kid01_part487),(kid01_part488),(kid01_part489),(kid01_part490),(kid01_part491),(kid01_part492),(kid01_part493),(kid01_part494),(kid01_part495),(kid01_part496),(kid01_part497),(kid01_part498),(kid01_part499),(kid01_part500),(kid01_part501),(kid01_part502),(kid01_part503)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part480_checked

  · exact kid01_part486_checked

  · exact kid01_part492_checked

  · exact kid01_part498_checked

  · exact kid01_part481_checked

  · exact kid01_part487_checked

  · exact kid01_part493_checked

  · exact kid01_part499_checked

  · exact kid01_part482_checked

  · exact kid01_part488_checked

  · exact kid01_part494_checked

  · exact kid01_part500_checked

  · exact kid01_part483_checked

  · exact kid01_part489_checked

  · exact kid01_part495_checked

  · exact kid01_part501_checked

  · exact kid01_part484_checked

  · exact kid01_part490_checked

  · exact kid01_part496_checked

  · exact kid01_part502_checked

  · exact kid01_part485_checked

  · exact kid01_part491_checked

  · exact kid01_part497_checked

  · exact kid01_part503_checked

def kid01_part504 : Audit := .split 10 (5,true) (byMove [
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
.cycle 15 4 true (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 12 1 false (0),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 6 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 17 (4,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.last 14 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 22 1 false (2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (4),
.last 15 (4,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 2 11 true (0),
.last 14 (4,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
]),
.cycle 11 1 false (1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 26 1 false (2),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 10 6 false (0),
.last 34 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 26 1 false (2),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 15 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.last 29 (4,true),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 2 13 true (0),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 16 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 2 true (0),
.last 27 (4,true),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 4 true (2),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.last 38 (4,true),
.cycle 16 1 false (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 2 11 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (2)
]),
.cycle 9 2 true (0)
])
theorem kid01_part504_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part504) = true := by rfl

def kid01_part505 : Audit := .cycle 2 9 true (1)
theorem kid01_part505_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part505) = true := by rfl

def kid01_part506 : Audit := .cycle 8 2 true (1)
theorem kid01_part506_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part506) = true := by rfl

def kid01_part507 : Audit := .cycle 1 10 true (1)
theorem kid01_part507_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part507) = true := by rfl

def kid01_part508 : Audit := .cycle 0 11 true (0)
theorem kid01_part508_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part508) = true := by rfl

def kid01_part510 : Audit := .cycle 0 11 true (0)
theorem kid01_part510_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part510) = true := by rfl

def kid01_part511 : Audit := .cycle 1 10 true (1)
theorem kid01_part511_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part511) = true := by rfl

def kid01_part512 : Audit := .cycle 21 1 false (1)
theorem kid01_part512_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part512) = true := by rfl

def kid01_part513 : Audit := .cycle 23 1 false (1)
theorem kid01_part513_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part513) = true := by rfl

def kid01_part514 : Audit := .split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1)
])
theorem kid01_part514_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part514) = true := by rfl

def kid01_part515 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
])
theorem kid01_part515_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part515) = true := by rfl

def kid01_part516 : Audit := .cycle 0 11 true (0)
theorem kid01_part516_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part516) = true := by rfl

def kid01_part517 : Audit := .cycle 1 10 true (1)
theorem kid01_part517_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part517) = true := by rfl

def kid01_part518 : Audit := .cycle 35 1 false (7)
theorem kid01_part518_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part518) = true := by rfl

def kid01_part519 : Audit := .cycle 20 1 false (2)
theorem kid01_part519_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part519) = true := by rfl

def kid01_part520 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid01_part520_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part520) = true := by rfl

def kid01_part521 : Audit := .split 12 (4,false) (byMove [
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
.last 15 (5,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 24 (5,true),
.last 17 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid01_part521_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part521) = true := by rfl

def kid01_part522 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 29 true (-2),
.cycle 29 1 false (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.last 16 (4,false),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.last 16 (4,false),
.cycle 19 3 false (0),
.cycle 14 8 false (0),
.cycle 16 15 true (0),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 14 5 false (0),
.cycle 2 13 true (1),
.cycle 12 2 true (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 17 9 false (1),
.last 16 (4,false)
])
theorem kid01_part522_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part522) = true := by rfl

def kid01_part523 : Audit := .split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 21 5 false (3),
.cycle 15 5 false (1),
.cycle 22 5 false (2),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.last 17 (4,false),
.cycle 13 3 false (1),
.cycle 15 5 false (0),
.cycle 23 5 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 16 5 false (0),
.last 17 (4,false)
])
theorem kid01_part523_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part523) = true := by rfl

def kid01_part524 : Audit := .cycle 0 13 true (0)
theorem kid01_part524_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part524) = true := by rfl

def kid01_part525 : Audit := .cycle 18 1 false (0)
theorem kid01_part525_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part525) = true := by rfl

def kid01_part526 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 25 1 false (-1),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 20 (5,true),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid01_part526_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part526) = true := by rfl

def kid01_part527 : Audit := .cycle 9 2 true (1)
theorem kid01_part527_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part527) = true := by rfl

def kid01_part528 : Audit := .cycle 0 11 true (0)
theorem kid01_part528_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part528) = true := by rfl

def kid01_part529 : Audit := .cycle 1 10 true (1)
theorem kid01_part529_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part529) = true := by rfl

def kid01_part530 : Audit := .cycle 2 9 true (1)
theorem kid01_part530_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part530) = true := by rfl

def kid01_part531 : Audit := .cycle 2 12 true (1)
theorem kid01_part531_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part531) = true := by rfl

def kid01_part532 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (1),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid01_part532_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part532) = true := by rfl

def kid01_part533 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.cycle 9 13 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid01_part533_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part533) = true := by rfl

def kid01_part509 : Audit := .split 10 (4,true) (byMove [(kid01_part510),(kid01_part511),(kid01_part512),(kid01_part513),(kid01_part514),(kid01_part515),(kid01_part516),(kid01_part517),(kid01_part518),(kid01_part519),(kid01_part520),(kid01_part521),(kid01_part522),(kid01_part523),(kid01_part524),(kid01_part525),(kid01_part526),(kid01_part527),(kid01_part528),(kid01_part529),(kid01_part530),(kid01_part531),(kid01_part532),(kid01_part533)])

theorem kid01_part509_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part509) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid01_part510),(kid01_part511),(kid01_part512),(kid01_part513),(kid01_part514),(kid01_part515),(kid01_part516),(kid01_part517),(kid01_part518),(kid01_part519),(kid01_part520),(kid01_part521),(kid01_part522),(kid01_part523),(kid01_part524),(kid01_part525),(kid01_part526),(kid01_part527),(kid01_part528),(kid01_part529),(kid01_part530),(kid01_part531),(kid01_part532),(kid01_part533)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part510_checked

  · exact kid01_part516_checked

  · exact kid01_part522_checked

  · exact kid01_part528_checked

  · exact kid01_part511_checked

  · exact kid01_part517_checked

  · exact kid01_part523_checked

  · exact kid01_part529_checked

  · exact kid01_part512_checked

  · exact kid01_part518_checked

  · exact kid01_part524_checked

  · exact kid01_part530_checked

  · exact kid01_part513_checked

  · exact kid01_part519_checked

  · exact kid01_part525_checked

  · exact kid01_part531_checked

  · exact kid01_part514_checked

  · exact kid01_part520_checked

  · exact kid01_part526_checked

  · exact kid01_part532_checked

  · exact kid01_part515_checked

  · exact kid01_part521_checked

  · exact kid01_part527_checked

  · exact kid01_part533_checked

def kid01_part534 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 12 1 true (2),
.cycle 16 4 false (0),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
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
.last 14 (4,true),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 15 (4,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 40 true (-2),
.cycle 25 1 false (-1),
.cycle 17 1 false (-1),
.last 12 (4,true),
.cycle 12 4 true (-2),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 16 4 false (0),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.last 14 (4,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (1),
.last 15 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid01_part534_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part534) = true := by rfl

def kid01_part535 : Audit := .split 16 (5,true) (byMove [
.cycle 15 5 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 15, 15, 1, 64, 15, 64],80⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.last 42 (4,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.last 40 (4,true),
.cycle 18 1 false (-2),
.last 19 (4,true),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 21 (4,true),
.cycle 15 5 false (-1),
.last 40 (4,true),
.cycle 10 10 false (1),
.last 19 (4,true),
.cycle 9 9 false (1)
]),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.cycle 12 5 false (0),
.cycle 0 41 true (-2),
.cycle 0 21 true (-2),
.split 17 (4,true) (byMove [
.cycle 0 24 false (3),
.cycle 0 41 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.last 18 (4,false),
.cycle 13 5 false (-1),
.cycle 0 21 true (-2),
.cycle 12 6 true (-2),
.cycle 10 14 true (-2),
.cycle 23 1 false (3),
.last 19 (4,false),
.last 19 (4,false),
.cycle 14 4 true (-2),
.cycle 11 8 false (1),
.cycle 0 23 true (-2),
.cycle 18 1 false (-2),
.last 18 (4,false),
.cycle 13 5 false (-1),
.cycle 0 21 true (-2),
.cycle 1 25 true (-2),
.cycle 11 7 false (1),
.cycle 28 38 true (1),
.last 19 (4,false),
.last 19 (4,false)
]),
.cycle 23 5 true (1),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 15 6 false (-1),
.last 28 (4,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.last 42 (4,true),
.cycle 10 9 false (1),
.last 18 (4,true),
.cycle 16 2 true (-3),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 10 10 false (1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 15 5 false (-1),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.cycle 5 13 false (3),
.last 18 (4,true),
.last 19 (4,true)
]),
.cycle 13 4 false (-1),
.cycle 2 20 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.split 17 (4,true) (byMove [
.cycle 0 41 true (-2),
.cycle 12 6 false (0),
.cycle 10 14 false (1),
.cycle 0 31 true (-2),
.last 19 (4,false),
.last 19 (4,false),
.cycle 0 21 true (-2),
.cycle 8 10 false (2),
.cycle 1 18 false (3),
.cycle 0 35 true (-2),
.last 19 (4,false),
.last 19 (4,false),
.cycle 10 8 false (1),
.cycle 12 6 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 15, 15, 1, 15, 16, 64],80⟩,
.cycle 10 9 false (1),
.last 19 (4,false),
.cycle 16 2 true (-2),
.cycle 0 21 true (-2),
.cycle 18 19 true (-1),
.cycle 2 20 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 15, 15, 1, 8, 16, 64],80⟩,
.last 19 (4,false),
.last 19 (4,false)
]),
.cycle 17 6 true (-1)
])
theorem kid01_part535_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part535) = true := by rfl

def kid01_part536 : Audit := .cycle 10 4 false (0)
theorem kid01_part536_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part536) = true := by rfl

def kid01_part537 : Audit := .cycle 12 11 true (0)
theorem kid01_part537_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part537) = true := by rfl

def kid01_part538 : Audit := .cycle 15 1 false (-1)
theorem kid01_part538_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part538) = true := by rfl

def kid01_part540 : Audit := .split 15 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.last 17 (4,false),
.cycle 0 19 true (-1),
.last 18 (4,false),
.last 26 (4,false),
.cycle 0 21 true (-1),
.cycle 0 21 true (-1),
.last 18 (4,false),
.cycle 14 3 false (0),
.last 20 (4,false),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.last 17 (4,false),
.cycle 0 19 true (-1),
.cycle 14 2 true (-1),
.last 19 (4,false),
.cycle 0 21 true (-1),
.last 26 (4,false),
.last 31 (4,false)
])
theorem kid01_part540_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part540) = true := by rfl

def kid01_part541 : Audit := .split 23 (4,false) (byMove [
.last 28 (5,true),
.cycle 11 13 true (-1),
.cycle 34 1 false (-2),
.cycle 12 15 true (-1),
.cycle 35 1 false (-3),
.last 31 (5,true),
.cycle 6 23 false (4),
.cycle 24 11 false (2),
.cycle 0 28 true (-1),
.cycle 13 11 true (1),
.cycle 0 28 true (-1),
.last 24 (5,true),
.last 26 (5,true),
.last 27 (5,true),
.cycle 24 9 false (3),
.cycle 31 1 false (-3),
.cycle 24 9 false (2),
.last 34 (5,true),
.last 27 (5,true),
.last 25 (5,true),
.cycle 0 34 true (-2),
.cycle 13 11 true (1),
.cycle 0 34 true (-2),
.last 24 (5,true)
])
theorem kid01_part541_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part541) = true := by rfl

def kid01_part542 : Audit := .cycle 12 1 false (0)
theorem kid01_part542_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part542) = true := by rfl

def kid01_part543 : Audit := .cycle 11 1 false (-1)
theorem kid01_part543_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part543) = true := by rfl

def kid01_part544 : Audit := .split 11 (4,false) (byMove [
.last 30 (5,true),
.cycle 26 13 true (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (5,true),
.cycle 14 3 false (0),
.cycle 0 28 true (-1),
.cycle 12 1 false (0),
.cycle 17 1 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 16 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 34 true (-2),
.cycle 0 23 true (-2),
.cycle 25 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid01_part544_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part544) = true := by rfl

def kid01_part545 : Audit := .split 12 (4,false) (byMove [
.last 17 (5,true),
.last 18 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 6 25 false (4),
.cycle 11 3 false (-1),
.last 30 (5,true),
.last 16 (5,true),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 15 (5,true),
.cycle 11 5 false (-1),
.cycle 28 9 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 29 (5,true),
.last 14 (5,true),
.cycle 11 4 false (-1),
.last 16 (5,true),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid01_part545_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part545) = true := by rfl

def kid01_part546 : Audit := .split 15 (4,false) (byMove [
.last 20 (5,true),
.cycle 11 13 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.cycle 13 3 false (1),
.cycle 0 20 true (-1),
.cycle 11 11 true (-1),
.cycle 11 11 true (-1),
.last 16 (5,true),
.last 18 (5,true),
.cycle 12 5 false (2),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 19 (5,true),
.last 17 (5,true),
.cycle 12 4 false (2),
.cycle 11 11 true (-1),
.cycle 11 11 true (-1),
.last 16 (5,true)
])
theorem kid01_part546_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part546) = true := by rfl

def kid01_part547 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.cycle 29 13 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 5 false (1),
.cycle 11 3 false (1),
.cycle 0 32 true (-1),
.cycle 14 11 true (-1),
.cycle 10 4 true (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.last 17 (5,true),
.last 15 (5,true),
.cycle 11 4 false (1),
.cycle 5 9 false (3),
.cycle 8 7 false (2),
.last 14 (5,true)
])
theorem kid01_part547_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part547) = true := by rfl

def kid01_part548 : Audit := .cycle 0 15 true (0)
theorem kid01_part548_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part548) = true := by rfl

def kid01_part549 : Audit := .split 21 (4,false) (byMove [
.last 26 (5,true),
.cycle 11 13 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 17 5 false (4),
.cycle 19 3 false (3),
.cycle 0 26 true (0),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.last 22 (5,true),
.last 24 (5,true),
.cycle 18 5 false (4),
.cycle 16 7 false (4),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.last 25 (5,true),
.last 23 (5,true),
.cycle 18 4 false (4),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.last 22 (5,true)
])
theorem kid01_part549_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part549) = true := by rfl

def kid01_part550 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 15 13 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 21 3 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.last 16 (5,true),
.last 16 (5,true),
.cycle 13 5 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (5),
.cycle 15 11 true (3),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid01_part550_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part550) = true := by rfl

def kid01_part551 : Audit := .split 11 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.last 21 (4,false),
.last 14 (4,false),
.last 22 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 11 3 false (1),
.last 16 (4,false),
.last 23 (4,false),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 2 11 true (0),
.cycle 11 2 true (1),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.cycle 12 3 true (2)
])
theorem kid01_part551_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part551) = true := by rfl

def kid01_part552 : Audit := .split 13 (5,true) (byMove [
.cycle 12 5 false (0),
.last 21 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.last 27 (4,false),
.last 19 (4,false),
.cycle 10 4 true (-1),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 18 (4,false),
.last 20 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 21 true (-1),
.cycle 12 2 true (-1),
.last 17 (4,false),
.cycle 5 9 false (3),
.last 19 (4,false),
.last 37 (4,false)
])
theorem kid01_part552_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part552) = true := by rfl

def kid01_part553 : Audit := .split 15 (4,false) (byMove [
.last 20 (5,true),
.cycle 20 13 true (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 5 false (0),
.cycle 13 3 false (-1),
.last 22 (5,true),
.cycle 19 11 true (1),
.cycle 10 6 false (0),
.last 16 (5,true),
.last 18 (5,true),
.cycle 11 5 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.last 17 (5,true),
.cycle 12 4 false (0),
.cycle 19 11 true (1),
.cycle 13 4 false (-1),
.last 16 (5,true)
])
theorem kid01_part553_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part553) = true := by rfl

def kid01_part554 : Audit := .split 17 (4,false) (byMove [
.last 22 (5,true),
.cycle 12 13 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.cycle 15 3 false (1),
.cycle 0 22 true (-1),
.cycle 12 11 true (-1),
.cycle 12 13 true (-1),
.last 18 (5,true),
.last 20 (5,true),
.cycle 14 5 false (2),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.last 19 (5,true),
.cycle 14 4 false (2),
.cycle 12 11 true (-1),
.cycle 12 15 true (-2),
.last 18 (5,true)
])
theorem kid01_part554_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part554) = true := by rfl

def kid01_part555 : Audit := .cycle 11 1 false (-1)
theorem kid01_part555_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part555) = true := by rfl

def kid01_part556 : Audit := .split 11 (4,false) (byMove [
.last 16 (5,true),
.cycle 27 13 true (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 5 false (1),
.cycle 11 3 false (0),
.cycle 0 30 true (-1),
.cycle 12 11 true (-1),
.cycle 10 2 true (-1),
.last 12 (5,true),
.last 14 (5,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 13 (5,true),
.cycle 11 4 false (0),
.cycle 5 7 false (3),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid01_part556_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part556) = true := by rfl

def kid01_part557 : Audit := .split 12 (4,false) (byMove [
.last 17 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M19.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M19.never m hm),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.cycle 11 3 false (-1),
.cycle 0 26 true (-2),
.cycle 0 23 true (-2),
.cycle 10 3 false (0),
.last 13 (5,true),
.last 15 (5,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid01_part557_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part557) = true := by rfl

def kid01_part558 : Audit := .split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 13 3 false (1),
.last 19 (4,false),
.last 26 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.last 18 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 2 17 true (0)
])
theorem kid01_part558_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part558) = true := by rfl

def kid01_part559 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.last 25 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 15 (4,false),
.cycle 0 17 true (0),
.last 23 (4,false),
.cycle 1 16 true (0),
.last 16 (4,false),
.cycle 11 3 false (1),
.last 17 (4,false),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 2 16 true (0),
.cycle 11 2 true (0),
.last 16 (4,false),
.last 23 (4,false),
.cycle 1 16 true (0),
.cycle 13 5 true (1)
])
theorem kid01_part559_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part559) = true := by rfl

def kid01_part560 : Audit := .split 14 (4,false) (byMove [
.last 19 (5,true),
.proven (BB6.Agent11Raw39B1RCPumps.M20.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M20.never m hm),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 5 false (1),
.cycle 12 3 false (0),
.last 21 (5,true),
.cycle 0 19 true (-2),
.cycle 10 5 false (1),
.last 15 (5,true),
.last 17 (5,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.last 16 (5,true),
.cycle 11 4 false (1),
.cycle 0 19 true (-2),
.last 18 (5,true),
.last 15 (5,true)
])
theorem kid01_part560_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part560) = true := by rfl

def kid01_part561 : Audit := .split 21 (4,false) (byMove [
.last 39 (5,true),
.cycle 29 13 true (1),
.cycle 34 1 false (-2),
.last 25 (5,true),
.cycle 29 1 false (-1),
.last 22 (5,true),
.cycle 6 16 true (0),
.cycle 5 20 true (0),
.cycle 0 26 true (0),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.last 22 (5,true),
.last 29 (5,true),
.cycle 22 5 false (0),
.cycle 16 9 false (4),
.cycle 28 1 false (-2),
.cycle 5 18 true (0),
.last 22 (5,true),
.last 25 (5,true),
.last 23 (5,true),
.last 24 (5,true),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.last 22 (5,true)
])
theorem kid01_part561_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part561) = true := by rfl

def kid01_part562 : Audit := .split 13 (4,false) (byMove [
.cycle 2 13 true (0),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 10 17 true (0),
.cycle 1 27 true (0),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.last 16 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 5 29 true (0),
.cycle 11 3 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 11 true (3),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid01_part562_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part562) = true := by rfl

def kid01_part563 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 14 (4,false),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 9 4 true (0),
.last 14 (4,false),
.last 21 (4,false),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 16 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.last 14 (4,false),
.last 25 (4,false),
.last 17 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 2 11 true (0),
.cycle 11 2 true (1),
.last 18 (4,false),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 12 3 true (2)
])
theorem kid01_part563_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part563) = true := by rfl

def kid01_part539 : Audit := .split 10 (4,true) (byMove [(kid01_part540),(kid01_part541),(kid01_part542),(kid01_part543),(kid01_part544),(kid01_part545),(kid01_part546),(kid01_part547),(kid01_part548),(kid01_part549),(kid01_part550),(kid01_part551),(kid01_part552),(kid01_part553),(kid01_part554),(kid01_part555),(kid01_part556),(kid01_part557),(kid01_part558),(kid01_part559),(kid01_part560),(kid01_part561),(kid01_part562),(kid01_part563)])

theorem kid01_part539_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part539) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part540),(kid01_part541),(kid01_part542),(kid01_part543),(kid01_part544),(kid01_part545),(kid01_part546),(kid01_part547),(kid01_part548),(kid01_part549),(kid01_part550),(kid01_part551),(kid01_part552),(kid01_part553),(kid01_part554),(kid01_part555),(kid01_part556),(kid01_part557),(kid01_part558),(kid01_part559),(kid01_part560),(kid01_part561),(kid01_part562),(kid01_part563)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part540_checked

  · exact kid01_part546_checked

  · exact kid01_part552_checked

  · exact kid01_part558_checked

  · exact kid01_part541_checked

  · exact kid01_part547_checked

  · exact kid01_part553_checked

  · exact kid01_part559_checked

  · exact kid01_part542_checked

  · exact kid01_part548_checked

  · exact kid01_part554_checked

  · exact kid01_part560_checked

  · exact kid01_part543_checked

  · exact kid01_part549_checked

  · exact kid01_part555_checked

  · exact kid01_part561_checked

  · exact kid01_part544_checked

  · exact kid01_part550_checked

  · exact kid01_part556_checked

  · exact kid01_part562_checked

  · exact kid01_part545_checked

  · exact kid01_part551_checked

  · exact kid01_part557_checked

  · exact kid01_part563_checked

def kid01_part564 : Audit := .split 10 (5,true) (byMove [
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 28 (4,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 10 4 true (-1),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 1 false (0),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 10 6 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 15 (4,true),
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.cycle 12 1 false (0),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.split 11 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 2 11 true (0),
.cycle 1 14 true (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 13 1 false (3),
.cycle 10 3 false (0),
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
.cycle 13 1 false (-1),
.cycle 25 11 false (2),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 10 4 false (0),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 10 5 false (1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 5 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 2 14 true (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 5 18 true (0),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 6 18 true (0),
.cycle 8 4 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 25 11 false (2),
.cycle 16 1 false (0),
.last 13 (4,false),
.cycle 10 2 true (0),
.cycle 2 11 true (0),
.cycle 1 14 true (0),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false)
]),
.cycle 11 3 true (1)
])
theorem kid01_part564_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part564) = true := by rfl

def kid01_part565 : Audit := .cycle 2 9 true (1)
theorem kid01_part565_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part565) = true := by rfl

def kid01_part566 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 0 17 true (-1),
.last 16 (4,false),
.last 19 (4,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 16 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 18 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 16 (4,false),
.cycle 10 4 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 9 4 true (0)
]),
.cycle 0 17 true (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 1 13 true (1),
.cycle 10 4 true (1),
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
.cycle 1 13 true (1)
]),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.last 18 (4,false),
.last 27 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 18 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 0 17 true (0),
.last 25 (4,false),
.last 15 (4,false),
.last 14 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 16 (4,false),
.last 17 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 25 (4,false),
.last 15 (4,false),
.cycle 11 2 true (0)
]),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 5 false (1),
.cycle 13 13 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 1 13 true (1),
.cycle 15 7 false (1),
.cycle 13 5 false (1),
.cycle 0 31 true (-2),
.cycle 2 13 true (1),
.last 15 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 1 13 true (1)
]),
.cycle 1 13 true (1)
])
theorem kid01_part566_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part566) = true := by rfl

def kid01_part567 : Audit := .split 12 (5,true) (byMove [
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
.cycle 11 4 true (-1),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 15 (4,true),
.cycle 14 3 false (1),
.cycle 11 4 false (1),
.cycle 15 3 false (-1),
.cycle 11 6 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.last 17 (4,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 9 5 false (2)
]),
.cycle 0 16 true (-1),
.cycle 19 3 false (3),
.cycle 13 3 false (1),
.cycle 20 3 false (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
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
.cycle 11 4 true (0),
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
.cycle 20 3 false (4),
.cycle 11 3 false (1),
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
.cycle 14 3 false (0),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.last 14 (4,true),
.cycle 12 2 true (-1),
.cycle 11 4 false (1),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 3 false (-1),
.cycle 10 5 false (2),
.cycle 11 3 false (1),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 3 false (0),
.cycle 2 12 true (0),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 20 3 false (2),
.cycle 14 3 false (0),
.cycle 21 3 false (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.last 14 (4,false),
.cycle 7 16 true (0),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.last 15 (4,false),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 18 true (0),
.last 14 (4,false),
.cycle 2 13 true (0)
]),
.cycle 2 13 true (0)
])
theorem kid01_part567_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part567) = true := by rfl

def kid01_part568 : Audit := .cycle 0 11 true (0)
theorem kid01_part568_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part568) = true := by rfl

def kid01_part570 : Audit := .cycle 2 10 true (1)
theorem kid01_part570_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part570) = true := by rfl

def kid01_part571 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 20 3 false (2),
.cycle 13 3 false (1),
.cycle 21 3 false (1),
.cycle 0 14 true (0),
.cycle 21 3 false (1),
.last 15 (4,false),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 22 3 false (2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 2 12 true (0),
.cycle 11 2 true (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 13 3 false (1),
.last 15 (4,false)
])
theorem kid01_part571_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part571) = true := by rfl

def kid01_part572 : Audit := .cycle 11 11 false (1)
theorem kid01_part572_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part572) = true := by rfl

def kid01_part573 : Audit := .cycle 0 12 true (0)
theorem kid01_part573_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part573) = true := by rfl

def kid01_part574 : Audit := .split 13 (4,false) (byMove [
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
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.cycle 10 15 false (3),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-1),
.cycle 13 1 true (-1),
.cycle 13 2 true (-1)
])
theorem kid01_part574_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part574) = true := by rfl

def kid01_part575 : Audit := .split 11 (5,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 14 (4,false),
.cycle 12 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid01_part575_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part575) = true := by rfl

def kid01_part576 : Audit := .cycle 0 11 true (0)
theorem kid01_part576_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part576) = true := by rfl

def kid01_part577 : Audit := .cycle 1 10 true (1)
theorem kid01_part577_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part577) = true := by rfl

def kid01_part578 : Audit := .cycle 0 23 true (0)
theorem kid01_part578_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part578) = true := by rfl

def kid01_part579 : Audit := .cycle 3 8 true (1)
theorem kid01_part579_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part579) = true := by rfl

def kid01_part580 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 17 1 false (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 14 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 25 1 false (5),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid01_part580_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part580) = true := by rfl

def kid01_part581 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 1 13 true (1),
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
.last 16 (5,true),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid01_part581_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part581) = true := by rfl

def kid01_part582 : Audit := .split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 20 5 false (3),
.cycle 15 5 false (1),
.cycle 21 5 false (2),
.cycle 0 16 true (0),
.cycle 13 4 true (0),
.last 17 (4,false),
.cycle 13 3 false (1),
.cycle 16 5 false (0),
.cycle 22 5 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 2 14 true (0),
.cycle 13 2 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.last 17 (4,false)
])
theorem kid01_part582_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part582) = true := by rfl

def kid01_part583 : Audit := .split 12 (5,true) (byMove [
.cycle 11 5 false (1),
.cycle 26 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 15 3 false (1),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.cycle 21 3 false (3),
.cycle 16 3 false (0),
.last 16 (4,false),
.cycle 11 3 false (1),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 2 16 true (0),
.cycle 11 2 true (0),
.cycle 14 3 false (0),
.cycle 5 24 true (0),
.cycle 13 3 false (1),
.last 16 (4,false)
])
theorem kid01_part583_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part583) = true := by rfl

def kid01_part584 : Audit := .split 21 (5,true) (byMove [
.cycle 0 35 true (-2),
.cycle 0 25 true (-2),
.cycle 11 17 false (2),
.cycle 20 17 false (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 0 36 true (-2),
.cycle 0 29 true (-2),
.cycle 0 37 true (-2),
.cycle 0 23 true (-2),
.cycle 0 25 true (-2),
.last 24 (4,false),
.cycle 11 18 false (2),
.cycle 7 16 false (3),
.cycle 0 38 true (-2),
.cycle 11 15 false (2),
.last 22 (4,false),
.cycle 0 42 true (-2),
.cycle 2 21 true (-2),
.cycle 20 2 true (1),
.cycle 0 30 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 16, 64],[4, 1, 10, 1, 1, 8, 64],112⟩,
.cycle 0 27 true (-2),
.last 24 (4,false)
])
theorem kid01_part584_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part584) = true := by rfl

def kid01_part585 : Audit := .cycle 2 11 true (1)
theorem kid01_part585_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part585) = true := by rfl

def kid01_part586 : Audit := .split 13 (4,false) (byMove [
.last 18 (5,true),
.cycle 33 15 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 11 5 false (1),
.cycle 0 34 true (-1),
.cycle 14 13 true (-1),
.cycle 12 2 true (-1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 11 6 false (1),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.last 14 (5,true)
])
theorem kid01_part586_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part586) = true := by rfl

def kid01_part587 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.cycle 25 1 false (-1),
.cycle 16 1 false (0),
.last 16 (4,false),
.last 14 (4,false),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.last 14 (4,false),
.cycle 17 3 false (-1),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 2 11 true (1),
.cycle 11 2 true (1),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 14 (4,false)
])
theorem kid01_part587_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part587) = true := by rfl

def kid01_part588 : Audit := .cycle 0 11 true (0)
theorem kid01_part588_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part588) = true := by rfl

def kid01_part589 : Audit := .cycle 1 10 true (1)
theorem kid01_part589_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part589) = true := by rfl

def kid01_part590 : Audit := .cycle 2 9 true (1)
theorem kid01_part590_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part590) = true := by rfl

def kid01_part591 : Audit := .cycle 2 12 true (1)
theorem kid01_part591_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part591) = true := by rfl

def kid01_part592 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 15 (5,true),
.last 13 (5,true),
.last 14 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid01_part592_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part592) = true := by rfl

def kid01_part593 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 14 (5,true),
.last 15 (5,true),
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
.last 14 (5,true),
.last 15 (5,true),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid01_part593_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part593) = true := by rfl

def kid01_part569 : Audit := .split 10 (4,true) (byMove [(kid01_part570),(kid01_part571),(kid01_part572),(kid01_part573),(kid01_part574),(kid01_part575),(kid01_part576),(kid01_part577),(kid01_part578),(kid01_part579),(kid01_part580),(kid01_part581),(kid01_part582),(kid01_part583),(kid01_part584),(kid01_part585),(kid01_part586),(kid01_part587),(kid01_part588),(kid01_part589),(kid01_part590),(kid01_part591),(kid01_part592),(kid01_part593)])

theorem kid01_part569_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part569) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid01_part570),(kid01_part571),(kid01_part572),(kid01_part573),(kid01_part574),(kid01_part575),(kid01_part576),(kid01_part577),(kid01_part578),(kid01_part579),(kid01_part580),(kid01_part581),(kid01_part582),(kid01_part583),(kid01_part584),(kid01_part585),(kid01_part586),(kid01_part587),(kid01_part588),(kid01_part589),(kid01_part590),(kid01_part591),(kid01_part592),(kid01_part593)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part570_checked

  · exact kid01_part576_checked

  · exact kid01_part582_checked

  · exact kid01_part588_checked

  · exact kid01_part571_checked

  · exact kid01_part577_checked

  · exact kid01_part583_checked

  · exact kid01_part589_checked

  · exact kid01_part572_checked

  · exact kid01_part578_checked

  · exact kid01_part584_checked

  · exact kid01_part590_checked

  · exact kid01_part573_checked

  · exact kid01_part579_checked

  · exact kid01_part585_checked

  · exact kid01_part591_checked

  · exact kid01_part574_checked

  · exact kid01_part580_checked

  · exact kid01_part586_checked

  · exact kid01_part592_checked

  · exact kid01_part575_checked

  · exact kid01_part581_checked

  · exact kid01_part587_checked

  · exact kid01_part593_checked

def kid01_part594 : Audit := .split 10 (5,true) (byMove [
.cycle 2 10 true (1),
.cycle 0 16 true (-1),
.cycle 11 11 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.last 21 (4,false),
.cycle 12 6 false (0),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
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
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3),
.cycle 13 3 false (1),
.cycle 15 3 false (-1),
.cycle 0 38 true (-2),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 22 (4,false),
.cycle 25 1 false (-1),
.last 16 (4,false),
.last 13 (4,false),
.last 13 (4,false),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.last 21 (4,false),
.cycle 12 6 false (0),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 2 11 true (1),
.last 17 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 10 2 true (1)
]),
.cycle 11 3 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 12 1 true (4)
]),
.cycle 11 1 true (3)
])
theorem kid01_part594_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part594) = true := by rfl

def kid01_part474 : Audit := .split 9 (5,false) (byMove [(kid01_part475),(kid01_part476),(kid01_part477),(kid01_part478),(kid01_part479),(kid01_part504),(kid01_part505),(kid01_part506),(kid01_part507),(kid01_part508),(kid01_part509),(kid01_part534),(kid01_part535),(kid01_part536),(kid01_part537),(kid01_part538),(kid01_part539),(kid01_part564),(kid01_part565),(kid01_part566),(kid01_part567),(kid01_part568),(kid01_part569),(kid01_part594)])

theorem kid01_part474_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (kid01_part474) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid01_part475),(kid01_part476),(kid01_part477),(kid01_part478),(kid01_part479),(kid01_part504),(kid01_part505),(kid01_part506),(kid01_part507),(kid01_part508),(kid01_part509),(kid01_part534),(kid01_part535),(kid01_part536),(kid01_part537),(kid01_part538),(kid01_part539),(kid01_part564),(kid01_part565),(kid01_part566),(kid01_part567),(kid01_part568),(kid01_part569),(kid01_part594)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part475_checked

  · exact kid01_part505_checked

  · exact kid01_part535_checked

  · exact kid01_part565_checked

  · exact kid01_part476_checked

  · exact kid01_part506_checked

  · exact kid01_part536_checked

  · exact kid01_part566_checked

  · exact kid01_part477_checked

  · exact kid01_part507_checked

  · exact kid01_part537_checked

  · exact kid01_part567_checked

  · exact kid01_part478_checked

  · exact kid01_part508_checked

  · exact kid01_part538_checked

  · exact kid01_part568_checked

  · exact kid01_part479_checked

  · exact kid01_part509_checked

  · exact kid01_part539_checked

  · exact kid01_part569_checked

  · exact kid01_part504_checked

  · exact kid01_part534_checked

  · exact kid01_part564_checked

  · exact kid01_part594_checked

def kid01_part595 : Audit := .cycle 0 9 true (0)
theorem kid01_part595_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,0⟩)) (kid01_part595) = true := by rfl

def kid01_part596 : Audit := .cycle 1 8 true (1)
theorem kid01_part596_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,1⟩)) (kid01_part596) = true := by rfl

def kid01_part597 : Audit := .cycle 2 7 true (1)
theorem kid01_part597_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,2⟩)) (kid01_part597) = true := by rfl

def kid01_part598 : Audit := .cycle 2 10 true (1)
theorem kid01_part598_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,3⟩)) (kid01_part598) = true := by rfl

def kid01_part600 : Audit := .cycle 2 9 true (1)
theorem kid01_part600_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part600) = true := by rfl

def kid01_part601 : Audit := .cycle 8 2 true (2)
theorem kid01_part601_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part601) = true := by rfl

def kid01_part602 : Audit := .cycle 1 10 true (1)
theorem kid01_part602_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part602) = true := by rfl

def kid01_part603 : Audit := .cycle 0 11 true (0)
theorem kid01_part603_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part603) = true := by rfl

def kid01_part604 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.last 22 (5,true),
.last 14 (5,true),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 14 1 false (-2),
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
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 9 false (2),
.cycle 15 2 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 23 (5,true),
.cycle 25 1 false (-1),
.last 17 (5,true),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 21 (5,true),
.last 14 (5,true),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 9 4 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid01_part604_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part604) = true := by rfl

def kid01_part606 : Audit := .cycle 0 11 true (0)
theorem kid01_part606_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part606) = true := by rfl

def kid01_part607 : Audit := .cycle 1 10 true (1)
theorem kid01_part607_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part607) = true := by rfl

def kid01_part608 : Audit := .cycle 21 1 false (1)
theorem kid01_part608_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part608) = true := by rfl

def kid01_part609 : Audit := .cycle 23 1 false (1)
theorem kid01_part609_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part609) = true := by rfl

def kid01_part610 : Audit := .split 14 (5,false) (byMove [
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
.last 19 (4,true),
.cycle 11 7 false (1),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 28 (4,true),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 11 4 false (1),
.cycle 14 1 true (-2)
])
theorem kid01_part610_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part610) = true := by rfl

def kid01_part611 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 2 true (1),
.cycle 11 1 true (1),
.cycle 16 6 false (0),
.last 13 (4,true),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 14 3 false (0),
.cycle 11 1 true (1)
])
theorem kid01_part611_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part611) = true := by rfl

def kid01_part612 : Audit := .cycle 0 11 true (0)
theorem kid01_part612_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part612) = true := by rfl

def kid01_part613 : Audit := .cycle 1 10 true (1)
theorem kid01_part613_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part613) = true := by rfl

def kid01_part614 : Audit := .cycle 35 1 false (7)
theorem kid01_part614_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part614) = true := by rfl

def kid01_part615 : Audit := .cycle 20 1 false (2)
theorem kid01_part615_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part615) = true := by rfl

def kid01_part616 : Audit := .split 12 (5,false) (byMove [
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
.cycle 21 13 false (2),
.last 21 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
])
theorem kid01_part616_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part616) = true := by rfl

def kid01_part617 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid01_part617_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part617) = true := by rfl

def kid01_part618 : Audit := .cycle 17 9 false (2)
theorem kid01_part618_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part618) = true := by rfl

def kid01_part619 : Audit := .split 17 (4,true) (byMove [
.cycle 24 5 false (2),
.cycle 18 5 false (1),
.cycle 25 5 false (1),
.cycle 0 19 true (0),
.last 20 (5,false),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 7 22 true (0),
.cycle 24 5 false (2),
.cycle 22 5 false (2),
.last 19 (5,false),
.last 18 (5,false),
.cycle 19 5 false (1),
.cycle 16 2 true (0),
.cycle 0 22 true (-1),
.cycle 25 5 false (3),
.last 20 (5,false),
.cycle 18 5 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 7 24 true (0),
.cycle 14 4 true (0),
.last 18 (5,false)
])
theorem kid01_part619_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part619) = true := by rfl

def kid01_part620 : Audit := .cycle 0 13 true (0)
theorem kid01_part620_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part620) = true := by rfl

def kid01_part621 : Audit := .cycle 18 1 false (0)
theorem kid01_part621_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part621) = true := by rfl

def kid01_part622 : Audit := .split 14 (5,false) (byMove [
.last 23 (4,true),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 19 (4,true),
.cycle 11 7 false (1),
.last 21 (4,true),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 12 4 true (-2),
.last 19 (4,true),
.cycle 11 7 false (1),
.last 21 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 19 (4,true),
.last 20 (4,true),
.last 21 (4,true),
.cycle 11 9 false (1),
.cycle 11 4 false (1),
.last 17 (4,true)
])
theorem kid01_part622_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part622) = true := by rfl

def kid01_part623 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 42 true (-2),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 20 (4,true),
.last 13 (4,true),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 2 11 true (1),
.last 19 (4,true),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid01_part623_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part623) = true := by rfl

def kid01_part624 : Audit := .cycle 0 11 true (0)
theorem kid01_part624_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part624) = true := by rfl

def kid01_part625 : Audit := .cycle 1 10 true (1)
theorem kid01_part625_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part625) = true := by rfl

def kid01_part626 : Audit := .cycle 2 9 true (1)
theorem kid01_part626_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part626) = true := by rfl

def kid01_part627 : Audit := .cycle 2 12 true (1)
theorem kid01_part627_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part627) = true := by rfl

def kid01_part628 : Audit := .cycle 9 2 true (2)
theorem kid01_part628_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part628) = true := by rfl

def kid01_part629 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid01_part629_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part629) = true := by rfl

def kid01_part605 : Audit := .split 10 (5,true) (byMove [(kid01_part606),(kid01_part607),(kid01_part608),(kid01_part609),(kid01_part610),(kid01_part611),(kid01_part612),(kid01_part613),(kid01_part614),(kid01_part615),(kid01_part616),(kid01_part617),(kid01_part618),(kid01_part619),(kid01_part620),(kid01_part621),(kid01_part622),(kid01_part623),(kid01_part624),(kid01_part625),(kid01_part626),(kid01_part627),(kid01_part628),(kid01_part629)])

theorem kid01_part605_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part605) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part606),(kid01_part607),(kid01_part608),(kid01_part609),(kid01_part610),(kid01_part611),(kid01_part612),(kid01_part613),(kid01_part614),(kid01_part615),(kid01_part616),(kid01_part617),(kid01_part618),(kid01_part619),(kid01_part620),(kid01_part621),(kid01_part622),(kid01_part623),(kid01_part624),(kid01_part625),(kid01_part626),(kid01_part627),(kid01_part628),(kid01_part629)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part606_checked

  · exact kid01_part612_checked

  · exact kid01_part618_checked

  · exact kid01_part624_checked

  · exact kid01_part607_checked

  · exact kid01_part613_checked

  · exact kid01_part619_checked

  · exact kid01_part625_checked

  · exact kid01_part608_checked

  · exact kid01_part614_checked

  · exact kid01_part620_checked

  · exact kid01_part626_checked

  · exact kid01_part609_checked

  · exact kid01_part615_checked

  · exact kid01_part621_checked

  · exact kid01_part627_checked

  · exact kid01_part610_checked

  · exact kid01_part616_checked

  · exact kid01_part622_checked

  · exact kid01_part628_checked

  · exact kid01_part611_checked

  · exact kid01_part617_checked

  · exact kid01_part623_checked

  · exact kid01_part629_checked

def kid01_part630 : Audit := .cycle 0 10 true (0)
theorem kid01_part630_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part630) = true := by rfl

def kid01_part631 : Audit := .cycle 1 9 true (1)
theorem kid01_part631_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part631) = true := by rfl

def kid01_part632 : Audit := .cycle 1 19 true (1)
theorem kid01_part632_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part632) = true := by rfl

def kid01_part633 : Audit := .cycle 3 7 true (1)
theorem kid01_part633_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part633) = true := by rfl

def kid01_part634 : Audit := .cycle 9 1 true (3)
theorem kid01_part634_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part634) = true := by rfl

def kid01_part635 : Audit := .split 10 (5,false) (byMove [
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
.cycle 0 53 true (0),
.cycle 12 9 true (0),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.cycle 21 13 false (3),
.last 21 (4,true),
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
.cycle 1 24 true (1),
.cycle 0 25 true (0),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 4, 64],[4, 16, 40, 1, 64, 32, 64],64⟩,
.last 24 (4,true),
.cycle 7 21 true (2),
.cycle 2 23 true (1),
.cycle 4 25 true (1),
.cycle 20 2 true (4),
.cycle 0 27 true (0),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
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
.cycle 1 31 true (1),
.cycle 11 9 true (2),
.last 33 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 8, 64],[4, 16, 40, 1, 64, 32, 64],64⟩,
.cycle 8 13 true (2),
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
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 24 true (1),
.cycle 11 9 true (2),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.last 14 (4,true)
]),
.split 12 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 26 1 false (6),
.last 15 (4,true),
.last 31 (4,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 13 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid01_part635_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part635) = true := by rfl

def kid01_part636 : Audit := .cycle 6 4 true (2)
theorem kid01_part636_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part636) = true := by rfl

def kid01_part637 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 13 8 false (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 8 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 7 8 true (2),
.last 13 (5,false),
.cycle 21 13 false (2),
.cycle 20 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 8 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 7 7 true (2),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 7 8 true (2),
.cycle 12 1 true (4),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 13 8 false (1),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 13 8 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 21 11 false (2),
.cycle 20 7 false (1),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.cycle 13 8 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 7 8 true (2),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.last 18 (5,true),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part637_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part637) = true := by rfl

def kid01_part638 : Audit := .cycle 0 14 true (0)
theorem kid01_part638_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part638) = true := by rfl

def kid01_part639 : Audit := .cycle 2 10 true (1)
theorem kid01_part639_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part639) = true := by rfl

def kid01_part640 : Audit := .split 10 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.last 19 (5,true),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 16 (5,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 13 (5,true),
.last 22 (5,true),
.last 14 (5,true),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 1 11 true (1),
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
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.last 21 (5,false),
.last 12 (5,false),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 18 13 false (2),
.cycle 15 2 true (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 32 (5,true),
.cycle 27 14 true (0),
.cycle 25 1 false (-1),
.last 16 (5,true),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 6 6 true (1),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 21 (5,true),
.last 14 (5,true),
.cycle 14 8 true (0),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.cycle 2 12 true (1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.cycle 9 3 true (2),
.split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.last 17 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.last 14 (5,false),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
])
theorem kid01_part640_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part640) = true := by rfl

def kid01_part642 : Audit := .cycle 0 20 true (0)
theorem kid01_part642_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part642) = true := by rfl

def kid01_part643 : Audit := .cycle 0 14 true (0)
theorem kid01_part643_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part643) = true := by rfl

def kid01_part644 : Audit := .cycle 21 1 false (1)
theorem kid01_part644_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part644) = true := by rfl

def kid01_part645 : Audit := .cycle 0 16 true (0)
theorem kid01_part645_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part645) = true := by rfl

def kid01_part646 : Audit := .split 14 (5,false) (byMove [
.last 21 (4,true),
.last 22 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 22 (4,true),
.cycle 11 5 false (1),
.cycle 11 13 false (1),
.last 20 (4,true),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 11 7 false (1),
.last 24 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 22 (4,true),
.last 18 (4,true),
.cycle 11 6 false (1),
.last 20 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid01_part646_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part646) = true := by rfl

def kid01_part647 : Audit := .split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 21 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 13 8 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 14 1 true (2),
.cycle 16 6 false (0),
.last 13 (4,true),
.cycle 17 10 true (0),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 13 1 false (-1),
.last 34 (4,true),
.cycle 1 19 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 14 3 false (0),
.cycle 17 1 true (-1)
])
theorem kid01_part647_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part647) = true := by rfl

def kid01_part648 : Audit := .cycle 2 10 true (1)
theorem kid01_part648_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part648) = true := by rfl

def kid01_part649 : Audit := .cycle 8 3 true (2)
theorem kid01_part649_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part649) = true := by rfl

def kid01_part650 : Audit := .cycle 1 11 true (1)
theorem kid01_part650_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part650) = true := by rfl

def kid01_part651 : Audit := .cycle 0 12 true (0)
theorem kid01_part651_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part651) = true := by rfl

def kid01_part652 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.last 13 (5,false),
.last 12 (5,false),
.cycle 8 5 true (2),
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
theorem kid01_part652_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part652) = true := by rfl

def kid01_part653 : Audit := .split 12 (5,false) (byMove [
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
.cycle 8 6 true (2),
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
theorem kid01_part653_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part653) = true := by rfl

def kid01_part654 : Audit := .split 13 (4,true) (byMove [
.cycle 2 13 true (1),
.cycle 19 11 false (2),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.last 18 (5,false),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 27 true (1),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 19 13 false (2),
.cycle 12 2 true (2),
.cycle 19 7 false (1),
.cycle 2 14 true (1),
.last 18 (5,false),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 64, 64],[1, 1, 2, 1, 1, 1, 64],112⟩,
.last 14 (5,false)
])
theorem kid01_part654_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part654) = true := by rfl

def kid01_part655 : Audit := .split 17 (4,true) (byMove [
.cycle 32 20 true (0),
.cycle 18 5 false (1),
.cycle 25 5 false (1),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 18 5 false (0),
.cycle 6 12 true (0),
.cycle 8 36 true (0),
.cycle 0 22 true (0),
.cycle 30 18 true (0),
.last 21 (5,false),
.cycle 10 8 true (0),
.cycle 19 5 false (1),
.cycle 16 2 true (0),
.cycle 7 21 false (3),
.cycle 20 5 false (2),
.last 20 (5,false),
.cycle 18 5 false (0),
.cycle 2 24 true (0),
.cycle 1 19 true (0),
.cycle 12 6 true (0),
.cycle 5 36 true (0),
.cycle 18 5 true (2),
.last 24 (5,false)
])
theorem kid01_part655_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part655) = true := by rfl

def kid01_part656 : Audit := .cycle 2 12 true (1)
theorem kid01_part656_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part656) = true := by rfl

def kid01_part657 : Audit := .cycle 18 1 false (0)
theorem kid01_part657_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part657) = true := by rfl

def kid01_part658 : Audit := .split 14 (5,false) (byMove [
.last 21 (4,true),
.cycle 11 15 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 7 false (1),
.last 16 (4,true),
.cycle 29 16 true (0),
.cycle 11 8 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.last 16 (4,true),
.cycle 11 6 false (1),
.cycle 5 10 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid01_part658_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part658) = true := by rfl

def kid01_part659 : Audit := .split 11 (5,false) (byMove [
.cycle 49 8 false (1),
.cycle 27 14 true (0),
.cycle 25 1 false (-1),
.last 15 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 20 (4,true),
.last 13 (4,true),
.cycle 14 8 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 17 7 false (1),
.last 13 (4,true),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid01_part659_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part659) = true := by rfl

def kid01_part660 : Audit := .cycle 2 10 true (1)
theorem kid01_part660_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part660) = true := by rfl

def kid01_part661 : Audit := .cycle 8 3 true (2)
theorem kid01_part661_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part661) = true := by rfl

def kid01_part662 : Audit := .cycle 7 4 true (2)
theorem kid01_part662_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part662) = true := by rfl

def kid01_part663 : Audit := .cycle 0 12 true (0)
theorem kid01_part663_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part663) = true := by rfl

def kid01_part664 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 18 (5,false),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 18 (5,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid01_part664_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part664) = true := by rfl

def kid01_part665 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
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
.last 14 (4,true),
.cycle 10 7 true (2),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part665_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part665) = true := by rfl

def kid01_part641 : Audit := .split 10 (5,true) (byMove [(kid01_part642),(kid01_part643),(kid01_part644),(kid01_part645),(kid01_part646),(kid01_part647),(kid01_part648),(kid01_part649),(kid01_part650),(kid01_part651),(kid01_part652),(kid01_part653),(kid01_part654),(kid01_part655),(kid01_part656),(kid01_part657),(kid01_part658),(kid01_part659),(kid01_part660),(kid01_part661),(kid01_part662),(kid01_part663),(kid01_part664),(kid01_part665)])

theorem kid01_part641_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part641) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part642),(kid01_part643),(kid01_part644),(kid01_part645),(kid01_part646),(kid01_part647),(kid01_part648),(kid01_part649),(kid01_part650),(kid01_part651),(kid01_part652),(kid01_part653),(kid01_part654),(kid01_part655),(kid01_part656),(kid01_part657),(kid01_part658),(kid01_part659),(kid01_part660),(kid01_part661),(kid01_part662),(kid01_part663),(kid01_part664),(kid01_part665)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part642_checked

  · exact kid01_part648_checked

  · exact kid01_part654_checked

  · exact kid01_part660_checked

  · exact kid01_part643_checked

  · exact kid01_part649_checked

  · exact kid01_part655_checked

  · exact kid01_part661_checked

  · exact kid01_part644_checked

  · exact kid01_part650_checked

  · exact kid01_part656_checked

  · exact kid01_part662_checked

  · exact kid01_part645_checked

  · exact kid01_part651_checked

  · exact kid01_part657_checked

  · exact kid01_part663_checked

  · exact kid01_part646_checked

  · exact kid01_part652_checked

  · exact kid01_part658_checked

  · exact kid01_part664_checked

  · exact kid01_part647_checked

  · exact kid01_part653_checked

  · exact kid01_part659_checked

  · exact kid01_part665_checked

def kid01_part666 : Audit := .cycle 0 10 true (0)
theorem kid01_part666_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part666) = true := by rfl

def kid01_part667 : Audit := .cycle 1 9 true (1)
theorem kid01_part667_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part667) = true := by rfl

def kid01_part668 : Audit := .cycle 2 8 true (1)
theorem kid01_part668_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part668) = true := by rfl

def kid01_part669 : Audit := .cycle 2 11 true (1)
theorem kid01_part669_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part669) = true := by rfl

def kid01_part670 : Audit := .cycle 9 1 true (3)
theorem kid01_part670_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part670) = true := by rfl

def kid01_part672 : Audit := .cycle 2 10 true (1)
theorem kid01_part672_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part672) = true := by rfl

def kid01_part673 : Audit := .cycle 8 3 true (2)
theorem kid01_part673_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part673) = true := by rfl

def kid01_part674 : Audit := .cycle 7 4 true (2)
theorem kid01_part674_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part674) = true := by rfl

def kid01_part675 : Audit := .cycle 0 12 true (0)
theorem kid01_part675_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part675) = true := by rfl

def kid01_part676 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
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
.cycle 11 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid01_part676_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part676) = true := by rfl

def kid01_part677 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
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
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
])
theorem kid01_part677_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part677) = true := by rfl

def kid01_part678 : Audit := .cycle 0 11 true (0)
theorem kid01_part678_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part678) = true := by rfl

def kid01_part679 : Audit := .cycle 1 10 true (1)
theorem kid01_part679_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part679) = true := by rfl

def kid01_part680 : Audit := .split 20 (5,true) (byMove [
.cycle 2 20 true (1),
.cycle 8 13 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.cycle 9 12 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 45, 32, 4, 64],[4, 16, 40, 1, 64, 32, 64],64⟩,
.cycle 6 15 true (2),
.last 22 (4,true),
.cycle 17 4 true (4),
.cycle 2 21 true (1),
.last 21 (4,true),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 9 12 true (3),
.cycle 10 11 true (3)
])
theorem kid01_part680_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part680) = true := by rfl

def kid01_part681 : Audit := .cycle 3 8 true (1)
theorem kid01_part681_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part681) = true := by rfl

def kid01_part682 : Audit := .cycle 9 2 true (3)
theorem kid01_part682_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part682) = true := by rfl

def kid01_part683 : Audit := .cycle 10 1 true (4)
theorem kid01_part683_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part683) = true := by rfl

def kid01_part684 : Audit := .cycle 6 5 true (2)
theorem kid01_part684_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part684) = true := by rfl

def kid01_part685 : Audit := .split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 19 5 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 7 8 true (2),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 16 (5,true),
.cycle 2 13 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part685_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part685) = true := by rfl

def kid01_part686 : Audit := .split 14 (5,true) (byMove [
.cycle 2 14 true (1),
.cycle 8 7 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 22 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.cycle 6 9 true (2),
.last 16 (4,true),
.cycle 11 4 true (2),
.cycle 2 15 true (1),
.last 15 (4,true),
.cycle 20 10 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 9 6 true (2),
.cycle 10 5 true (2)
])
theorem kid01_part686_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part686) = true := by rfl

def kid01_part687 : Audit := .cycle 2 11 true (1)
theorem kid01_part687_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part687) = true := by rfl

def kid01_part688 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 14 (5,true),
.last 22 (5,true),
.cycle 8 6 true (2),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true),
.last 16 (5,true),
.cycle 11 2 true (2),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.last 12 (5,true)
])
theorem kid01_part688_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part688) = true := by rfl

def kid01_part689 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 7 16 true (1),
.cycle 8 6 true (2),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 33 1 false (7),
.cycle 6 11 true (2),
.last 13 (4,true),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 3 true (3)
])
theorem kid01_part689_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part689) = true := by rfl

def kid01_part690 : Audit := .cycle 0 11 true (0)
theorem kid01_part690_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part690) = true := by rfl

def kid01_part691 : Audit := .cycle 1 10 true (1)
theorem kid01_part691_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part691) = true := by rfl

def kid01_part692 : Audit := .cycle 2 9 true (1)
theorem kid01_part692_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part692) = true := by rfl

def kid01_part693 : Audit := .cycle 2 12 true (1)
theorem kid01_part693_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part693) = true := by rfl

def kid01_part694 : Audit := .cycle 9 2 true (3)
theorem kid01_part694_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part694) = true := by rfl

def kid01_part695 : Audit := .cycle 10 1 true (4)
theorem kid01_part695_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part695) = true := by rfl

def kid01_part671 : Audit := .split 10 (5,false) (byMove [(kid01_part672),(kid01_part673),(kid01_part674),(kid01_part675),(kid01_part676),(kid01_part677),(kid01_part678),(kid01_part679),(kid01_part680),(kid01_part681),(kid01_part682),(kid01_part683),(kid01_part684),(kid01_part685),(kid01_part686),(kid01_part687),(kid01_part688),(kid01_part689),(kid01_part690),(kid01_part691),(kid01_part692),(kid01_part693),(kid01_part694),(kid01_part695)])

theorem kid01_part671_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part671) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part672),(kid01_part673),(kid01_part674),(kid01_part675),(kid01_part676),(kid01_part677),(kid01_part678),(kid01_part679),(kid01_part680),(kid01_part681),(kid01_part682),(kid01_part683),(kid01_part684),(kid01_part685),(kid01_part686),(kid01_part687),(kid01_part688),(kid01_part689),(kid01_part690),(kid01_part691),(kid01_part692),(kid01_part693),(kid01_part694),(kid01_part695)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part672_checked

  · exact kid01_part678_checked

  · exact kid01_part684_checked

  · exact kid01_part690_checked

  · exact kid01_part673_checked

  · exact kid01_part679_checked

  · exact kid01_part685_checked

  · exact kid01_part691_checked

  · exact kid01_part674_checked

  · exact kid01_part680_checked

  · exact kid01_part686_checked

  · exact kid01_part692_checked

  · exact kid01_part675_checked

  · exact kid01_part681_checked

  · exact kid01_part687_checked

  · exact kid01_part693_checked

  · exact kid01_part676_checked

  · exact kid01_part682_checked

  · exact kid01_part688_checked

  · exact kid01_part694_checked

  · exact kid01_part677_checked

  · exact kid01_part683_checked

  · exact kid01_part689_checked

  · exact kid01_part695_checked

def kid01_part599 : Audit := .split 9 (4,false) (byMove [(kid01_part600),(kid01_part601),(kid01_part602),(kid01_part603),(kid01_part604),(kid01_part605),(kid01_part630),(kid01_part631),(kid01_part632),(kid01_part633),(kid01_part634),(kid01_part635),(kid01_part636),(kid01_part637),(kid01_part638),(kid01_part639),(kid01_part640),(kid01_part641),(kid01_part666),(kid01_part667),(kid01_part668),(kid01_part669),(kid01_part670),(kid01_part671)])

theorem kid01_part599_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (kid01_part599) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid01_part600),(kid01_part601),(kid01_part602),(kid01_part603),(kid01_part604),(kid01_part605),(kid01_part630),(kid01_part631),(kid01_part632),(kid01_part633),(kid01_part634),(kid01_part635),(kid01_part636),(kid01_part637),(kid01_part638),(kid01_part639),(kid01_part640),(kid01_part641),(kid01_part666),(kid01_part667),(kid01_part668),(kid01_part669),(kid01_part670),(kid01_part671)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part600_checked

  · exact kid01_part630_checked

  · exact kid01_part636_checked

  · exact kid01_part666_checked

  · exact kid01_part601_checked

  · exact kid01_part631_checked

  · exact kid01_part637_checked

  · exact kid01_part667_checked

  · exact kid01_part602_checked

  · exact kid01_part632_checked

  · exact kid01_part638_checked

  · exact kid01_part668_checked

  · exact kid01_part603_checked

  · exact kid01_part633_checked

  · exact kid01_part639_checked

  · exact kid01_part669_checked

  · exact kid01_part604_checked

  · exact kid01_part634_checked

  · exact kid01_part640_checked

  · exact kid01_part670_checked

  · exact kid01_part605_checked

  · exact kid01_part635_checked

  · exact kid01_part641_checked

  · exact kid01_part671_checked

def kid01_part697 : Audit := .cycle 2 9 true (1)
theorem kid01_part697_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part697) = true := by rfl

def kid01_part698 : Audit := .cycle 8 2 true (2)
theorem kid01_part698_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part698) = true := by rfl

def kid01_part699 : Audit := .cycle 1 10 true (1)
theorem kid01_part699_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part699) = true := by rfl

def kid01_part700 : Audit := .cycle 0 11 true (0)
theorem kid01_part700_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part700) = true := by rfl

def kid01_part702 : Audit := .cycle 0 11 true (0)
theorem kid01_part702_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part702) = true := by rfl

def kid01_part703 : Audit := .cycle 1 10 true (1)
theorem kid01_part703_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part703) = true := by rfl

def kid01_part704 : Audit := .cycle 21 1 false (1)
theorem kid01_part704_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part704) = true := by rfl

def kid01_part705 : Audit := .cycle 23 1 false (1)
theorem kid01_part705_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part705) = true := by rfl

def kid01_part706 : Audit := .split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 16 6 false (0),
.last 13 (5,true),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 14 3 false (0)
])
theorem kid01_part706_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part706) = true := by rfl

def kid01_part707 : Audit := .split 14 (4,false) (byMove [
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
.last 19 (5,true),
.cycle 11 7 false (1),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 28 (5,true),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid01_part707_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part707) = true := by rfl

def kid01_part708 : Audit := .cycle 0 11 true (0)
theorem kid01_part708_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part708) = true := by rfl

def kid01_part709 : Audit := .cycle 1 10 true (1)
theorem kid01_part709_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part709) = true := by rfl

def kid01_part710 : Audit := .cycle 35 1 false (7)
theorem kid01_part710_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part710) = true := by rfl

def kid01_part711 : Audit := .cycle 20 1 false (2)
theorem kid01_part711_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part711) = true := by rfl

def kid01_part712 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid01_part712_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part712) = true := by rfl

def kid01_part713 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 21 13 false (2),
.last 21 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
])
theorem kid01_part713_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part713) = true := by rfl

def kid01_part714 : Audit := .cycle 17 9 false (2)
theorem kid01_part714_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part714) = true := by rfl

def kid01_part715 : Audit := .split 17 (5,true) (byMove [
.cycle 24 5 false (2),
.cycle 18 5 false (1),
.cycle 25 5 false (1),
.cycle 0 19 true (0),
.cycle 18 5 false (0),
.last 20 (4,false),
.cycle 0 18 true (0),
.cycle 7 22 true (0),
.cycle 24 5 false (2),
.cycle 22 5 false (2),
.last 18 (4,false),
.last 19 (4,false),
.cycle 19 5 false (1),
.cycle 16 2 true (0),
.cycle 0 22 true (-1),
.cycle 25 5 false (3),
.cycle 18 5 false (0),
.last 20 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 7 24 true (0),
.last 18 (4,false),
.cycle 14 4 true (0)
])
theorem kid01_part715_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part715) = true := by rfl

def kid01_part716 : Audit := .cycle 0 13 true (0)
theorem kid01_part716_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part716) = true := by rfl

def kid01_part717 : Audit := .cycle 18 1 false (0)
theorem kid01_part717_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part717) = true := by rfl

def kid01_part718 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 42 true (-2),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 20 (5,true),
.last 13 (5,true),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 19 (5,true),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid01_part718_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part718) = true := by rfl

def kid01_part719 : Audit := .split 14 (4,false) (byMove [
.last 23 (5,true),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 19 (5,true),
.cycle 11 7 false (1),
.last 21 (5,true),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.last 19 (5,true),
.cycle 11 7 false (1),
.last 21 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 19 (5,true),
.last 20 (5,true),
.last 21 (5,true),
.cycle 11 9 false (1),
.last 17 (5,true),
.cycle 11 4 false (1)
])
theorem kid01_part719_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part719) = true := by rfl

def kid01_part720 : Audit := .cycle 0 11 true (0)
theorem kid01_part720_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part720) = true := by rfl

def kid01_part721 : Audit := .cycle 1 10 true (1)
theorem kid01_part721_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part721) = true := by rfl

def kid01_part722 : Audit := .cycle 2 9 true (1)
theorem kid01_part722_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part722) = true := by rfl

def kid01_part723 : Audit := .cycle 2 12 true (1)
theorem kid01_part723_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part723) = true := by rfl

def kid01_part724 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid01_part724_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part724) = true := by rfl

def kid01_part725 : Audit := .cycle 9 2 true (2)
theorem kid01_part725_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part725) = true := by rfl

def kid01_part701 : Audit := .split 10 (4,true) (byMove [(kid01_part702),(kid01_part703),(kid01_part704),(kid01_part705),(kid01_part706),(kid01_part707),(kid01_part708),(kid01_part709),(kid01_part710),(kid01_part711),(kid01_part712),(kid01_part713),(kid01_part714),(kid01_part715),(kid01_part716),(kid01_part717),(kid01_part718),(kid01_part719),(kid01_part720),(kid01_part721),(kid01_part722),(kid01_part723),(kid01_part724),(kid01_part725)])

theorem kid01_part701_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part701) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part702),(kid01_part703),(kid01_part704),(kid01_part705),(kid01_part706),(kid01_part707),(kid01_part708),(kid01_part709),(kid01_part710),(kid01_part711),(kid01_part712),(kid01_part713),(kid01_part714),(kid01_part715),(kid01_part716),(kid01_part717),(kid01_part718),(kid01_part719),(kid01_part720),(kid01_part721),(kid01_part722),(kid01_part723),(kid01_part724),(kid01_part725)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part702_checked

  · exact kid01_part708_checked

  · exact kid01_part714_checked

  · exact kid01_part720_checked

  · exact kid01_part703_checked

  · exact kid01_part709_checked

  · exact kid01_part715_checked

  · exact kid01_part721_checked

  · exact kid01_part704_checked

  · exact kid01_part710_checked

  · exact kid01_part716_checked

  · exact kid01_part722_checked

  · exact kid01_part705_checked

  · exact kid01_part711_checked

  · exact kid01_part717_checked

  · exact kid01_part723_checked

  · exact kid01_part706_checked

  · exact kid01_part712_checked

  · exact kid01_part718_checked

  · exact kid01_part724_checked

  · exact kid01_part707_checked

  · exact kid01_part713_checked

  · exact kid01_part719_checked

  · exact kid01_part725_checked

def kid01_part726 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 16 1 false (0),
.last 22 (4,true),
.last 14 (4,true),
.cycle 0 16 true (-1),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.last 14 (4,true)
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
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 18 1 false (2),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 15 1 false (1),
.cycle 17 9 false (2),
.cycle 15 2 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 23 (4,true),
.cycle 25 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 21 (4,true),
.last 14 (4,true),
.cycle 14 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 2 11 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid01_part726_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part726) = true := by rfl

def kid01_part727 : Audit := .cycle 0 10 true (0)
theorem kid01_part727_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part727) = true := by rfl

def kid01_part728 : Audit := .cycle 1 9 true (1)
theorem kid01_part728_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part728) = true := by rfl

def kid01_part729 : Audit := .cycle 1 19 true (1)
theorem kid01_part729_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part729) = true := by rfl

def kid01_part730 : Audit := .cycle 3 7 true (1)
theorem kid01_part730_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part730) = true := by rfl

def kid01_part731 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 53 true (0),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 21 13 false (3),
.last 21 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 21 (4,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 4, 16, 64],[4, 32, 24, 1, 16, 64, 64],64⟩,
.last 22 (5,true),
.last 24 (5,true),
.cycle 7 21 true (2),
.cycle 2 23 true (1),
.cycle 4 25 true (1),
.cycle 0 27 true (0),
.cycle 20 2 true (4),
.cycle 2 21 true (1),
.cycle 8 14 true (2),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.last 22 (5,true)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 3 18 true (1),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 31 true (1),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 8, 16, 64],[4, 32, 24, 1, 16, 64, 64],64⟩,
.last 33 (5,true),
.cycle 8 13 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 22 true (0),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 3 18 true (1),
.cycle 9 11 true (2)
]),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.cycle 26 1 false (6),
.last 13 (5,true),
.last 15 (5,true),
.last 31 (5,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 13 3 true (3),
.last 13 (5,true)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 24 true (1),
.cycle 11 9 true (2),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid01_part731_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part731) = true := by rfl

def kid01_part732 : Audit := .cycle 9 1 true (3)
theorem kid01_part732_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part732) = true := by rfl

def kid01_part733 : Audit := .cycle 6 4 true (2)
theorem kid01_part733_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part733) = true := by rfl

def kid01_part734 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 7 8 true (2),
.cycle 21 13 false (2),
.cycle 20 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 9 4 true (2)
]),
.cycle 13 8 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 7 8 true (2),
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
]),
.cycle 7 7 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 21 11 false (2),
.cycle 20 7 false (1),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 13 8 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 7 8 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.last 18 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
]),
.cycle 9 3 true (2)
])
theorem kid01_part734_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part734) = true := by rfl

def kid01_part735 : Audit := .cycle 0 14 true (0)
theorem kid01_part735_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part735) = true := by rfl

def kid01_part736 : Audit := .cycle 2 10 true (1)
theorem kid01_part736_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part736) = true := by rfl

def kid01_part738 : Audit := .cycle 0 20 true (0)
theorem kid01_part738_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid01_part738) = true := by rfl

def kid01_part739 : Audit := .cycle 0 14 true (0)
theorem kid01_part739_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid01_part739) = true := by rfl

def kid01_part740 : Audit := .cycle 21 1 false (1)
theorem kid01_part740_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid01_part740) = true := by rfl

def kid01_part741 : Audit := .cycle 0 16 true (0)
theorem kid01_part741_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid01_part741) = true := by rfl

def kid01_part742 : Audit := .split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 13 8 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.last 14 (5,true),
.cycle 16 6 false (0),
.last 13 (5,true),
.cycle 17 10 true (0),
.cycle 0 16 true (0),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 34 (5,true),
.cycle 1 19 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 14 3 false (0)
])
theorem kid01_part742_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid01_part742) = true := by rfl

def kid01_part743 : Audit := .split 14 (4,false) (byMove [
.last 21 (5,true),
.last 22 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 22 (5,true),
.cycle 11 5 false (1),
.cycle 11 13 false (1),
.last 20 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.cycle 11 7 false (1),
.last 24 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 22 (5,true),
.last 18 (5,true),
.cycle 11 6 false (1),
.last 20 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid01_part743_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid01_part743) = true := by rfl

def kid01_part744 : Audit := .cycle 2 10 true (1)
theorem kid01_part744_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid01_part744) = true := by rfl

def kid01_part745 : Audit := .cycle 8 3 true (2)
theorem kid01_part745_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid01_part745) = true := by rfl

def kid01_part746 : Audit := .cycle 1 11 true (1)
theorem kid01_part746_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid01_part746) = true := by rfl

def kid01_part747 : Audit := .cycle 0 12 true (0)
theorem kid01_part747_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid01_part747) = true := by rfl

def kid01_part748 : Audit := .split 12 (4,false) (byMove [
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
.cycle 8 6 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.cycle 21 2 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid01_part748_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid01_part748) = true := by rfl

def kid01_part749 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.last 12 (4,false),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid01_part749_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid01_part749) = true := by rfl

def kid01_part750 : Audit := .split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.cycle 19 11 false (2),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.cycle 19 9 false (1),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 27 true (1),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 19 13 false (2),
.cycle 12 2 true (2),
.cycle 19 7 false (1),
.cycle 2 14 true (1),
.cycle 19 9 false (1),
.last 18 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 64, 16, 64],[1, 1, 2, 1, 1, 1, 64],112⟩
])
theorem kid01_part750_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid01_part750) = true := by rfl

def kid01_part751 : Audit := .split 17 (5,true) (byMove [
.cycle 32 20 true (0),
.cycle 18 5 false (1),
.cycle 25 5 false (1),
.cycle 0 23 true (0),
.cycle 18 5 false (0),
.last 20 (4,false),
.cycle 6 12 true (0),
.cycle 8 36 true (0),
.cycle 0 22 true (0),
.cycle 30 18 true (0),
.cycle 10 8 true (0),
.last 21 (4,false),
.cycle 19 5 false (1),
.cycle 16 2 true (0),
.cycle 7 21 false (3),
.cycle 20 5 false (2),
.cycle 18 5 false (0),
.last 20 (4,false),
.cycle 2 24 true (0),
.cycle 1 19 true (0),
.cycle 12 6 true (0),
.cycle 5 36 true (0),
.last 24 (4,false),
.cycle 18 5 true (2)
])
theorem kid01_part751_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid01_part751) = true := by rfl

def kid01_part752 : Audit := .cycle 2 12 true (1)
theorem kid01_part752_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid01_part752) = true := by rfl

def kid01_part753 : Audit := .cycle 18 1 false (0)
theorem kid01_part753_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid01_part753) = true := by rfl

def kid01_part754 : Audit := .split 11 (4,false) (byMove [
.cycle 49 8 false (1),
.cycle 27 14 true (0),
.cycle 25 1 false (-1),
.last 15 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.last 20 (5,true),
.last 13 (5,true),
.cycle 14 8 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 17 7 false (1),
.last 13 (5,true),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid01_part754_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid01_part754) = true := by rfl

def kid01_part755 : Audit := .split 14 (4,false) (byMove [
.last 21 (5,true),
.cycle 11 15 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 29 16 true (0),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.last 16 (5,true),
.cycle 11 6 false (1),
.cycle 5 10 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid01_part755_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid01_part755) = true := by rfl

def kid01_part756 : Audit := .cycle 2 10 true (1)
theorem kid01_part756_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid01_part756) = true := by rfl

def kid01_part757 : Audit := .cycle 8 3 true (2)
theorem kid01_part757_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid01_part757) = true := by rfl

def kid01_part758 : Audit := .cycle 7 4 true (2)
theorem kid01_part758_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid01_part758) = true := by rfl

def kid01_part759 : Audit := .cycle 0 12 true (0)
theorem kid01_part759_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid01_part759) = true := by rfl

def kid01_part760 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
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
.last 14 (5,true),
.cycle 10 7 true (2),
.cycle 2 13 true (1),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid01_part760_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid01_part760) = true := by rfl

def kid01_part761 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 9 4 true (2),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid01_part761_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid01_part761) = true := by rfl

def kid01_part737 : Audit := .split 10 (4,true) (byMove [(kid01_part738),(kid01_part739),(kid01_part740),(kid01_part741),(kid01_part742),(kid01_part743),(kid01_part744),(kid01_part745),(kid01_part746),(kid01_part747),(kid01_part748),(kid01_part749),(kid01_part750),(kid01_part751),(kid01_part752),(kid01_part753),(kid01_part754),(kid01_part755),(kid01_part756),(kid01_part757),(kid01_part758),(kid01_part759),(kid01_part760),(kid01_part761)])

theorem kid01_part737_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part737) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid01_part738),(kid01_part739),(kid01_part740),(kid01_part741),(kid01_part742),(kid01_part743),(kid01_part744),(kid01_part745),(kid01_part746),(kid01_part747),(kid01_part748),(kid01_part749),(kid01_part750),(kid01_part751),(kid01_part752),(kid01_part753),(kid01_part754),(kid01_part755),(kid01_part756),(kid01_part757),(kid01_part758),(kid01_part759),(kid01_part760),(kid01_part761)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part738_checked

  · exact kid01_part744_checked

  · exact kid01_part750_checked

  · exact kid01_part756_checked

  · exact kid01_part739_checked

  · exact kid01_part745_checked

  · exact kid01_part751_checked

  · exact kid01_part757_checked

  · exact kid01_part740_checked

  · exact kid01_part746_checked

  · exact kid01_part752_checked

  · exact kid01_part758_checked

  · exact kid01_part741_checked

  · exact kid01_part747_checked

  · exact kid01_part753_checked

  · exact kid01_part759_checked

  · exact kid01_part742_checked

  · exact kid01_part748_checked

  · exact kid01_part754_checked

  · exact kid01_part760_checked

  · exact kid01_part743_checked

  · exact kid01_part749_checked

  · exact kid01_part755_checked

  · exact kid01_part761_checked

def kid01_part762 : Audit := .split 10 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.last 19 (4,true),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.cycle 16 1 false (0),
.last 22 (4,true),
.last 14 (4,true),
.last 20 (4,true),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 1 11 true (1),
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
.cycle 0 107 true (0),
.cycle 35 1 false (7),
.last 12 (4,false),
.last 21 (4,false),
.cycle 8 5 true (2),
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
]),
.cycle 21 1 false (5),
.cycle 18 13 false (2),
.cycle 15 2 true (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 32 (4,true),
.cycle 27 14 true (0),
.cycle 25 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 6 6 true (1),
.last 14 (4,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.last 21 (4,true),
.last 14 (4,true),
.cycle 14 8 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 2 10 true (1),
.cycle 8 3 true (2),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 17 (4,false),
.cycle 6 6 true (2),
.last 14 (4,false),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 13 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 9 3 true (2)
])
theorem kid01_part762_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part762) = true := by rfl

def kid01_part763 : Audit := .cycle 0 10 true (0)
theorem kid01_part763_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part763) = true := by rfl

def kid01_part764 : Audit := .cycle 1 9 true (1)
theorem kid01_part764_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part764) = true := by rfl

def kid01_part765 : Audit := .cycle 2 8 true (1)
theorem kid01_part765_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part765) = true := by rfl

def kid01_part766 : Audit := .cycle 2 11 true (1)
theorem kid01_part766_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part766) = true := by rfl

def kid01_part768 : Audit := .cycle 2 10 true (1)
theorem kid01_part768_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid01_part768) = true := by rfl

def kid01_part769 : Audit := .cycle 8 3 true (2)
theorem kid01_part769_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid01_part769) = true := by rfl

def kid01_part770 : Audit := .cycle 7 4 true (2)
theorem kid01_part770_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid01_part770) = true := by rfl

def kid01_part771 : Audit := .cycle 0 12 true (0)
theorem kid01_part771_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid01_part771) = true := by rfl

def kid01_part772 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
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
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid01_part772_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid01_part772) = true := by rfl

def kid01_part773 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
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
.cycle 11 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid01_part773_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid01_part773) = true := by rfl

def kid01_part774 : Audit := .cycle 0 11 true (0)
theorem kid01_part774_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid01_part774) = true := by rfl

def kid01_part775 : Audit := .cycle 1 10 true (1)
theorem kid01_part775_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid01_part775) = true := by rfl

def kid01_part776 : Audit := .split 20 (4,true) (byMove [
.cycle 2 20 true (1),
.cycle 8 13 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 4, 16, 64],[4, 32, 24, 1, 16, 64, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.last 22 (5,true),
.cycle 17 4 true (4),
.cycle 2 21 true (1),
.cycle 2 27 true (1),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
])
theorem kid01_part776_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid01_part776) = true := by rfl

def kid01_part777 : Audit := .cycle 3 8 true (1)
theorem kid01_part777_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid01_part777) = true := by rfl

def kid01_part778 : Audit := .cycle 10 1 true (4)
theorem kid01_part778_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid01_part778) = true := by rfl

def kid01_part779 : Audit := .cycle 9 2 true (3)
theorem kid01_part779_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid01_part779) = true := by rfl

def kid01_part780 : Audit := .cycle 6 5 true (2)
theorem kid01_part780_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid01_part780) = true := by rfl

def kid01_part781 : Audit := .split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 8 5 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 7 8 true (2),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 16 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3)
])
theorem kid01_part781_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid01_part781) = true := by rfl

def kid01_part782 : Audit := .split 14 (4,true) (byMove [
.cycle 2 14 true (1),
.cycle 8 7 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 0 22 true (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 0 18 true (0),
.cycle 0 21 true (0),
.cycle 6 9 true (2),
.last 16 (5,true),
.cycle 11 4 true (2),
.cycle 2 15 true (1),
.cycle 20 10 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 10 5 true (2),
.cycle 9 6 true (2)
])
theorem kid01_part782_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid01_part782) = true := by rfl

def kid01_part783 : Audit := .cycle 2 11 true (1)
theorem kid01_part783_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid01_part783) = true := by rfl

def kid01_part784 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 8 7 true (2),
.cycle 7 16 true (1),
.cycle 8 6 true (2),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.last 12 (5,true),
.cycle 6 11 true (2),
.last 13 (5,true),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.last 12 (5,true)
])
theorem kid01_part784_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid01_part784) = true := by rfl

def kid01_part785 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 14 (4,true),
.last 22 (4,true),
.cycle 8 6 true (2),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3),
.last 16 (4,true),
.cycle 11 2 true (2),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 4 true (3)
])
theorem kid01_part785_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid01_part785) = true := by rfl

def kid01_part786 : Audit := .cycle 0 11 true (0)
theorem kid01_part786_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid01_part786) = true := by rfl

def kid01_part787 : Audit := .cycle 1 10 true (1)
theorem kid01_part787_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid01_part787) = true := by rfl

def kid01_part788 : Audit := .cycle 2 9 true (1)
theorem kid01_part788_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid01_part788) = true := by rfl

def kid01_part789 : Audit := .cycle 2 12 true (1)
theorem kid01_part789_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid01_part789) = true := by rfl

def kid01_part790 : Audit := .cycle 10 1 true (4)
theorem kid01_part790_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid01_part790) = true := by rfl

def kid01_part791 : Audit := .cycle 9 2 true (3)
theorem kid01_part791_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid01_part791) = true := by rfl

def kid01_part767 : Audit := .split 10 (4,false) (byMove [(kid01_part768),(kid01_part769),(kid01_part770),(kid01_part771),(kid01_part772),(kid01_part773),(kid01_part774),(kid01_part775),(kid01_part776),(kid01_part777),(kid01_part778),(kid01_part779),(kid01_part780),(kid01_part781),(kid01_part782),(kid01_part783),(kid01_part784),(kid01_part785),(kid01_part786),(kid01_part787),(kid01_part788),(kid01_part789),(kid01_part790),(kid01_part791)])

theorem kid01_part767_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part767) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid01_part768),(kid01_part769),(kid01_part770),(kid01_part771),(kid01_part772),(kid01_part773),(kid01_part774),(kid01_part775),(kid01_part776),(kid01_part777),(kid01_part778),(kid01_part779),(kid01_part780),(kid01_part781),(kid01_part782),(kid01_part783),(kid01_part784),(kid01_part785),(kid01_part786),(kid01_part787),(kid01_part788),(kid01_part789),(kid01_part790),(kid01_part791)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part768_checked

  · exact kid01_part774_checked

  · exact kid01_part780_checked

  · exact kid01_part786_checked

  · exact kid01_part769_checked

  · exact kid01_part775_checked

  · exact kid01_part781_checked

  · exact kid01_part787_checked

  · exact kid01_part770_checked

  · exact kid01_part776_checked

  · exact kid01_part782_checked

  · exact kid01_part788_checked

  · exact kid01_part771_checked

  · exact kid01_part777_checked

  · exact kid01_part783_checked

  · exact kid01_part789_checked

  · exact kid01_part772_checked

  · exact kid01_part778_checked

  · exact kid01_part784_checked

  · exact kid01_part790_checked

  · exact kid01_part773_checked

  · exact kid01_part779_checked

  · exact kid01_part785_checked

  · exact kid01_part791_checked

def kid01_part792 : Audit := .cycle 9 1 true (3)
theorem kid01_part792_checked : zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part792) = true := by rfl

def kid01_part696 : Audit := .split 9 (5,false) (byMove [(kid01_part697),(kid01_part698),(kid01_part699),(kid01_part700),(kid01_part701),(kid01_part726),(kid01_part727),(kid01_part728),(kid01_part729),(kid01_part730),(kid01_part731),(kid01_part732),(kid01_part733),(kid01_part734),(kid01_part735),(kid01_part736),(kid01_part737),(kid01_part762),(kid01_part763),(kid01_part764),(kid01_part765),(kid01_part766),(kid01_part767),(kid01_part792)])

theorem kid01_part696_checked : zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (kid01_part696) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part697),(kid01_part698),(kid01_part699),(kid01_part700),(kid01_part701),(kid01_part726),(kid01_part727),(kid01_part728),(kid01_part729),(kid01_part730),(kid01_part731),(kid01_part732),(kid01_part733),(kid01_part734),(kid01_part735),(kid01_part736),(kid01_part737),(kid01_part762),(kid01_part763),(kid01_part764),(kid01_part765),(kid01_part766),(kid01_part767),(kid01_part792)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part697_checked

  · exact kid01_part727_checked

  · exact kid01_part733_checked

  · exact kid01_part763_checked

  · exact kid01_part698_checked

  · exact kid01_part728_checked

  · exact kid01_part734_checked

  · exact kid01_part764_checked

  · exact kid01_part699_checked

  · exact kid01_part729_checked

  · exact kid01_part735_checked

  · exact kid01_part765_checked

  · exact kid01_part700_checked

  · exact kid01_part730_checked

  · exact kid01_part736_checked

  · exact kid01_part766_checked

  · exact kid01_part701_checked

  · exact kid01_part731_checked

  · exact kid01_part737_checked

  · exact kid01_part767_checked

  · exact kid01_part726_checked

  · exact kid01_part732_checked

  · exact kid01_part762_checked

  · exact kid01_part792_checked

def kid01 : Audit := .split 8 (1,true) (byMove [(kid01_part1),(kid01_part2),(kid01_part3),(kid01_part4),(kid01_part5),(kid01_part102),(kid01_part199),(kid01_part200),(kid01_part201),(kid01_part202),(kid01_part203),(kid01_part276),(kid01_part349),(kid01_part350),(kid01_part351),(kid01_part352),(kid01_part353),(kid01_part474),(kid01_part595),(kid01_part596),(kid01_part597),(kid01_part598),(kid01_part599),(kid01_part696)])

theorem check01 : zipCheck 1882 (child ⟨false,false,1⟩) (kid01) = true := by

  change (zipQueryOK 1882 (child ⟨false,false,1⟩) 8 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (child ⟨false,false,1⟩) (1,true) (some mv)) (byMove [(kid01_part1),(kid01_part2),(kid01_part3),(kid01_part4),(kid01_part5),(kid01_part102),(kid01_part199),(kid01_part200),(kid01_part201),(kid01_part202),(kid01_part203),(kid01_part276),(kid01_part349),(kid01_part350),(kid01_part351),(kid01_part352),(kid01_part353),(kid01_part474),(kid01_part595),(kid01_part596),(kid01_part597),(kid01_part598),(kid01_part599),(kid01_part696)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1_checked

  · exact kid01_part199_checked

  · exact kid01_part349_checked

  · exact kid01_part595_checked

  · exact kid01_part2_checked

  · exact kid01_part200_checked

  · exact kid01_part350_checked

  · exact kid01_part596_checked

  · exact kid01_part3_checked

  · exact kid01_part201_checked

  · exact kid01_part351_checked

  · exact kid01_part597_checked

  · exact kid01_part4_checked

  · exact kid01_part202_checked

  · exact kid01_part352_checked

  · exact kid01_part598_checked

  · exact kid01_part5_checked

  · exact kid01_part203_checked

  · exact kid01_part353_checked

  · exact kid01_part599_checked

  · exact kid01_part102_checked

  · exact kid01_part276_checked

  · exact kid01_part474_checked

  · exact kid01_part696_checked

end BB6.Agent11Raw39B1RC
