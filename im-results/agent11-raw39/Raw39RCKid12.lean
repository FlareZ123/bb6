import Raw39RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid12_part1 : Audit := .cycle 26 1 false (6)
theorem kid12_part1_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,0⟩)) (kid12_part1) = true := by rfl

def kid12_part2 : Audit := .cycle 1 10 true (1)
theorem kid12_part2_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,1⟩)) (kid12_part2) = true := by rfl

def kid12_part3 : Audit := .cycle 15 3 false (1)
theorem kid12_part3_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,2⟩)) (kid12_part3) = true := by rfl

def kid12_part4 : Audit := .cycle 0 11 true (0)
theorem kid12_part4_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,3⟩)) (kid12_part4) = true := by rfl

def kid12_part6 : Audit := .cycle 0 11 true (0)
theorem kid12_part6_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part6) = true := by rfl

def kid12_part7 : Audit := .cycle 1 10 true (1)
theorem kid12_part7_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part7) = true := by rfl

def kid12_part8 : Audit := .cycle 21 1 false (1)
theorem kid12_part8_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part8) = true := by rfl

def kid12_part9 : Audit := .cycle 15 1 false (3)
theorem kid12_part9_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part9) = true := by rfl

def kid12_part10 : Audit := .split 11 (4,false) (byMove [
.cycle 14 1 false (2),
.cycle 13 11 false (0),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 24 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,false),
.cycle 17 1 false (3),
.cycle 11 2 true (0),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 11 2 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
]),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 0 31 false (3),
.cycle 15 1 false (3),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 23 (5,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 1 false (3),
.last 15 (5,false),
.last 18 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 25 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.cycle 0 14 true (0),
.last 16 (5,false),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.cycle 11 1 true (1),
.split 12 (5,false) (byMove [
.cycle 28 1 false (2),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.cycle 18 7 false (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
])
theorem kid12_part10_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part10) = true := by rfl

def kid12_part12 : Audit := .cycle 14 1 false (2)
theorem kid12_part12_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part12) = true := by rfl

def kid12_part13 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 11 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 11 false (1),
.cycle 14 11 false (-1),
.cycle 16 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 47 (5,true),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 18 1 false (2),
.cycle 13 1 true (-1),
.cycle 11 3 false (1)
])
theorem kid12_part13_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part13) = true := by rfl

def kid12_part14 : Audit := .cycle 18 1 false (-2)
theorem kid12_part14_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part14) = true := by rfl

def kid12_part15 : Audit := .cycle 0 13 true (0)
theorem kid12_part15_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part15) = true := by rfl

def kid12_part16 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 15 false (3),
.cycle 12 12 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 true (-2),
.cycle 13 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 28 (5,true),
.cycle 1 14 false (3),
.cycle 12 11 false (0),
.cycle 19 1 false (1),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid12_part16_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part16) = true := by rfl

def kid12_part17 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (3),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid12_part17_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part17) = true := by rfl

def kid12_part18 : Audit := .cycle 0 12 true (0)
theorem kid12_part18_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part18) = true := by rfl

def kid12_part19 : Audit := .cycle 1 11 true (1)
theorem kid12_part19_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part19) = true := by rfl

def kid12_part20 : Audit := .cycle 24 1 false (2)
theorem kid12_part20_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part20) = true := by rfl

def kid12_part21 : Audit := .cycle 21 1 false (1)
theorem kid12_part21_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part21) = true := by rfl

def kid12_part22 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.last 16 (5,true),
.last 20 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
])
theorem kid12_part22_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part22) = true := by rfl

def kid12_part23 : Audit := .cycle 11 1 true (1)
theorem kid12_part23_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part23) = true := by rfl

def kid12_part24 : Audit := .cycle 14 4 false (1)
theorem kid12_part24_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part24) = true := by rfl

def kid12_part25 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 19 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.cycle 14 8 false (1),
.cycle 14 8 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 8 false (1),
.cycle 14 8 false (0),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.last 17 (5,true),
.last 21 (5,true),
.cycle 0 16 true (-1),
.cycle 16 8 false (1),
.last 16 (5,true),
.cycle 11 3 false (1)
])
theorem kid12_part25_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part25) = true := by rfl

def kid12_part26 : Audit := .split 27 (5,true) (byMove [
.cycle 0 28 false (3),
.cycle 0 41 false (3),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.last 28 (4,false),
.cycle 0 31 false (3),
.cycle 0 28 true (-3),
.cycle 0 41 true (-3),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.last 28 (4,false),
.cycle 0 31 true (-3),
.cycle 0 34 false (3),
.cycle 0 38 false (3),
.cycle 0 30 true (-3),
.cycle 28 1 false (-2),
.last 28 (4,false),
.cycle 33 1 false (1),
.cycle 12 30 true (-3),
.cycle 1 27 false (3),
.cycle 0 40 true (-3),
.cycle 32 1 false (2),
.last 28 (4,false),
.cycle 11 17 false (1)
])
theorem kid12_part26_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part26) = true := by rfl

def kid12_part27 : Audit := .cycle 15 1 false (3)
theorem kid12_part27_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part27) = true := by rfl

def kid12_part28 : Audit := .split 14 (4,false) (byMove [
.last 23 (5,true),
.proven (BB6.Agent11Raw39RCPumps.M690.table) (fun m hm => BB6.Agent11Raw39RCPumps.M690.never m hm),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.cycle 0 20 true (-2),
.cycle 12 6 false (0),
.cycle 0 22 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 20 true (-3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 8 8 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid12_part28_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part28) = true := by rfl

def kid12_part29 : Audit := .split 12 (5,true) (byMove [
.cycle 0 22 false (3),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 15 1 false (3),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 24 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 11 3 true (0)
])
theorem kid12_part29_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part29) = true := by rfl

def kid12_part30 : Audit := .cycle 0 12 true (0)
theorem kid12_part30_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part30) = true := by rfl

def kid12_part31 : Audit := .cycle 1 11 true (1)
theorem kid12_part31_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part31) = true := by rfl

def kid12_part32 : Audit := .cycle 2 10 true (1)
theorem kid12_part32_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part32) = true := by rfl

def kid12_part33 : Audit := .cycle 34 1 false (6)
theorem kid12_part33_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part33) = true := by rfl

def kid12_part34 : Audit := .split 12 (4,false) (byMove [
.cycle 28 1 false (2),
.cycle 13 14 false (1),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.last 18 (5,true),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
])
theorem kid12_part34_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part34) = true := by rfl

def kid12_part35 : Audit := .cycle 11 1 true (1)
theorem kid12_part35_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part35) = true := by rfl

def kid12_part11 : Audit := .split 11 (5,false) (byMove [(kid12_part12),(kid12_part13),(kid12_part14),(kid12_part15),(kid12_part16),(kid12_part17),(kid12_part18),(kid12_part19),(kid12_part20),(kid12_part21),(kid12_part22),(kid12_part23),(kid12_part24),(kid12_part25),(kid12_part26),(kid12_part27),(kid12_part28),(kid12_part29),(kid12_part30),(kid12_part31),(kid12_part32),(kid12_part33),(kid12_part34),(kid12_part35)])

theorem kid12_part11_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part11) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part12),(kid12_part13),(kid12_part14),(kid12_part15),(kid12_part16),(kid12_part17),(kid12_part18),(kid12_part19),(kid12_part20),(kid12_part21),(kid12_part22),(kid12_part23),(kid12_part24),(kid12_part25),(kid12_part26),(kid12_part27),(kid12_part28),(kid12_part29),(kid12_part30),(kid12_part31),(kid12_part32),(kid12_part33),(kid12_part34),(kid12_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part12_checked

  · exact kid12_part18_checked

  · exact kid12_part24_checked

  · exact kid12_part30_checked

  · exact kid12_part13_checked

  · exact kid12_part19_checked

  · exact kid12_part25_checked

  · exact kid12_part31_checked

  · exact kid12_part14_checked

  · exact kid12_part20_checked

  · exact kid12_part26_checked

  · exact kid12_part32_checked

  · exact kid12_part15_checked

  · exact kid12_part21_checked

  · exact kid12_part27_checked

  · exact kid12_part33_checked

  · exact kid12_part16_checked

  · exact kid12_part22_checked

  · exact kid12_part28_checked

  · exact kid12_part34_checked

  · exact kid12_part17_checked

  · exact kid12_part23_checked

  · exact kid12_part29_checked

  · exact kid12_part35_checked

def kid12_part36 : Audit := .cycle 0 11 true (0)
theorem kid12_part36_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part36) = true := by rfl

def kid12_part37 : Audit := .cycle 1 10 true (1)
theorem kid12_part37_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part37) = true := by rfl

def kid12_part38 : Audit := .cycle 26 1 false (6)
theorem kid12_part38_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part38) = true := by rfl

def kid12_part39 : Audit := .cycle 20 1 false (2)
theorem kid12_part39_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part39) = true := by rfl

def kid12_part40 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 14 (5,true),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 2 true (3),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (5,true),
.last 25 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 23 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 31 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.split 12 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 51 1 false (7),
.last 18 (5,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.last 27 (5,true),
.cycle 21 3 false (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 22 (5,true),
.last 18 (5,true),
.last 29 (5,true),
.cycle 10 4 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid12_part40_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part40) = true := by rfl

def kid12_part41 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.cycle 10 4 true (2)
]),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 25 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 25 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 22 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 1 false (2),
.cycle 19 1 false (3),
.last 15 (4,false),
.cycle 13 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.split 12 (4,false) (byMove [
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
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 24 (5,true),
.last 17 (5,true),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.last 15 (5,true),
.cycle 51 1 false (7),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 15 (5,true),
.last 15 (5,true),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true)
]),
.split 14 (5,true) (byMove [
.cycle 12 11 false (2),
.cycle 11 13 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 20 1 false (2),
.last 16 (4,false),
.cycle 19 1 false (1),
.cycle 21 1 false (3),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 18 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 12 8 true (0),
.cycle 17 1 false (1),
.cycle 21 1 false (1),
.cycle 5 10 true (0),
.last 23 (4,false),
.cycle 16 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.split 12 (4,false) (byMove [
.last 28 (5,true),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 14 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (2),
.cycle 25 11 false (1),
.cycle 10 8 true (2),
.last 30 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid12_part41_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part41) = true := by rfl

def kid12_part42 : Audit := .cycle 16 3 false (1)
theorem kid12_part42_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part42) = true := by rfl

def kid12_part43 : Audit := .split 19 (4,false) (byMove [
.cycle 0 24 true (-2),
.cycle 25 7 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.split 20 (5,false) (byMove [
.cycle 0 21 false (3),
.cycle 26 7 false (-1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 11 11 false (2),
.cycle 0 24 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.last 23 (5,true),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 11 13 false (2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 29 7 false (-1),
.cycle 0 24 true (-2),
.cycle 25 7 false (0),
.cycle 0 26 true (-2),
.last 22 (5,true),
.last 23 (5,true)
]),
.cycle 20 7 false (1),
.cycle 20 7 false (1),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 21 7 false (1),
.split 20 (5,false) (byMove [
.cycle 11 11 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 true (-1),
.cycle 20 1 false (0),
.cycle 23 1 false (3),
.cycle 29 7 false (4),
.cycle 21 7 false (1),
.cycle 0 22 true (-1),
.cycle 21 7 false (1),
.last 21 (5,true),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 25 1 false (3),
.cycle 21 1 false (-1),
.last 22 (5,true),
.cycle 20 1 false (0),
.cycle 27 7 false (2),
.cycle 21 7 false (1),
.cycle 21 7 false (1),
.cycle 0 22 true (-1),
.cycle 17 4 true (-1),
.last 21 (5,true)
]),
.cycle 20 7 false (-1),
.cycle 20 7 false (-1),
.cycle 22 7 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.split 20 (5,false) (byMove [
.cycle 11 11 false (2),
.cycle 6 23 false (3),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 0 24 true (-2),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 21 (5,true),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 0 26 true (-3),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 0 24 true (-2),
.cycle 21 7 false (-1),
.cycle 21 7 false (-1),
.cycle 8 14 false (3),
.cycle 17 4 false (1),
.last 21 (5,true)
]),
.cycle 15 5 false (2),
.cycle 11 9 false (2),
.cycle 0 22 true (-1),
.cycle 22 7 false (1),
.cycle 22 7 false (0),
.split 20 (5,false) (byMove [
.cycle 0 24 true (-1),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 21 (5,true),
.cycle 28 7 false (1),
.cycle 48 7 false (0),
.cycle 14 7 false (2),
.cycle 0 22 true (-1),
.cycle 10 11 false (2),
.last 21 (5,true),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 21 (5,true),
.cycle 3 21 false (3),
.cycle 16 5 false (2),
.cycle 12 9 false (2),
.cycle 0 22 true (-1),
.cycle 22 7 false (0),
.last 21 (5,true)
])
])
theorem kid12_part43_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part43) = true := by rfl

def kid12_part44 : Audit := .cycle 0 13 true (0)
theorem kid12_part44_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part44) = true := by rfl

def kid12_part45 : Audit := .cycle 18 1 false (0)
theorem kid12_part45_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part45) = true := by rfl

def kid12_part46 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 3 43 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 11 2 true (0),
.last 13 (5,false)
]),
.cycle 30 1 false (6),
.cycle 1 13 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 14 (5,false),
.last 13 (5,false)
]),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 23 (5,false),
.last 30 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.cycle 16 1 false (4),
.last 15 (5,false),
.last 15 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.last 27 (5,false),
.last 16 (5,false),
.last 15 (5,false)
]),
.cycle 0 27 true (0),
.cycle 14 3 false (0),
.cycle 18 7 false (0),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.last 19 (5,false),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 18 7 false (0),
.last 19 (5,false),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
])
theorem kid12_part46_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part46) = true := by rfl

def kid12_part48 : Audit := .cycle 0 15 true (0)
theorem kid12_part48_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part48) = true := by rfl

def kid12_part49 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.last 36 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 69 32 false (0),
.last 22 (5,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 0 21 true (-1),
.cycle 0 36 true (-2),
.last 42 (5,true),
.last 50 (5,true),
.last 24 (5,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 26 (5,true),
.last 22 (5,true),
.cycle 0 17 true (-1),
.cycle 0 34 true (-2),
.cycle 0 19 true (-1),
.last 17 (5,true),
.cycle 11 3 false (1)
])
theorem kid12_part49_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part49) = true := by rfl

def kid12_part50 : Audit := .cycle 18 1 false (-2)
theorem kid12_part50_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part50) = true := by rfl

def kid12_part51 : Audit := .cycle 17 1 false (-1)
theorem kid12_part51_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part51) = true := by rfl

def kid12_part52 : Audit := .split 14 (4,false) (byMove [
.cycle 12 22 false (2),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 24 true (-2),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.last 22 (5,true),
.cycle 0 24 true (-2),
.cycle 12 9 false (0),
.last 17 (5,true),
.cycle 11 4 false (1)
])
theorem kid12_part52_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part52) = true := by rfl

def kid12_part53 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid12_part53_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part53) = true := by rfl

def kid12_part54 : Audit := .cycle 30 1 false (6)
theorem kid12_part54_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part54) = true := by rfl

def kid12_part55 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 1 14 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.last 31 (5,true),
.cycle 17 1 false (3),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 13 1 true (1),
.cycle 1 14 true (1)
])
theorem kid12_part55_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part55) = true := by rfl

def kid12_part56 : Audit := .split 16 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 20 true (-1),
.cycle 19 1 false (3),
.last 18 (4,false),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 17 5 false (1),
.cycle 20 1 false (4),
.cycle 17 5 false (0),
.cycle 20 5 false (0),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 5 false (0),
.cycle 24 5 false (2),
.cycle 17 5 false (1),
.cycle 19 5 false (1),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 0 39 true (0)
])
theorem kid12_part56_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part56) = true := by rfl

def kid12_part57 : Audit := .cycle 0 13 true (0)
theorem kid12_part57_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part57) = true := by rfl

def kid12_part58 : Audit := .cycle 10 2 true (1)
theorem kid12_part58_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part58) = true := by rfl

def kid12_part59 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.cycle 13 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 13 1 true (3),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.cycle 13 1 true (3)
])
theorem kid12_part59_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part59) = true := by rfl

def kid12_part60 : Audit := .cycle 14 4 false (1)
theorem kid12_part60_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part60) = true := by rfl

def kid12_part61 : Audit := .split 13 (4,false) (byMove [
.cycle 63 8 false (-3),
.cycle 19 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.cycle 14 8 false (1),
.cycle 14 8 false (1),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 15 8 false (1),
.cycle 14 8 false (0),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.last 17 (5,true),
.last 21 (5,true),
.cycle 24 8 false (1),
.cycle 16 8 false (1),
.last 16 (5,true),
.cycle 11 3 false (1)
])
theorem kid12_part61_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part61) = true := by rfl

def kid12_part62 : Audit := .cycle 24 1 false (4)
theorem kid12_part62_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part62) = true := by rfl

def kid12_part63 : Audit := .cycle 19 1 false (-1)
theorem kid12_part63_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part63) = true := by rfl

def kid12_part64 : Audit := .split 14 (4,false) (byMove [
.last 23 (5,true),
.last 224 (5,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 7 false (0),
.cycle 12 11 false (0),
.cycle 12 6 false (0),
.cycle 0 27 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 9 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 5 10 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid12_part64_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part64) = true := by rfl

def kid12_part65 : Audit := .split 12 (5,true) (byMove [
.cycle 12 9 false (1),
.cycle 29 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (4),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 30 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 26 1 false (0),
.cycle 12 2 true (0),
.cycle 13 3 true (1)
])
theorem kid12_part65_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part65) = true := by rfl

def kid12_part66 : Audit := .cycle 0 27 true (0)
theorem kid12_part66_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part66) = true := by rfl

def kid12_part67 : Audit := .split 14 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 12 9 false (2),
.cycle 17 1 false (3),
.last 16 (4,false),
.cycle 17 3 false (1),
.cycle 0 16 true (0),
.cycle 15 3 false (1),
.cycle 1 16 true (0),
.cycle 16 3 false (0),
.cycle 20 3 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 3 false (0),
.cycle 24 3 false (2),
.cycle 15 3 false (1),
.cycle 19 3 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 1 16 true (0)
])
theorem kid12_part67_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part67) = true := by rfl

def kid12_part68 : Audit := .split 18 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 0 22 true (-1),
.cycle 21 1 false (3),
.last 20 (4,false),
.cycle 19 7 false (1),
.cycle 0 20 true (0),
.cycle 19 7 false (1),
.cycle 25 7 false (4),
.cycle 19 7 false (0),
.cycle 20 7 false (0),
.cycle 23 1 false (3),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 19 7 false (0),
.cycle 25 7 false (2),
.cycle 19 7 false (1),
.cycle 19 7 false (1),
.cycle 0 20 true (0),
.cycle 17 2 true (0),
.cycle 2 19 true (0)
])
theorem kid12_part68_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part68) = true := by rfl

def kid12_part69 : Audit := .cycle 0 13 true (0)
theorem kid12_part69_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part69) = true := by rfl

def kid12_part70 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 15 (4,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 18 (4,false),
.last 16 (4,false),
.cycle 34 1 false (6),
.last 15 (4,false),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.last 16 (4,false),
.cycle 16 6 false (1),
.last 15 (4,false),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 14 3 false (0),
.cycle 0 31 true (0),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.last 16 (4,false)
])
theorem kid12_part70_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part70) = true := by rfl

def kid12_part71 : Audit := .split 12 (5,true) (byMove [
.cycle 28 1 false (2),
.last 18 (4,false),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 13 1 true (3),
.cycle 19 7 false (0),
.last 18 (4,false),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.last 15 (4,false),
.cycle 13 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 13 (4,false),
.cycle 13 1 true (3)
])
theorem kid12_part71_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part71) = true := by rfl

def kid12_part47 : Audit := .split 11 (5,false) (byMove [(kid12_part48),(kid12_part49),(kid12_part50),(kid12_part51),(kid12_part52),(kid12_part53),(kid12_part54),(kid12_part55),(kid12_part56),(kid12_part57),(kid12_part58),(kid12_part59),(kid12_part60),(kid12_part61),(kid12_part62),(kid12_part63),(kid12_part64),(kid12_part65),(kid12_part66),(kid12_part67),(kid12_part68),(kid12_part69),(kid12_part70),(kid12_part71)])

theorem kid12_part47_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part47) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part48),(kid12_part49),(kid12_part50),(kid12_part51),(kid12_part52),(kid12_part53),(kid12_part54),(kid12_part55),(kid12_part56),(kid12_part57),(kid12_part58),(kid12_part59),(kid12_part60),(kid12_part61),(kid12_part62),(kid12_part63),(kid12_part64),(kid12_part65),(kid12_part66),(kid12_part67),(kid12_part68),(kid12_part69),(kid12_part70),(kid12_part71)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part48_checked

  · exact kid12_part54_checked

  · exact kid12_part60_checked

  · exact kid12_part66_checked

  · exact kid12_part49_checked

  · exact kid12_part55_checked

  · exact kid12_part61_checked

  · exact kid12_part67_checked

  · exact kid12_part50_checked

  · exact kid12_part56_checked

  · exact kid12_part62_checked

  · exact kid12_part68_checked

  · exact kid12_part51_checked

  · exact kid12_part57_checked

  · exact kid12_part63_checked

  · exact kid12_part69_checked

  · exact kid12_part52_checked

  · exact kid12_part58_checked

  · exact kid12_part64_checked

  · exact kid12_part70_checked

  · exact kid12_part53_checked

  · exact kid12_part59_checked

  · exact kid12_part65_checked

  · exact kid12_part71_checked

def kid12_part72 : Audit := .cycle 0 11 true (0)
theorem kid12_part72_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part72) = true := by rfl

def kid12_part73 : Audit := .cycle 1 10 true (1)
theorem kid12_part73_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part73) = true := by rfl

def kid12_part74 : Audit := .cycle 2 9 true (1)
theorem kid12_part74_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part74) = true := by rfl

def kid12_part75 : Audit := .cycle 51 1 false (7)
theorem kid12_part75_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part75) = true := by rfl

def kid12_part76 : Audit := .split 11 (4,false) (byMove [
.cycle 30 1 false (6),
.cycle 13 13 false (1),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 20 5 false (1),
.last 24 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 11 2 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (5,true),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 13 10 false (1),
.cycle 19 5 false (1),
.cycle 51 1 false (7),
.cycle 10 3 true (2),
.split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 51 1 false (7),
.last 15 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 14 (5,false),
.cycle 20 5 false (1),
.last 24 (5,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.last 25 (5,true),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 16 (5,true),
.last 20 (5,true),
.last 27 (5,true),
.cycle 10 4 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid12_part76_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part76) = true := by rfl

def kid12_part78 : Audit := .cycle 30 1 false (6)
theorem kid12_part78_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part78) = true := by rfl

def kid12_part79 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 1 14 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 0 39 false (3),
.cycle 17 1 false (3),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 13 1 true (1),
.cycle 17 3 false (1)
])
theorem kid12_part79_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part79) = true := by rfl

def kid12_part80 : Audit := .cycle 19 5 false (1)
theorem kid12_part80_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part80) = true := by rfl

def kid12_part81 : Audit := .cycle 0 13 true (0)
theorem kid12_part81_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part81) = true := by rfl

def kid12_part82 : Audit := .cycle 10 2 true (2)
theorem kid12_part82_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part82) = true := by rfl

def kid12_part83 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 17 1 false (1),
.cycle 20 5 false (1),
.last 23 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.cycle 11 2 true (2)
])
theorem kid12_part83_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part83) = true := by rfl

def kid12_part84 : Audit := .cycle 0 12 true (0)
theorem kid12_part84_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part84) = true := by rfl

def kid12_part85 : Audit := .cycle 1 11 true (1)
theorem kid12_part85_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part85) = true := by rfl

def kid12_part86 : Audit := .cycle 7 16 true (2)
theorem kid12_part86_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part86) = true := by rfl

def kid12_part87 : Audit := .cycle 3 9 true (1)
theorem kid12_part87_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part87) = true := by rfl

def kid12_part88 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 30 (5,true),
.cycle 10 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (5,true),
.cycle 10 13 true (2),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 30 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid12_part88_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part88) = true := by rfl

def kid12_part89 : Audit := .cycle 11 1 true (3)
theorem kid12_part89_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part89) = true := by rfl

def kid12_part90 : Audit := .cycle 6 6 true (2)
theorem kid12_part90_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part90) = true := by rfl

def kid12_part91 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 29 1 false (-1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 10 5 true (1),
.cycle 23 11 false (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 15 8 true (-3),
.cycle 0 18 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 18 9 false (2),
.cycle 22 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 30 (5,true),
.cycle 17 3 false (1)
])
theorem kid12_part91_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part91) = true := by rfl

def kid12_part92 : Audit := .cycle 19 5 false (1)
theorem kid12_part92_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part92) = true := by rfl

def kid12_part93 : Audit := .cycle 51 1 false (7)
theorem kid12_part93_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part93) = true := by rfl

def kid12_part94 : Audit := .split 13 (5,true) (byMove [
.cycle 34 1 false (6),
.last 15 (4,false),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.last 15 (4,false),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.cycle 12 2 true (2),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.last 14 (4,false),
.cycle 11 3 true (2)
])
theorem kid12_part94_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part94) = true := by rfl

def kid12_part95 : Audit := .split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 51 1 false (7),
.last 14 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 23 1 false (5),
.cycle 20 5 false (1),
.last 23 (4,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 3 true (2)
])
theorem kid12_part95_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part95) = true := by rfl

def kid12_part96 : Audit := .cycle 0 12 true (0)
theorem kid12_part96_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part96) = true := by rfl

def kid12_part97 : Audit := .cycle 1 11 true (1)
theorem kid12_part97_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part97) = true := by rfl

def kid12_part98 : Audit := .cycle 2 10 true (1)
theorem kid12_part98_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part98) = true := by rfl

def kid12_part99 : Audit := .cycle 13 14 true (2)
theorem kid12_part99_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part99) = true := by rfl

def kid12_part100 : Audit := .split 12 (4,false) (byMove [
.cycle 10 15 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 14 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (2),
.cycle 10 6 true (2),
.cycle 10 10 true (2),
.last 28 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (5,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid12_part100_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part100) = true := by rfl

def kid12_part101 : Audit := .cycle 11 1 true (3)
theorem kid12_part101_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part101) = true := by rfl

def kid12_part77 : Audit := .split 11 (5,false) (byMove [(kid12_part78),(kid12_part79),(kid12_part80),(kid12_part81),(kid12_part82),(kid12_part83),(kid12_part84),(kid12_part85),(kid12_part86),(kid12_part87),(kid12_part88),(kid12_part89),(kid12_part90),(kid12_part91),(kid12_part92),(kid12_part93),(kid12_part94),(kid12_part95),(kid12_part96),(kid12_part97),(kid12_part98),(kid12_part99),(kid12_part100),(kid12_part101)])

theorem kid12_part77_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part77) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part78),(kid12_part79),(kid12_part80),(kid12_part81),(kid12_part82),(kid12_part83),(kid12_part84),(kid12_part85),(kid12_part86),(kid12_part87),(kid12_part88),(kid12_part89),(kid12_part90),(kid12_part91),(kid12_part92),(kid12_part93),(kid12_part94),(kid12_part95),(kid12_part96),(kid12_part97),(kid12_part98),(kid12_part99),(kid12_part100),(kid12_part101)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part78_checked

  · exact kid12_part84_checked

  · exact kid12_part90_checked

  · exact kid12_part96_checked

  · exact kid12_part79_checked

  · exact kid12_part85_checked

  · exact kid12_part91_checked

  · exact kid12_part97_checked

  · exact kid12_part80_checked

  · exact kid12_part86_checked

  · exact kid12_part92_checked

  · exact kid12_part98_checked

  · exact kid12_part81_checked

  · exact kid12_part87_checked

  · exact kid12_part93_checked

  · exact kid12_part99_checked

  · exact kid12_part82_checked

  · exact kid12_part88_checked

  · exact kid12_part94_checked

  · exact kid12_part100_checked

  · exact kid12_part83_checked

  · exact kid12_part89_checked

  · exact kid12_part95_checked

  · exact kid12_part101_checked

def kid12_part5 : Audit := .split 10 (4,true) (byMove [(kid12_part6),(kid12_part7),(kid12_part8),(kid12_part9),(kid12_part10),(kid12_part11),(kid12_part36),(kid12_part37),(kid12_part38),(kid12_part39),(kid12_part40),(kid12_part41),(kid12_part42),(kid12_part43),(kid12_part44),(kid12_part45),(kid12_part46),(kid12_part47),(kid12_part72),(kid12_part73),(kid12_part74),(kid12_part75),(kid12_part76),(kid12_part77)])

theorem kid12_part5_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (kid12_part5) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid12_part6),(kid12_part7),(kid12_part8),(kid12_part9),(kid12_part10),(kid12_part11),(kid12_part36),(kid12_part37),(kid12_part38),(kid12_part39),(kid12_part40),(kid12_part41),(kid12_part42),(kid12_part43),(kid12_part44),(kid12_part45),(kid12_part46),(kid12_part47),(kid12_part72),(kid12_part73),(kid12_part74),(kid12_part75),(kid12_part76),(kid12_part77)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part6_checked

  · exact kid12_part36_checked

  · exact kid12_part42_checked

  · exact kid12_part72_checked

  · exact kid12_part7_checked

  · exact kid12_part37_checked

  · exact kid12_part43_checked

  · exact kid12_part73_checked

  · exact kid12_part8_checked

  · exact kid12_part38_checked

  · exact kid12_part44_checked

  · exact kid12_part74_checked

  · exact kid12_part9_checked

  · exact kid12_part39_checked

  · exact kid12_part45_checked

  · exact kid12_part75_checked

  · exact kid12_part10_checked

  · exact kid12_part40_checked

  · exact kid12_part46_checked

  · exact kid12_part76_checked

  · exact kid12_part11_checked

  · exact kid12_part41_checked

  · exact kid12_part47_checked

  · exact kid12_part77_checked

def kid12_part103 : Audit := .cycle 0 11 true (0)
theorem kid12_part103_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part103) = true := by rfl

def kid12_part104 : Audit := .cycle 1 10 true (1)
theorem kid12_part104_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part104) = true := by rfl

def kid12_part105 : Audit := .cycle 21 1 false (1)
theorem kid12_part105_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part105) = true := by rfl

def kid12_part106 : Audit := .cycle 15 1 false (3)
theorem kid12_part106_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part106) = true := by rfl

def kid12_part108 : Audit := .cycle 14 1 false (2)
theorem kid12_part108_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part108) = true := by rfl

def kid12_part109 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 11 false (-1),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 11 false (1),
.cycle 13 1 true (-1),
.cycle 14 11 false (-1),
.cycle 16 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 47 (4,true),
.cycle 13 1 false (-1),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 18 1 false (2),
.cycle 11 3 false (1),
.cycle 13 1 true (-1)
])
theorem kid12_part109_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part109) = true := by rfl

def kid12_part110 : Audit := .cycle 18 1 false (-2)
theorem kid12_part110_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part110) = true := by rfl

def kid12_part111 : Audit := .cycle 0 13 true (0)
theorem kid12_part111_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part111) = true := by rfl

def kid12_part112 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (3),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid12_part112_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part112) = true := by rfl

def kid12_part113 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 15 false (3),
.cycle 12 12 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 14 1 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 28 (4,true),
.cycle 1 14 false (3),
.cycle 12 11 false (0),
.cycle 19 1 false (1),
.cycle 11 4 false (1),
.cycle 14 1 true (-2)
])
theorem kid12_part113_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part113) = true := by rfl

def kid12_part114 : Audit := .cycle 0 12 true (0)
theorem kid12_part114_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part114) = true := by rfl

def kid12_part115 : Audit := .cycle 1 11 true (1)
theorem kid12_part115_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part115) = true := by rfl

def kid12_part116 : Audit := .cycle 24 1 false (2)
theorem kid12_part116_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part116) = true := by rfl

def kid12_part117 : Audit := .cycle 21 1 false (1)
theorem kid12_part117_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part117) = true := by rfl

def kid12_part118 : Audit := .cycle 11 1 true (1)
theorem kid12_part118_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part118) = true := by rfl

def kid12_part119 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 11 2 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.last 16 (4,true),
.last 20 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 10 4 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
theorem kid12_part119_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part119) = true := by rfl

def kid12_part120 : Audit := .cycle 14 4 false (1)
theorem kid12_part120_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part120) = true := by rfl

def kid12_part121 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 19 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (1),
.cycle 14 8 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 8 false (0),
.cycle 15 8 false (1),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 21 (4,true),
.cycle 0 16 true (-1),
.cycle 16 8 false (1),
.cycle 11 3 false (1),
.last 16 (4,true)
])
theorem kid12_part121_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part121) = true := by rfl

def kid12_part122 : Audit := .split 27 (4,true) (byMove [
.cycle 0 28 false (3),
.cycle 0 41 false (3),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 31 false (3),
.last 28 (5,false),
.cycle 0 28 true (-3),
.cycle 0 41 true (-3),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 0 31 true (-3),
.last 28 (5,false),
.cycle 0 34 false (3),
.cycle 0 38 false (3),
.cycle 0 30 true (-3),
.cycle 28 1 false (-2),
.cycle 33 1 false (1),
.last 28 (5,false),
.cycle 12 30 true (-3),
.cycle 1 27 false (3),
.cycle 0 40 true (-3),
.cycle 32 1 false (2),
.cycle 11 17 false (1),
.last 28 (5,false)
])
theorem kid12_part122_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part122) = true := by rfl

def kid12_part123 : Audit := .cycle 15 1 false (3)
theorem kid12_part123_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part123) = true := by rfl

def kid12_part124 : Audit := .split 12 (4,true) (byMove [
.cycle 0 22 false (3),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 15 1 false (3),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 14 1 false (2),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 24 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 11 3 true (0),
.last 15 (5,false)
])
theorem kid12_part124_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part124) = true := by rfl

def kid12_part125 : Audit := .split 14 (5,false) (byMove [
.last 23 (4,true),
.proven (BB6.Agent11Raw39RCPumps.M691.table) (fun m hm => BB6.Agent11Raw39RCPumps.M691.never m hm),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 0 20 true (-2),
.cycle 12 6 false (0),
.cycle 0 22 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 20 true (-3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 8 8 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid12_part125_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part125) = true := by rfl

def kid12_part126 : Audit := .cycle 0 12 true (0)
theorem kid12_part126_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part126) = true := by rfl

def kid12_part127 : Audit := .cycle 1 11 true (1)
theorem kid12_part127_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part127) = true := by rfl

def kid12_part128 : Audit := .cycle 2 10 true (1)
theorem kid12_part128_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part128) = true := by rfl

def kid12_part129 : Audit := .cycle 34 1 false (6)
theorem kid12_part129_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part129) = true := by rfl

def kid12_part130 : Audit := .cycle 11 1 true (1)
theorem kid12_part130_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part130) = true := by rfl

def kid12_part131 : Audit := .split 12 (5,false) (byMove [
.cycle 28 1 false (2),
.cycle 13 14 false (1),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.last 18 (4,true),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
theorem kid12_part131_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part131) = true := by rfl

def kid12_part107 : Audit := .split 11 (4,false) (byMove [(kid12_part108),(kid12_part109),(kid12_part110),(kid12_part111),(kid12_part112),(kid12_part113),(kid12_part114),(kid12_part115),(kid12_part116),(kid12_part117),(kid12_part118),(kid12_part119),(kid12_part120),(kid12_part121),(kid12_part122),(kid12_part123),(kid12_part124),(kid12_part125),(kid12_part126),(kid12_part127),(kid12_part128),(kid12_part129),(kid12_part130),(kid12_part131)])

theorem kid12_part107_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part107) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part108),(kid12_part109),(kid12_part110),(kid12_part111),(kid12_part112),(kid12_part113),(kid12_part114),(kid12_part115),(kid12_part116),(kid12_part117),(kid12_part118),(kid12_part119),(kid12_part120),(kid12_part121),(kid12_part122),(kid12_part123),(kid12_part124),(kid12_part125),(kid12_part126),(kid12_part127),(kid12_part128),(kid12_part129),(kid12_part130),(kid12_part131)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part108_checked

  · exact kid12_part114_checked

  · exact kid12_part120_checked

  · exact kid12_part126_checked

  · exact kid12_part109_checked

  · exact kid12_part115_checked

  · exact kid12_part121_checked

  · exact kid12_part127_checked

  · exact kid12_part110_checked

  · exact kid12_part116_checked

  · exact kid12_part122_checked

  · exact kid12_part128_checked

  · exact kid12_part111_checked

  · exact kid12_part117_checked

  · exact kid12_part123_checked

  · exact kid12_part129_checked

  · exact kid12_part112_checked

  · exact kid12_part118_checked

  · exact kid12_part124_checked

  · exact kid12_part130_checked

  · exact kid12_part113_checked

  · exact kid12_part119_checked

  · exact kid12_part125_checked

  · exact kid12_part131_checked

def kid12_part132 : Audit := .split 11 (5,false) (byMove [
.cycle 14 1 false (2),
.cycle 13 11 false (0),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 24 (4,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (4,false),
.cycle 17 1 false (3),
.last 13 (4,false),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
]),
.cycle 11 1 true (1),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 0 31 false (3),
.cycle 15 1 false (3),
.split 12 (4,true) (byMove [
.last 23 (4,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 15 1 false (3),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 17 1 false (3),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 25 (4,false),
.last 16 (4,false),
.last 20 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 34 1 false (6),
.split 12 (4,false) (byMove [
.cycle 28 1 false (2),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.cycle 18 7 false (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
]),
.cycle 11 1 true (1)
])
theorem kid12_part132_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part132) = true := by rfl

def kid12_part133 : Audit := .cycle 0 11 true (0)
theorem kid12_part133_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part133) = true := by rfl

def kid12_part134 : Audit := .cycle 1 10 true (1)
theorem kid12_part134_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part134) = true := by rfl

def kid12_part135 : Audit := .cycle 26 1 false (6)
theorem kid12_part135_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part135) = true := by rfl

def kid12_part136 : Audit := .cycle 20 1 false (2)
theorem kid12_part136_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part136) = true := by rfl

def kid12_part137 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 25 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 25 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 18 1 false (0),
.cycle 22 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 1 false (2),
.cycle 19 1 false (3),
.cycle 13 2 true (0),
.last 15 (5,false)
]),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 10 4 true (2),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
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
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 24 (4,true),
.cycle 10 4 true (2),
.last 17 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.split 14 (4,true) (byMove [
.cycle 12 11 false (2),
.cycle 11 13 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 20 1 false (2),
.last 16 (5,false),
.cycle 19 1 false (1),
.cycle 21 1 false (3),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 18 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (2),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 12 8 true (0),
.cycle 17 1 false (1),
.cycle 21 1 false (1),
.cycle 5 10 true (0),
.cycle 16 3 true (2),
.last 23 (5,false)
]),
.split 12 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 15 (4,true),
.cycle 16 1 false (0),
.cycle 51 1 false (7),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 15 (4,true),
.last 15 (4,true),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.last 28 (4,true),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 14 true (2),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 25 11 false (1),
.cycle 10 8 true (2),
.last 30 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid12_part137_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part137) = true := by rfl

def kid12_part138 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.last 14 (4,true)
]),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 26 1 false (6),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (4,true),
.last 25 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 23 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 31 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 51 1 false (7),
.last 18 (4,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2)
]),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 37 true (0),
.split 12 (4,false) (byMove [
.last 27 (4,true),
.cycle 21 3 false (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (2),
.last 22 (4,true),
.last 18 (4,true),
.last 29 (4,true),
.last 13 (4,true),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid12_part138_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part138) = true := by rfl

def kid12_part139 : Audit := .cycle 16 3 false (1)
theorem kid12_part139_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part139) = true := by rfl

def kid12_part140 : Audit := .split 19 (5,false) (byMove [
.cycle 0 24 true (-2),
.cycle 25 7 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.cycle 0 21 false (3),
.cycle 26 7 false (-1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 11 11 false (2),
.cycle 0 24 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 23 (4,true),
.cycle 19 2 true (-2),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 11 13 false (2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 29 7 false (-1),
.cycle 0 24 true (-2),
.cycle 25 7 false (0),
.cycle 0 26 true (-2),
.last 23 (4,true),
.last 22 (4,true)
]),
.cycle 19 1 false (-1),
.cycle 20 7 false (1),
.cycle 20 7 false (1),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.split 20 (4,false) (byMove [
.cycle 11 11 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 true (-1),
.cycle 23 1 false (3),
.cycle 29 7 false (4),
.cycle 21 7 false (1),
.cycle 0 22 true (-1),
.last 21 (4,true),
.cycle 21 7 false (1),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 25 1 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.last 22 (4,true),
.cycle 27 7 false (2),
.cycle 21 7 false (1),
.cycle 21 7 false (1),
.cycle 0 22 true (-1),
.last 21 (4,true),
.cycle 17 4 true (-1)
]),
.cycle 21 7 false (1),
.cycle 20 7 false (-1),
.cycle 20 7 false (-1),
.cycle 22 7 false (1),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.cycle 11 11 false (2),
.cycle 6 23 false (3),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 0 24 true (-2),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 21 (4,true),
.cycle 21 7 false (-1),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 0 26 true (-3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 0 24 true (-2),
.cycle 21 7 false (-1),
.cycle 21 7 false (-1),
.cycle 8 14 false (3),
.last 21 (4,true),
.cycle 17 4 false (1)
]),
.cycle 19 1 false (-1),
.cycle 15 5 false (2),
.cycle 11 9 false (2),
.cycle 0 22 true (-1),
.cycle 22 7 false (1),
.split 20 (4,false) (byMove [
.cycle 0 24 true (-1),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 21 (4,true),
.cycle 21 7 false (-1),
.cycle 28 7 false (1),
.cycle 48 7 false (0),
.cycle 14 7 false (2),
.cycle 0 22 true (-1),
.last 21 (4,true),
.cycle 10 11 false (2),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 21 (4,true),
.cycle 21 7 false (-1),
.cycle 3 21 false (3),
.cycle 16 5 false (2),
.cycle 12 9 false (2),
.cycle 0 22 true (-1),
.last 21 (4,true),
.cycle 22 7 false (0)
]),
.cycle 22 7 false (0)
])
theorem kid12_part140_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part140) = true := by rfl

def kid12_part141 : Audit := .cycle 0 13 true (0)
theorem kid12_part141_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part141) = true := by rfl

def kid12_part142 : Audit := .cycle 18 1 false (0)
theorem kid12_part142_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part142) = true := by rfl

def kid12_part144 : Audit := .cycle 0 15 true (0)
theorem kid12_part144_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part144) = true := by rfl

def kid12_part145 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.last 36 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 69 32 false (0),
.cycle 13 1 false (-1),
.last 22 (4,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 0 36 true (-2),
.cycle 0 21 true (-1),
.last 42 (4,true),
.last 50 (4,true),
.last 24 (4,true),
.cycle 14 1 false (-2),
.last 26 (4,true),
.cycle 13 1 false (-1),
.last 22 (4,true),
.cycle 0 17 true (-1),
.cycle 0 34 true (-2),
.cycle 0 19 true (-1),
.cycle 11 3 false (1),
.last 17 (4,true)
])
theorem kid12_part145_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part145) = true := by rfl

def kid12_part146 : Audit := .cycle 18 1 false (-2)
theorem kid12_part146_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part146) = true := by rfl

def kid12_part147 : Audit := .cycle 17 1 false (-1)
theorem kid12_part147_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part147) = true := by rfl

def kid12_part148 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 28 1 false (0),
.cycle 23 1 false (-1),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid12_part148_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part148) = true := by rfl

def kid12_part149 : Audit := .split 14 (5,false) (byMove [
.cycle 12 22 false (2),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 24 true (-2),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 12 4 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.last 22 (4,true),
.cycle 0 24 true (-2),
.cycle 12 9 false (0),
.cycle 11 4 false (1),
.last 17 (4,true)
])
theorem kid12_part149_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part149) = true := by rfl

def kid12_part150 : Audit := .cycle 30 1 false (6)
theorem kid12_part150_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part150) = true := by rfl

def kid12_part151 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.last 31 (4,true),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 1 14 true (1),
.cycle 13 1 true (1)
])
theorem kid12_part151_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part151) = true := by rfl

def kid12_part152 : Audit := .split 16 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.last 17 (5,false),
.cycle 19 1 false (3),
.last 18 (5,false),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 20 1 false (4),
.cycle 17 5 false (1),
.cycle 17 5 false (0),
.cycle 20 5 false (0),
.cycle 21 1 false (3),
.cycle 17 1 false (-1),
.cycle 17 5 false (0),
.last 17 (5,false),
.cycle 24 5 false (2),
.cycle 17 5 false (1),
.cycle 19 5 false (1),
.cycle 0 18 true (0),
.cycle 0 39 true (0),
.cycle 15 2 true (0)
])
theorem kid12_part152_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part152) = true := by rfl

def kid12_part153 : Audit := .cycle 0 13 true (0)
theorem kid12_part153_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part153) = true := by rfl

def kid12_part154 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 13 1 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 13 1 true (3),
.last 13 (5,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 13 1 true (3),
.last 13 (5,false)
])
theorem kid12_part154_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part154) = true := by rfl

def kid12_part155 : Audit := .cycle 10 2 true (1)
theorem kid12_part155_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part155) = true := by rfl

def kid12_part156 : Audit := .cycle 14 4 false (1)
theorem kid12_part156_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part156) = true := by rfl

def kid12_part157 : Audit := .split 13 (5,false) (byMove [
.cycle 63 8 false (-3),
.cycle 19 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (1),
.cycle 14 8 false (1),
.cycle 18 1 false (4),
.cycle 14 1 false (0),
.cycle 14 8 false (0),
.cycle 15 8 false (1),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 21 (4,true),
.cycle 24 8 false (1),
.cycle 16 8 false (1),
.cycle 11 3 false (1),
.last 16 (4,true)
])
theorem kid12_part157_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part157) = true := by rfl

def kid12_part158 : Audit := .cycle 24 1 false (4)
theorem kid12_part158_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part158) = true := by rfl

def kid12_part159 : Audit := .cycle 19 1 false (-1)
theorem kid12_part159_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part159) = true := by rfl

def kid12_part160 : Audit := .split 12 (4,true) (byMove [
.cycle 12 9 false (1),
.cycle 29 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 18 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 30 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 26 1 false (0),
.cycle 13 3 true (1),
.cycle 12 2 true (0)
])
theorem kid12_part160_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part160) = true := by rfl

def kid12_part161 : Audit := .split 14 (5,false) (byMove [
.last 23 (4,true),
.last 224 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 7 false (0),
.cycle 12 11 false (0),
.cycle 12 6 false (0),
.cycle 0 27 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 9 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 5 10 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid12_part161_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part161) = true := by rfl

def kid12_part162 : Audit := .cycle 0 27 true (0)
theorem kid12_part162_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part162) = true := by rfl

def kid12_part163 : Audit := .split 14 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 9 false (2),
.last 15 (5,false),
.cycle 17 1 false (3),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 20 3 false (0),
.cycle 19 1 false (3),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.last 15 (5,false),
.cycle 24 3 false (2),
.cycle 15 3 false (1),
.cycle 19 3 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 13 2 true (0)
])
theorem kid12_part163_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part163) = true := by rfl

def kid12_part164 : Audit := .split 18 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 22 true (-1),
.last 19 (5,false),
.cycle 21 1 false (3),
.last 20 (5,false),
.cycle 19 7 false (1),
.cycle 0 20 true (0),
.cycle 25 7 false (4),
.cycle 19 7 false (1),
.cycle 19 7 false (0),
.cycle 20 7 false (0),
.cycle 23 1 false (3),
.cycle 19 1 false (-1),
.cycle 19 7 false (0),
.last 19 (5,false),
.cycle 25 7 false (2),
.cycle 19 7 false (1),
.cycle 19 7 false (1),
.cycle 0 20 true (0),
.cycle 2 19 true (0),
.cycle 17 2 true (0)
])
theorem kid12_part164_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part164) = true := by rfl

def kid12_part165 : Audit := .cycle 0 13 true (0)
theorem kid12_part165_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part165) = true := by rfl

def kid12_part166 : Audit := .split 12 (4,true) (byMove [
.cycle 28 1 false (2),
.last 18 (5,false),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.cycle 15 1 true (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 13 1 true (3),
.last 13 (5,false),
.cycle 19 7 false (0),
.last 18 (5,false),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.cycle 13 3 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.cycle 13 1 true (3),
.last 13 (5,false)
])
theorem kid12_part166_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part166) = true := by rfl

def kid12_part167 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 15 (5,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 34 1 false (6),
.last 15 (5,false),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.last 15 (5,false),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.last 18 (5,false),
.cycle 0 31 true (0),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 12 2 true (1)
])
theorem kid12_part167_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part167) = true := by rfl

def kid12_part143 : Audit := .split 11 (4,false) (byMove [(kid12_part144),(kid12_part145),(kid12_part146),(kid12_part147),(kid12_part148),(kid12_part149),(kid12_part150),(kid12_part151),(kid12_part152),(kid12_part153),(kid12_part154),(kid12_part155),(kid12_part156),(kid12_part157),(kid12_part158),(kid12_part159),(kid12_part160),(kid12_part161),(kid12_part162),(kid12_part163),(kid12_part164),(kid12_part165),(kid12_part166),(kid12_part167)])

theorem kid12_part143_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part143) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part144),(kid12_part145),(kid12_part146),(kid12_part147),(kid12_part148),(kid12_part149),(kid12_part150),(kid12_part151),(kid12_part152),(kid12_part153),(kid12_part154),(kid12_part155),(kid12_part156),(kid12_part157),(kid12_part158),(kid12_part159),(kid12_part160),(kid12_part161),(kid12_part162),(kid12_part163),(kid12_part164),(kid12_part165),(kid12_part166),(kid12_part167)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part144_checked

  · exact kid12_part150_checked

  · exact kid12_part156_checked

  · exact kid12_part162_checked

  · exact kid12_part145_checked

  · exact kid12_part151_checked

  · exact kid12_part157_checked

  · exact kid12_part163_checked

  · exact kid12_part146_checked

  · exact kid12_part152_checked

  · exact kid12_part158_checked

  · exact kid12_part164_checked

  · exact kid12_part147_checked

  · exact kid12_part153_checked

  · exact kid12_part159_checked

  · exact kid12_part165_checked

  · exact kid12_part148_checked

  · exact kid12_part154_checked

  · exact kid12_part160_checked

  · exact kid12_part166_checked

  · exact kid12_part149_checked

  · exact kid12_part155_checked

  · exact kid12_part161_checked

  · exact kid12_part167_checked

def kid12_part168 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 3 43 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 22 (4,false),
.cycle 0 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
.cycle 30 1 false (6),
.cycle 1 13 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.last 14 (4,false)
]),
.cycle 10 2 true (1),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 24 1 false (4),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.last 23 (4,false),
.last 30 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 16 1 false (4),
.last 15 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 20 (4,false),
.last 16 (4,false),
.last 20 (4,false),
.last 27 (4,false),
.last 15 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 0 27 true (0),
.cycle 14 3 false (0),
.cycle 18 7 false (0),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 28 1 false (2),
.last 19 (4,false),
.cycle 15 6 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 18 7 false (0),
.last 19 (4,false),
.cycle 15 6 false (1),
.cycle 34 1 false (6),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 34 true (1),
.last 13 (4,false),
.last 14 (4,false)
]),
.cycle 13 3 false (1)
])
theorem kid12_part168_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part168) = true := by rfl

def kid12_part169 : Audit := .cycle 0 11 true (0)
theorem kid12_part169_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part169) = true := by rfl

def kid12_part170 : Audit := .cycle 1 10 true (1)
theorem kid12_part170_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part170) = true := by rfl

def kid12_part171 : Audit := .cycle 2 9 true (1)
theorem kid12_part171_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part171) = true := by rfl

def kid12_part172 : Audit := .cycle 51 1 false (7)
theorem kid12_part172_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part172) = true := by rfl

def kid12_part174 : Audit := .cycle 30 1 false (6)
theorem kid12_part174_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part174) = true := by rfl

def kid12_part175 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 0 39 false (3),
.cycle 17 1 false (3),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 17 3 false (1),
.cycle 13 1 true (1)
])
theorem kid12_part175_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part175) = true := by rfl

def kid12_part176 : Audit := .cycle 19 5 false (1)
theorem kid12_part176_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part176) = true := by rfl

def kid12_part177 : Audit := .cycle 0 13 true (0)
theorem kid12_part177_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part177) = true := by rfl

def kid12_part178 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 17 1 false (1),
.last 13 (5,false),
.cycle 20 5 false (1),
.last 23 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 11 2 true (2),
.last 13 (5,false)
])
theorem kid12_part178_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part178) = true := by rfl

def kid12_part179 : Audit := .cycle 10 2 true (2)
theorem kid12_part179_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part179) = true := by rfl

def kid12_part180 : Audit := .cycle 0 12 true (0)
theorem kid12_part180_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part180) = true := by rfl

def kid12_part181 : Audit := .cycle 1 11 true (1)
theorem kid12_part181_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part181) = true := by rfl

def kid12_part182 : Audit := .cycle 7 16 true (2)
theorem kid12_part182_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part182) = true := by rfl

def kid12_part183 : Audit := .cycle 3 9 true (1)
theorem kid12_part183_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part183) = true := by rfl

def kid12_part184 : Audit := .cycle 11 1 true (3)
theorem kid12_part184_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part184) = true := by rfl

def kid12_part185 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 30 (4,true),
.cycle 11 2 true (3),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 10 13 true (2),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 4 true (2),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 30 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid12_part185_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part185) = true := by rfl

def kid12_part186 : Audit := .cycle 6 6 true (2)
theorem kid12_part186_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part186) = true := by rfl

def kid12_part187 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.cycle 29 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 23 11 false (1),
.cycle 10 5 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 15 8 true (-3),
.cycle 0 18 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 18 9 false (2),
.cycle 22 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 3 false (1),
.last 30 (4,true)
])
theorem kid12_part187_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part187) = true := by rfl

def kid12_part188 : Audit := .cycle 19 5 false (1)
theorem kid12_part188_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part188) = true := by rfl

def kid12_part189 : Audit := .cycle 51 1 false (7)
theorem kid12_part189_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part189) = true := by rfl

def kid12_part190 : Audit := .split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 51 1 false (7),
.last 14 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 23 1 false (5),
.cycle 10 3 true (2),
.cycle 20 5 false (1),
.last 23 (5,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 3 true (2),
.cycle 10 3 true (2)
])
theorem kid12_part190_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part190) = true := by rfl

def kid12_part191 : Audit := .split 13 (4,true) (byMove [
.cycle 34 1 false (6),
.last 15 (5,false),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.last 20 (5,false),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.last 15 (5,false),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.last 20 (5,false),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 11 3 true (2),
.last 14 (5,false)
])
theorem kid12_part191_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part191) = true := by rfl

def kid12_part192 : Audit := .cycle 0 12 true (0)
theorem kid12_part192_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part192) = true := by rfl

def kid12_part193 : Audit := .cycle 1 11 true (1)
theorem kid12_part193_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part193) = true := by rfl

def kid12_part194 : Audit := .cycle 2 10 true (1)
theorem kid12_part194_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part194) = true := by rfl

def kid12_part195 : Audit := .cycle 13 14 true (2)
theorem kid12_part195_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part195) = true := by rfl

def kid12_part196 : Audit := .cycle 11 1 true (3)
theorem kid12_part196_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part196) = true := by rfl

def kid12_part197 : Audit := .split 12 (5,false) (byMove [
.cycle 10 15 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 14 true (2),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 10 6 true (2),
.cycle 10 10 true (2),
.last 28 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid12_part197_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part197) = true := by rfl

def kid12_part173 : Audit := .split 11 (4,false) (byMove [(kid12_part174),(kid12_part175),(kid12_part176),(kid12_part177),(kid12_part178),(kid12_part179),(kid12_part180),(kid12_part181),(kid12_part182),(kid12_part183),(kid12_part184),(kid12_part185),(kid12_part186),(kid12_part187),(kid12_part188),(kid12_part189),(kid12_part190),(kid12_part191),(kid12_part192),(kid12_part193),(kid12_part194),(kid12_part195),(kid12_part196),(kid12_part197)])

theorem kid12_part173_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part173) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part174),(kid12_part175),(kid12_part176),(kid12_part177),(kid12_part178),(kid12_part179),(kid12_part180),(kid12_part181),(kid12_part182),(kid12_part183),(kid12_part184),(kid12_part185),(kid12_part186),(kid12_part187),(kid12_part188),(kid12_part189),(kid12_part190),(kid12_part191),(kid12_part192),(kid12_part193),(kid12_part194),(kid12_part195),(kid12_part196),(kid12_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part174_checked

  · exact kid12_part180_checked

  · exact kid12_part186_checked

  · exact kid12_part192_checked

  · exact kid12_part175_checked

  · exact kid12_part181_checked

  · exact kid12_part187_checked

  · exact kid12_part193_checked

  · exact kid12_part176_checked

  · exact kid12_part182_checked

  · exact kid12_part188_checked

  · exact kid12_part194_checked

  · exact kid12_part177_checked

  · exact kid12_part183_checked

  · exact kid12_part189_checked

  · exact kid12_part195_checked

  · exact kid12_part178_checked

  · exact kid12_part184_checked

  · exact kid12_part190_checked

  · exact kid12_part196_checked

  · exact kid12_part179_checked

  · exact kid12_part185_checked

  · exact kid12_part191_checked

  · exact kid12_part197_checked

def kid12_part198 : Audit := .split 11 (5,false) (byMove [
.cycle 30 1 false (6),
.cycle 13 13 false (1),
.cycle 19 5 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 20 5 false (1),
.last 24 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.cycle 11 2 true (2)
]),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 16 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (4,true),
.last 14 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 29 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 13 10 false (1),
.cycle 19 5 false (1),
.cycle 51 1 false (7),
.split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 51 1 false (7),
.last 15 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 10 3 true (2),
.cycle 20 5 false (1),
.last 24 (4,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 10 3 true (2)
]),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 13 14 true (2),
.split 12 (4,false) (byMove [
.last 25 (4,true),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (2),
.last 16 (4,true),
.last 20 (4,true),
.last 27 (4,true),
.last 13 (4,true),
.cycle 10 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid12_part198_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part198) = true := by rfl

def kid12_part102 : Audit := .split 10 (5,true) (byMove [(kid12_part103),(kid12_part104),(kid12_part105),(kid12_part106),(kid12_part107),(kid12_part132),(kid12_part133),(kid12_part134),(kid12_part135),(kid12_part136),(kid12_part137),(kid12_part138),(kid12_part139),(kid12_part140),(kid12_part141),(kid12_part142),(kid12_part143),(kid12_part168),(kid12_part169),(kid12_part170),(kid12_part171),(kid12_part172),(kid12_part173),(kid12_part198)])

theorem kid12_part102_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (kid12_part102) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid12_part103),(kid12_part104),(kid12_part105),(kid12_part106),(kid12_part107),(kid12_part132),(kid12_part133),(kid12_part134),(kid12_part135),(kid12_part136),(kid12_part137),(kid12_part138),(kid12_part139),(kid12_part140),(kid12_part141),(kid12_part142),(kid12_part143),(kid12_part168),(kid12_part169),(kid12_part170),(kid12_part171),(kid12_part172),(kid12_part173),(kid12_part198)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part103_checked

  · exact kid12_part133_checked

  · exact kid12_part139_checked

  · exact kid12_part169_checked

  · exact kid12_part104_checked

  · exact kid12_part134_checked

  · exact kid12_part140_checked

  · exact kid12_part170_checked

  · exact kid12_part105_checked

  · exact kid12_part135_checked

  · exact kid12_part141_checked

  · exact kid12_part171_checked

  · exact kid12_part106_checked

  · exact kid12_part136_checked

  · exact kid12_part142_checked

  · exact kid12_part172_checked

  · exact kid12_part107_checked

  · exact kid12_part137_checked

  · exact kid12_part143_checked

  · exact kid12_part173_checked

  · exact kid12_part132_checked

  · exact kid12_part138_checked

  · exact kid12_part168_checked

  · exact kid12_part198_checked

def kid12_part199 : Audit := .cycle 0 10 true (0)
theorem kid12_part199_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,0⟩)) (kid12_part199) = true := by rfl

def kid12_part200 : Audit := .cycle 1 9 true (1)
theorem kid12_part200_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,1⟩)) (kid12_part200) = true := by rfl

def kid12_part201 : Audit := .cycle 7 12 true (2)
theorem kid12_part201_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,2⟩)) (kid12_part201) = true := by rfl

def kid12_part202 : Audit := .cycle 3 7 true (1)
theorem kid12_part202_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,3⟩)) (kid12_part202) = true := by rfl

def kid12_part204 : Audit := .cycle 0 11 true (0)
theorem kid12_part204_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part204) = true := by rfl

def kid12_part205 : Audit := .cycle 1 10 true (1)
theorem kid12_part205_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part205) = true := by rfl

def kid12_part206 : Audit := .cycle 2 9 true (1)
theorem kid12_part206_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part206) = true := by rfl

def kid12_part207 : Audit := .split 25 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (0),
.cycle 57 1 false (7),
.cycle 33 1 false (7),
.cycle 0 38 true (0),
.split 26 (5,false) (byMove [
.cycle 29 1 false (3),
.cycle 29 1 false (1),
.cycle 35 1 false (3),
.cycle 0 38 true (0),
.cycle 30 1 false (-2),
.last 27 (5,true),
.cycle 0 31 true (0),
.cycle 6 66 true (0),
.cycle 70 11 true (6),
.cycle 57 1 false (7),
.cycle 35 1 false (7),
.last 28 (5,true),
.cycle 39 1 false (7),
.cycle 41 1 false (3),
.cycle 22 5 false (3),
.cycle 33 1 false (7),
.cycle 30 1 false (-2),
.last 27 (5,true),
.cycle 0 31 true (0),
.cycle 1 34 true (0),
.cycle 12 16 true (0),
.cycle 4 46 true (0),
.cycle 0 35 true (0),
.last 28 (5,true)
]),
.cycle 0 52 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 14, 64, 64],[4, 16, 16, 1, 2, 64, 64],96⟩,
.cycle 7 34 true (0),
.cycle 64 9 true (6),
.cycle 63 1 false (7),
.split 26 (5,true) (byMove [
.cycle 0 50 true (0),
.cycle 0 30 true (0),
.last 48 (5,false),
.cycle 0 40 true (0),
.cycle 32 1 false (4),
.last 27 (5,false),
.last 70 (5,false),
.proven (BB6.Agent11Raw39RCPumps.M693.table) (fun m hm => BB6.Agent11Raw39RCPumps.M693.never m hm),
.last 52 (5,false),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false),
.last 30 (5,false),
.last 34 (5,false),
.last 76 (5,false),
.last 44 (5,false),
.cycle 35 1 false (7),
.last 27 (5,false),
.last 38 (5,false),
.last 48 (5,false),
.last 56 (5,false),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false)
]),
.cycle 26 20 true (2),
.cycle 28 28 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.cycle 45 1 false (7),
.split 26 (5,false) (byMove [
.cycle 39 1 false (7),
.cycle 29 1 false (1),
.cycle 45 1 false (7),
.cycle 45 1 false (7),
.cycle 30 1 false (-2),
.last 27 (5,true),
.cycle 6 40 true (0),
.cycle 75 1 false (7),
.cycle 27 24 true (2),
.cycle 0 58 true (0),
.cycle 25 2 true (2),
.last 27 (5,true),
.cycle 21 6 true (1),
.cycle 21 11 false (3),
.cycle 22 5 false (3),
.cycle 51 1 false (7),
.cycle 30 1 false (-2),
.last 27 (5,true),
.cycle 27 12 true (3),
.cycle 27 20 true (3),
.cycle 28 28 true (2),
.cycle 5 22 true (0),
.last 28 (5,true),
.last 27 (5,true)
]),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 6 58 true (0),
.cycle 0 40 true (0),
.cycle 0 30 true (0),
.split 26 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 42 true (0),
.cycle 0 36 true (0),
.last 52 (5,false),
.last 28 (5,false),
.last 28 (5,false),
.cycle 0 40 true (0),
.last 56 (5,false),
.last 56 (5,false),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false),
.last 32 (5,false),
.last 32 (5,false),
.last 36 (5,false),
.last 56 (5,false),
.cycle 25 2 true (3),
.last 28 (5,false),
.last 38 (5,false),
.cycle 1 43 true (0),
.cycle 2 46 true (0),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false)
])
])
theorem kid12_part207_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part207) = true := by rfl

def kid12_part208 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (0),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.cycle 13 1 true (1),
.cycle 16 6 false (2),
.cycle 15 10 false (1),
.cycle 12 5 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 4 25 true (0),
.last 16 (5,true),
.cycle 13 1 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (0),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (0),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 26 (5,true),
.last 24 (5,true),
.cycle 20 1 false (2),
.cycle 13 1 true (3),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 12 9 true (0),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 30 (5,true),
.cycle 11 3 true (2),
.cycle 13 1 true (3)
]),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 6 21 true (0),
.cycle 21 1 false (1),
.last 20 (5,true),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.last 14 (5,true),
.cycle 12 6 true (0),
.cycle 12 11 false (2),
.cycle 12 5 false (2),
.cycle 23 1 false (-1),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 12 12 true (1),
.last 18 (5,true),
.last 22 (5,true),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 11 2 true (2),
.split 13 (5,false) (byMove [
.last 26 (5,true),
.cycle 21 1 false (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (2),
.cycle 3 11 true (1),
.cycle 10 4 true (2),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.cycle 12 3 true (2),
.cycle 12 5 true (1),
.last 28 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (5,true),
.cycle 11 3 true (2),
.cycle 13 1 true (3)
])
])
theorem kid12_part208_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part208) = true := by rfl

def kid12_part210 : Audit := .split 23 (4,true) (byMove [
.cycle 0 44 true (0),
.cycle 0 27 true (0),
.cycle 45 1 false (5),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 27 1 false (3),
.cycle 24 19 true (1),
.cycle 0 27 true (0),
.cycle 7 17 true (0),
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.last 24 (5,true),
.cycle 24 15 true (2),
.cycle 26 19 true (2),
.cycle 26 21 true (1),
.cycle 41 1 false (5),
.last 25 (5,true),
.cycle 30 1 false (6),
.cycle 0 35 true (0),
.cycle 9 15 true (0),
.cycle 6 19 true (0),
.cycle 0 25 true (0),
.last 26 (5,true),
.last 24 (5,true)
])
theorem kid12_part210_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part210) = true := by rfl

def kid12_part211 : Audit := .cycle 1 14 true (1)
theorem kid12_part211_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part211) = true := by rfl

def kid12_part212 : Audit := .cycle 19 5 false (2)
theorem kid12_part212_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part212) = true := by rfl

def kid12_part213 : Audit := .cycle 0 13 true (0)
theorem kid12_part213_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part213) = true := by rfl

def kid12_part214 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (0),
.cycle 12 9 true (0),
.last 16 (5,true),
.cycle 17 2 false (1),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.last 14 (5,true),
.cycle 11 2 true (2)
])
theorem kid12_part214_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part214) = true := by rfl

def kid12_part215 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.cycle 20 5 false (2),
.last 23 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.cycle 12 2 true (2),
.cycle 11 2 true (2)
])
theorem kid12_part215_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part215) = true := by rfl

def kid12_part216 : Audit := .cycle 0 12 true (0)
theorem kid12_part216_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part216) = true := by rfl

def kid12_part217 : Audit := .cycle 1 11 true (1)
theorem kid12_part217_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part217) = true := by rfl

def kid12_part218 : Audit := .split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 63 1 false (9),
.last 23 (5,true),
.cycle 11 11 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.last 35 (5,true),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (5,true),
.cycle 7 16 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.last 23 (5,true),
.cycle 11 11 true (2)
])
theorem kid12_part218_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part218) = true := by rfl

def kid12_part219 : Audit := .cycle 3 9 true (1)
theorem kid12_part219_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part219) = true := by rfl

def kid12_part220 : Audit := .cycle 10 2 true (3)
theorem kid12_part220_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part220) = true := by rfl

def kid12_part221 : Audit := .cycle 11 1 true (3)
theorem kid12_part221_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part221) = true := by rfl

def kid12_part222 : Audit := .cycle 6 6 true (2)
theorem kid12_part222_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part222) = true := by rfl

def kid12_part223 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.cycle 14 12 false (2),
.cycle 25 11 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 34 true (0),
.cycle 0 25 true (0),
.cycle 6 12 true (2),
.cycle 6 11 true (2),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 14 12 false (2),
.cycle 23 11 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 5 25 true (0),
.last 15 (5,true),
.cycle 11 3 true (2)
])
theorem kid12_part223_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part223) = true := by rfl

def kid12_part224 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 35 true (0),
.last 17 (5,true),
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 20 true (1),
.cycle 12 9 true (1),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.cycle 12 10 true (1),
.cycle 12 14 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 45 true (0),
.last 17 (5,true),
.cycle 11 5 true (1)
])
theorem kid12_part224_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part224) = true := by rfl

def kid12_part225 : Audit := .split 25 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (0),
.cycle 57 1 false (7),
.cycle 33 1 false (7),
.last 27 (5,true),
.cycle 33 1 false (7),
.cycle 0 52 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.cycle 7 34 true (0),
.cycle 64 9 true (6),
.cycle 63 1 false (7),
.last 26 (5,true),
.cycle 26 20 true (2),
.cycle 28 28 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.last 27 (5,true),
.cycle 51 1 false (7),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 6 58 true (0),
.cycle 0 40 true (0),
.last 29 (5,true),
.last 26 (5,true)
])
theorem kid12_part225_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part225) = true := by rfl

def kid12_part226 : Audit := .split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.cycle 0 18 true (0),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 0 52 true (0),
.cycle 20 2 false (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 20 2 false (2),
.last 13 (5,true),
.cycle 13 10 true (1),
.cycle 12 18 true (1),
.cycle 0 62 true (0),
.cycle 29 1 false (1),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 0 24 true (0),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid12_part226_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part226) = true := by rfl

def kid12_part227 : Audit := .split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.last 21 (4,true),
.cycle 0 18 true (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 25 (4,true),
.last 20 (4,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 23 1 false (5),
.last 15 (4,true),
.last 19 (4,true),
.last 27 (4,true),
.last 19 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 23 (4,true),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (2)
])
theorem kid12_part227_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part227) = true := by rfl

def kid12_part228 : Audit := .cycle 0 12 true (0)
theorem kid12_part228_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part228) = true := by rfl

def kid12_part229 : Audit := .cycle 1 11 true (1)
theorem kid12_part229_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part229) = true := by rfl

def kid12_part230 : Audit := .cycle 2 10 true (1)
theorem kid12_part230_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part230) = true := by rfl

def kid12_part231 : Audit := .split 25 (4,true) (byMove [
.cycle 6 23 true (2),
.cycle 0 29 true (0),
.cycle 2 33 true (1),
.cycle 0 31 true (0),
.last 27 (5,true),
.cycle 4 23 true (1),
.cycle 6 33 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.last 26 (5,true),
.cycle 8 21 true (2),
.cycle 6 29 true (2),
.cycle 5 37 true (1),
.cycle 4 29 true (1),
.last 27 (5,true),
.cycle 13 14 true (2),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 28 (5,true),
.last 26 (5,true)
])
theorem kid12_part231_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part231) = true := by rfl

def kid12_part232 : Audit := .split 13 (5,true) (byMove [
.last 25 (4,true),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.cycle 10 4 true (3),
.cycle 11 3 true (3),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 12 2 true (3),
.cycle 11 3 true (3)
])
theorem kid12_part232_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part232) = true := by rfl

def kid12_part233 : Audit := .cycle 11 1 true (3)
theorem kid12_part233_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part233) = true := by rfl

def kid12_part209 : Audit := .split 11 (5,false) (byMove [(kid12_part210),(kid12_part211),(kid12_part212),(kid12_part213),(kid12_part214),(kid12_part215),(kid12_part216),(kid12_part217),(kid12_part218),(kid12_part219),(kid12_part220),(kid12_part221),(kid12_part222),(kid12_part223),(kid12_part224),(kid12_part225),(kid12_part226),(kid12_part227),(kid12_part228),(kid12_part229),(kid12_part230),(kid12_part231),(kid12_part232),(kid12_part233)])

theorem kid12_part209_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part209) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part210),(kid12_part211),(kid12_part212),(kid12_part213),(kid12_part214),(kid12_part215),(kid12_part216),(kid12_part217),(kid12_part218),(kid12_part219),(kid12_part220),(kid12_part221),(kid12_part222),(kid12_part223),(kid12_part224),(kid12_part225),(kid12_part226),(kid12_part227),(kid12_part228),(kid12_part229),(kid12_part230),(kid12_part231),(kid12_part232),(kid12_part233)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part210_checked

  · exact kid12_part216_checked

  · exact kid12_part222_checked

  · exact kid12_part228_checked

  · exact kid12_part211_checked

  · exact kid12_part217_checked

  · exact kid12_part223_checked

  · exact kid12_part229_checked

  · exact kid12_part212_checked

  · exact kid12_part218_checked

  · exact kid12_part224_checked

  · exact kid12_part230_checked

  · exact kid12_part213_checked

  · exact kid12_part219_checked

  · exact kid12_part225_checked

  · exact kid12_part231_checked

  · exact kid12_part214_checked

  · exact kid12_part220_checked

  · exact kid12_part226_checked

  · exact kid12_part232_checked

  · exact kid12_part215_checked

  · exact kid12_part221_checked

  · exact kid12_part227_checked

  · exact kid12_part233_checked

def kid12_part234 : Audit := .cycle 0 11 true (0)
theorem kid12_part234_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part234) = true := by rfl

def kid12_part235 : Audit := .cycle 1 10 true (1)
theorem kid12_part235_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part235) = true := by rfl

def kid12_part236 : Audit := .split 21 (4,true) (byMove [
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.split 22 (5,false) (byMove [
.cycle 39 1 false (3),
.cycle 0 27 true (0),
.cycle 0 29 true (0),
.cycle 6 21 true (2),
.cycle 41 1 false (1),
.last 23 (5,true),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 3 29 true (1),
.cycle 7 17 true (2),
.last 24 (5,true),
.cycle 7 21 true (2),
.cycle 0 35 true (0),
.cycle 35 5 false (2),
.cycle 0 27 true (0),
.cycle 7 27 true (1),
.last 23 (5,true),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.cycle 7 17 true (2),
.last 24 (5,true)
]),
.cycle 6 29 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[4, 16, 16, 1, 2, 64, 64],96⟩,
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 33 (5,false),
.cycle 3 20 true (1),
.cycle 10 13 true (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 7 29 true (2),
.cycle 12 11 true (2),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 4, 16777216, 128, 256, 32768, 1048580, 16384, 16777216, 524288, 1048576, 2097152, 65536, 1048576, 16777216, 128, 256, 32768, 8404992, 16384, 16777216, 16777216],[4, 16, 65536, 1, 32, 16, 16384, 65536, 65536, 4096, 131072, 65536, 1048576, 4194304, 65536, 262144, 8388608, 4194304, 16384, 65536, 65536, 4096, 131072, 65536, 16777216],31607840⟩,
.last 23 (5,false),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.last 31 (5,false),
.cycle 7 17 true (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 11 31 true (2),
.last 34 (5,false),
.last 23 (5,false)
]),
.cycle 8 17 true (2),
.cycle 6 25 true (2),
.cycle 5 33 true (1),
.cycle 4 25 true (1),
.cycle 7 21 true (2),
.split 22 (5,false) (byMove [
.cycle 77 1 false (13),
.cycle 7 25 true (2),
.cycle 7 29 true (2),
.cycle 8 21 true (2),
.cycle 8 29 true (1),
.last 23 (5,true),
.cycle 6 17 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 32, 64, 64],64⟩,
.cycle 7 21 true (2),
.cycle 5 33 true (1),
.cycle 21 2 true (4),
.last 23 (5,true),
.cycle 17 6 true (3),
.cycle 45 11 false (2),
.cycle 35 5 false (2),
.cycle 5 25 true (1),
.last 32 (5,true),
.last 23 (5,true),
.cycle 6 17 true (2),
.cycle 9 17 true (2),
.cycle 6 25 true (2),
.cycle 11 14 true (2),
.last 24 (5,true),
.last 23 (5,true)
]),
.cycle 0 33 true (0),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.split 22 (5,true) (byMove [
.cycle 11 13 true (2),
.cycle 7 33 true (2),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 33 (5,false),
.cycle 3 20 true (1),
.cycle 10 13 true (2),
.last 23 (5,false),
.cycle 6 17 true (2),
.last 25 (5,false),
.last 27 (5,false),
.cycle 5 33 true (1),
.cycle 21 2 true (5),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 11 15 true (2),
.last 34 (5,false),
.last 23 (5,false)
])
])
theorem kid12_part236_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part236) = true := by rfl

def kid12_part237 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 59 1 false (9),
.cycle 3 18 true (1),
.split 20 (5,false) (byMove [
.cycle 37 1 false (3),
.cycle 37 1 false (3),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 45 1 false (1),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.cycle 10 11 true (2),
.cycle 20 1 true (4),
.cycle 6 15 true (2),
.cycle 6 20 true (2),
.cycle 33 5 false (2),
.cycle 59 1 false (9),
.cycle 8 17 true (1),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 4 32 true (1),
.cycle 3 19 true (1),
.cycle 20 1 true (4)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 24 true (2),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.cycle 10 11 true (2),
.last 23 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 33 (5,true),
.last 31 (5,true),
.last 33 (5,true),
.cycle 20 1 true (6),
.cycle 8 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 12 9 true (2),
.cycle 0 23 true (0),
.last 23 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.last 37 (5,true),
.cycle 3 19 true (1),
.cycle 20 1 true (6)
]),
.cycle 8 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 22 true (0),
.split 20 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 8 14 true (2),
.cycle 36 1 false (0),
.last 21 (5,true),
.cycle 6 28 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 32, 64, 64],64⟩,
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 19 2 true (4),
.last 21 (5,true),
.cycle 15 6 true (3),
.cycle 43 11 false (2),
.cycle 33 5 false (2),
.cycle 5 16 true (1),
.cycle 14 10 true (1),
.last 21 (5,true),
.cycle 11 12 true (2),
.cycle 9 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 21 (5,true)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 0 49 true (0),
.cycle 3 18 true (1),
.split 20 (5,false) (byMove [
.last 33 (5,true),
.last 33 (5,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.cycle 10 11 true (2),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.cycle 18 3 true (4),
.cycle 16 5 true (3),
.last 35 (5,true),
.last 22 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.last 35 (5,true),
.cycle 3 19 true (1),
.cycle 20 1 true (6)
])
])
theorem kid12_part237_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part237) = true := by rfl

def kid12_part238 : Audit := .cycle 10 1 true (4)
theorem kid12_part238_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part238) = true := by rfl

def kid12_part240 : Audit := .cycle 0 12 true (0)
theorem kid12_part240_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part240) = true := by rfl

def kid12_part241 : Audit := .cycle 1 11 true (1)
theorem kid12_part241_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part241) = true := by rfl

def kid12_part242 : Audit := .split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 63 1 false (9),
.cycle 2 22 true (1),
.cycle 7 16 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 11 11 true (2),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (5,true),
.last 27 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.cycle 2 22 true (1),
.cycle 7 16 true (2)
])
theorem kid12_part242_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part242) = true := by rfl

def kid12_part243 : Audit := .cycle 3 9 true (1)
theorem kid12_part243_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part243) = true := by rfl

def kid12_part244 : Audit := .cycle 10 2 true (4)
theorem kid12_part244_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part244) = true := by rfl

def kid12_part245 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 19 1 false (3),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 22 1 false (2),
.cycle 19 1 false (1),
.cycle 24 7 false (3),
.last 27 (4,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 14 2 true (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 29 (4,true),
.cycle 12 4 true (2),
.cycle 13 2 true (2)
])
theorem kid12_part245_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part245) = true := by rfl

def kid12_part246 : Audit := .cycle 0 12 true (0)
theorem kid12_part246_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part246) = true := by rfl

def kid12_part247 : Audit := .cycle 1 11 true (1)
theorem kid12_part247_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part247) = true := by rfl

def kid12_part248 : Audit := .split 23 (4,true) (byMove [
.cycle 0 32 true (0),
.cycle 12 16 true (2),
.cycle 2 40 true (1),
.cycle 63 1 false (11),
.cycle 7 38 true (2),
.cycle 5 38 true (1),
.cycle 6 18 true (2),
.cycle 1 25 true (1),
.cycle 7 32 true (2),
.cycle 5 34 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 24 (5,true),
.cycle 8 22 true (2),
.cycle 6 34 true (2),
.cycle 5 20 true (1),
.cycle 4 34 true (1),
.last 25 (5,true),
.cycle 7 28 true (2),
.cycle 6 18 true (2),
.cycle 1 25 true (1),
.cycle 2 28 true (1),
.cycle 0 38 true (0),
.cycle 24 14 true (6),
.last 24 (5,true)
])
theorem kid12_part248_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part248) = true := by rfl

def kid12_part249 : Audit := .split 21 (4,true) (byMove [
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 3 29 true (1),
.cycle 6 29 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[4, 16, 16, 1, 2, 64, 64],64⟩,
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 22 (5,true),
.cycle 8 17 true (2),
.cycle 6 25 true (2),
.cycle 5 33 true (1),
.cycle 4 25 true (1),
.last 23 (5,true),
.cycle 5 33 true (1),
.cycle 0 33 true (0),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.last 22 (5,true)
])
theorem kid12_part249_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part249) = true := by rfl

def kid12_part250 : Audit := .cycle 10 2 true (4)
theorem kid12_part250_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part250) = true := by rfl

def kid12_part251 : Audit := .cycle 11 1 true (5)
theorem kid12_part251_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part251) = true := by rfl

def kid12_part252 : Audit := .cycle 8 4 true (2)
theorem kid12_part252_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part252) = true := by rfl

def kid12_part253 : Audit := .cycle 6 8 true (2)
theorem kid12_part253_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part253) = true := by rfl

def kid12_part254 : Audit := .cycle 0 14 true (0)
theorem kid12_part254_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part254) = true := by rfl

def kid12_part255 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 59 1 false (9),
.cycle 4 18 true (1),
.cycle 59 1 false (9),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 24 true (2),
.cycle 12 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 11 9 true (2),
.cycle 8 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 5 16 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 0 49 true (0),
.cycle 4 18 true (1),
.last 35 (5,true)
])
theorem kid12_part255_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part255) = true := by rfl

def kid12_part256 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.cycle 10 4 true (4),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 10 4 true (4),
.cycle 11 3 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (4,true),
.cycle 12 2 true (4),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (4,true),
.cycle 10 4 true (4),
.last 15 (4,true)
])
theorem kid12_part256_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part256) = true := by rfl

def kid12_part257 : Audit := .split 14 (5,true) (byMove [
.last 22 (4,true),
.cycle 5 12 true (1),
.last 23 (4,true),
.cycle 29 1 false (3),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.last 19 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.cycle 31 1 false (7),
.last 17 (4,true),
.last 21 (4,true),
.last 21 (4,true),
.last 21 (4,true),
.cycle 14 2 true (1),
.cycle 17 1 false (-1),
.last 19 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.cycle 16 3 true (4)
])
theorem kid12_part257_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part257) = true := by rfl

def kid12_part258 : Audit := .cycle 0 12 true (0)
theorem kid12_part258_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part258) = true := by rfl

def kid12_part259 : Audit := .cycle 1 11 true (1)
theorem kid12_part259_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part259) = true := by rfl

def kid12_part260 : Audit := .cycle 2 10 true (1)
theorem kid12_part260_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part260) = true := by rfl

def kid12_part261 : Audit := .split 27 (4,true) (byMove [
.cycle 6 33 true (2),
.cycle 5 25 true (1),
.cycle 2 53 true (1),
.cycle 5 27 true (1),
.cycle 5 25 true (1),
.cycle 4 33 true (1),
.cycle 0 33 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[4, 16, 16, 1, 2, 64, 64],64⟩,
.cycle 7 25 true (2),
.cycle 5 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 28 (5,true),
.cycle 8 29 true (2),
.cycle 6 45 true (2),
.cycle 0 37 true (0),
.cycle 4 45 true (1),
.last 29 (5,true),
.cycle 0 37 true (0),
.cycle 0 33 true (0),
.cycle 9 21 true (2),
.cycle 6 29 true (2),
.cycle 5 23 true (1),
.cycle 28 19 true (6),
.last 28 (5,true)
])
theorem kid12_part261_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part261) = true := by rfl

def kid12_part262 : Audit := .cycle 10 2 true (4)
theorem kid12_part262_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part262) = true := by rfl

def kid12_part263 : Audit := .cycle 11 1 true (5)
theorem kid12_part263_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part263) = true := by rfl

def kid12_part239 : Audit := .split 11 (5,false) (byMove [(kid12_part240),(kid12_part241),(kid12_part242),(kid12_part243),(kid12_part244),(kid12_part245),(kid12_part246),(kid12_part247),(kid12_part248),(kid12_part249),(kid12_part250),(kid12_part251),(kid12_part252),(kid12_part253),(kid12_part254),(kid12_part255),(kid12_part256),(kid12_part257),(kid12_part258),(kid12_part259),(kid12_part260),(kid12_part261),(kid12_part262),(kid12_part263)])

theorem kid12_part239_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part239) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part240),(kid12_part241),(kid12_part242),(kid12_part243),(kid12_part244),(kid12_part245),(kid12_part246),(kid12_part247),(kid12_part248),(kid12_part249),(kid12_part250),(kid12_part251),(kid12_part252),(kid12_part253),(kid12_part254),(kid12_part255),(kid12_part256),(kid12_part257),(kid12_part258),(kid12_part259),(kid12_part260),(kid12_part261),(kid12_part262),(kid12_part263)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part240_checked

  · exact kid12_part246_checked

  · exact kid12_part252_checked

  · exact kid12_part258_checked

  · exact kid12_part241_checked

  · exact kid12_part247_checked

  · exact kid12_part253_checked

  · exact kid12_part259_checked

  · exact kid12_part242_checked

  · exact kid12_part248_checked

  · exact kid12_part254_checked

  · exact kid12_part260_checked

  · exact kid12_part243_checked

  · exact kid12_part249_checked

  · exact kid12_part255_checked

  · exact kid12_part261_checked

  · exact kid12_part244_checked

  · exact kid12_part250_checked

  · exact kid12_part256_checked

  · exact kid12_part262_checked

  · exact kid12_part245_checked

  · exact kid12_part251_checked

  · exact kid12_part257_checked

  · exact kid12_part263_checked

def kid12_part264 : Audit := .cycle 8 3 true (2)
theorem kid12_part264_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part264) = true := by rfl

def kid12_part265 : Audit := .cycle 6 7 true (2)
theorem kid12_part265_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part265) = true := by rfl

def kid12_part266 : Audit := .cycle 0 13 true (0)
theorem kid12_part266_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part266) = true := by rfl

def kid12_part267 : Audit := .cycle 4 7 true (1)
theorem kid12_part267_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part267) = true := by rfl

def kid12_part268 : Audit := .split 12 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 12 16 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (6),
.cycle 15 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 25 true (0),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.cycle 0 70 true (0),
.cycle 43 1 false (3),
.cycle 18 1 false (0),
.last 15 (5,true),
.cycle 16 6 false (2),
.cycle 15 10 false (1),
.cycle 12 5 false (2),
.cycle 20 1 false (6),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.cycle 12 16 true (1),
.cycle 4 33 true (1),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 7 21 true (2),
.cycle 0 60 true (0),
.cycle 26 1 false (6),
.split 13 (5,true) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.last 35 (5,false),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.last 14 (5,false),
.cycle 0 60 true (0),
.cycle 26 1 false (6),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 0 70 true (0),
.last 31 (5,false),
.cycle 18 1 false (0),
.last 14 (5,false),
.last 25 (5,false),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false)
]),
.cycle 13 13 true (1),
.cycle 12 25 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.split 13 (5,false) (byMove [
.cycle 0 64 true (0),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 31 1 false (1),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 6 27 true (1),
.cycle 44 1 false (6),
.last 30 (5,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.last 14 (5,true),
.cycle 12 6 true (0),
.cycle 12 11 false (2),
.cycle 12 5 false (2),
.cycle 37 1 false (1),
.cycle 16 1 false (-2),
.last 14 (5,true),
.cycle 14 12 true (2),
.last 24 (5,true),
.last 36 (5,true),
.cycle 5 9 true (1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.cycle 13 3 true (3),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 21 1 false (1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 27 true (0),
.last 22 (5,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 23 (5,false),
.cycle 5 9 true (1),
.cycle 12 2 true (2),
.last 15 (5,false),
.last 25 (5,false),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false)
])
])
theorem kid12_part268_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part268) = true := by rfl

def kid12_part270 : Audit := .cycle 0 15 true (0)
theorem kid12_part270_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part270) = true := by rfl

def kid12_part271 : Audit := .split 30 (4,true) (byMove [
.cycle 0 39 true (0),
.cycle 15 16 true (1),
.cycle 2 47 true (1),
.cycle 0 67 true (0),
.last 32 (5,true),
.cycle 0 48 true (0),
.cycle 6 25 true (1),
.cycle 1 32 true (1),
.cycle 7 39 true (1),
.cycle 5 41 true (1),
.cycle 0 38 true (0),
.last 31 (5,true),
.cycle 5 92 true (1),
.cycle 5 116 true (1),
.cycle 5 27 true (1),
.cycle 4 41 true (1),
.last 32 (5,true),
.cycle 11 32 true (1),
.cycle 5 40 true (1),
.cycle 1 32 true (1),
.cycle 2 35 true (1),
.cycle 0 45 true (0),
.last 34 (5,true),
.last 31 (5,true)
])
theorem kid12_part271_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part271) = true := by rfl

def kid12_part272 : Audit := .cycle 19 5 false (2)
theorem kid12_part272_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part272) = true := by rfl

def kid12_part273 : Audit := .cycle 8 5 true (2)
theorem kid12_part273_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part273) = true := by rfl

def kid12_part274 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 22 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 0 23 true (0),
.last 16 (5,true),
.cycle 17 2 false (1),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 11 2 true (2)
])
theorem kid12_part274_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part274) = true := by rfl

def kid12_part275 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.last 22 (4,true),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.cycle 20 5 false (2),
.last 23 (4,true),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (4,true),
.cycle 11 2 true (2)
])
theorem kid12_part275_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part275) = true := by rfl

def kid12_part276 : Audit := .split 23 (4,true) (byMove [
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 2 31 true (1),
.cycle 0 29 true (0),
.last 25 (5,true),
.cycle 8 17 true (2),
.cycle 6 31 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 8, 1, 8, 8, 64, 64],64⟩,
.last 24 (5,true),
.cycle 8 19 true (2),
.cycle 6 27 true (2),
.cycle 5 35 true (1),
.cycle 4 27 true (1),
.last 25 (5,true),
.cycle 6 19 true (2),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.last 26 (5,true),
.last 24 (5,true)
])
theorem kid12_part276_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part276) = true := by rfl

def kid12_part277 : Audit := .cycle 9 3 true (3)
theorem kid12_part277_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part277) = true := by rfl

def kid12_part278 : Audit := .cycle 7 5 true (2)
theorem kid12_part278_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part278) = true := by rfl

def kid12_part279 : Audit := .cycle 0 13 true (0)
theorem kid12_part279_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part279) = true := by rfl

def kid12_part280 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 35 1 false (7),
.last 14 (5,true),
.cycle 10 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 12 9 true (2),
.cycle 10 3 true (3),
.cycle 10 4 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.last 14 (5,true),
.cycle 10 4 true (3)
])
theorem kid12_part280_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part280) = true := by rfl

def kid12_part281 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.cycle 16 3 false (0),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 10 3 true (3),
.cycle 13 1 true (5),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 16 3 false (0),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.last 15 (4,true),
.cycle 13 1 true (5)
])
theorem kid12_part281_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part281) = true := by rfl

def kid12_part282 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 39 1 false (7),
.last 18 (5,true),
.cycle 6 12 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 7 21 true (2),
.cycle 12 9 true (2),
.cycle 14 5 true (2),
.cycle 8 10 true (2),
.cycle 8 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.last 18 (5,true),
.cycle 11 6 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 46 true (0),
.last 18 (5,true),
.cycle 6 12 true (2)
])
theorem kid12_part282_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part282) = true := by rfl

def kid12_part283 : Audit := .split 13 (4,true) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 46 1 false (4),
.cycle 25 1 false (1),
.last 28 (5,true),
.cycle 25 11 false (1),
.cycle 0 33 true (0),
.cycle 1 23 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 14 9 true (3),
.last 14 (5,true),
.cycle 8 9 true (2),
.cycle 6 17 true (2),
.cycle 0 39 true (0),
.cycle 39 1 false (3),
.last 28 (5,true),
.cycle 23 11 false (2),
.cycle 0 25 true (0),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid12_part283_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part283) = true := by rfl

def kid12_part284 : Audit := .split 15 (4,true) (byMove [
.cycle 12 15 true (1),
.cycle 0 19 true (0),
.cycle 2 23 true (1),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 19 5 false (2),
.cycle 6 23 true (1),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 4, 64],[9, 13, 1, 9, 9, 64, 64],64⟩,
.cycle 7 9 true (1),
.cycle 0 17 true (0),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 4, 64],[9, 13, 1, 9, 13, 64, 64],64⟩,
.last 16 (5,true),
.cycle 12 13 true (1),
.cycle 12 21 true (1),
.cycle 5 27 true (1),
.cycle 4 19 true (1),
.last 17 (5,true),
.cycle 19 5 false (2),
.cycle 0 27 true (0),
.cycle 9 7 true (1),
.cycle 6 11 true (1),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid12_part284_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part284) = true := by rfl

def kid12_part285 : Audit := .cycle 5 7 true (1)
theorem kid12_part285_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part285) = true := by rfl

def kid12_part286 : Audit := .split 12 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 12 16 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (6),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 7 21 true (2),
.cycle 0 60 true (0),
.last 20 (5,true),
.last 13 (5,true),
.cycle 13 13 true (1),
.cycle 12 25 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.last 14 (5,true),
.cycle 15 2 false (-1),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid12_part286_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part286) = true := by rfl

def kid12_part287 : Audit := .split 12 (5,true) (byMove [
.last 20 (4,true),
.last 28 (4,true),
.last 21 (4,true),
.cycle 20 1 false (6),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 16 (4,true),
.last 27 (4,true),
.last 13 (4,true),
.cycle 26 1 false (6),
.last 15 (4,true),
.last 19 (4,true),
.cycle 5 9 true (1),
.last 19 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 18 (4,true),
.last 25 (4,true),
.last 13 (4,true),
.cycle 13 3 true (3)
])
theorem kid12_part287_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part287) = true := by rfl

def kid12_part288 : Audit := .split 22 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 77 1 false (11),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 7 27 true (2),
.cycle 14 9 true (3),
.cycle 10 13 true (3),
.cycle 0 24 true (0),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.last 24 (5,true),
.cycle 11 12 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 52 true (0),
.last 24 (5,true),
.cycle 0 24 true (0)
])
theorem kid12_part288_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part288) = true := by rfl

def kid12_part289 : Audit := .cycle 9 3 true (3)
theorem kid12_part289_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part289) = true := by rfl

def kid12_part290 : Audit := .cycle 6 7 true (2)
theorem kid12_part290_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part290) = true := by rfl

def kid12_part291 : Audit := .cycle 0 13 true (0)
theorem kid12_part291_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part291) = true := by rfl

def kid12_part292 : Audit := .split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 27 true (2),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 6 11 true (2),
.cycle 0 21 true (0),
.cycle 4 29 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid12_part292_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part292) = true := by rfl

def kid12_part293 : Audit := .split 12 (5,true) (byMove [
.last 23 (4,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 18 (4,true),
.last 25 (4,true),
.last 13 (4,true),
.cycle 17 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (4,true),
.last 15 (4,true),
.cycle 13 1 true (5)
])
theorem kid12_part293_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part293) = true := by rfl

def kid12_part269 : Audit := .split 11 (5,false) (byMove [(kid12_part270),(kid12_part271),(kid12_part272),(kid12_part273),(kid12_part274),(kid12_part275),(kid12_part276),(kid12_part277),(kid12_part278),(kid12_part279),(kid12_part280),(kid12_part281),(kid12_part282),(kid12_part283),(kid12_part284),(kid12_part285),(kid12_part286),(kid12_part287),(kid12_part288),(kid12_part289),(kid12_part290),(kid12_part291),(kid12_part292),(kid12_part293)])

theorem kid12_part269_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part269) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part270),(kid12_part271),(kid12_part272),(kid12_part273),(kid12_part274),(kid12_part275),(kid12_part276),(kid12_part277),(kid12_part278),(kid12_part279),(kid12_part280),(kid12_part281),(kid12_part282),(kid12_part283),(kid12_part284),(kid12_part285),(kid12_part286),(kid12_part287),(kid12_part288),(kid12_part289),(kid12_part290),(kid12_part291),(kid12_part292),(kid12_part293)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part270_checked

  · exact kid12_part276_checked

  · exact kid12_part282_checked

  · exact kid12_part288_checked

  · exact kid12_part271_checked

  · exact kid12_part277_checked

  · exact kid12_part283_checked

  · exact kid12_part289_checked

  · exact kid12_part272_checked

  · exact kid12_part278_checked

  · exact kid12_part284_checked

  · exact kid12_part290_checked

  · exact kid12_part273_checked

  · exact kid12_part279_checked

  · exact kid12_part285_checked

  · exact kid12_part291_checked

  · exact kid12_part274_checked

  · exact kid12_part280_checked

  · exact kid12_part286_checked

  · exact kid12_part292_checked

  · exact kid12_part275_checked

  · exact kid12_part281_checked

  · exact kid12_part287_checked

  · exact kid12_part293_checked

def kid12_part294 : Audit := .cycle 0 11 true (0)
theorem kid12_part294_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part294) = true := by rfl

def kid12_part295 : Audit := .cycle 1 10 true (1)
theorem kid12_part295_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part295) = true := by rfl

def kid12_part296 : Audit := .cycle 2 9 true (1)
theorem kid12_part296_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part296) = true := by rfl

def kid12_part297 : Audit := .split 25 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (2),
.cycle 2 42 true (1),
.cycle 65 1 false (11),
.cycle 4 46 true (1),
.split 26 (5,false) (byMove [
.cycle 43 1 false (3),
.cycle 95 1 false (11),
.cycle 7 32 true (2),
.cycle 0 38 true (0),
.cycle 52 1 false (2),
.last 27 (5,true),
.cycle 0 31 true (0),
.cycle 1 34 true (1),
.cycle 5 40 true (1),
.cycle 3 42 true (1),
.cycle 0 44 true (0),
.last 28 (5,true),
.cycle 0 52 true (0),
.cycle 6 44 true (2),
.cycle 39 5 false (2),
.cycle 65 1 false (11),
.cycle 0 56 true (0),
.last 27 (5,true),
.cycle 0 31 true (0),
.cycle 1 34 true (1),
.cycle 12 16 true (2),
.cycle 4 46 true (1),
.cycle 0 44 true (0),
.last 28 (5,true)
]),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 7 34 true (2),
.cycle 5 36 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 26 (5,true) (byMove [
.cycle 6 24 true (2),
.cycle 0 30 true (0),
.last 48 (5,false),
.cycle 0 36 true (0),
.cycle 4 24 true (1),
.last 27 (5,false),
.cycle 6 36 true (2),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 0, 1],[0, 0, 2097152, 512, 512, 1073741824, 0, 0, 1073741824, 2097152, 1073741824, 1073741824, 1210089984, 1210089984, 1210089984, 32768, 1210089984, 1073741824, 1073741824, 1073741824, 2097152, 134217728, 512, 1073741824, 0, 0, 0, 512, 0, 1073741824, 1073741824],[134217728, 2097152, 64, 0, 1073741824, 0, 0, 1073741824, 262144, 512, 0, 134217728, 1210089984, 1210089984, 4096, 1210089984, 1210089984, 1210089984, 1073741824, 0, 16777216, 0, 512, 1073741824, 0, 2097152, 64, 1073741824, 1073741824, 0, 1073741824],1620016416⟩,
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false),
.last 30 (5,false),
.last 34 (5,false),
.cycle 5 40 true (1),
.last 44 (5,false),
.cycle 0 44 true (0),
.last 27 (5,false),
.last 38 (5,false),
.cycle 9 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false)
]),
.cycle 8 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.cycle 4 36 true (1),
.cycle 5 22 true (1),
.split 26 (5,false) (byMove [
.cycle 5 24 true (1),
.cycle 5 24 true (1),
.cycle 5 26 true (1),
.cycle 8 30 true (2),
.cycle 5 32 true (1),
.last 27 (5,true),
.cycle 6 40 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 32, 64, 64],64⟩,
.cycle 7 30 true (2),
.cycle 5 22 true (1),
.cycle 25 2 true (4),
.last 27 (5,true),
.cycle 21 6 true (3),
.cycle 49 11 false (2),
.cycle 39 5 false (2),
.cycle 5 36 true (1),
.last 40 (5,true),
.last 27 (5,true),
.cycle 27 12 true (5),
.cycle 9 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.last 28 (5,true),
.last 27 (5,true)
]),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 2 30 true (1),
.cycle 0 40 true (0),
.cycle 26 16 true (6),
.split 26 (5,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 30 true (0),
.cycle 0 32 true (0),
.cycle 8 20 true (2),
.last 28 (5,false),
.last 28 (5,false),
.cycle 0 40 true (0),
.last 48 (5,false),
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false),
.last 32 (5,false),
.last 32 (5,false),
.last 36 (5,false),
.cycle 5 22 true (1),
.cycle 25 2 true (5),
.last 28 (5,false),
.last 38 (5,false),
.cycle 9 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.last 28 (5,false),
.last 28 (5,false)
])
])
theorem kid12_part297_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part297) = true := by rfl

def kid12_part298 : Audit := .cycle 10 1 true (4)
theorem kid12_part298_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part298) = true := by rfl

def kid12_part300 : Audit := .split 23 (4,true) (byMove [
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 2 31 true (1),
.cycle 0 29 true (0),
.cycle 0 29 true (0),
.cycle 41 1 false (3),
.cycle 6 31 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 12, 64],[4, 16, 16, 1, 2, 64, 64],64⟩,
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 12, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 24 (5,true),
.cycle 8 19 true (2),
.cycle 6 27 true (2),
.cycle 5 35 true (1),
.cycle 4 27 true (1),
.last 25 (5,true),
.cycle 81 1 false (13),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 24 13 true (6),
.last 24 (5,true)
])
theorem kid12_part300_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part300) = true := by rfl

def kid12_part301 : Audit := .cycle 9 3 true (3)
theorem kid12_part301_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part301) = true := by rfl

def kid12_part302 : Audit := .cycle 7 5 true (2)
theorem kid12_part302_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part302) = true := by rfl

def kid12_part303 : Audit := .cycle 0 13 true (0)
theorem kid12_part303_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part303) = true := by rfl

def kid12_part304 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 35 1 false (7),
.cycle 20 3 false (0),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 12 9 true (2),
.cycle 10 3 true (4),
.cycle 10 4 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 10 3 true (4),
.cycle 11 2 true (4)
])
theorem kid12_part304_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part304) = true := by rfl

def kid12_part305 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.last 16 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 10 3 true (4),
.cycle 21 1 false (1),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.cycle 10 3 true (4),
.cycle 11 2 true (4)
])
theorem kid12_part305_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part305) = true := by rfl

def kid12_part306 : Audit := .cycle 0 12 true (0)
theorem kid12_part306_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part306) = true := by rfl

def kid12_part307 : Audit := .cycle 1 11 true (1)
theorem kid12_part307_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part307) = true := by rfl

def kid12_part308 : Audit := .split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 5 37 true (1),
.cycle 10 12 true (4),
.cycle 11 11 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (4),
.cycle 10 12 true (4),
.last 35 (5,true),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (5,true),
.cycle 7 16 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.cycle 10 12 true (4),
.cycle 11 11 true (4)
])
theorem kid12_part308_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part308) = true := by rfl

def kid12_part309 : Audit := .cycle 3 9 true (1)
theorem kid12_part309_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part309) = true := by rfl

def kid12_part310 : Audit := .cycle 10 2 true (4)
theorem kid12_part310_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part310) = true := by rfl

def kid12_part311 : Audit := .cycle 11 1 true (5)
theorem kid12_part311_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part311) = true := by rfl

def kid12_part312 : Audit := .cycle 6 6 true (2)
theorem kid12_part312_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part312) = true := by rfl

def kid12_part313 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 22 true (1),
.cycle 3 11 true (1),
.cycle 10 4 true (4),
.cycle 6 11 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 34 true (2),
.cycle 0 25 true (0),
.cycle 10 4 true (4),
.cycle 6 11 true (2),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 18 true (1),
.last 15 (5,true),
.cycle 37 11 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 5 25 true (1),
.cycle 10 4 true (4),
.cycle 11 3 true (4)
])
theorem kid12_part313_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part313) = true := by rfl

def kid12_part314 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 35 true (0),
.cycle 12 8 true (3),
.cycle 31 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 20 true (2),
.cycle 12 9 true (3),
.cycle 10 6 true (3),
.cycle 0 19 true (0),
.cycle 8 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 31 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 45 true (0),
.cycle 12 8 true (3),
.cycle 11 5 true (3)
])
theorem kid12_part314_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part314) = true := by rfl

def kid12_part315 : Audit := .split 25 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (2),
.cycle 2 42 true (1),
.cycle 65 1 false (11),
.cycle 5 46 true (1),
.cycle 65 1 false (11),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 7 34 true (2),
.cycle 5 36 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 26 (5,true),
.cycle 8 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.cycle 4 36 true (1),
.last 27 (5,true),
.cycle 5 36 true (1),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 2 30 true (1),
.cycle 0 40 true (0),
.cycle 26 16 true (6),
.last 26 (5,true)
])
theorem kid12_part315_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part315) = true := by rfl

def kid12_part316 : Audit := .split 12 (4,true) (byMove [
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 2 20 true (1),
.cycle 0 18 true (0),
.cycle 20 3 false (0),
.last 19 (5,true),
.cycle 6 20 true (2),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (4),
.last 13 (5,true),
.cycle 8 8 true (2),
.cycle 6 16 true (2),
.cycle 5 24 true (1),
.cycle 4 16 true (1),
.last 14 (5,true),
.last 19 (5,true),
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (4),
.last 13 (5,true)
])
theorem kid12_part316_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part316) = true := by rfl

def kid12_part317 : Audit := .split 12 (5,true) (byMove [
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (4,true),
.cycle 0 18 true (0),
.last 16 (4,true),
.cycle 17 1 false (-1),
.last 25 (4,true),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 38 1 false (8),
.last 15 (4,true),
.last 19 (4,true),
.last 27 (4,true),
.last 19 (4,true),
.last 15 (4,true),
.cycle 17 1 false (-1),
.last 23 (4,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (4)
])
theorem kid12_part317_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part317) = true := by rfl

def kid12_part318 : Audit := .cycle 0 12 true (0)
theorem kid12_part318_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part318) = true := by rfl

def kid12_part319 : Audit := .cycle 1 11 true (1)
theorem kid12_part319_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part319) = true := by rfl

def kid12_part320 : Audit := .cycle 2 10 true (1)
theorem kid12_part320_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part320) = true := by rfl

def kid12_part321 : Audit := .split 25 (4,true) (byMove [
.cycle 6 23 true (2),
.cycle 0 29 true (0),
.cycle 2 33 true (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 4 23 true (1),
.cycle 6 33 true (2),
.cycle 9 17 true (3),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (4),
.last 26 (5,true),
.cycle 8 21 true (2),
.cycle 6 29 true (2),
.cycle 5 37 true (1),
.cycle 4 29 true (1),
.last 27 (5,true),
.cycle 13 14 true (4),
.cycle 0 37 true (0),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (4),
.last 26 (5,true)
])
theorem kid12_part321_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part321) = true := by rfl

def kid12_part322 : Audit := .cycle 10 2 true (4)
theorem kid12_part322_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part322) = true := by rfl

def kid12_part323 : Audit := .cycle 11 1 true (5)
theorem kid12_part323_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part323) = true := by rfl

def kid12_part299 : Audit := .split 11 (5,false) (byMove [(kid12_part300),(kid12_part301),(kid12_part302),(kid12_part303),(kid12_part304),(kid12_part305),(kid12_part306),(kid12_part307),(kid12_part308),(kid12_part309),(kid12_part310),(kid12_part311),(kid12_part312),(kid12_part313),(kid12_part314),(kid12_part315),(kid12_part316),(kid12_part317),(kid12_part318),(kid12_part319),(kid12_part320),(kid12_part321),(kid12_part322),(kid12_part323)])

theorem kid12_part299_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part299) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part300),(kid12_part301),(kid12_part302),(kid12_part303),(kid12_part304),(kid12_part305),(kid12_part306),(kid12_part307),(kid12_part308),(kid12_part309),(kid12_part310),(kid12_part311),(kid12_part312),(kid12_part313),(kid12_part314),(kid12_part315),(kid12_part316),(kid12_part317),(kid12_part318),(kid12_part319),(kid12_part320),(kid12_part321),(kid12_part322),(kid12_part323)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part300_checked

  · exact kid12_part306_checked

  · exact kid12_part312_checked

  · exact kid12_part318_checked

  · exact kid12_part301_checked

  · exact kid12_part307_checked

  · exact kid12_part313_checked

  · exact kid12_part319_checked

  · exact kid12_part302_checked

  · exact kid12_part308_checked

  · exact kid12_part314_checked

  · exact kid12_part320_checked

  · exact kid12_part303_checked

  · exact kid12_part309_checked

  · exact kid12_part315_checked

  · exact kid12_part321_checked

  · exact kid12_part304_checked

  · exact kid12_part310_checked

  · exact kid12_part316_checked

  · exact kid12_part322_checked

  · exact kid12_part305_checked

  · exact kid12_part311_checked

  · exact kid12_part317_checked

  · exact kid12_part323_checked

def kid12_part203 : Audit := .split 10 (4,false) (byMove [(kid12_part204),(kid12_part205),(kid12_part206),(kid12_part207),(kid12_part208),(kid12_part209),(kid12_part234),(kid12_part235),(kid12_part236),(kid12_part237),(kid12_part238),(kid12_part239),(kid12_part264),(kid12_part265),(kid12_part266),(kid12_part267),(kid12_part268),(kid12_part269),(kid12_part294),(kid12_part295),(kid12_part296),(kid12_part297),(kid12_part298),(kid12_part299)])

theorem kid12_part203_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (kid12_part203) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part204),(kid12_part205),(kid12_part206),(kid12_part207),(kid12_part208),(kid12_part209),(kid12_part234),(kid12_part235),(kid12_part236),(kid12_part237),(kid12_part238),(kid12_part239),(kid12_part264),(kid12_part265),(kid12_part266),(kid12_part267),(kid12_part268),(kid12_part269),(kid12_part294),(kid12_part295),(kid12_part296),(kid12_part297),(kid12_part298),(kid12_part299)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part204_checked

  · exact kid12_part234_checked

  · exact kid12_part264_checked

  · exact kid12_part294_checked

  · exact kid12_part205_checked

  · exact kid12_part235_checked

  · exact kid12_part265_checked

  · exact kid12_part295_checked

  · exact kid12_part206_checked

  · exact kid12_part236_checked

  · exact kid12_part266_checked

  · exact kid12_part296_checked

  · exact kid12_part207_checked

  · exact kid12_part237_checked

  · exact kid12_part267_checked

  · exact kid12_part297_checked

  · exact kid12_part208_checked

  · exact kid12_part238_checked

  · exact kid12_part268_checked

  · exact kid12_part298_checked

  · exact kid12_part209_checked

  · exact kid12_part239_checked

  · exact kid12_part269_checked

  · exact kid12_part299_checked

def kid12_part325 : Audit := .cycle 0 11 true (0)
theorem kid12_part325_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part325) = true := by rfl

def kid12_part326 : Audit := .cycle 1 10 true (1)
theorem kid12_part326_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part326) = true := by rfl

def kid12_part327 : Audit := .cycle 2 9 true (1)
theorem kid12_part327_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part327) = true := by rfl

def kid12_part328 : Audit := .split 25 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (0),
.cycle 57 1 false (7),
.cycle 33 1 false (7),
.split 26 (4,false) (byMove [
.cycle 29 1 false (3),
.cycle 29 1 false (1),
.cycle 35 1 false (3),
.cycle 0 38 true (0),
.last 27 (4,true),
.cycle 30 1 false (-2),
.cycle 0 31 true (0),
.cycle 6 66 true (0),
.cycle 70 11 true (6),
.cycle 57 1 false (7),
.last 28 (4,true),
.cycle 35 1 false (7),
.cycle 39 1 false (7),
.cycle 41 1 false (3),
.cycle 22 5 false (3),
.cycle 33 1 false (7),
.last 27 (4,true),
.cycle 30 1 false (-2),
.cycle 0 31 true (0),
.cycle 1 34 true (0),
.cycle 12 16 true (0),
.cycle 4 46 true (0),
.last 28 (4,true),
.cycle 0 35 true (0)
]),
.cycle 0 38 true (0),
.cycle 0 52 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 14, 64],[4, 32, 32, 1, 64, 2, 64],80⟩,
.cycle 7 34 true (0),
.cycle 64 9 true (6),
.split 26 (4,true) (byMove [
.cycle 0 50 true (0),
.cycle 0 30 true (0),
.last 48 (4,false),
.cycle 0 40 true (0),
.last 27 (4,false),
.cycle 32 1 false (4),
.last 70 (4,false),
.proven (BB6.Agent11Raw39RCPumps.M722.table) (fun m hm => BB6.Agent11Raw39RCPumps.M722.never m hm),
.last 52 (4,false),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false),
.last 30 (4,false),
.last 34 (4,false),
.last 76 (4,false),
.last 44 (4,false),
.last 27 (4,false),
.cycle 35 1 false (7),
.last 38 (4,false),
.last 48 (4,false),
.last 56 (4,false),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false)
]),
.cycle 63 1 false (7),
.cycle 26 20 true (2),
.cycle 28 28 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.split 26 (4,false) (byMove [
.cycle 39 1 false (7),
.cycle 29 1 false (1),
.cycle 45 1 false (7),
.cycle 45 1 false (7),
.last 27 (4,true),
.cycle 30 1 false (-2),
.cycle 6 40 true (0),
.cycle 75 1 false (7),
.cycle 27 24 true (2),
.cycle 0 58 true (0),
.last 27 (4,true),
.cycle 25 2 true (2),
.cycle 21 6 true (1),
.cycle 21 11 false (3),
.cycle 22 5 false (3),
.cycle 51 1 false (7),
.last 27 (4,true),
.cycle 30 1 false (-2),
.cycle 27 12 true (3),
.cycle 27 20 true (3),
.cycle 28 28 true (2),
.cycle 5 22 true (0),
.last 27 (4,true),
.last 28 (4,true)
]),
.cycle 45 1 false (7),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 6 58 true (0),
.cycle 0 40 true (0),
.split 26 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 42 true (0),
.cycle 0 36 true (0),
.last 52 (4,false),
.last 28 (4,false),
.last 28 (4,false),
.cycle 0 40 true (0),
.last 56 (4,false),
.last 56 (4,false),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false),
.last 32 (4,false),
.last 32 (4,false),
.last 36 (4,false),
.last 56 (4,false),
.last 28 (4,false),
.cycle 25 2 true (3),
.last 38 (4,false),
.cycle 1 43 true (0),
.cycle 2 46 true (0),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false)
]),
.cycle 0 30 true (0)
])
theorem kid12_part328_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part328) = true := by rfl

def kid12_part330 : Audit := .split 23 (5,true) (byMove [
.cycle 0 44 true (0),
.cycle 0 27 true (0),
.cycle 45 1 false (5),
.cycle 0 29 true (0),
.cycle 27 1 false (3),
.last 25 (4,true),
.cycle 24 19 true (1),
.cycle 0 27 true (0),
.cycle 7 17 true (0),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 0 27 true (0),
.cycle 24 15 true (2),
.cycle 26 19 true (2),
.cycle 26 21 true (1),
.cycle 41 1 false (5),
.cycle 30 1 false (6),
.last 25 (4,true),
.cycle 0 35 true (0),
.cycle 9 15 true (0),
.cycle 6 19 true (0),
.cycle 0 25 true (0),
.last 24 (4,true),
.last 26 (4,true)
])
theorem kid12_part330_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part330) = true := by rfl

def kid12_part331 : Audit := .cycle 1 14 true (1)
theorem kid12_part331_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part331) = true := by rfl

def kid12_part332 : Audit := .cycle 19 5 false (2)
theorem kid12_part332_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part332) = true := by rfl

def kid12_part333 : Audit := .cycle 0 13 true (0)
theorem kid12_part333_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part333) = true := by rfl

def kid12_part334 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 20 5 false (2),
.last 23 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 11 2 true (2),
.cycle 12 2 true (2)
])
theorem kid12_part334_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part334) = true := by rfl

def kid12_part335 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (0),
.cycle 12 9 true (0),
.cycle 17 2 false (1),
.last 16 (4,true),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 11 2 true (2),
.last 14 (4,true)
])
theorem kid12_part335_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part335) = true := by rfl

def kid12_part336 : Audit := .cycle 0 12 true (0)
theorem kid12_part336_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part336) = true := by rfl

def kid12_part337 : Audit := .cycle 1 11 true (1)
theorem kid12_part337_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part337) = true := by rfl

def kid12_part338 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 63 1 false (9),
.cycle 11 11 true (2),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (2),
.last 35 (4,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 7 16 true (2),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.cycle 11 11 true (2),
.last 23 (4,true)
])
theorem kid12_part338_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part338) = true := by rfl

def kid12_part339 : Audit := .cycle 3 9 true (1)
theorem kid12_part339_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part339) = true := by rfl

def kid12_part340 : Audit := .cycle 11 1 true (3)
theorem kid12_part340_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part340) = true := by rfl

def kid12_part341 : Audit := .cycle 10 2 true (3)
theorem kid12_part341_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part341) = true := by rfl

def kid12_part342 : Audit := .cycle 6 6 true (2)
theorem kid12_part342_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part342) = true := by rfl

def kid12_part343 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.cycle 25 11 false (1),
.cycle 14 12 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 34 true (0),
.cycle 0 25 true (0),
.cycle 6 11 true (2),
.cycle 6 12 true (2),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 23 11 false (2),
.cycle 14 12 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 5 25 true (0),
.cycle 11 3 true (2),
.last 15 (4,true)
])
theorem kid12_part343_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part343) = true := by rfl

def kid12_part344 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 35 true (0),
.cycle 19 5 false (2),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 20 true (1),
.cycle 12 9 true (1),
.cycle 0 19 true (0),
.cycle 0 20 true (0),
.cycle 12 10 true (1),
.cycle 12 14 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 19 5 false (2),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 45 true (0),
.cycle 11 5 true (1),
.last 17 (4,true)
])
theorem kid12_part344_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part344) = true := by rfl

def kid12_part345 : Audit := .split 25 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (0),
.cycle 57 1 false (7),
.cycle 33 1 false (7),
.cycle 33 1 false (7),
.last 27 (4,true),
.cycle 0 52 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 7 34 true (0),
.cycle 64 9 true (6),
.last 26 (4,true),
.cycle 63 1 false (7),
.cycle 26 20 true (2),
.cycle 28 28 true (2),
.cycle 0 58 true (0),
.cycle 51 1 false (7),
.cycle 51 1 false (7),
.last 27 (4,true),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 6 58 true (0),
.cycle 0 40 true (0),
.last 26 (4,true),
.last 29 (4,true)
])
theorem kid12_part345_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part345) = true := by rfl

def kid12_part346 : Audit := .split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.last 21 (5,true),
.cycle 0 18 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 25 (5,true),
.last 20 (5,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 23 1 false (5),
.last 13 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 27 (5,true),
.last 19 (5,true),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 23 (5,true),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 3 true (2),
.last 13 (5,true)
])
theorem kid12_part346_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part346) = true := by rfl

def kid12_part347 : Audit := .split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 34 1 false (2),
.cycle 0 18 true (0),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 0 52 true (0),
.cycle 20 2 false (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 20 2 false (2),
.cycle 13 10 true (1),
.cycle 12 18 true (1),
.cycle 0 62 true (0),
.cycle 29 1 false (1),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 0 24 true (0),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid12_part347_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part347) = true := by rfl

def kid12_part348 : Audit := .cycle 0 12 true (0)
theorem kid12_part348_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part348) = true := by rfl

def kid12_part349 : Audit := .cycle 1 11 true (1)
theorem kid12_part349_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part349) = true := by rfl

def kid12_part350 : Audit := .cycle 2 10 true (1)
theorem kid12_part350_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part350) = true := by rfl

def kid12_part351 : Audit := .split 25 (5,true) (byMove [
.cycle 6 23 true (2),
.cycle 0 29 true (0),
.cycle 2 33 true (1),
.cycle 0 31 true (0),
.cycle 4 23 true (1),
.last 27 (4,true),
.cycle 6 33 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 8 21 true (2),
.cycle 6 29 true (2),
.cycle 5 37 true (1),
.cycle 4 29 true (1),
.cycle 13 14 true (2),
.last 27 (4,true),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.last 28 (4,true)
])
theorem kid12_part351_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part351) = true := by rfl

def kid12_part352 : Audit := .cycle 11 1 true (3)
theorem kid12_part352_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part352) = true := by rfl

def kid12_part353 : Audit := .split 13 (4,true) (byMove [
.last 25 (5,true),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.cycle 18 3 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 11 3 true (3),
.cycle 10 4 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 11 3 true (3),
.cycle 12 2 true (3)
])
theorem kid12_part353_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part353) = true := by rfl

def kid12_part329 : Audit := .split 11 (4,false) (byMove [(kid12_part330),(kid12_part331),(kid12_part332),(kid12_part333),(kid12_part334),(kid12_part335),(kid12_part336),(kid12_part337),(kid12_part338),(kid12_part339),(kid12_part340),(kid12_part341),(kid12_part342),(kid12_part343),(kid12_part344),(kid12_part345),(kid12_part346),(kid12_part347),(kid12_part348),(kid12_part349),(kid12_part350),(kid12_part351),(kid12_part352),(kid12_part353)])

theorem kid12_part329_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part329) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part330),(kid12_part331),(kid12_part332),(kid12_part333),(kid12_part334),(kid12_part335),(kid12_part336),(kid12_part337),(kid12_part338),(kid12_part339),(kid12_part340),(kid12_part341),(kid12_part342),(kid12_part343),(kid12_part344),(kid12_part345),(kid12_part346),(kid12_part347),(kid12_part348),(kid12_part349),(kid12_part350),(kid12_part351),(kid12_part352),(kid12_part353)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part330_checked

  · exact kid12_part336_checked

  · exact kid12_part342_checked

  · exact kid12_part348_checked

  · exact kid12_part331_checked

  · exact kid12_part337_checked

  · exact kid12_part343_checked

  · exact kid12_part349_checked

  · exact kid12_part332_checked

  · exact kid12_part338_checked

  · exact kid12_part344_checked

  · exact kid12_part350_checked

  · exact kid12_part333_checked

  · exact kid12_part339_checked

  · exact kid12_part345_checked

  · exact kid12_part351_checked

  · exact kid12_part334_checked

  · exact kid12_part340_checked

  · exact kid12_part346_checked

  · exact kid12_part352_checked

  · exact kid12_part335_checked

  · exact kid12_part341_checked

  · exact kid12_part347_checked

  · exact kid12_part353_checked

def kid12_part354 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (0),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 18 1 false (0),
.cycle 16 6 false (2),
.cycle 15 10 false (1),
.cycle 12 5 false (2),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 4 25 true (0),
.cycle 13 1 true (1),
.last 16 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (0),
.cycle 12 9 true (0),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (0),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 26 (4,true),
.last 24 (4,true),
.cycle 13 1 true (3),
.cycle 20 1 false (2),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 12 9 true (0),
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 30 (4,true),
.cycle 13 1 true (3),
.cycle 11 3 true (2)
]),
.cycle 17 1 false (1),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.split 13 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 6 21 true (0),
.cycle 21 1 false (1),
.last 20 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (1),
.cycle 12 6 true (0),
.cycle 12 11 false (2),
.cycle 12 5 false (2),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 12 12 true (1),
.last 18 (4,true),
.last 22 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.split 13 (4,false) (byMove [
.last 26 (4,true),
.cycle 21 1 false (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 11 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 10 4 true (2),
.cycle 6 8 true (2),
.cycle 12 3 true (2),
.cycle 12 5 true (1),
.last 28 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (4,true),
.cycle 13 1 true (3),
.cycle 11 3 true (2)
]),
.cycle 11 2 true (2)
])
theorem kid12_part354_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part354) = true := by rfl

def kid12_part355 : Audit := .cycle 0 11 true (0)
theorem kid12_part355_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part355) = true := by rfl

def kid12_part356 : Audit := .cycle 1 10 true (1)
theorem kid12_part356_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part356) = true := by rfl

def kid12_part357 : Audit := .split 21 (5,true) (byMove [
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.split 22 (4,false) (byMove [
.cycle 39 1 false (3),
.cycle 0 27 true (0),
.cycle 0 29 true (0),
.cycle 6 21 true (2),
.last 23 (4,true),
.cycle 41 1 false (1),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 3 29 true (1),
.last 24 (4,true),
.cycle 7 17 true (2),
.cycle 7 21 true (2),
.cycle 0 35 true (0),
.cycle 35 5 false (2),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 7 27 true (1),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.last 24 (4,true),
.cycle 7 17 true (2)
]),
.cycle 0 25 true (0),
.cycle 6 29 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[4, 32, 32, 1, 64, 2, 64],80⟩,
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.split 22 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 33 (4,false),
.cycle 3 20 true (1),
.last 23 (4,false),
.cycle 10 13 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 7 29 true (2),
.cycle 12 11 true (2),
.last 23 (4,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 16777216, 4, 128, 256, 32768, 1048580, 16777216, 16384, 524288, 1048576, 2097152, 131072, 16777216, 1048576, 128, 256, 32768, 4210688, 16777216, 16384, 16777216],[4, 32, 131072, 1, 32, 16, 16384, 131072, 131072, 4096, 131072, 65536, 1048576, 8388608, 131072, 262144, 8388608, 4194304, 16384, 131072, 131072, 4096, 131072, 65536, 16777216],31542288⟩,
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.last 31 (4,false),
.last 23 (4,false),
.cycle 7 17 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 11 31 true (2),
.last 23 (4,false),
.last 34 (4,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 64, 4, 64],[4, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 8 17 true (2),
.cycle 6 25 true (2),
.cycle 5 33 true (1),
.cycle 4 25 true (1),
.split 22 (4,false) (byMove [
.cycle 77 1 false (13),
.cycle 7 25 true (2),
.cycle 7 29 true (2),
.cycle 8 21 true (2),
.last 23 (4,true),
.cycle 8 29 true (1),
.cycle 6 17 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 7 21 true (2),
.cycle 5 33 true (1),
.last 23 (4,true),
.cycle 21 2 true (4),
.cycle 17 6 true (3),
.cycle 45 11 false (2),
.cycle 35 5 false (2),
.cycle 5 25 true (1),
.last 23 (4,true),
.last 32 (4,true),
.cycle 6 17 true (2),
.cycle 9 17 true (2),
.cycle 6 25 true (2),
.cycle 11 14 true (2),
.last 23 (4,true),
.last 24 (4,true)
]),
.cycle 7 21 true (2),
.cycle 0 33 true (0),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.split 22 (4,true) (byMove [
.cycle 11 13 true (2),
.cycle 7 33 true (2),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 33 (4,false),
.cycle 3 20 true (1),
.last 23 (4,false),
.cycle 10 13 true (2),
.cycle 6 17 true (2),
.last 25 (4,false),
.last 27 (4,false),
.cycle 5 33 true (1),
.last 24 (4,false),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 11 15 true (2),
.last 23 (4,false),
.last 34 (4,false)
]),
.cycle 22 11 true (6)
])
theorem kid12_part357_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part357) = true := by rfl

def kid12_part358 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 59 1 false (9),
.split 20 (4,false) (byMove [
.cycle 37 1 false (3),
.cycle 37 1 false (3),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 45 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (4),
.cycle 10 11 true (2),
.cycle 6 15 true (2),
.cycle 6 20 true (2),
.cycle 33 5 false (2),
.cycle 59 1 false (9),
.last 21 (4,true),
.cycle 8 17 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 4 32 true (1),
.cycle 20 1 true (4),
.cycle 3 19 true (1)
]),
.cycle 3 18 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 24 true (2),
.cycle 11 9 true (2),
.split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.last 23 (4,true),
.cycle 10 11 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 33 (4,true),
.last 31 (4,true),
.cycle 20 1 true (6),
.last 33 (4,true),
.cycle 8 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 12 9 true (2),
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.last 37 (4,true),
.cycle 20 1 true (6),
.cycle 3 19 true (1)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 64, 8, 64],[4, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 8 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.split 20 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 8 14 true (2),
.last 21 (4,true),
.cycle 36 1 false (0),
.cycle 6 28 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 2 true (4),
.cycle 15 6 true (3),
.cycle 43 11 false (2),
.cycle 33 5 false (2),
.cycle 5 16 true (1),
.last 21 (4,true),
.cycle 14 10 true (1),
.cycle 11 12 true (2),
.cycle 9 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 0 49 true (0),
.split 20 (4,false) (byMove [
.last 33 (4,true),
.last 33 (4,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (6),
.cycle 10 11 true (2),
.cycle 6 15 true (2),
.cycle 18 3 true (4),
.cycle 16 5 true (3),
.last 35 (4,true),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.last 35 (4,true),
.cycle 20 1 true (6),
.cycle 3 19 true (1)
]),
.cycle 3 18 true (1)
])
theorem kid12_part358_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part358) = true := by rfl

def kid12_part360 : Audit := .cycle 0 12 true (0)
theorem kid12_part360_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part360) = true := by rfl

def kid12_part361 : Audit := .cycle 1 11 true (1)
theorem kid12_part361_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part361) = true := by rfl

def kid12_part362 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 63 1 false (9),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (2),
.cycle 11 11 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 52, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 27 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.cycle 7 16 true (2),
.cycle 2 22 true (1)
])
theorem kid12_part362_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part362) = true := by rfl

def kid12_part363 : Audit := .cycle 3 9 true (1)
theorem kid12_part363_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part363) = true := by rfl

def kid12_part364 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 19 1 false (3),
.cycle 17 1 false (-1),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 19 1 false (1),
.cycle 22 1 false (2),
.cycle 24 7 false (3),
.last 27 (5,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 17 1 false (-1),
.cycle 14 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 29 (5,true),
.cycle 13 2 true (2),
.cycle 12 4 true (2)
])
theorem kid12_part364_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part364) = true := by rfl

def kid12_part365 : Audit := .cycle 10 2 true (4)
theorem kid12_part365_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part365) = true := by rfl

def kid12_part366 : Audit := .cycle 0 12 true (0)
theorem kid12_part366_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part366) = true := by rfl

def kid12_part367 : Audit := .cycle 1 11 true (1)
theorem kid12_part367_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part367) = true := by rfl

def kid12_part368 : Audit := .split 23 (5,true) (byMove [
.cycle 0 32 true (0),
.cycle 12 16 true (2),
.cycle 2 40 true (1),
.cycle 63 1 false (11),
.cycle 5 38 true (1),
.cycle 7 38 true (2),
.cycle 6 18 true (2),
.cycle 1 25 true (1),
.cycle 7 32 true (2),
.cycle 5 34 true (1),
.last 24 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 4, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 22 true (2),
.cycle 6 34 true (2),
.cycle 5 20 true (1),
.cycle 4 34 true (1),
.cycle 7 28 true (2),
.last 25 (4,true),
.cycle 6 18 true (2),
.cycle 1 25 true (1),
.cycle 2 28 true (1),
.cycle 0 38 true (0),
.last 24 (4,true),
.cycle 24 14 true (6)
])
theorem kid12_part368_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part368) = true := by rfl

def kid12_part369 : Audit := .split 21 (5,true) (byMove [
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.cycle 0 27 true (0),
.cycle 3 29 true (1),
.cycle 0 25 true (0),
.cycle 6 29 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[4, 32, 32, 1, 64, 2, 64],64⟩,
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 8, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 17 true (2),
.cycle 6 25 true (2),
.cycle 5 33 true (1),
.cycle 4 25 true (1),
.cycle 5 33 true (1),
.last 23 (4,true),
.cycle 0 33 true (0),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 22 11 true (6)
])
theorem kid12_part369_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part369) = true := by rfl

def kid12_part370 : Audit := .cycle 11 1 true (5)
theorem kid12_part370_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part370) = true := by rfl

def kid12_part371 : Audit := .cycle 10 2 true (4)
theorem kid12_part371_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part371) = true := by rfl

def kid12_part372 : Audit := .cycle 8 4 true (2)
theorem kid12_part372_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part372) = true := by rfl

def kid12_part373 : Audit := .cycle 6 8 true (2)
theorem kid12_part373_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part373) = true := by rfl

def kid12_part374 : Audit := .cycle 0 14 true (0)
theorem kid12_part374_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part374) = true := by rfl

def kid12_part375 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 59 1 false (9),
.cycle 59 1 false (9),
.cycle 4 18 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 24 true (2),
.cycle 12 9 true (2),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 36, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 12 true (2),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 5 16 true (1),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 0 49 true (0),
.last 35 (4,true),
.cycle 4 18 true (1)
])
theorem kid12_part375_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part375) = true := by rfl

def kid12_part376 : Audit := .split 14 (4,true) (byMove [
.last 22 (5,true),
.cycle 5 12 true (1),
.last 23 (5,true),
.cycle 29 1 false (3),
.cycle 17 1 false (-1),
.cycle 20 1 false (0),
.last 19 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.cycle 5 10 true (1),
.cycle 31 1 false (7),
.last 15 (5,true),
.last 17 (5,true),
.last 21 (5,true),
.last 21 (5,true),
.last 21 (5,true),
.cycle 17 1 false (-1),
.cycle 14 2 true (1),
.last 19 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.cycle 5 10 true (1),
.cycle 16 3 true (4),
.last 15 (5,true)
])
theorem kid12_part376_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part376) = true := by rfl

def kid12_part377 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.last 18 (5,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 3 true (4),
.cycle 10 4 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (5,true),
.last 18 (5,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (5,true),
.last 15 (5,true),
.cycle 10 4 true (4)
])
theorem kid12_part377_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part377) = true := by rfl

def kid12_part378 : Audit := .cycle 0 12 true (0)
theorem kid12_part378_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part378) = true := by rfl

def kid12_part379 : Audit := .cycle 1 11 true (1)
theorem kid12_part379_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part379) = true := by rfl

def kid12_part380 : Audit := .cycle 2 10 true (1)
theorem kid12_part380_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part380) = true := by rfl

def kid12_part381 : Audit := .split 27 (5,true) (byMove [
.cycle 6 33 true (2),
.cycle 5 25 true (1),
.cycle 2 53 true (1),
.cycle 5 27 true (1),
.cycle 4 33 true (1),
.cycle 5 25 true (1),
.cycle 0 33 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[4, 32, 32, 1, 64, 2, 64],64⟩,
.cycle 7 25 true (2),
.cycle 5 23 true (1),
.last 28 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 8, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 29 true (2),
.cycle 6 45 true (2),
.cycle 0 37 true (0),
.cycle 4 45 true (1),
.cycle 0 37 true (0),
.last 29 (4,true),
.cycle 0 33 true (0),
.cycle 9 21 true (2),
.cycle 6 29 true (2),
.cycle 5 23 true (1),
.last 28 (4,true),
.cycle 28 19 true (6)
])
theorem kid12_part381_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part381) = true := by rfl

def kid12_part382 : Audit := .cycle 11 1 true (5)
theorem kid12_part382_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part382) = true := by rfl

def kid12_part383 : Audit := .cycle 10 2 true (4)
theorem kid12_part383_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part383) = true := by rfl

def kid12_part359 : Audit := .split 11 (4,false) (byMove [(kid12_part360),(kid12_part361),(kid12_part362),(kid12_part363),(kid12_part364),(kid12_part365),(kid12_part366),(kid12_part367),(kid12_part368),(kid12_part369),(kid12_part370),(kid12_part371),(kid12_part372),(kid12_part373),(kid12_part374),(kid12_part375),(kid12_part376),(kid12_part377),(kid12_part378),(kid12_part379),(kid12_part380),(kid12_part381),(kid12_part382),(kid12_part383)])

theorem kid12_part359_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part359) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part360),(kid12_part361),(kid12_part362),(kid12_part363),(kid12_part364),(kid12_part365),(kid12_part366),(kid12_part367),(kid12_part368),(kid12_part369),(kid12_part370),(kid12_part371),(kid12_part372),(kid12_part373),(kid12_part374),(kid12_part375),(kid12_part376),(kid12_part377),(kid12_part378),(kid12_part379),(kid12_part380),(kid12_part381),(kid12_part382),(kid12_part383)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part360_checked

  · exact kid12_part366_checked

  · exact kid12_part372_checked

  · exact kid12_part378_checked

  · exact kid12_part361_checked

  · exact kid12_part367_checked

  · exact kid12_part373_checked

  · exact kid12_part379_checked

  · exact kid12_part362_checked

  · exact kid12_part368_checked

  · exact kid12_part374_checked

  · exact kid12_part380_checked

  · exact kid12_part363_checked

  · exact kid12_part369_checked

  · exact kid12_part375_checked

  · exact kid12_part381_checked

  · exact kid12_part364_checked

  · exact kid12_part370_checked

  · exact kid12_part376_checked

  · exact kid12_part382_checked

  · exact kid12_part365_checked

  · exact kid12_part371_checked

  · exact kid12_part377_checked

  · exact kid12_part383_checked

def kid12_part384 : Audit := .cycle 10 1 true (4)
theorem kid12_part384_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part384) = true := by rfl

def kid12_part385 : Audit := .cycle 8 3 true (2)
theorem kid12_part385_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part385) = true := by rfl

def kid12_part386 : Audit := .cycle 6 7 true (2)
theorem kid12_part386_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part386) = true := by rfl

def kid12_part387 : Audit := .cycle 0 13 true (0)
theorem kid12_part387_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part387) = true := by rfl

def kid12_part388 : Audit := .cycle 4 7 true (1)
theorem kid12_part388_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part388) = true := by rfl

def kid12_part390 : Audit := .cycle 0 15 true (0)
theorem kid12_part390_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part390) = true := by rfl

def kid12_part391 : Audit := .split 30 (5,true) (byMove [
.cycle 0 39 true (0),
.cycle 15 16 true (1),
.cycle 2 47 true (1),
.cycle 0 67 true (0),
.cycle 0 48 true (0),
.last 32 (4,true),
.cycle 6 25 true (1),
.cycle 1 32 true (1),
.cycle 7 39 true (1),
.cycle 5 41 true (1),
.last 31 (4,true),
.cycle 0 38 true (0),
.cycle 5 92 true (1),
.cycle 5 116 true (1),
.cycle 5 27 true (1),
.cycle 4 41 true (1),
.cycle 11 32 true (1),
.last 32 (4,true),
.cycle 5 40 true (1),
.cycle 1 32 true (1),
.cycle 2 35 true (1),
.cycle 0 45 true (0),
.last 31 (4,true),
.last 34 (4,true)
])
theorem kid12_part391_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part391) = true := by rfl

def kid12_part392 : Audit := .cycle 19 5 false (2)
theorem kid12_part392_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part392) = true := by rfl

def kid12_part393 : Audit := .cycle 8 5 true (2)
theorem kid12_part393_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part393) = true := by rfl

def kid12_part394 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.last 22 (5,true),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 20 5 false (2),
.last 23 (5,true),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (2),
.last 15 (5,true)
])
theorem kid12_part394_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part394) = true := by rfl

def kid12_part395 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 22 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 0 23 true (0),
.cycle 17 2 false (1),
.last 16 (4,true),
.cycle 20 5 false (2),
.cycle 23 9 false (2),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (2),
.last 14 (4,true)
])
theorem kid12_part395_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part395) = true := by rfl

def kid12_part396 : Audit := .split 23 (5,true) (byMove [
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 2 31 true (1),
.cycle 0 29 true (0),
.cycle 8 17 true (2),
.last 25 (4,true),
.cycle 6 31 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.last 24 (4,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 8 19 true (2),
.cycle 6 27 true (2),
.cycle 5 35 true (1),
.cycle 4 27 true (1),
.cycle 6 19 true (2),
.last 25 (4,true),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.last 24 (4,true),
.last 26 (4,true)
])
theorem kid12_part396_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part396) = true := by rfl

def kid12_part397 : Audit := .cycle 9 3 true (3)
theorem kid12_part397_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part397) = true := by rfl

def kid12_part398 : Audit := .cycle 7 5 true (2)
theorem kid12_part398_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part398) = true := by rfl

def kid12_part399 : Audit := .cycle 0 13 true (0)
theorem kid12_part399_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part399) = true := by rfl

def kid12_part400 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 13 1 true (3),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 13 1 true (5),
.cycle 10 3 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (3),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 13 1 true (5),
.last 15 (5,true)
])
theorem kid12_part400_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part400) = true := by rfl

def kid12_part401 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 35 1 false (7),
.cycle 10 4 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 12 9 true (2),
.cycle 10 4 true (3),
.cycle 10 3 true (3),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 2 true (3),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 10 4 true (3),
.last 14 (4,true)
])
theorem kid12_part401_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part401) = true := by rfl

def kid12_part402 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 39 1 false (7),
.cycle 6 12 true (2),
.last 18 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 7 21 true (2),
.cycle 12 9 true (2),
.cycle 8 10 true (2),
.cycle 14 5 true (2),
.cycle 8 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.cycle 11 6 true (2),
.last 18 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 46 true (0),
.cycle 6 12 true (2),
.last 18 (4,true)
])
theorem kid12_part402_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part402) = true := by rfl

def kid12_part403 : Audit := .split 13 (5,true) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 46 1 false (4),
.cycle 25 1 false (1),
.cycle 25 11 false (1),
.last 28 (4,true),
.cycle 0 33 true (0),
.cycle 1 23 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 14 9 true (3),
.cycle 8 9 true (2),
.cycle 6 17 true (2),
.cycle 0 39 true (0),
.cycle 39 1 false (3),
.cycle 23 11 false (2),
.last 28 (4,true),
.cycle 0 25 true (0),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid12_part403_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part403) = true := by rfl

def kid12_part404 : Audit := .split 15 (5,true) (byMove [
.cycle 12 15 true (1),
.cycle 0 19 true (0),
.cycle 2 23 true (1),
.cycle 0 21 true (0),
.cycle 19 5 false (2),
.last 17 (4,true),
.cycle 6 23 true (1),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 4, 16, 64],[9, 13, 1, 9, 64, 9, 64],64⟩,
.cycle 7 9 true (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 4, 16, 64],[9, 13, 1, 9, 64, 13, 64],64⟩,
.cycle 12 13 true (1),
.cycle 12 21 true (1),
.cycle 5 27 true (1),
.cycle 4 19 true (1),
.cycle 19 5 false (2),
.last 17 (4,true),
.cycle 0 27 true (0),
.cycle 9 7 true (1),
.cycle 6 11 true (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.last 18 (4,true)
])
theorem kid12_part404_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part404) = true := by rfl

def kid12_part405 : Audit := .cycle 5 7 true (1)
theorem kid12_part405_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part405) = true := by rfl

def kid12_part406 : Audit := .split 12 (4,true) (byMove [
.last 20 (5,true),
.last 28 (5,true),
.last 21 (5,true),
.cycle 20 1 false (6),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 16 (5,true),
.last 27 (5,true),
.cycle 26 1 false (6),
.last 13 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 5 9 true (1),
.last 19 (5,true),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.last 25 (5,true),
.cycle 13 3 true (3),
.last 13 (5,true)
])
theorem kid12_part406_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part406) = true := by rfl

def kid12_part407 : Audit := .split 12 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 12 16 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (6),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 7 21 true (2),
.cycle 0 60 true (0),
.last 13 (4,true),
.last 20 (4,true),
.cycle 13 13 true (1),
.cycle 12 25 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 2 false (-1),
.last 14 (4,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid12_part407_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part407) = true := by rfl

def kid12_part408 : Audit := .split 22 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 77 1 false (11),
.cycle 0 24 true (0),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 7 27 true (2),
.cycle 14 9 true (3),
.cycle 0 24 true (0),
.cycle 10 13 true (3),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.cycle 11 12 true (3),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 52 true (0),
.cycle 0 24 true (0),
.last 24 (4,true)
])
theorem kid12_part408_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part408) = true := by rfl

def kid12_part409 : Audit := .cycle 9 3 true (3)
theorem kid12_part409_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part409) = true := by rfl

def kid12_part410 : Audit := .cycle 6 7 true (2)
theorem kid12_part410_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part410) = true := by rfl

def kid12_part411 : Audit := .cycle 0 13 true (0)
theorem kid12_part411_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part411) = true := by rfl

def kid12_part412 : Audit := .split 12 (4,true) (byMove [
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 15 1 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 13 1 true (5),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.last 25 (5,true),
.cycle 17 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (5,true),
.cycle 13 1 true (5),
.last 15 (5,true)
])
theorem kid12_part412_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part412) = true := by rfl

def kid12_part413 : Audit := .split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 27 true (2),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.cycle 6 11 true (2),
.cycle 0 21 true (0),
.cycle 4 29 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.last 15 (4,true),
.last 14 (4,true)
])
theorem kid12_part413_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part413) = true := by rfl

def kid12_part389 : Audit := .split 11 (4,false) (byMove [(kid12_part390),(kid12_part391),(kid12_part392),(kid12_part393),(kid12_part394),(kid12_part395),(kid12_part396),(kid12_part397),(kid12_part398),(kid12_part399),(kid12_part400),(kid12_part401),(kid12_part402),(kid12_part403),(kid12_part404),(kid12_part405),(kid12_part406),(kid12_part407),(kid12_part408),(kid12_part409),(kid12_part410),(kid12_part411),(kid12_part412),(kid12_part413)])

theorem kid12_part389_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part389) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part390),(kid12_part391),(kid12_part392),(kid12_part393),(kid12_part394),(kid12_part395),(kid12_part396),(kid12_part397),(kid12_part398),(kid12_part399),(kid12_part400),(kid12_part401),(kid12_part402),(kid12_part403),(kid12_part404),(kid12_part405),(kid12_part406),(kid12_part407),(kid12_part408),(kid12_part409),(kid12_part410),(kid12_part411),(kid12_part412),(kid12_part413)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part390_checked

  · exact kid12_part396_checked

  · exact kid12_part402_checked

  · exact kid12_part408_checked

  · exact kid12_part391_checked

  · exact kid12_part397_checked

  · exact kid12_part403_checked

  · exact kid12_part409_checked

  · exact kid12_part392_checked

  · exact kid12_part398_checked

  · exact kid12_part404_checked

  · exact kid12_part410_checked

  · exact kid12_part393_checked

  · exact kid12_part399_checked

  · exact kid12_part405_checked

  · exact kid12_part411_checked

  · exact kid12_part394_checked

  · exact kid12_part400_checked

  · exact kid12_part406_checked

  · exact kid12_part412_checked

  · exact kid12_part395_checked

  · exact kid12_part401_checked

  · exact kid12_part407_checked

  · exact kid12_part413_checked

def kid12_part414 : Audit := .split 12 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 12 16 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (6),
.split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 25 true (0),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.cycle 0 70 true (0),
.cycle 43 1 false (3),
.last 15 (4,true),
.cycle 18 1 false (0),
.cycle 16 6 false (2),
.cycle 15 10 false (1),
.cycle 12 5 false (2),
.cycle 20 1 false (6),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.cycle 12 16 true (1),
.cycle 4 33 true (1),
.last 15 (4,true),
.last 16 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 7 21 true (2),
.cycle 0 60 true (0),
.split 13 (4,true) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.last 35 (4,false),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 18 1 false (0),
.cycle 0 60 true (0),
.cycle 26 1 false (6),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 0 70 true (0),
.last 31 (4,false),
.last 14 (4,false),
.cycle 18 1 false (0),
.last 25 (4,false),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false)
]),
.cycle 26 1 false (6),
.cycle 13 13 true (1),
.cycle 12 25 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.split 13 (4,false) (byMove [
.cycle 0 64 true (0),
.cycle 15 1 false (1),
.cycle 22 1 false (-2),
.cycle 31 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 6 27 true (1),
.cycle 44 1 false (6),
.last 30 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.cycle 12 6 true (0),
.cycle 12 11 false (2),
.cycle 12 5 false (2),
.cycle 37 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (-2),
.cycle 14 12 true (2),
.last 24 (4,true),
.last 36 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 21 1 false (1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 27 true (0),
.last 22 (4,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.cycle 5 9 true (1),
.last 15 (4,false),
.cycle 12 2 true (2),
.last 25 (4,false),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false)
]),
.cycle 13 3 true (3)
])
theorem kid12_part414_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part414) = true := by rfl

def kid12_part415 : Audit := .cycle 0 11 true (0)
theorem kid12_part415_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part415) = true := by rfl

def kid12_part416 : Audit := .cycle 1 10 true (1)
theorem kid12_part416_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part416) = true := by rfl

def kid12_part417 : Audit := .cycle 2 9 true (1)
theorem kid12_part417_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part417) = true := by rfl

def kid12_part418 : Audit := .split 25 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (2),
.cycle 2 42 true (1),
.cycle 65 1 false (11),
.split 26 (4,false) (byMove [
.cycle 43 1 false (3),
.cycle 95 1 false (11),
.cycle 7 32 true (2),
.cycle 0 38 true (0),
.last 27 (4,true),
.cycle 52 1 false (2),
.cycle 0 31 true (0),
.cycle 1 34 true (1),
.cycle 5 40 true (1),
.cycle 3 42 true (1),
.last 28 (4,true),
.cycle 0 44 true (0),
.cycle 0 52 true (0),
.cycle 6 44 true (2),
.cycle 39 5 false (2),
.cycle 65 1 false (11),
.last 27 (4,true),
.cycle 0 56 true (0),
.cycle 0 31 true (0),
.cycle 1 34 true (1),
.cycle 12 16 true (2),
.cycle 4 46 true (1),
.last 28 (4,true),
.cycle 0 44 true (0)
]),
.cycle 4 46 true (1),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 7 34 true (2),
.cycle 5 36 true (1),
.split 26 (4,true) (byMove [
.cycle 6 24 true (2),
.cycle 0 30 true (0),
.last 48 (4,false),
.cycle 0 36 true (0),
.last 27 (4,false),
.cycle 4 24 true (1),
.cycle 6 36 true (2),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 0, 1],[0, 0, 2097152, 512, 1073741824, 512, 0, 0, 1073741824, 2097152, 1073741824, 1073741824, 1210089984, 1210089984, 1210089984, 32768, 1073741824, 1210089984, 1073741824, 1073741824, 2097152, 134217728, 1073741824, 512, 0, 0, 0, 512, 1073741824, 0, 1073741824],[134217728, 2097152, 64, 0, 0, 1073741824, 0, 1073741824, 262144, 512, 134217728, 0, 1210089984, 1210089984, 4096, 1210089984, 1210089984, 1210089984, 1073741824, 0, 16777216, 0, 1073741824, 512, 0, 2097152, 64, 1073741824, 0, 1073741824, 1073741824],1347386640⟩,
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false),
.last 30 (4,false),
.last 34 (4,false),
.cycle 5 40 true (1),
.last 44 (4,false),
.last 27 (4,false),
.cycle 0 44 true (0),
.last 38 (4,false),
.cycle 9 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 64, 8, 64],[4, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 8 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.cycle 4 36 true (1),
.split 26 (4,false) (byMove [
.cycle 5 24 true (1),
.cycle 5 24 true (1),
.cycle 5 26 true (1),
.cycle 8 30 true (2),
.last 27 (4,true),
.cycle 5 32 true (1),
.cycle 6 40 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 7 30 true (2),
.cycle 5 22 true (1),
.last 27 (4,true),
.cycle 25 2 true (4),
.cycle 21 6 true (3),
.cycle 49 11 false (2),
.cycle 39 5 false (2),
.cycle 5 36 true (1),
.last 27 (4,true),
.last 40 (4,true),
.cycle 27 12 true (5),
.cycle 9 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.last 27 (4,true),
.last 28 (4,true)
]),
.cycle 5 22 true (1),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 2 30 true (1),
.cycle 0 40 true (0),
.split 26 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 30 true (0),
.cycle 0 32 true (0),
.cycle 8 20 true (2),
.last 28 (4,false),
.last 28 (4,false),
.cycle 0 40 true (0),
.last 48 (4,false),
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false),
.last 32 (4,false),
.last 32 (4,false),
.last 36 (4,false),
.cycle 5 22 true (1),
.last 28 (4,false),
.cycle 25 2 true (5),
.last 38 (4,false),
.cycle 9 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.last 28 (4,false),
.last 28 (4,false)
]),
.cycle 26 16 true (6)
])
theorem kid12_part418_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part418) = true := by rfl

def kid12_part420 : Audit := .split 23 (5,true) (byMove [
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 2 31 true (1),
.cycle 0 29 true (0),
.cycle 41 1 false (3),
.cycle 0 29 true (0),
.cycle 6 31 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 12, 16, 64],[4, 32, 32, 1, 64, 2, 64],64⟩,
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.last 24 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 12, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 19 true (2),
.cycle 6 27 true (2),
.cycle 5 35 true (1),
.cycle 4 27 true (1),
.cycle 81 1 false (13),
.last 25 (4,true),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.last 24 (4,true),
.cycle 24 13 true (6)
])
theorem kid12_part420_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part420) = true := by rfl

def kid12_part421 : Audit := .cycle 9 3 true (3)
theorem kid12_part421_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part421) = true := by rfl

def kid12_part422 : Audit := .cycle 7 5 true (2)
theorem kid12_part422_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part422) = true := by rfl

def kid12_part423 : Audit := .cycle 0 13 true (0)
theorem kid12_part423_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part423) = true := by rfl

def kid12_part424 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 17 1 false (-1),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 10 3 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 11 2 true (4),
.cycle 10 3 true (4)
])
theorem kid12_part424_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part424) = true := by rfl

def kid12_part425 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 35 1 false (7),
.cycle 15 4 false (1),
.cycle 20 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 12 9 true (2),
.cycle 10 4 true (4),
.cycle 10 3 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 11 2 true (4),
.cycle 10 3 true (4)
])
theorem kid12_part425_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part425) = true := by rfl

def kid12_part426 : Audit := .cycle 0 12 true (0)
theorem kid12_part426_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part426) = true := by rfl

def kid12_part427 : Audit := .cycle 1 11 true (1)
theorem kid12_part427_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part427) = true := by rfl

def kid12_part428 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 5 37 true (1),
.cycle 11 11 true (4),
.cycle 10 12 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 7 26 true (2),
.cycle 13 9 true (4),
.last 35 (4,true),
.cycle 10 12 true (4),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 7 16 true (2),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 51 true (0),
.cycle 11 11 true (4),
.cycle 10 12 true (4)
])
theorem kid12_part428_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part428) = true := by rfl

def kid12_part429 : Audit := .cycle 3 9 true (1)
theorem kid12_part429_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part429) = true := by rfl

def kid12_part430 : Audit := .cycle 11 1 true (5)
theorem kid12_part430_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part430) = true := by rfl

def kid12_part431 : Audit := .cycle 10 2 true (4)
theorem kid12_part431_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part431) = true := by rfl

def kid12_part432 : Audit := .cycle 6 6 true (2)
theorem kid12_part432_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part432) = true := by rfl

def kid12_part433 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 22 true (1),
.cycle 3 11 true (1),
.cycle 6 11 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 34 true (2),
.cycle 0 25 true (0),
.cycle 6 11 true (2),
.cycle 10 4 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 18 true (1),
.cycle 37 11 false (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 5 25 true (1),
.cycle 11 3 true (4),
.cycle 10 4 true (4)
])
theorem kid12_part433_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part433) = true := by rfl

def kid12_part434 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 35 true (0),
.cycle 31 5 false (2),
.cycle 12 8 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 20 true (2),
.cycle 12 9 true (3),
.cycle 0 19 true (0),
.cycle 10 6 true (3),
.cycle 8 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 31 5 false (2),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 45 true (0),
.cycle 11 5 true (3),
.cycle 12 8 true (3)
])
theorem kid12_part434_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part434) = true := by rfl

def kid12_part435 : Audit := .split 25 (5,true) (byMove [
.cycle 0 34 true (0),
.cycle 12 16 true (2),
.cycle 2 42 true (1),
.cycle 65 1 false (11),
.cycle 65 1 false (11),
.cycle 5 46 true (1),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 7 34 true (2),
.cycle 5 36 true (1),
.last 26 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 36, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 8 24 true (2),
.cycle 6 36 true (2),
.cycle 5 22 true (1),
.cycle 4 36 true (1),
.cycle 5 36 true (1),
.last 27 (4,true),
.cycle 6 20 true (2),
.cycle 1 27 true (1),
.cycle 2 30 true (1),
.cycle 0 40 true (0),
.last 26 (4,true),
.cycle 26 16 true (6)
])
theorem kid12_part435_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part435) = true := by rfl

def kid12_part436 : Audit := .split 12 (4,true) (byMove [
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (5,true),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.last 16 (5,true),
.last 25 (5,true),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 38 1 false (8),
.last 13 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 27 (5,true),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 15 (5,true),
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.last 13 (5,true)
])
theorem kid12_part436_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part436) = true := by rfl

def kid12_part437 : Audit := .split 12 (5,true) (byMove [
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 2 20 true (1),
.cycle 0 18 true (0),
.last 19 (4,true),
.cycle 20 3 false (0),
.cycle 6 20 true (2),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 4 true (4),
.cycle 8 8 true (2),
.cycle 6 16 true (2),
.cycle 5 24 true (1),
.cycle 4 16 true (1),
.last 19 (4,true),
.last 14 (4,true),
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 4 true (4)
])
theorem kid12_part437_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part437) = true := by rfl

def kid12_part438 : Audit := .cycle 0 12 true (0)
theorem kid12_part438_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part438) = true := by rfl

def kid12_part439 : Audit := .cycle 1 11 true (1)
theorem kid12_part439_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part439) = true := by rfl

def kid12_part440 : Audit := .cycle 2 10 true (1)
theorem kid12_part440_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part440) = true := by rfl

def kid12_part441 : Audit := .split 25 (5,true) (byMove [
.cycle 6 23 true (2),
.cycle 0 29 true (0),
.cycle 2 33 true (1),
.cycle 0 31 true (0),
.cycle 4 23 true (1),
.cycle 0 29 true (0),
.cycle 6 33 true (2),
.cycle 9 17 true (3),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 10 17 true (4),
.cycle 8 21 true (2),
.cycle 6 29 true (2),
.cycle 5 37 true (1),
.cycle 4 29 true (1),
.cycle 13 14 true (4),
.last 27 (4,true),
.cycle 0 37 true (0),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 10 17 true (4)
])
theorem kid12_part441_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part441) = true := by rfl

def kid12_part442 : Audit := .cycle 11 1 true (5)
theorem kid12_part442_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part442) = true := by rfl

def kid12_part443 : Audit := .cycle 10 2 true (4)
theorem kid12_part443_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part443) = true := by rfl

def kid12_part419 : Audit := .split 11 (4,false) (byMove [(kid12_part420),(kid12_part421),(kid12_part422),(kid12_part423),(kid12_part424),(kid12_part425),(kid12_part426),(kid12_part427),(kid12_part428),(kid12_part429),(kid12_part430),(kid12_part431),(kid12_part432),(kid12_part433),(kid12_part434),(kid12_part435),(kid12_part436),(kid12_part437),(kid12_part438),(kid12_part439),(kid12_part440),(kid12_part441),(kid12_part442),(kid12_part443)])

theorem kid12_part419_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part419) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part420),(kid12_part421),(kid12_part422),(kid12_part423),(kid12_part424),(kid12_part425),(kid12_part426),(kid12_part427),(kid12_part428),(kid12_part429),(kid12_part430),(kid12_part431),(kid12_part432),(kid12_part433),(kid12_part434),(kid12_part435),(kid12_part436),(kid12_part437),(kid12_part438),(kid12_part439),(kid12_part440),(kid12_part441),(kid12_part442),(kid12_part443)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part420_checked

  · exact kid12_part426_checked

  · exact kid12_part432_checked

  · exact kid12_part438_checked

  · exact kid12_part421_checked

  · exact kid12_part427_checked

  · exact kid12_part433_checked

  · exact kid12_part439_checked

  · exact kid12_part422_checked

  · exact kid12_part428_checked

  · exact kid12_part434_checked

  · exact kid12_part440_checked

  · exact kid12_part423_checked

  · exact kid12_part429_checked

  · exact kid12_part435_checked

  · exact kid12_part441_checked

  · exact kid12_part424_checked

  · exact kid12_part430_checked

  · exact kid12_part436_checked

  · exact kid12_part442_checked

  · exact kid12_part425_checked

  · exact kid12_part431_checked

  · exact kid12_part437_checked

  · exact kid12_part443_checked

def kid12_part444 : Audit := .cycle 10 1 true (4)
theorem kid12_part444_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part444) = true := by rfl

def kid12_part324 : Audit := .split 10 (5,false) (byMove [(kid12_part325),(kid12_part326),(kid12_part327),(kid12_part328),(kid12_part329),(kid12_part354),(kid12_part355),(kid12_part356),(kid12_part357),(kid12_part358),(kid12_part359),(kid12_part384),(kid12_part385),(kid12_part386),(kid12_part387),(kid12_part388),(kid12_part389),(kid12_part414),(kid12_part415),(kid12_part416),(kid12_part417),(kid12_part418),(kid12_part419),(kid12_part444)])

theorem kid12_part324_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (kid12_part324) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part325),(kid12_part326),(kid12_part327),(kid12_part328),(kid12_part329),(kid12_part354),(kid12_part355),(kid12_part356),(kid12_part357),(kid12_part358),(kid12_part359),(kid12_part384),(kid12_part385),(kid12_part386),(kid12_part387),(kid12_part388),(kid12_part389),(kid12_part414),(kid12_part415),(kid12_part416),(kid12_part417),(kid12_part418),(kid12_part419),(kid12_part444)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part325_checked

  · exact kid12_part355_checked

  · exact kid12_part385_checked

  · exact kid12_part415_checked

  · exact kid12_part326_checked

  · exact kid12_part356_checked

  · exact kid12_part386_checked

  · exact kid12_part416_checked

  · exact kid12_part327_checked

  · exact kid12_part357_checked

  · exact kid12_part387_checked

  · exact kid12_part417_checked

  · exact kid12_part328_checked

  · exact kid12_part358_checked

  · exact kid12_part388_checked

  · exact kid12_part418_checked

  · exact kid12_part329_checked

  · exact kid12_part359_checked

  · exact kid12_part389_checked

  · exact kid12_part419_checked

  · exact kid12_part354_checked

  · exact kid12_part384_checked

  · exact kid12_part414_checked

  · exact kid12_part444_checked

def kid12_part445 : Audit := .cycle 6 4 true (2)
theorem kid12_part445_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,0⟩)) (kid12_part445) = true := by rfl

def kid12_part446 : Audit := .cycle 17 7 false (1)
theorem kid12_part446_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,1⟩)) (kid12_part446) = true := by rfl

def kid12_part447 : Audit := .cycle 15 3 false (1)
theorem kid12_part447_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,2⟩)) (kid12_part447) = true := by rfl

def kid12_part448 : Audit := .cycle 41 1 false (7)
theorem kid12_part448_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,3⟩)) (kid12_part448) = true := by rfl

def kid12_part450 : Audit := .cycle 0 22 true (0)
theorem kid12_part450_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part450) = true := by rfl

def kid12_part451 : Audit := .cycle 0 14 true (0)
theorem kid12_part451_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part451) = true := by rfl

def kid12_part452 : Audit := .cycle 21 1 false (1)
theorem kid12_part452_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part452) = true := by rfl

def kid12_part453 : Audit := .cycle 0 16 true (0)
theorem kid12_part453_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part453) = true := by rfl

def kid12_part454 : Audit := .split 11 (4,false) (byMove [
.cycle 14 1 false (2),
.cycle 1 26 false (3),
.cycle 18 1 false (-2),
.cycle 23 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 23 (5,false),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 25 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 24 (5,false),
.cycle 0 16 true (0),
.last 23 (5,false),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.last 13 (5,false)
]),
.cycle 8 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.split 12 (5,false) (byMove [
.cycle 0 25 false (3),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 11 2 true (1),
.last 14 (5,true),
.cycle 51 1 false (7),
.last 15 (5,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 14 2 true (2),
.last 13 (5,true),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 28 6 true (2),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 15 2 true (1),
.last 13 (5,true)
]),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 13 6 true (-3),
.cycle 0 16 true (0),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 23 (5,false),
.last 20 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 15 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 20 (5,false),
.cycle 8 6 true (0),
.last 16 (5,false),
.last 14 (5,false)
]),
.cycle 0 22 true (-1),
.cycle 1 21 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.split 12 (5,false) (byMove [
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 6 28 true (1),
.last 15 (5,true),
.cycle 0 58 true (-2),
.cycle 0 14 true (0),
.cycle 14 2 true (2),
.last 13 (5,true),
.cycle 18 7 false (0),
.last 19 (5,true),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 0 78 true (-2),
.cycle 0 22 true (-1),
.cycle 2 21 false (3),
.cycle 0 14 true (0),
.cycle 17 2 true (-1),
.last 13 (5,true)
])
])
theorem kid12_part454_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part454) = true := by rfl

def kid12_part456 : Audit := .cycle 14 1 false (2)
theorem kid12_part456_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part456) = true := by rfl

def kid12_part457 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.last 25 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 11 false (-1),
.cycle 16 1 false (2),
.cycle 12 2 true (-1),
.cycle 14 11 false (0),
.last 23 (5,true),
.cycle 14 11 false (0),
.last 14 (5,true),
.cycle 14 11 false (-1),
.cycle 16 11 false (-1),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 23 11 false (-1),
.cycle 17 11 false (1),
.cycle 14 11 false (0),
.cycle 15 11 false (0),
.last 23 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid12_part457_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part457) = true := by rfl

def kid12_part458 : Audit := .cycle 18 1 false (-2)
theorem kid12_part458_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part458) = true := by rfl

def kid12_part459 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 33 1 false (-1),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.last 22 (4,false),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 30 1 false (0),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 23 1 false (1),
.cycle 26 1 false (-2),
.cycle 30 1 false (-2),
.cycle 28 1 false (0),
.cycle 22 1 false (0),
.last 22 (4,false),
.cycle 23 1 false (-1),
.cycle 18 4 true (1),
.cycle 14 8 true (1),
.cycle 0 24 true (0),
.cycle 30 1 false (0),
.last 22 (4,false),
.cycle 28 1 false (0)
])
theorem kid12_part459_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part459) = true := by rfl

def kid12_part460 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 15 false (3),
.cycle 0 38 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 21 1 true (1),
.cycle 13 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 28 (5,true),
.cycle 1 14 false (3),
.cycle 12 11 false (0),
.cycle 19 1 false (1),
.last 20 (5,true),
.cycle 11 4 false (1)
])
theorem kid12_part460_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part460) = true := by rfl

def kid12_part461 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 29 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 18 4 true (1),
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid12_part461_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part461) = true := by rfl

def kid12_part462 : Audit := .cycle 8 4 true (1)
theorem kid12_part462_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part462) = true := by rfl

def kid12_part463 : Audit := .cycle 6 8 true (1)
theorem kid12_part463_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part463) = true := by rfl

def kid12_part464 : Audit := .cycle 0 14 true (0)
theorem kid12_part464_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part464) = true := by rfl

def kid12_part465 : Audit := .cycle 21 1 false (1)
theorem kid12_part465_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part465) = true := by rfl

def kid12_part466 : Audit := .split 12 (4,false) (byMove [
.last 21 (5,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 51 1 false (7),
.cycle 12 2 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 15 1 true (3),
.last 13 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.last 31 (5,true),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid12_part466_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part466) = true := by rfl

def kid12_part467 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (7),
.cycle 30 1 false (6),
.last 14 (4,false),
.cycle 14 1 true (4),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 43 true (0),
.last 14 (4,false),
.cycle 14 1 true (4)
])
theorem kid12_part467_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part467) = true := by rfl

def kid12_part468 : Audit := .cycle 14 4 false (1)
theorem kid12_part468_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part468) = true := by rfl

def kid12_part469 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.cycle 0 20 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.cycle 14 8 false (1),
.cycle 12 2 true (-1),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.cycle 14 8 false (0),
.last 14 (5,true),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.last 19 (5,true),
.cycle 14 8 false (0),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid12_part469_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part469) = true := by rfl

def kid12_part470 : Audit := .cycle 13 6 true (-3)
theorem kid12_part470_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part470) = true := by rfl

def kid12_part471 : Audit := .cycle 0 16 true (0)
theorem kid12_part471_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part471) = true := by rfl

def kid12_part472 : Audit := .split 14 (4,false) (byMove [
.last 23 (5,true),
.cycle 14 10 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 26 true (-2),
.cycle 14 2 true (-2),
.cycle 12 6 false (0),
.cycle 12 6 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 30 true (-3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 26 true (-2),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 8 8 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid12_part472_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part472) = true := by rfl

def kid12_part473 : Audit := .split 12 (5,true) (byMove [
.cycle 0 38 true (-2),
.cycle 0 28 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 17 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 6 true (0),
.last 15 (4,false),
.cycle 16 3 true (2)
])
theorem kid12_part473_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part473) = true := by rfl

def kid12_part474 : Audit := .split 15 (5,true) (byMove [
.cycle 18 1 false (2),
.last 17 (4,false),
.cycle 26 1 false (-2),
.cycle 26 1 false (0),
.cycle 0 22 true (-1),
.cycle 0 22 true (-1),
.cycle 8 8 true (1),
.cycle 6 12 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.last 16 (4,false),
.cycle 12 24 true (1),
.cycle 18 8 false (1),
.last 17 (4,false),
.cycle 17 10 true (-3),
.cycle 0 20 true (0),
.last 22 (4,false),
.cycle 0 40 true (-2),
.cycle 12 4 true (1),
.cycle 12 8 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 16 (4,false),
.cycle 12 24 true (1)
])
theorem kid12_part474_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part474) = true := by rfl

def kid12_part475 : Audit := .split 19 (5,true) (byMove [
.cycle 22 1 false (2),
.last 21 (4,false),
.cycle 34 1 false (-2),
.cycle 30 1 false (0),
.cycle 1 21 false (3),
.cycle 1 21 false (3),
.cycle 8 12 true (1),
.cycle 6 16 true (1),
.cycle 0 22 true (0),
.cycle 37 1 false (1),
.last 20 (4,false),
.cycle 9 12 true (1),
.cycle 22 12 false (1),
.last 21 (4,false),
.cycle 21 14 true (-3),
.cycle 0 24 true (0),
.last 30 (4,false),
.cycle 20 12 false (0),
.cycle 16 4 true (1),
.cycle 12 8 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.cycle 17 4 true (1)
])
theorem kid12_part475_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part475) = true := by rfl

def kid12_part476 : Audit := .cycle 0 14 true (0)
theorem kid12_part476_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part476) = true := by rfl

def kid12_part477 : Audit := .cycle 4 8 true (1)
theorem kid12_part477_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part477) = true := by rfl

def kid12_part478 : Audit := .split 12 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 16 12 false (1),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 6 28 true (1),
.cycle 12 2 true (2),
.last 17 (5,true),
.cycle 0 14 true (0),
.cycle 15 1 true (3),
.last 13 (5,true),
.last 18 (5,true),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.last 31 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid12_part478_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part478) = true := by rfl

def kid12_part479 : Audit := .split 13 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 25 5 false (1),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 17 1 true (-1),
.cycle 17 1 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 34 true (0),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 14 1 true (4),
.cycle 22 12 false (1),
.cycle 22 5 false (0),
.cycle 23 9 false (2),
.cycle 5 34 true (1),
.last 22 (4,false),
.cycle 15 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.last 14 (4,false),
.cycle 14 1 true (4)
])
theorem kid12_part479_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part479) = true := by rfl

def kid12_part455 : Audit := .split 11 (5,false) (byMove [(kid12_part456),(kid12_part457),(kid12_part458),(kid12_part459),(kid12_part460),(kid12_part461),(kid12_part462),(kid12_part463),(kid12_part464),(kid12_part465),(kid12_part466),(kid12_part467),(kid12_part468),(kid12_part469),(kid12_part470),(kid12_part471),(kid12_part472),(kid12_part473),(kid12_part474),(kid12_part475),(kid12_part476),(kid12_part477),(kid12_part478),(kid12_part479)])

theorem kid12_part455_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part455) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part456),(kid12_part457),(kid12_part458),(kid12_part459),(kid12_part460),(kid12_part461),(kid12_part462),(kid12_part463),(kid12_part464),(kid12_part465),(kid12_part466),(kid12_part467),(kid12_part468),(kid12_part469),(kid12_part470),(kid12_part471),(kid12_part472),(kid12_part473),(kid12_part474),(kid12_part475),(kid12_part476),(kid12_part477),(kid12_part478),(kid12_part479)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part456_checked

  · exact kid12_part462_checked

  · exact kid12_part468_checked

  · exact kid12_part474_checked

  · exact kid12_part457_checked

  · exact kid12_part463_checked

  · exact kid12_part469_checked

  · exact kid12_part475_checked

  · exact kid12_part458_checked

  · exact kid12_part464_checked

  · exact kid12_part470_checked

  · exact kid12_part476_checked

  · exact kid12_part459_checked

  · exact kid12_part465_checked

  · exact kid12_part471_checked

  · exact kid12_part477_checked

  · exact kid12_part460_checked

  · exact kid12_part466_checked

  · exact kid12_part472_checked

  · exact kid12_part478_checked

  · exact kid12_part461_checked

  · exact kid12_part467_checked

  · exact kid12_part473_checked

  · exact kid12_part479_checked

def kid12_part480 : Audit := .cycle 41 1 false (7)
theorem kid12_part480_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part480) = true := by rfl

def kid12_part481 : Audit := .split 12 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.last 25 (5,true),
.cycle 0 18 true (0),
.last 14 (5,true),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 12 2 true (1),
.last 15 (5,true),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 15 8 true (-3),
.cycle 0 18 true (0),
.cycle 16 2 false (0),
.last 14 (5,true),
.last 19 (5,true),
.last 23 (5,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 15 (5,true)
]),
.cycle 51 1 false (7),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (7),
.cycle 30 1 false (6),
.last 15 (5,false),
.last 14 (5,false),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 12 2 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 43 true (0),
.last 15 (5,false),
.last 14 (5,false)
]),
.cycle 20 5 false (1),
.cycle 22 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.split 13 (5,false) (byMove [
.cycle 19 1 false (5),
.last 131 (5,true),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 23 2 false (1),
.last 14 (5,true),
.cycle 6 8 true (1),
.last 16 (5,true),
.last 20 (5,true),
.cycle 61 1 false (7),
.cycle 10 4 true (1),
.last 14 (5,true),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 16 2 false (0),
.last 14 (5,true),
.last 21 (5,true),
.last 18 (5,true),
.last 22 (5,true),
.cycle 5 34 true (1),
.last 17 (5,true),
.last 14 (5,true)
]),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.split 13 (5,true) (byMove [
.cycle 34 1 false (6),
.cycle 19 3 false (1),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 19 3 false (1),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.cycle 10 4 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.last 15 (5,false),
.last 14 (5,false)
])
])
theorem kid12_part481_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part481) = true := by rfl

def kid12_part482 : Audit := .cycle 7 4 true (2)
theorem kid12_part482_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part482) = true := by rfl

def kid12_part483 : Audit := .cycle 0 12 true (0)
theorem kid12_part483_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part483) = true := by rfl

def kid12_part484 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 17 1 false (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 29 1 false (3),
.cycle 25 1 false (1),
.cycle 17 2 false (1),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 12 2 true (3),
.cycle 13 1 true (3),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 18 2 false (2),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 41 1 false (9),
.last 15 (5,true),
.cycle 13 1 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 12 2 true (4),
.last 18 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (11),
.cycle 33 1 false (9),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.last 15 (5,true),
.last 18 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 45 1 false (13),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
]),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.split 13 (5,false) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.cycle 17 2 false (1),
.last 16 (5,true),
.cycle 37 1 false (9),
.last 22 (5,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 10 7 true (2),
.cycle 10 11 true (2),
.cycle 41 1 false (9),
.cycle 27 1 false (3),
.cycle 21 2 false (5),
.last 16 (5,true),
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 41 1 false (11),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 37 1 false (9),
.last 16 (5,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 16 (5,true),
.cycle 10 8 true (2),
.cycle 41 1 false (11),
.cycle 10 4 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
])
])
theorem kid12_part484_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part484) = true := by rfl

def kid12_part486 : Audit := .cycle 0 12 true (0)
theorem kid12_part486_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part486) = true := by rfl

def kid12_part487 : Audit := .cycle 1 11 true (1)
theorem kid12_part487_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part487) = true := by rfl

def kid12_part488 : Audit := .cycle 24 1 false (2)
theorem kid12_part488_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part488) = true := by rfl

def kid12_part489 : Audit := .cycle 21 1 false (1)
theorem kid12_part489_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part489) = true := by rfl

def kid12_part490 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.last 13 (5,false),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid12_part490_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part490) = true := by rfl

def kid12_part491 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 20 5 false (1),
.last 23 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid12_part491_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part491) = true := by rfl

def kid12_part492 : Audit := .cycle 0 12 true (0)
theorem kid12_part492_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part492) = true := by rfl

def kid12_part493 : Audit := .cycle 1 11 true (1)
theorem kid12_part493_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part493) = true := by rfl

def kid12_part494 : Audit := .cycle 41 1 false (7)
theorem kid12_part494_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part494) = true := by rfl

def kid12_part495 : Audit := .cycle 26 1 false (6)
theorem kid12_part495_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part495) = true := by rfl

def kid12_part496 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.last 24 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.last 28 (5,false),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 21 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 36 (5,false),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part496_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part496) = true := by rfl

def kid12_part497 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 13 (4,false),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 13 (4,false),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 41 1 false (11),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part497_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part497) = true := by rfl

def kid12_part498 : Audit := .cycle 8 4 true (2)
theorem kid12_part498_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part498) = true := by rfl

def kid12_part499 : Audit := .cycle 6 8 true (2)
theorem kid12_part499_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part499) = true := by rfl

def kid12_part500 : Audit := .cycle 0 14 true (0)
theorem kid12_part500_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part500) = true := by rfl

def kid12_part501 : Audit := .cycle 21 1 false (1)
theorem kid12_part501_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part501) = true := by rfl

def kid12_part502 : Audit := .split 12 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 51 1 false (7),
.cycle 12 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 11 2 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 10 4 true (2)
])
theorem kid12_part502_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part502) = true := by rfl

def kid12_part503 : Audit := .split 12 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 51 1 false (7),
.last 14 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 11 2 true (2),
.cycle 20 5 false (1),
.last 23 (4,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 17 3 false (1)
])
theorem kid12_part503_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part503) = true := by rfl

def kid12_part504 : Audit := .cycle 0 12 true (0)
theorem kid12_part504_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part504) = true := by rfl

def kid12_part505 : Audit := .cycle 1 11 true (1)
theorem kid12_part505_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part505) = true := by rfl

def kid12_part506 : Audit := .cycle 2 10 true (1)
theorem kid12_part506_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part506) = true := by rfl

def kid12_part507 : Audit := .cycle 0 37 true (0)
theorem kid12_part507_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part507) = true := by rfl

def kid12_part508 : Audit := .split 12 (4,false) (byMove [
.last 30 (5,false),
.cycle 0 18 true (0),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,false),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1056, 1024, 1073741824, 8192, 16384, 8, 4, 1024, 1073741824, 33554432, 67108864, 2097152, 4, 32, 1073741824, 33554432, 67108864, 134217728, 1024, 805307424, 1073741824, 33554432, 67108864, 134217728, 872416288, 805307424, 1073741824, 1073741824],[4, 32, 1024, 1, 32, 1024, 4, 1024, 1024, 1, 32, 65536, 1048576, 1024, 1024, 262144, 8388608, 268435456, 67108864, 1024, 805307424, 16777216, 536870912, 268435456, 67108864, 805307424, 805307424, 16777216, 536870912, 268435456, 1073741824],2145368942⟩,
.last 19 (5,false),
.last 52 (5,false),
.cycle 10 3 true (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part508_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part508) = true := by rfl

def kid12_part509 : Audit := .split 12 (5,false) (byMove [
.cycle 28 14 true (4),
.last 14 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 13 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (4,false),
.cycle 13 9 true (2),
.cycle 30 17 true (4),
.cycle 10 3 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 18 true (3),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part509_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part509) = true := by rfl

def kid12_part485 : Audit := .split 11 (5,true) (byMove [(kid12_part486),(kid12_part487),(kid12_part488),(kid12_part489),(kid12_part490),(kid12_part491),(kid12_part492),(kid12_part493),(kid12_part494),(kid12_part495),(kid12_part496),(kid12_part497),(kid12_part498),(kid12_part499),(kid12_part500),(kid12_part501),(kid12_part502),(kid12_part503),(kid12_part504),(kid12_part505),(kid12_part506),(kid12_part507),(kid12_part508),(kid12_part509)])

theorem kid12_part485_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part485) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid12_part486),(kid12_part487),(kid12_part488),(kid12_part489),(kid12_part490),(kid12_part491),(kid12_part492),(kid12_part493),(kid12_part494),(kid12_part495),(kid12_part496),(kid12_part497),(kid12_part498),(kid12_part499),(kid12_part500),(kid12_part501),(kid12_part502),(kid12_part503),(kid12_part504),(kid12_part505),(kid12_part506),(kid12_part507),(kid12_part508),(kid12_part509)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part486_checked

  · exact kid12_part492_checked

  · exact kid12_part498_checked

  · exact kid12_part504_checked

  · exact kid12_part487_checked

  · exact kid12_part493_checked

  · exact kid12_part499_checked

  · exact kid12_part505_checked

  · exact kid12_part488_checked

  · exact kid12_part494_checked

  · exact kid12_part500_checked

  · exact kid12_part506_checked

  · exact kid12_part489_checked

  · exact kid12_part495_checked

  · exact kid12_part501_checked

  · exact kid12_part507_checked

  · exact kid12_part490_checked

  · exact kid12_part496_checked

  · exact kid12_part502_checked

  · exact kid12_part508_checked

  · exact kid12_part491_checked

  · exact kid12_part497_checked

  · exact kid12_part503_checked

  · exact kid12_part509_checked

def kid12_part510 : Audit := .cycle 16 3 false (1)
theorem kid12_part510_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part510) = true := by rfl

def kid12_part511 : Audit := .split 19 (4,false) (byMove [
.cycle 11 10 false (2),
.cycle 6 24 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.split 20 (5,false) (byMove [
.cycle 44 7 false (-2),
.cycle 26 7 false (-1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 23 7 false (2),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.last 22 (5,true),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 23 7 false (0),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 15 6 false (2),
.cycle 11 10 false (2),
.cycle 6 24 false (3),
.cycle 23 7 false (0),
.last 22 (5,true),
.last 22 (5,true)
]),
.cycle 20 7 false (1),
.cycle 18 2 true (-1),
.cycle 20 7 false (0),
.cycle 21 7 false (2),
.cycle 20 7 false (0),
.split 20 (5,true) (byMove [
.cycle 11 11 false (2),
.cycle 6 25 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 22 (5,false),
.last 21 (5,false),
.cycle 21 7 false (2),
.cycle 35 7 false (6),
.cycle 21 7 false (1),
.cycle 22 7 false (3),
.cycle 21 7 false (1),
.last 24 (5,false),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 23 7 false (2),
.cycle 21 1 false (-1),
.cycle 19 2 true (-1),
.last 21 (5,false),
.cycle 13 8 true (-1),
.cycle 21 7 false (1),
.cycle 21 7 false (1),
.cycle 5 16 true (-1),
.cycle 17 4 true (-1),
.last 24 (5,false)
]),
.cycle 20 7 false (-1),
.cycle 20 7 false (-1),
.cycle 22 7 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.split 20 (5,false) (byMove [
.cycle 11 11 false (2),
.cycle 6 25 false (3),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 21 (5,true),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 23 7 false (0),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 13 8 false (2),
.cycle 21 7 false (-1),
.cycle 21 7 false (-1),
.cycle 5 16 false (3),
.cycle 17 4 false (1),
.last 21 (5,true)
]),
.cycle 13 7 false (2),
.cycle 20 7 false (0),
.cycle 20 7 false (0),
.cycle 5 15 false (3),
.cycle 17 3 false (1),
.split 20 (5,true) (byMove [
.cycle 24 7 false (3),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 22 (5,false),
.cycle 6 15 false (3),
.cycle 56 7 false (0),
.cycle 14 7 false (2),
.cycle 6 23 false (3),
.cycle 10 11 false (2),
.last 24 (5,false),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.cycle 21 7 false (-1),
.last 22 (5,false),
.cycle 26 7 false (0),
.cycle 16 5 false (2),
.cycle 12 9 false (2),
.cycle 34 7 false (0),
.cycle 22 7 false (0),
.last 24 (5,false)
])
])
theorem kid12_part511_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part511) = true := by rfl

def kid12_part512 : Audit := .cycle 51 1 false (7)
theorem kid12_part512_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part512) = true := by rfl

def kid12_part513 : Audit := .cycle 18 1 false (0)
theorem kid12_part513_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part513) = true := by rfl

def kid12_part514 : Audit := .split 11 (4,false) (byMove [
.cycle 17 1 false (5),
.cycle 17 50 true (-4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 42 (5,false),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 17 1 false (5),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 29 (5,false),
.last 21 (5,false),
.cycle 11 2 true (0),
.last 13 (5,false)
]),
.cycle 6 6 true (1),
.cycle 11 2 true (1),
.cycle 16 5 false (0),
.cycle 51 1 false (7),
.cycle 10 2 true (1),
.split 12 (5,true) (byMove [
.cycle 21 11 false (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 14 (5,false),
.last 13 (5,false),
.cycle 51 1 false (7),
.cycle 1 15 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 17 (5,false),
.last 14 (5,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 13 (5,false),
.cycle 23 8 true (2),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 10 4 true (1),
.last 14 (5,false)
]),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 12 8 true (-3),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 23 (5,false),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 20 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.cycle 5 8 true (0),
.last 16 (5,false),
.last 16 (5,false)
]),
.cycle 17 7 false (1),
.cycle 14 3 false (0),
.cycle 18 7 false (0),
.cycle 5 28 true (1),
.cycle 13 3 false (1),
.split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 6 28 true (1),
.cycle 1 15 true (1),
.cycle 17 7 false (1),
.cycle 0 14 true (0),
.last 17 (5,false),
.last 14 (5,false),
.cycle 18 7 false (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 32 9 false (2),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.last 14 (5,false)
])
])
theorem kid12_part514_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part514) = true := by rfl

def kid12_part516 : Audit := .cycle 17 1 false (5)
theorem kid12_part516_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part516) = true := by rfl

def kid12_part517 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.cycle 17 50 true (-4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 157 (5,true),
.cycle 19 1 false (5),
.cycle 12 2 true (-1),
.last 115 (5,true),
.last 107 (5,true),
.cycle 19 50 true (-4),
.last 14 (5,true),
.last 141 (5,true),
.last 149 (5,true),
.cycle 21 1 false (5),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 111 (5,true),
.last 87 (5,true),
.last 113 (5,true),
.last 117 (5,true),
.cycle 8 7 false (3),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid12_part517_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part517) = true := by rfl

def kid12_part518 : Audit := .cycle 18 1 false (-2)
theorem kid12_part518_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part518) = true := by rfl

def kid12_part519 : Audit := .cycle 17 1 false (-1)
theorem kid12_part519_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part519) = true := by rfl

def kid12_part520 : Audit := .split 14 (4,false) (byMove [
.cycle 19 24 false (2),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 35 1 false (5),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.last 22 (5,true),
.last 48 (5,true),
.cycle 12 9 false (0),
.last 17 (5,true),
.cycle 11 4 false (1)
])
theorem kid12_part520_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part520) = true := by rfl

def kid12_part521 : Audit := .split 12 (5,true) (byMove [
.cycle 46 1 false (0),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 17 1 false (5),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 13 6 true (0),
.cycle 23 1 false (-1),
.cycle 28 1 false (0),
.cycle 20 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid12_part521_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part521) = true := by rfl

def kid12_part522 : Audit := .cycle 6 6 true (1)
theorem kid12_part522_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part522) = true := by rfl

def kid12_part523 : Audit := .split 13 (4,false) (byMove [
.cycle 19 1 false (5),
.cycle 19 60 true (-4),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (1),
.cycle 12 2 true (1),
.last 18 (5,true),
.cycle 61 1 false (7),
.cycle 10 4 true (1),
.last 14 (5,true),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 19 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.cycle 5 34 true (1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid12_part523_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part523) = true := by rfl

def kid12_part524 : Audit := .split 16 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 21 5 false (3),
.cycle 18 5 false (2),
.last 18 (4,false),
.cycle 17 5 false (1),
.cycle 19 5 false (3),
.cycle 17 5 false (1),
.cycle 22 1 false (6),
.cycle 17 5 false (0),
.cycle 20 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 5 false (0),
.cycle 12 6 true (0),
.cycle 17 5 false (1),
.cycle 19 5 false (1),
.cycle 5 12 true (0),
.cycle 15 2 true (0),
.cycle 16 21 true (0)
])
theorem kid12_part524_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part524) = true := by rfl

def kid12_part525 : Audit := .cycle 51 1 false (7)
theorem kid12_part525_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part525) = true := by rfl

def kid12_part526 : Audit := .cycle 10 2 true (1)
theorem kid12_part526_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part526) = true := by rfl

def kid12_part527 : Audit := .split 12 (5,true) (byMove [
.cycle 27 1 false (5),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 16 1 true (2),
.cycle 51 1 false (7),
.last 14 (4,false),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 14 1 true (4),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (1),
.cycle 25 6 true (3),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 12 2 true (2),
.cycle 14 1 true (4)
])
theorem kid12_part527_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part527) = true := by rfl

def kid12_part528 : Audit := .cycle 14 4 false (1)
theorem kid12_part528_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part528) = true := by rfl

def kid12_part529 : Audit := .split 13 (4,false) (byMove [
.last 22 (5,true),
.last 30 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.cycle 14 8 false (1),
.cycle 12 2 true (-1),
.cycle 14 8 false (0),
.cycle 15 8 false (2),
.cycle 14 8 false (0),
.last 14 (5,true),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (-2),
.last 19 (5,true),
.cycle 14 8 false (0),
.cycle 14 8 false (0),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid12_part529_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part529) = true := by rfl

def kid12_part530 : Audit := .cycle 12 8 true (-3)
theorem kid12_part530_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part530) = true := by rfl

def kid12_part531 : Audit := .cycle 19 1 false (-1)
theorem kid12_part531_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part531) = true := by rfl

def kid12_part532 : Audit := .split 14 (4,false) (byMove [
.last 23 (5,true),
.cycle 20 10 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 7 false (0),
.cycle 14 2 true (-2),
.cycle 12 6 false (0),
.cycle 12 8 true (-2),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 9 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 20 (5,true),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 5 10 false (3),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid12_part532_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part532) = true := by rfl

def kid12_part533 : Audit := .split 12 (5,true) (byMove [
.cycle 12 9 false (1),
.cycle 11 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 12 6 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 5 8 true (0),
.cycle 12 2 true (0),
.cycle 14 3 true (2)
])
theorem kid12_part533_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part533) = true := by rfl

def kid12_part534 : Audit := .split 17 (5,true) (byMove [
.cycle 23 1 false (5),
.last 19 (4,false),
.cycle 30 1 false (-2),
.cycle 29 1 false (-1),
.last 44 (4,false),
.cycle 12 11 false (3),
.cycle 6 12 true (1),
.last 19 (4,false),
.cycle 18 11 false (2),
.cycle 81 1 false (7),
.cycle 10 8 true (1),
.cycle 0 21 true (0),
.cycle 20 10 false (1),
.last 19 (4,false),
.cycle 18 14 true (-3),
.cycle 31 1 false (-1),
.last 26 (4,false),
.cycle 18 7 false (1),
.cycle 12 6 true (1),
.cycle 18 9 false (2),
.cycle 19 13 false (2),
.cycle 5 46 true (1),
.cycle 16 2 true (1),
.cycle 0 21 true (0)
])
theorem kid12_part534_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part534) = true := by rfl

def kid12_part535 : Audit := .split 14 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 9 15 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 12 9 false (2),
.cycle 18 3 false (2),
.last 16 (4,false),
.cycle 17 3 false (1),
.cycle 19 3 false (3),
.cycle 15 3 false (1),
.cycle 1 18 true (0),
.cycle 16 3 false (0),
.cycle 20 3 false (0),
.cycle 20 3 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 3 false (0),
.cycle 12 6 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (1),
.cycle 5 10 true (0),
.cycle 13 2 true (0),
.cycle 1 18 true (0)
])
theorem kid12_part535_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part535) = true := by rfl

def kid12_part536 : Audit := .split 18 (5,true) (byMove [
.cycle 12 9 false (2),
.cycle 6 23 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 6 23 false (3),
.cycle 19 7 false (2),
.last 20 (4,false),
.cycle 19 7 false (1),
.cycle 20 7 false (3),
.cycle 19 7 false (1),
.cycle 27 7 false (6),
.cycle 19 7 false (0),
.cycle 20 7 false (0),
.cycle 21 7 false (2),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 19 7 false (0),
.cycle 13 6 true (0),
.cycle 19 7 false (1),
.cycle 19 7 false (1),
.cycle 5 14 true (0),
.cycle 17 2 true (0),
.cycle 2 21 true (0)
])
theorem kid12_part536_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part536) = true := by rfl

def kid12_part537 : Audit := .cycle 5 28 true (1)
theorem kid12_part537_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part537) = true := by rfl

def kid12_part538 : Audit := .split 13 (5,true) (byMove [
.cycle 19 1 false (5),
.last 15 (4,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 18 (4,false),
.last 16 (4,false),
.cycle 6 8 true (1),
.last 15 (4,false),
.cycle 17 7 false (1),
.cycle 61 1 false (7),
.cycle 10 4 true (1),
.last 17 (4,false),
.cycle 16 6 false (1),
.last 15 (4,false),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 14 3 false (0),
.cycle 12 6 true (1),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 5 34 true (1),
.cycle 12 2 true (1),
.last 17 (4,false)
])
theorem kid12_part538_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part538) = true := by rfl

def kid12_part539 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 18 (4,false),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.last 15 (4,false),
.cycle 24 1 true (-2),
.cycle 6 28 true (1),
.last 14 (4,false),
.cycle 17 11 false (2),
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 14 1 true (4),
.cycle 19 7 false (0),
.last 18 (4,false),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 13 3 false (1),
.cycle 25 6 true (3),
.cycle 15 7 false (2),
.cycle 19 15 false (2),
.cycle 0 14 true (0),
.cycle 12 2 true (2),
.cycle 14 1 true (4)
])
theorem kid12_part539_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part539) = true := by rfl

def kid12_part515 : Audit := .split 11 (5,false) (byMove [(kid12_part516),(kid12_part517),(kid12_part518),(kid12_part519),(kid12_part520),(kid12_part521),(kid12_part522),(kid12_part523),(kid12_part524),(kid12_part525),(kid12_part526),(kid12_part527),(kid12_part528),(kid12_part529),(kid12_part530),(kid12_part531),(kid12_part532),(kid12_part533),(kid12_part534),(kid12_part535),(kid12_part536),(kid12_part537),(kid12_part538),(kid12_part539)])

theorem kid12_part515_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part515) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid12_part516),(kid12_part517),(kid12_part518),(kid12_part519),(kid12_part520),(kid12_part521),(kid12_part522),(kid12_part523),(kid12_part524),(kid12_part525),(kid12_part526),(kid12_part527),(kid12_part528),(kid12_part529),(kid12_part530),(kid12_part531),(kid12_part532),(kid12_part533),(kid12_part534),(kid12_part535),(kid12_part536),(kid12_part537),(kid12_part538),(kid12_part539)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part516_checked

  · exact kid12_part522_checked

  · exact kid12_part528_checked

  · exact kid12_part534_checked

  · exact kid12_part517_checked

  · exact kid12_part523_checked

  · exact kid12_part529_checked

  · exact kid12_part535_checked

  · exact kid12_part518_checked

  · exact kid12_part524_checked

  · exact kid12_part530_checked

  · exact kid12_part536_checked

  · exact kid12_part519_checked

  · exact kid12_part525_checked

  · exact kid12_part531_checked

  · exact kid12_part537_checked

  · exact kid12_part520_checked

  · exact kid12_part526_checked

  · exact kid12_part532_checked

  · exact kid12_part538_checked

  · exact kid12_part521_checked

  · exact kid12_part527_checked

  · exact kid12_part533_checked

  · exact kid12_part539_checked

def kid12_part540 : Audit := .cycle 6 16 true (2)
theorem kid12_part540_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part540) = true := by rfl

def kid12_part541 : Audit := .cycle 9 2 true (2)
theorem kid12_part541_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part541) = true := by rfl

def kid12_part542 : Audit := .cycle 6 6 true (2)
theorem kid12_part542_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part542) = true := by rfl

def kid12_part543 : Audit := .cycle 0 12 true (0)
theorem kid12_part543_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part543) = true := by rfl

def kid12_part544 : Audit := .split 12 (4,false) (byMove [
.cycle 10 14 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.split 13 (5,true) (byMove [
.cycle 26 15 true (2),
.last 38 (5,false),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 20 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.last 29 (5,false),
.cycle 14 10 true (1),
.cycle 28 18 true (2),
.cycle 10 4 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 12 2 true (3),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 12 2 true (4),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 16 true (2),
.cycle 10 13 true (2),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 21 true (2),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
]),
.cycle 6 7 true (2),
.cycle 10 5 true (2),
.cycle 10 9 true (2),
.cycle 10 17 true (2),
.cycle 10 3 true (2),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 23 true (-1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 20 (5,false),
.last 15 (5,false),
.cycle 10 17 true (2),
.last 19 (5,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 15 (5,false),
.cycle 10 9 true (2),
.cycle 25 7 true (1),
.cycle 14 11 true (1),
.cycle 5 9 true (1),
.cycle 10 5 true (2),
.last 15 (5,false),
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 10 6 true (2),
.cycle 10 10 true (2),
.cycle 10 18 true (2),
.cycle 10 4 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
])
])
theorem kid12_part544_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part544) = true := by rfl

def kid12_part546 : Audit := .cycle 30 1 false (6)
theorem kid12_part546_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part546) = true := by rfl

def kid12_part547 : Audit := .split 13 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 28 true (-2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 15 (5,false),
.last 28 (5,false),
.cycle 34 1 false (6),
.cycle 12 2 true (1),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.last 34 (5,false),
.cycle 0 31 true (0),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 17 3 false (1)
])
theorem kid12_part547_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part547) = true := by rfl

def kid12_part548 : Audit := .cycle 19 5 false (1)
theorem kid12_part548_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part548) = true := by rfl

def kid12_part549 : Audit := .cycle 0 13 true (0)
theorem kid12_part549_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part549) = true := by rfl

def kid12_part550 : Audit := .split 13 (5,false) (byMove [
.cycle 34 1 false (6),
.last 15 (4,false),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.last 15 (4,false),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.cycle 10 4 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.last 14 (4,false),
.cycle 13 1 true (3)
])
theorem kid12_part550_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part550) = true := by rfl

def kid12_part551 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.last 15 (4,false),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 13 1 true (1),
.cycle 16 6 false (1),
.last 15 (4,false),
.cycle 0 37 false (3),
.cycle 17 1 false (3),
.last 18 (4,false),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.last 14 (4,false),
.cycle 13 1 true (1)
])
theorem kid12_part551_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part551) = true := by rfl

def kid12_part552 : Audit := .cycle 0 12 true (0)
theorem kid12_part552_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part552) = true := by rfl

def kid12_part553 : Audit := .cycle 1 11 true (1)
theorem kid12_part553_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part553) = true := by rfl

def kid12_part554 : Audit := .cycle 7 16 true (2)
theorem kid12_part554_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part554) = true := by rfl

def kid12_part555 : Audit := .cycle 3 9 true (1)
theorem kid12_part555_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part555) = true := by rfl

def kid12_part556 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (5,false),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 15 true (2),
.last 24 (5,false),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (5,false),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part556_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part556) = true := by rfl

def kid12_part557 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 73 1 false (7),
.last 13 (4,false),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 16, 1, 8, 8, 8, 64],80⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 16, 1, 8, 8, 8, 64],80⟩,
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 28 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 16, 1, 8, 8, 8, 64],80⟩,
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part557_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part557) = true := by rfl

def kid12_part558 : Audit := .cycle 6 6 true (2)
theorem kid12_part558_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part558) = true := by rfl

def kid12_part559 : Audit := .split 13 (4,false) (byMove [
.cycle 19 1 false (5),
.cycle 19 60 true (-4),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 15 (5,false),
.last 25 (5,false),
.cycle 6 8 true (1),
.cycle 12 2 true (1),
.cycle 19 7 false (1),
.cycle 61 1 false (7),
.cycle 10 4 true (1),
.cycle 23 11 false (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.last 25 (5,false),
.cycle 20 11 false (2),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 5 34 true (1),
.cycle 17 7 false (2),
.cycle 17 3 false (1)
])
theorem kid12_part559_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part559) = true := by rfl

def kid12_part560 : Audit := .cycle 19 5 false (1)
theorem kid12_part560_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part560) = true := by rfl

def kid12_part561 : Audit := .cycle 51 1 false (7)
theorem kid12_part561_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part561) = true := by rfl

def kid12_part562 : Audit := .cycle 10 2 true (2)
theorem kid12_part562_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part562) = true := by rfl

def kid12_part563 : Audit := .split 13 (5,false) (byMove [
.cycle 19 1 false (5),
.last 15 (4,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.last 15 (4,false),
.cycle 19 7 false (1),
.cycle 61 1 false (7),
.cycle 10 4 true (1),
.cycle 12 2 true (1),
.cycle 16 6 false (1),
.last 15 (4,false),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 15 1 false (-1),
.cycle 20 9 false (2),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 5 34 true (1),
.cycle 16 5 false (2),
.cycle 15 3 false (1)
])
theorem kid12_part563_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part563) = true := by rfl

def kid12_part564 : Audit := .cycle 0 12 true (0)
theorem kid12_part564_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part564) = true := by rfl

def kid12_part565 : Audit := .cycle 1 11 true (1)
theorem kid12_part565_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part565) = true := by rfl

def kid12_part566 : Audit := .cycle 2 10 true (1)
theorem kid12_part566_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part566) = true := by rfl

def kid12_part567 : Audit := .cycle 13 14 true (2)
theorem kid12_part567_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part567) = true := by rfl

def kid12_part568 : Audit := .split 12 (4,false) (byMove [
.last 26 (5,false),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,false),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 17 (5,false),
.last 21 (5,false),
.cycle 10 17 true (2),
.cycle 10 3 true (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part568_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part568) = true := by rfl

def kid12_part569 : Audit := .split 12 (5,false) (byMove [
.cycle 11 14 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 12 2 true (3),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 13 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 11 5 true (2),
.cycle 11 9 true (2),
.cycle 11 17 true (2),
.cycle 10 3 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 18 true (3),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part569_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part569) = true := by rfl

def kid12_part545 : Audit := .split 11 (5,true) (byMove [(kid12_part546),(kid12_part547),(kid12_part548),(kid12_part549),(kid12_part550),(kid12_part551),(kid12_part552),(kid12_part553),(kid12_part554),(kid12_part555),(kid12_part556),(kid12_part557),(kid12_part558),(kid12_part559),(kid12_part560),(kid12_part561),(kid12_part562),(kid12_part563),(kid12_part564),(kid12_part565),(kid12_part566),(kid12_part567),(kid12_part568),(kid12_part569)])

theorem kid12_part545_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part545) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid12_part546),(kid12_part547),(kid12_part548),(kid12_part549),(kid12_part550),(kid12_part551),(kid12_part552),(kid12_part553),(kid12_part554),(kid12_part555),(kid12_part556),(kid12_part557),(kid12_part558),(kid12_part559),(kid12_part560),(kid12_part561),(kid12_part562),(kid12_part563),(kid12_part564),(kid12_part565),(kid12_part566),(kid12_part567),(kid12_part568),(kid12_part569)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part546_checked

  · exact kid12_part552_checked

  · exact kid12_part558_checked

  · exact kid12_part564_checked

  · exact kid12_part547_checked

  · exact kid12_part553_checked

  · exact kid12_part559_checked

  · exact kid12_part565_checked

  · exact kid12_part548_checked

  · exact kid12_part554_checked

  · exact kid12_part560_checked

  · exact kid12_part566_checked

  · exact kid12_part549_checked

  · exact kid12_part555_checked

  · exact kid12_part561_checked

  · exact kid12_part567_checked

  · exact kid12_part550_checked

  · exact kid12_part556_checked

  · exact kid12_part562_checked

  · exact kid12_part568_checked

  · exact kid12_part551_checked

  · exact kid12_part557_checked

  · exact kid12_part563_checked

  · exact kid12_part569_checked

def kid12_part449 : Audit := .split 10 (4,true) (byMove [(kid12_part450),(kid12_part451),(kid12_part452),(kid12_part453),(kid12_part454),(kid12_part455),(kid12_part480),(kid12_part481),(kid12_part482),(kid12_part483),(kid12_part484),(kid12_part485),(kid12_part510),(kid12_part511),(kid12_part512),(kid12_part513),(kid12_part514),(kid12_part515),(kid12_part540),(kid12_part541),(kid12_part542),(kid12_part543),(kid12_part544),(kid12_part545)])

theorem kid12_part449_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (kid12_part449) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid12_part450),(kid12_part451),(kid12_part452),(kid12_part453),(kid12_part454),(kid12_part455),(kid12_part480),(kid12_part481),(kid12_part482),(kid12_part483),(kid12_part484),(kid12_part485),(kid12_part510),(kid12_part511),(kid12_part512),(kid12_part513),(kid12_part514),(kid12_part515),(kid12_part540),(kid12_part541),(kid12_part542),(kid12_part543),(kid12_part544),(kid12_part545)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part450_checked

  · exact kid12_part480_checked

  · exact kid12_part510_checked

  · exact kid12_part540_checked

  · exact kid12_part451_checked

  · exact kid12_part481_checked

  · exact kid12_part511_checked

  · exact kid12_part541_checked

  · exact kid12_part452_checked

  · exact kid12_part482_checked

  · exact kid12_part512_checked

  · exact kid12_part542_checked

  · exact kid12_part453_checked

  · exact kid12_part483_checked

  · exact kid12_part513_checked

  · exact kid12_part543_checked

  · exact kid12_part454_checked

  · exact kid12_part484_checked

  · exact kid12_part514_checked

  · exact kid12_part544_checked

  · exact kid12_part455_checked

  · exact kid12_part485_checked

  · exact kid12_part515_checked

  · exact kid12_part545_checked

def kid12_part571 : Audit := .cycle 0 22 true (0)
theorem kid12_part571_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part571) = true := by rfl

def kid12_part572 : Audit := .cycle 0 14 true (0)
theorem kid12_part572_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part572) = true := by rfl

def kid12_part573 : Audit := .cycle 21 1 false (1)
theorem kid12_part573_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part573) = true := by rfl

def kid12_part574 : Audit := .cycle 0 16 true (0)
theorem kid12_part574_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part574) = true := by rfl

def kid12_part576 : Audit := .cycle 14 1 false (2)
theorem kid12_part576_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part576) = true := by rfl

def kid12_part577 : Audit := .split 13 (5,false) (byMove [
.last 22 (4,true),
.last 25 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 11 false (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (2),
.cycle 12 2 true (-1),
.cycle 14 11 false (0),
.last 23 (4,true),
.last 14 (4,true),
.cycle 14 11 false (0),
.cycle 14 11 false (-1),
.cycle 16 11 false (-1),
.cycle 18 1 false (2),
.cycle 14 1 false (-2),
.cycle 23 11 false (-1),
.cycle 13 1 false (-1),
.cycle 17 11 false (1),
.cycle 14 11 false (0),
.cycle 15 11 false (0),
.last 23 (4,true),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid12_part577_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part577) = true := by rfl

def kid12_part578 : Audit := .cycle 18 1 false (-2)
theorem kid12_part578_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part578) = true := by rfl

def kid12_part579 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 33 1 false (-1),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.last 22 (5,false),
.cycle 26 1 false (0),
.cycle 30 1 false (0),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 23 1 false (1),
.last 22 (5,false),
.cycle 26 1 false (-2),
.cycle 30 1 false (-2),
.cycle 28 1 false (0),
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.last 22 (5,false),
.cycle 18 4 true (1),
.cycle 14 8 true (1),
.cycle 0 24 true (0),
.cycle 30 1 false (0),
.cycle 28 1 false (0),
.last 22 (5,false)
])
theorem kid12_part579_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part579) = true := by rfl

def kid12_part580 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 29 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 18 4 true (1),
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid12_part580_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part580) = true := by rfl

def kid12_part581 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 15 false (3),
.cycle 0 38 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 21 1 true (1),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 28 (4,true),
.cycle 1 14 false (3),
.cycle 12 11 false (0),
.cycle 19 1 false (1),
.cycle 11 4 false (1),
.last 20 (4,true)
])
theorem kid12_part581_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part581) = true := by rfl

def kid12_part582 : Audit := .cycle 8 4 true (1)
theorem kid12_part582_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part582) = true := by rfl

def kid12_part583 : Audit := .cycle 6 8 true (1)
theorem kid12_part583_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part583) = true := by rfl

def kid12_part584 : Audit := .cycle 0 14 true (0)
theorem kid12_part584_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part584) = true := by rfl

def kid12_part585 : Audit := .cycle 21 1 false (1)
theorem kid12_part585_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part585) = true := by rfl

def kid12_part586 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 14 1 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (7),
.cycle 30 1 false (6),
.cycle 14 1 true (4),
.last 14 (5,false),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 12 2 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 43 true (0),
.cycle 14 1 true (4),
.last 14 (5,false)
])
theorem kid12_part586_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part586) = true := by rfl

def kid12_part587 : Audit := .split 12 (5,false) (byMove [
.last 21 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 11 2 true (1),
.cycle 16 1 false (0),
.cycle 51 1 false (7),
.cycle 12 2 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 true (3),
.last 16 (4,true),
.last 20 (4,true),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 10 4 true (1),
.cycle 16 1 false (0),
.last 31 (4,true),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid12_part587_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part587) = true := by rfl

def kid12_part588 : Audit := .cycle 14 4 false (1)
theorem kid12_part588_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part588) = true := by rfl

def kid12_part589 : Audit := .split 13 (5,false) (byMove [
.last 22 (4,true),
.cycle 0 20 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (1),
.cycle 12 2 true (-1),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.last 14 (4,true),
.cycle 14 8 false (0),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.last 19 (4,true),
.cycle 14 8 false (0),
.cycle 14 8 false (0),
.cycle 0 18 true (-1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid12_part589_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part589) = true := by rfl

def kid12_part590 : Audit := .cycle 13 6 true (-3)
theorem kid12_part590_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part590) = true := by rfl

def kid12_part591 : Audit := .cycle 0 16 true (0)
theorem kid12_part591_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part591) = true := by rfl

def kid12_part592 : Audit := .split 12 (4,true) (byMove [
.cycle 0 38 true (-2),
.cycle 0 28 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 17 1 false (1),
.cycle 14 1 false (2),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 8 6 true (0),
.cycle 16 3 true (2),
.last 15 (5,false)
])
theorem kid12_part592_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part592) = true := by rfl

def kid12_part593 : Audit := .split 14 (5,false) (byMove [
.last 23 (4,true),
.cycle 14 10 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 26 true (-2),
.cycle 14 2 true (-2),
.cycle 12 6 false (0),
.cycle 12 6 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 0 30 true (-3),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 26 true (-2),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 8 8 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid12_part593_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part593) = true := by rfl

def kid12_part594 : Audit := .split 15 (4,true) (byMove [
.cycle 18 1 false (2),
.last 17 (5,false),
.cycle 26 1 false (-2),
.cycle 26 1 false (0),
.cycle 0 22 true (-1),
.cycle 0 22 true (-1),
.cycle 8 8 true (1),
.cycle 6 12 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 12 24 true (1),
.last 16 (5,false),
.cycle 18 8 false (1),
.last 17 (5,false),
.cycle 17 10 true (-3),
.cycle 0 20 true (0),
.cycle 0 40 true (-2),
.last 22 (5,false),
.cycle 12 4 true (1),
.cycle 12 8 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 12 24 true (1),
.last 16 (5,false)
])
theorem kid12_part594_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part594) = true := by rfl

def kid12_part595 : Audit := .split 19 (4,true) (byMove [
.cycle 22 1 false (2),
.last 21 (5,false),
.cycle 34 1 false (-2),
.cycle 30 1 false (0),
.cycle 1 21 false (3),
.cycle 1 21 false (3),
.cycle 8 12 true (1),
.cycle 6 16 true (1),
.cycle 0 22 true (0),
.cycle 37 1 false (1),
.cycle 9 12 true (1),
.last 20 (5,false),
.cycle 22 12 false (1),
.last 21 (5,false),
.cycle 21 14 true (-3),
.cycle 0 24 true (0),
.cycle 20 12 false (0),
.last 30 (5,false),
.cycle 16 4 true (1),
.cycle 12 8 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 17 4 true (1),
.last 20 (5,false)
])
theorem kid12_part595_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part595) = true := by rfl

def kid12_part596 : Audit := .cycle 0 14 true (0)
theorem kid12_part596_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part596) = true := by rfl

def kid12_part597 : Audit := .cycle 4 8 true (1)
theorem kid12_part597_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part597) = true := by rfl

def kid12_part598 : Audit := .split 13 (4,true) (byMove [
.cycle 0 31 true (0),
.cycle 25 5 false (1),
.cycle 22 1 false (0),
.cycle 0 15 true (0),
.cycle 17 1 true (-1),
.cycle 17 1 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 34 true (0),
.cycle 3 11 true (1),
.cycle 14 1 true (4),
.last 14 (5,false),
.cycle 22 12 false (1),
.cycle 22 5 false (0),
.cycle 23 9 false (2),
.cycle 5 34 true (1),
.cycle 15 3 false (1),
.last 22 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 14 1 true (4),
.last 14 (5,false)
])
theorem kid12_part598_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part598) = true := by rfl

def kid12_part599 : Audit := .split 12 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 16 12 false (1),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 6 28 true (1),
.cycle 12 2 true (2),
.last 17 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 true (3),
.last 18 (4,true),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 14 (4,true),
.last 31 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid12_part599_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part599) = true := by rfl

def kid12_part575 : Audit := .split 11 (4,false) (byMove [(kid12_part576),(kid12_part577),(kid12_part578),(kid12_part579),(kid12_part580),(kid12_part581),(kid12_part582),(kid12_part583),(kid12_part584),(kid12_part585),(kid12_part586),(kid12_part587),(kid12_part588),(kid12_part589),(kid12_part590),(kid12_part591),(kid12_part592),(kid12_part593),(kid12_part594),(kid12_part595),(kid12_part596),(kid12_part597),(kid12_part598),(kid12_part599)])

theorem kid12_part575_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part575) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part576),(kid12_part577),(kid12_part578),(kid12_part579),(kid12_part580),(kid12_part581),(kid12_part582),(kid12_part583),(kid12_part584),(kid12_part585),(kid12_part586),(kid12_part587),(kid12_part588),(kid12_part589),(kid12_part590),(kid12_part591),(kid12_part592),(kid12_part593),(kid12_part594),(kid12_part595),(kid12_part596),(kid12_part597),(kid12_part598),(kid12_part599)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part576_checked

  · exact kid12_part582_checked

  · exact kid12_part588_checked

  · exact kid12_part594_checked

  · exact kid12_part577_checked

  · exact kid12_part583_checked

  · exact kid12_part589_checked

  · exact kid12_part595_checked

  · exact kid12_part578_checked

  · exact kid12_part584_checked

  · exact kid12_part590_checked

  · exact kid12_part596_checked

  · exact kid12_part579_checked

  · exact kid12_part585_checked

  · exact kid12_part591_checked

  · exact kid12_part597_checked

  · exact kid12_part580_checked

  · exact kid12_part586_checked

  · exact kid12_part592_checked

  · exact kid12_part598_checked

  · exact kid12_part581_checked

  · exact kid12_part587_checked

  · exact kid12_part593_checked

  · exact kid12_part599_checked

def kid12_part600 : Audit := .split 11 (5,false) (byMove [
.cycle 14 1 false (2),
.cycle 1 26 false (3),
.cycle 18 1 false (-2),
.cycle 23 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 23 (4,false),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.last 25 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 24 (4,false),
.cycle 0 16 true (0),
.last 23 (4,false),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
.cycle 8 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 25 false (3),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 14 (4,true),
.cycle 11 2 true (1),
.cycle 51 1 false (7),
.last 15 (4,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 2 true (2),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 28 6 true (2),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 2 true (1)
]),
.cycle 14 1 true (2),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 13 6 true (-3),
.cycle 0 16 true (0),
.split 12 (4,true) (byMove [
.last 23 (4,false),
.last 20 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 16 true (0),
.last 15 (4,false),
.last 18 (4,false),
.last 18 (4,false),
.last 14 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 20 (4,false),
.cycle 8 6 true (0),
.last 14 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 0 22 true (-1),
.cycle 1 21 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 12 (4,false) (byMove [
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 6 28 true (1),
.last 15 (4,true),
.cycle 0 58 true (-2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 2 true (2),
.cycle 18 7 false (0),
.last 19 (4,true),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 0 78 true (-2),
.cycle 0 22 true (-1),
.cycle 2 21 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 2 true (-1)
]),
.cycle 17 1 true (-1)
])
theorem kid12_part600_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part600) = true := by rfl

def kid12_part601 : Audit := .cycle 41 1 false (7)
theorem kid12_part601_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part601) = true := by rfl

def kid12_part602 : Audit := .split 12 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 14 13 false (0),
.cycle 22 1 false (-2),
.last 25 (4,true),
.last 14 (4,true),
.cycle 0 18 true (0),
.cycle 8 6 true (1),
.cycle 6 10 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 15 (4,true),
.cycle 12 2 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 15 8 true (-3),
.cycle 0 18 true (0),
.last 14 (4,true),
.cycle 16 2 false (0),
.last 19 (4,true),
.last 23 (4,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.last 15 (4,true)
]),
.cycle 0 18 true (0),
.cycle 51 1 false (7),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (7),
.cycle 30 1 false (6),
.last 14 (4,false),
.last 15 (4,false),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 43 true (0),
.last 14 (4,false),
.last 15 (4,false)
]),
.cycle 1 13 true (1),
.cycle 20 5 false (1),
.cycle 22 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.split 13 (4,false) (byMove [
.cycle 19 1 false (5),
.last 131 (4,true),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 23 2 false (1),
.cycle 6 8 true (1),
.last 16 (4,true),
.last 20 (4,true),
.cycle 61 1 false (7),
.last 14 (4,true),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 2 false (0),
.last 21 (4,true),
.last 18 (4,true),
.last 22 (4,true),
.cycle 5 34 true (1),
.last 14 (4,true),
.last 17 (4,true)
]),
.cycle 16 1 false (0),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 34 1 false (6),
.cycle 19 3 false (1),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.cycle 19 3 false (1),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.last 15 (4,false),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.last 14 (4,false),
.last 15 (4,false)
]),
.cycle 1 13 true (1)
])
theorem kid12_part602_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part602) = true := by rfl

def kid12_part603 : Audit := .cycle 7 4 true (2)
theorem kid12_part603_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part603) = true := by rfl

def kid12_part604 : Audit := .cycle 0 12 true (0)
theorem kid12_part604_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part604) = true := by rfl

def kid12_part606 : Audit := .cycle 0 12 true (0)
theorem kid12_part606_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part606) = true := by rfl

def kid12_part607 : Audit := .cycle 1 11 true (1)
theorem kid12_part607_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part607) = true := by rfl

def kid12_part608 : Audit := .cycle 24 1 false (2)
theorem kid12_part608_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part608) = true := by rfl

def kid12_part609 : Audit := .cycle 21 1 false (1)
theorem kid12_part609_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part609) = true := by rfl

def kid12_part610 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.last 13 (5,false),
.cycle 20 5 false (1),
.last 23 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid12_part610_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part610) = true := by rfl

def kid12_part611 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 30 1 false (6),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 61 1 false (7),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid12_part611_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part611) = true := by rfl

def kid12_part612 : Audit := .cycle 0 12 true (0)
theorem kid12_part612_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part612) = true := by rfl

def kid12_part613 : Audit := .cycle 1 11 true (1)
theorem kid12_part613_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part613) = true := by rfl

def kid12_part614 : Audit := .cycle 41 1 false (7)
theorem kid12_part614_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part614) = true := by rfl

def kid12_part615 : Audit := .cycle 26 1 false (6)
theorem kid12_part615_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part615) = true := by rfl

def kid12_part616 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 17 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 41 1 false (11),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part616_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part616) = true := by rfl

def kid12_part617 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.last 24 (4,false),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.last 28 (4,false),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 13 (4,false),
.last 21 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 36 (4,false),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part617_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part617) = true := by rfl

def kid12_part618 : Audit := .cycle 8 4 true (2)
theorem kid12_part618_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part618) = true := by rfl

def kid12_part619 : Audit := .cycle 6 8 true (2)
theorem kid12_part619_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part619) = true := by rfl

def kid12_part620 : Audit := .cycle 0 14 true (0)
theorem kid12_part620_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part620) = true := by rfl

def kid12_part621 : Audit := .cycle 21 1 false (1)
theorem kid12_part621_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part621) = true := by rfl

def kid12_part622 : Audit := .split 12 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 51 1 false (7),
.last 14 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 15 (5,false),
.cycle 20 5 false (1),
.last 23 (5,false),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 17 3 false (1),
.last 15 (5,false)
])
theorem kid12_part622_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part622) = true := by rfl

def kid12_part623 : Audit := .split 12 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 15 (4,false),
.cycle 51 1 false (7),
.cycle 12 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (4,false),
.cycle 20 5 false (1),
.cycle 23 9 false (-1),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 1 false (0),
.cycle 6 20 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (2),
.last 14 (4,false)
])
theorem kid12_part623_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part623) = true := by rfl

def kid12_part624 : Audit := .cycle 0 12 true (0)
theorem kid12_part624_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part624) = true := by rfl

def kid12_part625 : Audit := .cycle 1 11 true (1)
theorem kid12_part625_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part625) = true := by rfl

def kid12_part626 : Audit := .cycle 2 10 true (1)
theorem kid12_part626_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part626) = true := by rfl

def kid12_part627 : Audit := .cycle 0 37 true (0)
theorem kid12_part627_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part627) = true := by rfl

def kid12_part628 : Audit := .split 12 (4,false) (byMove [
.cycle 28 14 true (4),
.last 14 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 13 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 14 (5,false),
.cycle 13 9 true (2),
.cycle 30 17 true (4),
.cycle 11 3 true (3),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 18 true (3),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part628_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part628) = true := by rfl

def kid12_part629 : Audit := .split 12 (5,false) (byMove [
.last 30 (4,false),
.cycle 0 18 true (0),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 2064, 1073741824, 2048, 8192, 16384, 8, 4, 1073741824, 2048, 33554432, 67108864, 2097152, 4, 1073741824, 16, 33554432, 67108864, 134217728, 2048, 1073741824, 805308432, 33554432, 67108864, 134217728, 872417296, 1073741824, 805308432, 1073741824],[4, 16, 2048, 1, 2048, 16, 4, 2048, 2048, 1, 131072, 16, 1048576, 2048, 2048, 262144, 536870912, 4194304, 67108864, 2048, 805308432, 16777216, 536870912, 268435456, 67108864, 805308432, 805308432, 16777216, 536870912, 268435456, 1073741824],2145367902⟩,
.last 19 (4,false),
.last 52 (4,false),
.last 15 (4,false),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part629_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part629) = true := by rfl

def kid12_part605 : Audit := .split 11 (4,true) (byMove [(kid12_part606),(kid12_part607),(kid12_part608),(kid12_part609),(kid12_part610),(kid12_part611),(kid12_part612),(kid12_part613),(kid12_part614),(kid12_part615),(kid12_part616),(kid12_part617),(kid12_part618),(kid12_part619),(kid12_part620),(kid12_part621),(kid12_part622),(kid12_part623),(kid12_part624),(kid12_part625),(kid12_part626),(kid12_part627),(kid12_part628),(kid12_part629)])

theorem kid12_part605_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part605) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid12_part606),(kid12_part607),(kid12_part608),(kid12_part609),(kid12_part610),(kid12_part611),(kid12_part612),(kid12_part613),(kid12_part614),(kid12_part615),(kid12_part616),(kid12_part617),(kid12_part618),(kid12_part619),(kid12_part620),(kid12_part621),(kid12_part622),(kid12_part623),(kid12_part624),(kid12_part625),(kid12_part626),(kid12_part627),(kid12_part628),(kid12_part629)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part606_checked

  · exact kid12_part612_checked

  · exact kid12_part618_checked

  · exact kid12_part624_checked

  · exact kid12_part607_checked

  · exact kid12_part613_checked

  · exact kid12_part619_checked

  · exact kid12_part625_checked

  · exact kid12_part608_checked

  · exact kid12_part614_checked

  · exact kid12_part620_checked

  · exact kid12_part626_checked

  · exact kid12_part609_checked

  · exact kid12_part615_checked

  · exact kid12_part621_checked

  · exact kid12_part627_checked

  · exact kid12_part610_checked

  · exact kid12_part616_checked

  · exact kid12_part622_checked

  · exact kid12_part628_checked

  · exact kid12_part611_checked

  · exact kid12_part617_checked

  · exact kid12_part623_checked

  · exact kid12_part629_checked

def kid12_part630 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 29 1 false (3),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 17 2 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 13 1 true (3),
.cycle 12 2 true (3),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.last 16 (4,true),
.cycle 18 2 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 41 1 false (9),
.cycle 13 1 true (3),
.last 15 (4,true)
]),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.last 18 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (11),
.cycle 33 1 false (9),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.last 18 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 45 1 false (13),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.split 13 (4,false) (byMove [
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 17 2 false (1),
.cycle 37 1 false (9),
.last 22 (4,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 10 7 true (2),
.cycle 10 11 true (2),
.cycle 41 1 false (9),
.cycle 27 1 false (3),
.last 16 (4,true),
.cycle 21 2 false (5),
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 3 true (3)
]),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 41 1 false (11),
.split 13 (4,false) (byMove [
.cycle 37 1 false (9),
.last 16 (4,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 6 8 true (2),
.last 16 (4,true),
.cycle 10 8 true (2),
.cycle 41 1 false (11),
.last 14 (4,true),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4)
])
theorem kid12_part630_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part630) = true := by rfl

def kid12_part631 : Audit := .cycle 16 3 false (1)
theorem kid12_part631_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part631) = true := by rfl

def kid12_part632 : Audit := .split 19 (5,false) (byMove [
.cycle 11 10 false (2),
.cycle 6 24 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.cycle 44 7 false (-2),
.cycle 26 7 false (-1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 23 7 false (2),
.cycle 21 1 false (-1),
.last 22 (4,true),
.cycle 19 2 true (-2),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 23 7 false (0),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 15 6 false (2),
.cycle 11 10 false (2),
.cycle 6 24 false (3),
.cycle 23 7 false (0),
.last 22 (4,true),
.last 22 (4,true)
]),
.cycle 19 1 false (-1),
.cycle 20 7 false (1),
.cycle 18 2 true (-1),
.cycle 20 7 false (0),
.cycle 21 7 false (2),
.split 20 (4,true) (byMove [
.cycle 11 11 false (2),
.cycle 6 25 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 21 (4,false),
.last 22 (4,false),
.cycle 21 7 false (2),
.cycle 35 7 false (6),
.cycle 21 7 false (1),
.cycle 22 7 false (3),
.last 24 (4,false),
.cycle 21 7 false (1),
.cycle 21 7 false (0),
.cycle 21 7 false (0),
.cycle 23 7 false (2),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 19 2 true (-1),
.cycle 13 8 true (-1),
.cycle 21 7 false (1),
.cycle 21 7 false (1),
.cycle 5 16 true (-1),
.last 24 (4,false),
.cycle 17 4 true (-1)
]),
.cycle 20 7 false (0),
.cycle 20 7 false (-1),
.cycle 20 7 false (-1),
.cycle 22 7 false (1),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.cycle 11 11 false (2),
.cycle 6 25 false (3),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 21 (4,true),
.cycle 21 7 false (-1),
.cycle 21 7 false (-2),
.cycle 21 7 false (-2),
.cycle 23 7 false (0),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 13 8 false (2),
.cycle 21 7 false (-1),
.cycle 21 7 false (-1),
.cycle 5 16 false (3),
.last 21 (4,true),
.cycle 17 4 false (1)
]),
.cycle 19 1 false (-1),
.cycle 13 7 false (2),
.cycle 20 7 false (0),
.cycle 20 7 false (0),
.cycle 5 15 false (3),
.split 20 (4,true) (byMove [
.cycle 24 7 false (3),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 22 (4,false),
.cycle 21 7 false (-1),
.cycle 6 15 false (3),
.cycle 56 7 false (0),
.cycle 14 7 false (2),
.cycle 6 23 false (3),
.last 24 (4,false),
.cycle 10 11 false (2),
.cycle 21 7 false (0),
.cycle 18 3 false (0),
.cycle 21 7 false (-1),
.cycle 22 7 false (1),
.last 22 (4,false),
.cycle 21 7 false (-1),
.cycle 26 7 false (0),
.cycle 16 5 false (2),
.cycle 12 9 false (2),
.cycle 34 7 false (0),
.last 24 (4,false),
.cycle 22 7 false (0)
]),
.cycle 17 3 false (1)
])
theorem kid12_part632_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part632) = true := by rfl

def kid12_part633 : Audit := .cycle 51 1 false (7)
theorem kid12_part633_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part633) = true := by rfl

def kid12_part634 : Audit := .cycle 18 1 false (0)
theorem kid12_part634_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part634) = true := by rfl

def kid12_part636 : Audit := .cycle 17 1 false (5)
theorem kid12_part636_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part636) = true := by rfl

def kid12_part637 : Audit := .split 13 (5,false) (byMove [
.last 22 (4,true),
.cycle 17 50 true (-4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 157 (4,true),
.cycle 13 1 false (-1),
.cycle 19 1 false (5),
.cycle 12 2 true (-1),
.last 115 (4,true),
.last 107 (4,true),
.last 14 (4,true),
.cycle 19 50 true (-4),
.last 141 (4,true),
.last 149 (4,true),
.cycle 21 1 false (5),
.cycle 14 1 false (-2),
.last 111 (4,true),
.cycle 13 1 false (-1),
.last 87 (4,true),
.last 113 (4,true),
.last 117 (4,true),
.cycle 8 7 false (3),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid12_part637_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part637) = true := by rfl

def kid12_part638 : Audit := .cycle 18 1 false (-2)
theorem kid12_part638_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part638) = true := by rfl

def kid12_part639 : Audit := .cycle 17 1 false (-1)
theorem kid12_part639_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part639) = true := by rfl

def kid12_part640 : Audit := .split 12 (4,true) (byMove [
.cycle 46 1 false (0),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 16 1 false (0),
.cycle 20 1 false (0),
.cycle 17 1 false (5),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 13 6 true (0),
.cycle 23 1 false (-1),
.cycle 28 1 false (0),
.cycle 20 1 false (0),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid12_part640_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part640) = true := by rfl

def kid12_part641 : Audit := .split 14 (5,false) (byMove [
.cycle 19 24 false (2),
.cycle 12 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 35 1 false (5),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 12 4 true (-2),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.last 22 (4,true),
.last 48 (4,true),
.cycle 12 9 false (0),
.cycle 11 4 false (1),
.last 17 (4,true)
])
theorem kid12_part641_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part641) = true := by rfl

def kid12_part642 : Audit := .cycle 6 6 true (1)
theorem kid12_part642_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part642) = true := by rfl

def kid12_part643 : Audit := .split 13 (5,false) (byMove [
.cycle 19 1 false (5),
.cycle 19 60 true (-4),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (1),
.cycle 12 2 true (1),
.last 18 (4,true),
.cycle 61 1 false (7),
.last 14 (4,true),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.last 19 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 5 34 true (1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid12_part643_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part643) = true := by rfl

def kid12_part644 : Audit := .split 16 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 5 false (3),
.last 17 (5,false),
.cycle 18 5 false (2),
.last 18 (5,false),
.cycle 17 5 false (1),
.cycle 19 5 false (3),
.cycle 22 1 false (6),
.cycle 17 5 false (1),
.cycle 17 5 false (0),
.cycle 20 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.cycle 17 5 false (0),
.last 17 (5,false),
.cycle 12 6 true (0),
.cycle 17 5 false (1),
.cycle 19 5 false (1),
.cycle 5 12 true (0),
.cycle 16 21 true (0),
.cycle 15 2 true (0)
])
theorem kid12_part644_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part644) = true := by rfl

def kid12_part645 : Audit := .cycle 51 1 false (7)
theorem kid12_part645_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part645) = true := by rfl

def kid12_part646 : Audit := .split 12 (4,true) (byMove [
.cycle 27 1 false (5),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 16 1 true (2),
.last 13 (5,false),
.cycle 51 1 false (7),
.last 14 (5,false),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 16 (5,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 13 (5,false),
.cycle 25 6 true (3),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.cycle 12 2 true (2)
])
theorem kid12_part646_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part646) = true := by rfl

def kid12_part647 : Audit := .cycle 10 2 true (1)
theorem kid12_part647_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part647) = true := by rfl

def kid12_part648 : Audit := .cycle 14 4 false (1)
theorem kid12_part648_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part648) = true := by rfl

def kid12_part649 : Audit := .split 13 (5,false) (byMove [
.last 22 (4,true),
.last 30 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.cycle 14 8 false (1),
.cycle 12 2 true (-1),
.cycle 14 8 false (0),
.cycle 15 8 false (2),
.last 14 (4,true),
.cycle 14 8 false (0),
.cycle 14 8 false (-1),
.cycle 14 8 false (-1),
.cycle 16 8 false (1),
.cycle 14 1 false (-2),
.cycle 14 8 false (-2),
.cycle 13 1 false (-1),
.last 19 (4,true),
.cycle 14 8 false (0),
.cycle 14 8 false (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid12_part649_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part649) = true := by rfl

def kid12_part650 : Audit := .cycle 12 8 true (-3)
theorem kid12_part650_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part650) = true := by rfl

def kid12_part651 : Audit := .cycle 19 1 false (-1)
theorem kid12_part651_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part651) = true := by rfl

def kid12_part652 : Audit := .split 12 (4,true) (byMove [
.cycle 12 9 false (1),
.cycle 11 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 18 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 16 1 false (4),
.cycle 14 1 false (0),
.cycle 16 1 false (-2),
.cycle 20 1 false (-2),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 12 6 true (0),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.cycle 12 2 true (0)
])
theorem kid12_part652_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part652) = true := by rfl

def kid12_part653 : Audit := .split 14 (5,false) (byMove [
.last 23 (4,true),
.cycle 20 10 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 12 7 false (0),
.cycle 14 2 true (-2),
.cycle 12 6 false (0),
.cycle 12 8 true (-2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.cycle 12 9 false (0),
.cycle 12 9 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 12 4 false (0),
.cycle 12 8 false (0),
.cycle 5 10 false (3),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid12_part653_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part653) = true := by rfl

def kid12_part654 : Audit := .split 17 (4,true) (byMove [
.cycle 23 1 false (5),
.last 19 (5,false),
.cycle 30 1 false (-2),
.cycle 29 1 false (-1),
.cycle 12 11 false (3),
.last 44 (5,false),
.cycle 6 12 true (1),
.last 19 (5,false),
.cycle 18 11 false (2),
.cycle 81 1 false (7),
.cycle 0 21 true (0),
.cycle 10 8 true (1),
.cycle 20 10 false (1),
.last 19 (5,false),
.cycle 18 14 true (-3),
.cycle 31 1 false (-1),
.cycle 18 7 false (1),
.last 26 (5,false),
.cycle 12 6 true (1),
.cycle 18 9 false (2),
.cycle 19 13 false (2),
.cycle 5 46 true (1),
.cycle 0 21 true (0),
.cycle 16 2 true (1)
])
theorem kid12_part654_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part654) = true := by rfl

def kid12_part655 : Audit := .split 14 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 9 15 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 9 false (2),
.last 15 (5,false),
.cycle 18 3 false (2),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 19 3 false (3),
.cycle 1 18 true (0),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 20 3 false (0),
.cycle 20 3 false (2),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.last 15 (5,false),
.cycle 12 6 true (0),
.cycle 15 3 false (1),
.cycle 19 3 false (1),
.cycle 5 10 true (0),
.cycle 1 18 true (0),
.cycle 13 2 true (0)
])
theorem kid12_part655_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part655) = true := by rfl

def kid12_part656 : Audit := .split 18 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 6 23 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 23 false (3),
.last 19 (5,false),
.cycle 19 7 false (2),
.last 20 (5,false),
.cycle 19 7 false (1),
.cycle 20 7 false (3),
.cycle 27 7 false (6),
.cycle 19 7 false (1),
.cycle 19 7 false (0),
.cycle 20 7 false (0),
.cycle 21 7 false (2),
.cycle 19 1 false (-1),
.cycle 19 7 false (0),
.last 19 (5,false),
.cycle 13 6 true (0),
.cycle 19 7 false (1),
.cycle 19 7 false (1),
.cycle 5 14 true (0),
.cycle 2 21 true (0),
.cycle 17 2 true (0)
])
theorem kid12_part656_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part656) = true := by rfl

def kid12_part657 : Audit := .cycle 5 28 true (1)
theorem kid12_part657_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part657) = true := by rfl

def kid12_part658 : Audit := .split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.cycle 24 1 true (-2),
.last 15 (5,false),
.cycle 6 28 true (1),
.last 14 (5,false),
.cycle 17 11 false (2),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 16 (5,false),
.cycle 19 7 false (0),
.last 18 (5,false),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.cycle 13 3 false (1),
.last 15 (5,false),
.cycle 25 6 true (3),
.cycle 15 7 false (2),
.cycle 19 15 false (2),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.cycle 12 2 true (2)
])
theorem kid12_part658_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part658) = true := by rfl

def kid12_part659 : Audit := .split 13 (4,true) (byMove [
.cycle 19 1 false (5),
.last 15 (5,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 17 7 false (1),
.cycle 61 1 false (7),
.last 17 (5,false),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.last 15 (5,false),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 14 3 false (0),
.last 18 (5,false),
.cycle 12 6 true (1),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 5 34 true (1),
.last 17 (5,false),
.cycle 12 2 true (1)
])
theorem kid12_part659_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part659) = true := by rfl

def kid12_part635 : Audit := .split 11 (4,false) (byMove [(kid12_part636),(kid12_part637),(kid12_part638),(kid12_part639),(kid12_part640),(kid12_part641),(kid12_part642),(kid12_part643),(kid12_part644),(kid12_part645),(kid12_part646),(kid12_part647),(kid12_part648),(kid12_part649),(kid12_part650),(kid12_part651),(kid12_part652),(kid12_part653),(kid12_part654),(kid12_part655),(kid12_part656),(kid12_part657),(kid12_part658),(kid12_part659)])

theorem kid12_part635_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part635) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid12_part636),(kid12_part637),(kid12_part638),(kid12_part639),(kid12_part640),(kid12_part641),(kid12_part642),(kid12_part643),(kid12_part644),(kid12_part645),(kid12_part646),(kid12_part647),(kid12_part648),(kid12_part649),(kid12_part650),(kid12_part651),(kid12_part652),(kid12_part653),(kid12_part654),(kid12_part655),(kid12_part656),(kid12_part657),(kid12_part658),(kid12_part659)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part636_checked

  · exact kid12_part642_checked

  · exact kid12_part648_checked

  · exact kid12_part654_checked

  · exact kid12_part637_checked

  · exact kid12_part643_checked

  · exact kid12_part649_checked

  · exact kid12_part655_checked

  · exact kid12_part638_checked

  · exact kid12_part644_checked

  · exact kid12_part650_checked

  · exact kid12_part656_checked

  · exact kid12_part639_checked

  · exact kid12_part645_checked

  · exact kid12_part651_checked

  · exact kid12_part657_checked

  · exact kid12_part640_checked

  · exact kid12_part646_checked

  · exact kid12_part652_checked

  · exact kid12_part658_checked

  · exact kid12_part641_checked

  · exact kid12_part647_checked

  · exact kid12_part653_checked

  · exact kid12_part659_checked

def kid12_part660 : Audit := .split 11 (5,false) (byMove [
.cycle 17 1 false (5),
.cycle 17 50 true (-4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.split 12 (4,true) (byMove [
.last 42 (4,false),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.cycle 17 1 false (5),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 22 (4,false),
.last 29 (4,false),
.last 21 (4,false),
.last 13 (4,false),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 11 2 true (1),
.cycle 16 5 false (0),
.cycle 51 1 false (7),
.split 12 (4,true) (byMove [
.cycle 21 11 false (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 14 (4,false),
.cycle 51 1 false (7),
.cycle 1 15 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 16 5 false (0),
.cycle 20 9 false (0),
.cycle 61 1 false (7),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (1),
.cycle 23 8 true (2),
.cycle 9 4 true (1),
.cycle 6 8 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 10 4 true (1)
]),
.cycle 10 2 true (1),
.cycle 14 4 false (1),
.cycle 13 8 false (-1),
.cycle 12 8 true (-3),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.last 23 (4,false),
.last 22 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 20 (4,false),
.last 16 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.last 21 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 20 (4,false),
.last 16 (4,false),
.last 20 (4,false),
.cycle 5 8 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 17 7 false (1),
.cycle 14 3 false (0),
.cycle 18 7 false (0),
.cycle 5 28 true (1),
.split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 8 6 true (1),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 6 28 true (1),
.cycle 1 15 true (1),
.cycle 17 7 false (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 18 7 false (0),
.cycle 15 3 false (0),
.cycle 15 6 false (1),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 32 9 false (2),
.cycle 15 5 false (1),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 14 5 false (2)
]),
.cycle 13 3 false (1)
])
theorem kid12_part660_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part660) = true := by rfl

def kid12_part661 : Audit := .cycle 6 16 true (2)
theorem kid12_part661_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part661) = true := by rfl

def kid12_part662 : Audit := .cycle 9 2 true (2)
theorem kid12_part662_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part662) = true := by rfl

def kid12_part663 : Audit := .cycle 6 6 true (2)
theorem kid12_part663_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part663) = true := by rfl

def kid12_part664 : Audit := .cycle 0 12 true (0)
theorem kid12_part664_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part664) = true := by rfl

def kid12_part666 : Audit := .cycle 30 1 false (6)
theorem kid12_part666_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part666) = true := by rfl

def kid12_part667 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 28 true (-2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 28 (4,false),
.last 15 (4,false),
.cycle 34 1 false (6),
.cycle 12 2 true (1),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 28 1 false (4),
.cycle 23 1 false (-1),
.last 34 (4,false),
.cycle 17 1 false (-1),
.cycle 0 31 true (0),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.last 15 (4,false)
])
theorem kid12_part667_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part667) = true := by rfl

def kid12_part668 : Audit := .cycle 19 5 false (1)
theorem kid12_part668_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part668) = true := by rfl

def kid12_part669 : Audit := .cycle 0 13 true (0)
theorem kid12_part669_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part669) = true := by rfl

def kid12_part670 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.last 15 (5,false),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.last 14 (5,false),
.cycle 16 6 false (1),
.last 15 (5,false),
.cycle 0 37 false (3),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.last 18 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 38 1 false (6),
.cycle 13 1 true (1),
.last 14 (5,false)
])
theorem kid12_part670_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part670) = true := by rfl

def kid12_part671 : Audit := .split 13 (4,false) (byMove [
.cycle 34 1 false (6),
.last 15 (5,false),
.cycle 23 7 false (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.last 14 (5,false),
.cycle 6 8 true (2),
.last 15 (5,false),
.cycle 23 7 false (1),
.cycle 61 1 false (7),
.last 15 (5,false),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 15 16 true (2),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid12_part671_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part671) = true := by rfl

def kid12_part672 : Audit := .cycle 0 12 true (0)
theorem kid12_part672_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part672) = true := by rfl

def kid12_part673 : Audit := .cycle 1 11 true (1)
theorem kid12_part673_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part673) = true := by rfl

def kid12_part674 : Audit := .cycle 7 16 true (2)
theorem kid12_part674_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part674) = true := by rfl

def kid12_part675 : Audit := .cycle 3 9 true (1)
theorem kid12_part675_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part675) = true := by rfl

def kid12_part676 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 73 1 false (7),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 1, 8, 8, 8, 64],96⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 1, 8, 8, 8, 64],96⟩,
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 28 1 false (6),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 1, 8, 8, 8, 64],96⟩,
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part676_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part676) = true := by rfl

def kid12_part677 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (4,false),
.last 13 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 15 true (2),
.last 24 (4,false),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 32 (4,false),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part677_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part677) = true := by rfl

def kid12_part678 : Audit := .cycle 6 6 true (2)
theorem kid12_part678_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part678) = true := by rfl

def kid12_part679 : Audit := .split 13 (5,false) (byMove [
.cycle 19 1 false (5),
.cycle 19 60 true (-4),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.last 25 (4,false),
.last 15 (4,false),
.cycle 6 8 true (1),
.cycle 12 2 true (1),
.cycle 19 7 false (1),
.cycle 61 1 false (7),
.cycle 23 11 false (1),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.cycle 14 10 false (0),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.last 25 (4,false),
.cycle 17 1 false (-1),
.cycle 20 11 false (2),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 5 34 true (1),
.cycle 17 3 false (1),
.cycle 17 7 false (2)
])
theorem kid12_part679_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part679) = true := by rfl

def kid12_part680 : Audit := .cycle 19 5 false (1)
theorem kid12_part680_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part680) = true := by rfl

def kid12_part681 : Audit := .cycle 51 1 false (7)
theorem kid12_part681_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part681) = true := by rfl

def kid12_part682 : Audit := .split 13 (4,false) (byMove [
.cycle 19 1 false (5),
.last 15 (5,false),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 2 true (0),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 19 7 false (1),
.cycle 61 1 false (7),
.cycle 12 2 true (1),
.cycle 10 4 true (1),
.cycle 16 6 false (1),
.last 15 (5,false),
.cycle 14 10 true (-3),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (5,false),
.cycle 20 9 false (2),
.cycle 17 5 false (1),
.cycle 21 9 false (1),
.cycle 5 34 true (1),
.cycle 15 3 false (1),
.cycle 16 5 false (2)
])
theorem kid12_part682_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part682) = true := by rfl

def kid12_part683 : Audit := .cycle 10 2 true (2)
theorem kid12_part683_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part683) = true := by rfl

def kid12_part684 : Audit := .cycle 0 12 true (0)
theorem kid12_part684_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part684) = true := by rfl

def kid12_part685 : Audit := .cycle 1 11 true (1)
theorem kid12_part685_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part685) = true := by rfl

def kid12_part686 : Audit := .cycle 2 10 true (1)
theorem kid12_part686_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part686) = true := by rfl

def kid12_part687 : Audit := .cycle 13 14 true (2)
theorem kid12_part687_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part687) = true := by rfl

def kid12_part688 : Audit := .split 12 (4,false) (byMove [
.cycle 11 14 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 12 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 13 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 5 true (2),
.cycle 11 9 true (2),
.cycle 11 17 true (2),
.cycle 11 3 true (3),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 18 true (3),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid12_part688_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part688) = true := by rfl

def kid12_part689 : Audit := .split 12 (5,false) (byMove [
.last 26 (4,false),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 17 (4,false),
.last 21 (4,false),
.cycle 10 17 true (2),
.last 15 (4,false),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid12_part689_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part689) = true := by rfl

def kid12_part665 : Audit := .split 11 (4,true) (byMove [(kid12_part666),(kid12_part667),(kid12_part668),(kid12_part669),(kid12_part670),(kid12_part671),(kid12_part672),(kid12_part673),(kid12_part674),(kid12_part675),(kid12_part676),(kid12_part677),(kid12_part678),(kid12_part679),(kid12_part680),(kid12_part681),(kid12_part682),(kid12_part683),(kid12_part684),(kid12_part685),(kid12_part686),(kid12_part687),(kid12_part688),(kid12_part689)])

theorem kid12_part665_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part665) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid12_part666),(kid12_part667),(kid12_part668),(kid12_part669),(kid12_part670),(kid12_part671),(kid12_part672),(kid12_part673),(kid12_part674),(kid12_part675),(kid12_part676),(kid12_part677),(kid12_part678),(kid12_part679),(kid12_part680),(kid12_part681),(kid12_part682),(kid12_part683),(kid12_part684),(kid12_part685),(kid12_part686),(kid12_part687),(kid12_part688),(kid12_part689)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part666_checked

  · exact kid12_part672_checked

  · exact kid12_part678_checked

  · exact kid12_part684_checked

  · exact kid12_part667_checked

  · exact kid12_part673_checked

  · exact kid12_part679_checked

  · exact kid12_part685_checked

  · exact kid12_part668_checked

  · exact kid12_part674_checked

  · exact kid12_part680_checked

  · exact kid12_part686_checked

  · exact kid12_part669_checked

  · exact kid12_part675_checked

  · exact kid12_part681_checked

  · exact kid12_part687_checked

  · exact kid12_part670_checked

  · exact kid12_part676_checked

  · exact kid12_part682_checked

  · exact kid12_part688_checked

  · exact kid12_part671_checked

  · exact kid12_part677_checked

  · exact kid12_part683_checked

  · exact kid12_part689_checked

def kid12_part690 : Audit := .split 12 (5,false) (byMove [
.cycle 10 14 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 26 15 true (2),
.last 38 (4,false),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 20 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.last 29 (4,false),
.cycle 14 10 true (1),
.cycle 28 18 true (2),
.last 15 (4,false),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.last 14 (4,false),
.cycle 12 2 true (3)
]),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.last 15 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 16 true (2),
.cycle 10 13 true (2),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 21 true (2),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 10 5 true (2),
.cycle 10 9 true (2),
.cycle 10 17 true (2),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 23 true (-1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 15 (4,false),
.last 20 (4,false),
.cycle 10 17 true (2),
.last 19 (4,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 11 3 true (3),
.cycle 10 9 true (2),
.cycle 25 7 true (1),
.cycle 14 11 true (1),
.cycle 5 9 true (1),
.last 15 (4,false),
.cycle 10 5 true (2),
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 11 3 true (3)
]),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 10 18 true (2),
.split 13 (4,false) (byMove [
.cycle 10 15 true (2),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 14 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 6 8 true (2),
.cycle 10 6 true (2),
.cycle 10 10 true (2),
.cycle 10 18 true (2),
.last 14 (4,true),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 19 true (2),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4)
])
theorem kid12_part690_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part690) = true := by rfl

def kid12_part570 : Audit := .split 10 (5,true) (byMove [(kid12_part571),(kid12_part572),(kid12_part573),(kid12_part574),(kid12_part575),(kid12_part600),(kid12_part601),(kid12_part602),(kid12_part603),(kid12_part604),(kid12_part605),(kid12_part630),(kid12_part631),(kid12_part632),(kid12_part633),(kid12_part634),(kid12_part635),(kid12_part660),(kid12_part661),(kid12_part662),(kid12_part663),(kid12_part664),(kid12_part665),(kid12_part690)])

theorem kid12_part570_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (kid12_part570) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid12_part571),(kid12_part572),(kid12_part573),(kid12_part574),(kid12_part575),(kid12_part600),(kid12_part601),(kid12_part602),(kid12_part603),(kid12_part604),(kid12_part605),(kid12_part630),(kid12_part631),(kid12_part632),(kid12_part633),(kid12_part634),(kid12_part635),(kid12_part660),(kid12_part661),(kid12_part662),(kid12_part663),(kid12_part664),(kid12_part665),(kid12_part690)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part571_checked

  · exact kid12_part601_checked

  · exact kid12_part631_checked

  · exact kid12_part661_checked

  · exact kid12_part572_checked

  · exact kid12_part602_checked

  · exact kid12_part632_checked

  · exact kid12_part662_checked

  · exact kid12_part573_checked

  · exact kid12_part603_checked

  · exact kid12_part633_checked

  · exact kid12_part663_checked

  · exact kid12_part574_checked

  · exact kid12_part604_checked

  · exact kid12_part634_checked

  · exact kid12_part664_checked

  · exact kid12_part575_checked

  · exact kid12_part605_checked

  · exact kid12_part635_checked

  · exact kid12_part665_checked

  · exact kid12_part600_checked

  · exact kid12_part630_checked

  · exact kid12_part660_checked

  · exact kid12_part690_checked

def kid12_part691 : Audit := .cycle 0 10 true (0)
theorem kid12_part691_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,0⟩)) (kid12_part691) = true := by rfl

def kid12_part692 : Audit := .cycle 1 9 true (1)
theorem kid12_part692_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,1⟩)) (kid12_part692) = true := by rfl

def kid12_part693 : Audit := .cycle 2 8 true (1)
theorem kid12_part693_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,2⟩)) (kid12_part693) = true := by rfl

def kid12_part694 : Audit := .cycle 11 12 true (2)
theorem kid12_part694_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,3⟩)) (kid12_part694) = true := by rfl

def kid12_part696 : Audit := .split 21 (4,true) (byMove [
.cycle 11 11 true (2),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.split 22 (5,true) (byMove [
.cycle 39 1 false (3),
.cycle 43 1 false (3),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 12 11 true (2),
.cycle 3 20 true (1),
.cycle 0 24 true (0),
.last 23 (5,false),
.cycle 6 17 true (2),
.cycle 6 22 true (2),
.cycle 35 5 false (2),
.cycle 63 1 false (9),
.last 24 (5,false),
.last 24 (5,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 4 34 true (1),
.cycle 10 13 true (2),
.last 23 (5,false)
]),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (2),
.cycle 3 19 true (1),
.cycle 0 23 true (0),
.split 22 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 37 (5,true),
.cycle 10 13 true (2),
.last 24 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 34 (5,true),
.cycle 13 10 true (2),
.cycle 0 24 true (0),
.cycle 22 1 true (6),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.cycle 0 27 true (0),
.last 24 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 38 (5,true),
.last 36 (5,true),
.cycle 22 1 true (6)
]),
.cycle 6 16 true (2),
.cycle 20 2 true (4),
.cycle 17 6 true (3),
.cycle 5 30 true (1),
.cycle 33 12 false (3),
.split 22 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 8 16 true (2),
.last 24 (5,false),
.last 24 (5,false),
.cycle 6 30 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 64, 64],[8, 8, 1, 8, 32, 8, 64],96⟩,
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 24 (5,false),
.cycle 17 6 true (3),
.cycle 45 11 false (2),
.cycle 35 5 false (2),
.cycle 5 18 true (1),
.last 24 (5,false),
.last 24 (5,false),
.cycle 11 12 true (2),
.cycle 9 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 21 2 true (4),
.last 24 (5,false)
]),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.cycle 10 12 true (2),
.split 22 (5,false) (byMove [
.cycle 11 12 true (2),
.cycle 9 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 21 2 true (5),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 12 11 true (2),
.cycle 3 20 true (1),
.cycle 0 24 true (0),
.cycle 22 1 true (6),
.cycle 6 17 true (2),
.cycle 20 3 true (4),
.cycle 17 7 true (3),
.last 36 (5,true),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 37 (5,true),
.cycle 10 13 true (2),
.cycle 22 1 true (6)
])
])
theorem kid12_part696_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part696) = true := by rfl

def kid12_part697 : Audit := .cycle 9 2 true (3)
theorem kid12_part697_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part697) = true := by rfl

def kid12_part698 : Audit := .cycle 6 6 true (2)
theorem kid12_part698_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part698) = true := by rfl

def kid12_part699 : Audit := .cycle 0 12 true (0)
theorem kid12_part699_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part699) = true := by rfl

def kid12_part700 : Audit := .split 11 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 1 14 true (1),
.cycle 19 5 false (2),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 33 1 false (3),
.last 17 (5,false),
.last 13 (5,false),
.cycle 20 5 false (2),
.cycle 23 9 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 48 true (0),
.last 15 (5,false),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (5,true),
.cycle 20 1 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 11 10 true (2),
.cycle 24 1 false (2),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 20 1 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (5,true),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 12 6 true (1),
.cycle 5 40 true (0),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 30 1 false (0),
.cycle 0 18 true (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 6 40 true (0),
.last 16 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 13 6 true (1),
.cycle 21 11 false (2),
.cycle 24 5 false (3),
.cycle 29 1 false (1),
.last 15 (5,false),
.last 13 (5,false),
.cycle 11 12 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 27 true (0),
.cycle 10 2 true (3),
.split 12 (5,false) (byMove [
.cycle 11 12 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 11 true (3),
.cycle 3 10 true (1),
.cycle 10 4 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 11 7 true (2),
.last 26 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
])
])
theorem kid12_part700_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part700) = true := by rfl

def kid12_part702 : Audit := .split 23 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 29 1 false (3),
.cycle 33 1 false (3),
.cycle 8 17 true (0),
.last 27 (5,false),
.cycle 27 1 false (3),
.cycle 12 12 true (0),
.cycle 0 27 true (0),
.cycle 30 10 true (2),
.cycle 0 25 true (0),
.last 26 (5,false),
.cycle 0 25 true (0),
.cycle 24 17 true (2),
.cycle 22 2 true (2),
.cycle 19 6 true (1),
.cycle 5 19 true (0),
.last 27 (5,false),
.cycle 30 1 false (6),
.cycle 0 35 true (0),
.cycle 1 37 true (0),
.cycle 2 40 true (0),
.cycle 0 25 true (0),
.cycle 24 13 true (2),
.last 36 (5,false)
])
theorem kid12_part702_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part702) = true := by rfl

def kid12_part703 : Audit := .cycle 1 14 true (1)
theorem kid12_part703_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part703) = true := by rfl

def kid12_part704 : Audit := .cycle 19 5 false (2)
theorem kid12_part704_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part704) = true := by rfl

def kid12_part705 : Audit := .cycle 0 13 true (0)
theorem kid12_part705_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part705) = true := by rfl

def kid12_part706 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 10 true (2),
.cycle 3 19 true (0),
.last 14 (5,false),
.last 13 (5,false),
.cycle 20 5 false (2),
.cycle 21 2 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.last 18 (5,false),
.last 13 (5,false)
])
theorem kid12_part706_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part706) = true := by rfl

def kid12_part707 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.cycle 16 13 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 25 1 false (1),
.cycle 13 2 true (1),
.cycle 13 1 true (1),
.cycle 16 6 false (2),
.last 15 (4,true),
.last 17 (4,true),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 16 3 false (0),
.cycle 13 1 true (1)
])
theorem kid12_part707_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part707) = true := by rfl

def kid12_part708 : Audit := .cycle 0 12 true (0)
theorem kid12_part708_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part708) = true := by rfl

def kid12_part709 : Audit := .cycle 1 11 true (1)
theorem kid12_part709_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part709) = true := by rfl

def kid12_part710 : Audit := .split 21 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 25 (5,false),
.cycle 11 11 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (2),
.cycle 3 19 true (1),
.last 23 (5,false),
.last 22 (5,false),
.cycle 6 16 true (2),
.cycle 20 2 true (4),
.cycle 17 6 true (3),
.cycle 5 30 true (1),
.last 25 (5,false),
.cycle 7 16 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.cycle 10 12 true (2),
.last 22 (5,false)
])
theorem kid12_part710_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part710) = true := by rfl

def kid12_part711 : Audit := .cycle 3 9 true (1)
theorem kid12_part711_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part711) = true := by rfl

def kid12_part712 : Audit := .split 13 (5,false) (byMove [
.last 25 (4,true),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.cycle 12 2 true (3),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 10 4 true (3),
.cycle 13 1 true (3)
])
theorem kid12_part712_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part712) = true := by rfl

def kid12_part713 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.last 18 (4,true),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 18 (4,true),
.cycle 28 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
])
theorem kid12_part713_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part713) = true := by rfl

def kid12_part714 : Audit := .cycle 6 6 true (2)
theorem kid12_part714_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part714) = true := by rfl

def kid12_part715 : Audit := .split 13 (4,true) (byMove [
.cycle 0 29 true (0),
.cycle 27 13 false (2),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 29 (5,false),
.cycle 25 11 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 10 true (2),
.cycle 3 11 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.cycle 14 6 true (1),
.cycle 5 42 true (0),
.last 29 (5,false),
.cycle 23 11 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 29 true (0),
.cycle 10 4 true (2),
.last 14 (5,false)
])
theorem kid12_part715_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part715) = true := by rfl

def kid12_part716 : Audit := .split 15 (4,true) (byMove [
.cycle 12 11 true (1),
.cycle 21 7 false (2),
.cycle 25 11 false (2),
.cycle 0 17 true (0),
.last 20 (5,false),
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 10 true (1),
.cycle 3 13 true (1),
.last 17 (5,false),
.last 16 (5,false),
.cycle 12 12 true (1),
.cycle 14 2 true (2),
.cycle 12 6 true (1),
.cycle 5 24 true (1),
.last 20 (5,false),
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 31 true (0),
.cycle 12 8 true (1),
.last 16 (5,false)
])
theorem kid12_part716_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part716) = true := by rfl

def kid12_part717 : Audit := .split 25 (4,true) (byMove [
.cycle 70 11 true (6),
.cycle 35 1 false (7),
.cycle 39 1 false (7),
.cycle 0 31 true (0),
.last 29 (5,false),
.cycle 33 1 false (7),
.cycle 6 20 true (0),
.cycle 31 28 true (4),
.cycle 26 10 true (3),
.cycle 12 14 true (0),
.last 29 (5,false),
.last 34 (5,false),
.cycle 26 24 true (2),
.cycle 24 2 true (2),
.cycle 21 6 true (1),
.cycle 5 40 true (0),
.last 29 (5,false),
.cycle 51 1 false (7),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 2 30 true (0),
.cycle 0 40 true (0),
.cycle 26 16 true (3),
.cycle 5 22 true (0)
])
theorem kid12_part717_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part717) = true := by rfl

def kid12_part718 : Audit := .split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 20 true (0),
.last 17 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 13 12 true (1),
.cycle 18 2 true (2),
.cycle 23 6 true (1),
.cycle 5 28 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 24 true (0),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (2),
.cycle 11 2 true (2)
])
theorem kid12_part718_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part718) = true := by rfl

def kid12_part719 : Audit := .split 13 (5,false) (byMove [
.cycle 19 1 false (5),
.last 23 (4,true),
.cycle 22 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.last 15 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 28 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.last 26 (4,true),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid12_part719_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part719) = true := by rfl

def kid12_part720 : Audit := .cycle 0 12 true (0)
theorem kid12_part720_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part720) = true := by rfl

def kid12_part721 : Audit := .cycle 1 11 true (1)
theorem kid12_part721_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part721) = true := by rfl

def kid12_part722 : Audit := .cycle 2 10 true (1)
theorem kid12_part722_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part722) = true := by rfl

def kid12_part723 : Audit := .split 25 (4,true) (byMove [
.cycle 0 29 true (0),
.cycle 4 25 true (1),
.cycle 4 29 true (1),
.cycle 8 19 true (2),
.last 29 (5,false),
.cycle 4 23 true (1),
.cycle 14 12 true (2),
.cycle 1 45 true (1),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.last 28 (5,false),
.cycle 0 44 true (0),
.cycle 6 25 true (2),
.cycle 24 2 true (4),
.cycle 21 6 true (3),
.cycle 5 21 true (1),
.last 29 (5,false),
.cycle 13 14 true (2),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (2),
.cycle 11 15 true (2)
])
theorem kid12_part723_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part723) = true := by rfl

def kid12_part724 : Audit := .cycle 10 2 true (3)
theorem kid12_part724_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part724) = true := by rfl

def kid12_part725 : Audit := .split 12 (5,false) (byMove [
.last 23 (4,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 18 (4,true),
.last 25 (4,true),
.last 13 (4,true),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (4,true),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
])
theorem kid12_part725_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part725) = true := by rfl

def kid12_part701 : Audit := .split 11 (5,true) (byMove [(kid12_part702),(kid12_part703),(kid12_part704),(kid12_part705),(kid12_part706),(kid12_part707),(kid12_part708),(kid12_part709),(kid12_part710),(kid12_part711),(kid12_part712),(kid12_part713),(kid12_part714),(kid12_part715),(kid12_part716),(kid12_part717),(kid12_part718),(kid12_part719),(kid12_part720),(kid12_part721),(kid12_part722),(kid12_part723),(kid12_part724),(kid12_part725)])

theorem kid12_part701_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part701) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid12_part702),(kid12_part703),(kid12_part704),(kid12_part705),(kid12_part706),(kid12_part707),(kid12_part708),(kid12_part709),(kid12_part710),(kid12_part711),(kid12_part712),(kid12_part713),(kid12_part714),(kid12_part715),(kid12_part716),(kid12_part717),(kid12_part718),(kid12_part719),(kid12_part720),(kid12_part721),(kid12_part722),(kid12_part723),(kid12_part724),(kid12_part725)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part702_checked

  · exact kid12_part708_checked

  · exact kid12_part714_checked

  · exact kid12_part720_checked

  · exact kid12_part703_checked

  · exact kid12_part709_checked

  · exact kid12_part715_checked

  · exact kid12_part721_checked

  · exact kid12_part704_checked

  · exact kid12_part710_checked

  · exact kid12_part716_checked

  · exact kid12_part722_checked

  · exact kid12_part705_checked

  · exact kid12_part711_checked

  · exact kid12_part717_checked

  · exact kid12_part723_checked

  · exact kid12_part706_checked

  · exact kid12_part712_checked

  · exact kid12_part718_checked

  · exact kid12_part724_checked

  · exact kid12_part707_checked

  · exact kid12_part713_checked

  · exact kid12_part719_checked

  · exact kid12_part725_checked

def kid12_part726 : Audit := .cycle 0 11 true (0)
theorem kid12_part726_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part726) = true := by rfl

def kid12_part727 : Audit := .cycle 1 10 true (1)
theorem kid12_part727_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part727) = true := by rfl

def kid12_part728 : Audit := .split 20 (4,true) (byMove [
.cycle 11 11 true (3),
.cycle 9 12 true (3),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.split 21 (5,true) (byMove [
.cycle 51 1 false (3),
.cycle 9 13 true (3),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 11 11 true (3),
.cycle 3 19 true (1),
.cycle 7 29 true (2),
.last 22 (5,false),
.cycle 6 16 true (2),
.cycle 6 21 true (2),
.cycle 41 5 false (2),
.cycle 75 1 false (11),
.last 23 (5,false),
.last 23 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 4 33 true (1),
.cycle 10 12 true (3),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 36 (5,true),
.cycle 10 12 true (3),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 33 (5,true),
.cycle 12 10 true (3),
.last 35 (5,true),
.cycle 21 1 true (7),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 7 16 true (2),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 37 (5,true),
.cycle 10 12 true (3),
.cycle 21 1 true (7)
]),
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.cycle 16 6 true (4),
.cycle 5 29 true (1),
.cycle 36 7 false (2),
.split 21 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 7 17 true (2),
.cycle 7 19 true (2),
.cycle 8 15 true (2),
.last 23 (5,false),
.last 23 (5,false),
.cycle 6 29 true (2),
.cycle 9 13 true (3),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (5,false),
.last 23 (5,false),
.cycle 16 6 true (4),
.cycle 47 11 false (2),
.cycle 41 5 false (2),
.cycle 5 17 true (1),
.last 23 (5,false),
.last 23 (5,false),
.cycle 11 12 true (3),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 20 2 true (5),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 0 36 true (0),
.cycle 10 11 true (3),
.split 21 (5,false) (byMove [
.cycle 11 12 true (3),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 20 2 true (6),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 11 11 true (3),
.cycle 3 19 true (1),
.last 34 (5,true),
.cycle 21 1 true (7),
.cycle 6 16 true (2),
.cycle 19 3 true (5),
.cycle 16 7 true (4),
.last 35 (5,true),
.last 23 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 36 (5,true),
.cycle 10 12 true (3),
.cycle 21 1 true (7)
])
])
theorem kid12_part728_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part728) = true := by rfl

def kid12_part729 : Audit := .cycle 3 8 true (1)
theorem kid12_part729_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part729) = true := by rfl

def kid12_part730 : Audit := .cycle 10 1 true (4)
theorem kid12_part730_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part730) = true := by rfl

def kid12_part732 : Audit := .cycle 0 12 true (0)
theorem kid12_part732_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part732) = true := by rfl

def kid12_part733 : Audit := .cycle 1 11 true (1)
theorem kid12_part733_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part733) = true := by rfl

def kid12_part734 : Audit := .cycle 2 10 true (1)
theorem kid12_part734_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part734) = true := by rfl

def kid12_part735 : Audit := .split 25 (4,true) (byMove [
.cycle 0 29 true (0),
.last 28 (5,true),
.last 32 (5,true),
.cycle 8 19 true (2),
.cycle 57 1 false (1),
.last 26 (5,true),
.cycle 14 12 true (2),
.cycle 1 45 true (1),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.cycle 3 37 true (1),
.last 26 (5,true),
.cycle 6 25 true (2),
.cycle 24 2 true (4),
.cycle 21 6 true (3),
.cycle 5 21 true (1),
.last 29 (5,true),
.last 26 (5,true),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (2),
.last 26 (5,true)
])
theorem kid12_part735_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part735) = true := by rfl

def kid12_part736 : Audit := .cycle 10 2 true (4)
theorem kid12_part736_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part736) = true := by rfl

def kid12_part737 : Audit := .split 13 (5,true) (byMove [
.last 25 (4,true),
.cycle 1 18 true (1),
.cycle 23 7 false (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 10 4 true (3),
.cycle 12 2 true (3)
])
theorem kid12_part737_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part737) = true := by rfl

def kid12_part738 : Audit := .cycle 0 12 true (0)
theorem kid12_part738_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part738) = true := by rfl

def kid12_part739 : Audit := .cycle 1 11 true (1)
theorem kid12_part739_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part739) = true := by rfl

def kid12_part740 : Audit := .split 22 (4,true) (byMove [
.cycle 0 26 true (0),
.last 25 (5,true),
.last 29 (5,true),
.cycle 8 16 true (2),
.cycle 59 1 false (3),
.last 23 (5,true),
.cycle 12 12 true (3),
.cycle 9 14 true (3),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 23 (5,true),
.cycle 6 22 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 18 true (1),
.last 26 (5,true),
.last 23 (5,true),
.cycle 0 34 true (0),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 10 14 true (3),
.last 23 (5,true)
])
theorem kid12_part740_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part740) = true := by rfl

def kid12_part741 : Audit := .split 20 (4,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 12 true (3),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 12 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 11 10 true (3),
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.cycle 16 6 true (4),
.cycle 5 29 true (1),
.last 24 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 0 36 true (0),
.cycle 10 11 true (3),
.cycle 3 19 true (1)
])
theorem kid12_part741_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part741) = true := by rfl

def kid12_part742 : Audit := .cycle 10 2 true (4)
theorem kid12_part742_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part742) = true := by rfl

def kid12_part743 : Audit := .cycle 11 1 true (5)
theorem kid12_part743_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part743) = true := by rfl

def kid12_part744 : Audit := .cycle 8 4 true (2)
theorem kid12_part744_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part744) = true := by rfl

def kid12_part745 : Audit := .cycle 6 8 true (2)
theorem kid12_part745_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part745) = true := by rfl

def kid12_part746 : Audit := .cycle 0 14 true (0)
theorem kid12_part746_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part746) = true := by rfl

def kid12_part747 : Audit := .cycle 4 8 true (1)
theorem kid12_part747_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part747) = true := by rfl

def kid12_part748 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 10 4 true (4),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 10 4 true (4),
.cycle 11 3 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 12 2 true (4),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (4,true),
.cycle 10 4 true (4),
.last 15 (4,true)
])
theorem kid12_part748_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part748) = true := by rfl

def kid12_part749 : Audit := .split 13 (5,true) (byMove [
.last 31 (4,true),
.cycle 0 20 true (0),
.last 27 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.cycle 40 1 false (8),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 19 (4,true),
.last 26 (4,true),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid12_part749_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part749) = true := by rfl

def kid12_part750 : Audit := .cycle 0 12 true (0)
theorem kid12_part750_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part750) = true := by rfl

def kid12_part751 : Audit := .cycle 1 11 true (1)
theorem kid12_part751_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part751) = true := by rfl

def kid12_part752 : Audit := .cycle 2 10 true (1)
theorem kid12_part752_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part752) = true := by rfl

def kid12_part753 : Audit := .split 26 (4,true) (byMove [
.cycle 5 41 true (1),
.last 29 (5,true),
.last 33 (5,true),
.cycle 0 32 true (0),
.cycle 0 75 true (0),
.last 27 (5,true),
.cycle 6 21 true (2),
.cycle 1 28 true (1),
.cycle 27 10 true (6),
.cycle 13 14 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 27 (5,true),
.cycle 6 31 true (2),
.cycle 25 2 true (5),
.cycle 22 6 true (4),
.cycle 5 41 true (1),
.last 30 (5,true),
.last 27 (5,true),
.cycle 6 21 true (2),
.cycle 1 28 true (1),
.cycle 2 31 true (1),
.cycle 0 41 true (0),
.cycle 10 19 true (3),
.last 27 (5,true)
])
theorem kid12_part753_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part753) = true := by rfl

def kid12_part754 : Audit := .cycle 10 2 true (4)
theorem kid12_part754_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part754) = true := by rfl

def kid12_part755 : Audit := .cycle 11 1 true (5)
theorem kid12_part755_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part755) = true := by rfl

def kid12_part731 : Audit := .split 11 (5,false) (byMove [(kid12_part732),(kid12_part733),(kid12_part734),(kid12_part735),(kid12_part736),(kid12_part737),(kid12_part738),(kid12_part739),(kid12_part740),(kid12_part741),(kid12_part742),(kid12_part743),(kid12_part744),(kid12_part745),(kid12_part746),(kid12_part747),(kid12_part748),(kid12_part749),(kid12_part750),(kid12_part751),(kid12_part752),(kid12_part753),(kid12_part754),(kid12_part755)])

theorem kid12_part731_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part731) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part732),(kid12_part733),(kid12_part734),(kid12_part735),(kid12_part736),(kid12_part737),(kid12_part738),(kid12_part739),(kid12_part740),(kid12_part741),(kid12_part742),(kid12_part743),(kid12_part744),(kid12_part745),(kid12_part746),(kid12_part747),(kid12_part748),(kid12_part749),(kid12_part750),(kid12_part751),(kid12_part752),(kid12_part753),(kid12_part754),(kid12_part755)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part732_checked

  · exact kid12_part738_checked

  · exact kid12_part744_checked

  · exact kid12_part750_checked

  · exact kid12_part733_checked

  · exact kid12_part739_checked

  · exact kid12_part745_checked

  · exact kid12_part751_checked

  · exact kid12_part734_checked

  · exact kid12_part740_checked

  · exact kid12_part746_checked

  · exact kid12_part752_checked

  · exact kid12_part735_checked

  · exact kid12_part741_checked

  · exact kid12_part747_checked

  · exact kid12_part753_checked

  · exact kid12_part736_checked

  · exact kid12_part742_checked

  · exact kid12_part748_checked

  · exact kid12_part754_checked

  · exact kid12_part737_checked

  · exact kid12_part743_checked

  · exact kid12_part749_checked

  · exact kid12_part755_checked

def kid12_part756 : Audit := .cycle 6 5 true (2)
theorem kid12_part756_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part756) = true := by rfl

def kid12_part757 : Audit := .split 12 (4,true) (byMove [
.cycle 11 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 17 12 false (1),
.split 13 (5,true) (byMove [
.cycle 29 1 false (3),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 11 true (2),
.cycle 3 11 true (1),
.cycle 6 11 true (2),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 27 13 false (2),
.cycle 21 5 false (2),
.cycle 35 1 false (7),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 4 25 true (1),
.cycle 10 4 true (3),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.cycle 6 10 true (2),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (5,true),
.cycle 10 4 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.cycle 11 10 true (3),
.cycle 6 11 true (2),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (5,true),
.cycle 10 4 true (3),
.cycle 13 1 true (5)
]),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 11 6 true (2),
.cycle 5 21 true (1),
.cycle 17 10 false (1),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 11 36 true (1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 6 21 true (2),
.cycle 9 5 true (3),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 11 6 true (2),
.cycle 25 11 false (2),
.cycle 21 5 false (2),
.cycle 5 9 true (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 11 12 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.cycle 10 3 true (3),
.split 13 (5,false) (byMove [
.cycle 11 12 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 11 true (3),
.cycle 3 11 true (1),
.cycle 6 11 true (2),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.cycle 11 7 true (3),
.last 27 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (5,true),
.cycle 10 4 true (3),
.cycle 13 1 true (5)
])
])
theorem kid12_part757_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part757) = true := by rfl

def kid12_part758 : Audit := .split 16 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 0 29 false (4),
.split 17 (5,true) (byMove [
.cycle 33 1 false (3),
.cycle 29 7 false (2),
.cycle 31 11 false (2),
.cycle 0 19 true (0),
.last 19 (5,false),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 11 true (2),
.cycle 3 15 true (1),
.cycle 0 21 true (0),
.last 18 (5,false),
.cycle 6 12 true (2),
.cycle 35 17 false (2),
.cycle 25 5 false (2),
.cycle 39 1 false (7),
.last 19 (5,false),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 4 29 true (1),
.cycle 10 8 true (2),
.last 18 (5,false)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 12 10 true (2),
.cycle 3 14 true (1),
.cycle 0 20 true (0),
.split 17 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 32 (5,true),
.cycle 10 8 true (2),
.last 19 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (5,true),
.cycle 12 10 true (2),
.cycle 0 21 true (0),
.cycle 17 1 true (5),
.cycle 8 10 true (2),
.cycle 6 14 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 25 (5,true),
.last 19 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 33 (5,true),
.cycle 13 6 true (2),
.cycle 17 1 true (5)
]),
.cycle 6 11 true (2),
.cycle 15 2 true (3),
.cycle 11 6 true (2),
.cycle 5 25 true (1),
.cycle 20 10 true (-3),
.split 17 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 29 7 false (2),
.cycle 31 11 false (2),
.cycle 8 11 true (2),
.last 19 (5,false),
.last 19 (5,false),
.cycle 6 25 true (2),
.cycle 13 7 true (2),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.last 19 (5,false),
.last 19 (5,false),
.cycle 12 6 true (2),
.cycle 29 11 false (2),
.cycle 25 5 false (2),
.cycle 5 13 true (1),
.last 19 (5,false),
.last 19 (5,false),
.cycle 12 12 true (2),
.cycle 9 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.cycle 16 2 true (3),
.last 19 (5,false)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 32 true (0),
.cycle 10 7 true (2),
.split 17 (5,false) (byMove [
.cycle 12 12 true (2),
.cycle 9 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 11 true (2),
.cycle 3 15 true (1),
.cycle 0 21 true (0),
.cycle 17 1 true (5),
.cycle 6 12 true (2),
.cycle 15 3 true (3),
.cycle 11 7 true (2),
.last 31 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 32 (5,true),
.cycle 10 8 true (2),
.cycle 17 1 true (5)
])
])
theorem kid12_part758_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part758) = true := by rfl

def kid12_part759 : Audit := .split 23 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 5 21 true (1),
.cycle 5 25 true (1),
.cycle 8 17 true (2),
.cycle 50 1 false (0),
.split 24 (5,true) (byMove [
.cycle 41 1 false (3),
.cycle 0 31 true (0),
.cycle 0 33 true (0),
.cycle 6 23 true (2),
.last 26 (5,false),
.last 26 (5,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 3 31 true (1),
.cycle 4 31 true (1),
.last 25 (5,false),
.cycle 5 25 true (1),
.cycle 0 39 true (0),
.cycle 37 5 false (2),
.cycle 0 29 true (0),
.last 26 (5,false),
.last 26 (5,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 4 21 true (1),
.cycle 5 21 true (1),
.last 25 (5,false)
]),
.cycle 12 12 true (2),
.cycle 1 41 true (1),
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 4 31 true (1),
.split 24 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 11 15 true (2),
.cycle 10 15 true (2),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 13 12 true (2),
.last 34 (5,false),
.last 34 (5,false),
.last 25 (5,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 4 21 true (1),
.cycle 5 21 true (1),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 0 42 true (0),
.last 42 (5,false),
.last 25 (5,false)
]),
.cycle 6 23 true (2),
.cycle 22 2 true (4),
.cycle 19 6 true (3),
.cycle 5 19 true (1),
.cycle 37 1 false (-1),
.split 24 (5,true) (byMove [
.cycle 81 1 false (13),
.cycle 5 31 true (1),
.cycle 5 35 true (1),
.cycle 8 23 true (2),
.last 26 (5,false),
.last 26 (5,false),
.cycle 6 19 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 8, 1, 8, 32, 8, 64],96⟩,
.cycle 7 23 true (2),
.cycle 5 35 true (1),
.last 26 (5,false),
.last 27 (5,false),
.cycle 19 6 true (3),
.cycle 47 11 false (2),
.cycle 37 5 false (2),
.cycle 5 27 true (1),
.last 26 (5,false),
.last 26 (5,false),
.cycle 6 19 true (2),
.cycle 9 19 true (2),
.cycle 6 27 true (2),
.cycle 11 14 true (2),
.cycle 23 2 true (4),
.last 27 (5,false)
]),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 10 15 true (2),
.split 24 (5,true) (byMove [
.last 36 (5,false),
.cycle 9 16 true (2),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.last 26 (5,false),
.last 28 (5,false),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.last 35 (5,false),
.cycle 3 22 true (1),
.cycle 4 22 true (1),
.last 25 (5,false),
.cycle 6 19 true (2),
.last 27 (5,false),
.last 31 (5,false),
.cycle 11 14 true (2),
.cycle 23 2 true (5),
.last 28 (5,false),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 11 15 true (2),
.cycle 10 15 true (2),
.last 25 (5,false)
])
])
theorem kid12_part759_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part759) = true := by rfl

def kid12_part760 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 36 true (1),
.cycle 19 5 false (2),
.cycle 8 5 true (2),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.last 27 (5,false),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 15 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.last 17 (5,false),
.last 13 (5,false),
.cycle 20 5 false (2),
.cycle 23 9 false (1),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,false),
.last 13 (5,false)
]),
.cycle 11 12 true (2),
.cycle 9 3 true (3),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 34 true (0),
.cycle 20 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 12 true (2),
.last 22 (5,false),
.last 33 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 20 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 30 true (0),
.cycle 10 3 true (3),
.last 13 (5,false)
]),
.cycle 6 11 true (2),
.cycle 11 2 true (2),
.cycle 12 6 true (1),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 0 25 true (0),
.last 33 (5,false),
.cycle 30 1 false (0),
.cycle 20 1 false (6),
.last 15 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 19 (5,false),
.cycle 7 11 true (2),
.cycle 0 37 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 13 6 true (1),
.cycle 21 11 false (2),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.last 15 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 9 7 true (2),
.cycle 6 15 true (2),
.cycle 11 14 true (2),
.cycle 11 2 true (2),
.last 15 (5,false)
]),
.cycle 0 23 true (0),
.cycle 9 3 true (3),
.cycle 6 7 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.split 12 (5,true) (byMove [
.last 24 (5,false),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 3 10 true (1),
.last 18 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.last 19 (5,false),
.cycle 11 14 true (2),
.cycle 11 2 true (3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 15 true (3),
.cycle 10 3 true (3),
.last 13 (5,false)
])
])
theorem kid12_part760_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part760) = true := by rfl

def kid12_part762 : Audit := .cycle 0 15 true (0)
theorem kid12_part762_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid12_part762) = true := by rfl

def kid12_part763 : Audit := .split 30 (4,true) (byMove [
.cycle 5 45 true (1),
.cycle 9 36 true (1),
.cycle 6 44 true (1),
.cycle 0 36 true (0),
.cycle 15 24 true (-1),
.cycle 0 48 true (0),
.cycle 6 25 true (1),
.cycle 1 32 true (1),
.cycle 31 10 true (4),
.cycle 17 14 true (1),
.last 34 (5,false),
.cycle 0 35 true (0),
.cycle 5 104 true (1),
.cycle 29 2 true (3),
.cycle 26 6 true (2),
.cycle 5 45 true (1),
.last 46 (5,false),
.cycle 11 32 true (1),
.cycle 0 68 true (0),
.cycle 1 32 true (1),
.cycle 2 35 true (1),
.cycle 0 45 true (0),
.cycle 5 80 true (1),
.last 49 (5,false)
])
theorem kid12_part763_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid12_part763) = true := by rfl

def kid12_part764 : Audit := .cycle 19 5 false (2)
theorem kid12_part764_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid12_part764) = true := by rfl

def kid12_part765 : Audit := .cycle 8 5 true (2)
theorem kid12_part765_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid12_part765) = true := by rfl

def kid12_part766 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 9 14 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 16 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 0 23 true (0),
.last 14 (5,false),
.last 13 (5,false),
.cycle 20 5 false (2),
.cycle 21 2 true (0),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 18 (5,false),
.last 13 (5,false)
])
theorem kid12_part766_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid12_part766) = true := by rfl

def kid12_part767 : Audit := .split 13 (5,false) (byMove [
.cycle 16 1 false (2),
.last 27 (4,true),
.cycle 22 1 false (-2),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 30 true (0),
.cycle 0 17 true (0),
.last 23 (4,true),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 17 1 true (3),
.cycle 16 6 false (2),
.last 15 (4,true),
.last 17 (4,true),
.cycle 17 1 false (3),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 49 (4,true),
.cycle 0 17 true (0),
.last 22 (4,true),
.cycle 0 19 true (0),
.cycle 16 3 false (0),
.cycle 21 1 true (-1)
])
theorem kid12_part767_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid12_part767) = true := by rfl

def kid12_part768 : Audit := .split 23 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 6 21 true (2),
.cycle 6 25 true (2),
.cycle 8 17 true (2),
.last 27 (5,false),
.cycle 8 17 true (2),
.cycle 12 12 true (2),
.cycle 1 41 true (1),
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.last 26 (5,false),
.cycle 0 25 true (0),
.cycle 6 23 true (2),
.cycle 22 2 true (4),
.cycle 19 6 true (3),
.cycle 5 19 true (1),
.last 27 (5,false),
.cycle 6 19 true (2),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 10 15 true (2),
.cycle 0 25 true (0)
])
theorem kid12_part768_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid12_part768) = true := by rfl

def kid12_part769 : Audit := .cycle 9 3 true (3)
theorem kid12_part769_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid12_part769) = true := by rfl

def kid12_part770 : Audit := .cycle 7 5 true (2)
theorem kid12_part770_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid12_part770) = true := by rfl

def kid12_part771 : Audit := .cycle 0 13 true (0)
theorem kid12_part771_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid12_part771) = true := by rfl

def kid12_part772 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 33 true (0),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 3 19 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.cycle 10 3 true (3),
.last 13 (5,false)
])
theorem kid12_part772_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid12_part772) = true := by rfl

def kid12_part773 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 21 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.cycle 13 1 true (5),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (4,true),
.last 16 (4,true),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (4,true),
.cycle 10 4 true (3),
.cycle 13 1 true (5)
])
theorem kid12_part773_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid12_part773) = true := by rfl

def kid12_part774 : Audit := .split 16 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.last 27 (5,false),
.cycle 6 12 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 12 10 true (2),
.cycle 3 14 true (1),
.last 18 (5,false),
.last 17 (5,false),
.cycle 6 11 true (2),
.cycle 15 2 true (3),
.cycle 12 6 true (2),
.cycle 5 25 true (1),
.last 27 (5,false),
.cycle 11 6 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 32 true (0),
.cycle 10 7 true (2),
.last 17 (5,false)
])
theorem kid12_part774_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid12_part774) = true := by rfl

def kid12_part775 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 27 15 false (2),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 27 (5,false),
.cycle 25 11 false (1),
.cycle 12 12 true (2),
.cycle 1 23 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 6 11 true (2),
.cycle 6 13 true (2),
.cycle 12 2 true (2),
.cycle 14 6 true (1),
.cycle 5 9 true (1),
.last 27 (5,false),
.cycle 23 11 false (2),
.cycle 0 25 true (0),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 10 5 true (2),
.last 17 (5,false)
])
theorem kid12_part775_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid12_part775) = true := by rfl

def kid12_part776 : Audit := .split 15 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 21 7 false (2),
.cycle 25 11 false (2),
.cycle 8 9 true (1),
.last 20 (5,false),
.cycle 19 5 false (2),
.cycle 12 12 true (1),
.cycle 1 35 true (1),
.cycle 12 11 true (1),
.cycle 0 17 true (0),
.last 18 (5,false),
.cycle 0 19 true (0),
.cycle 12 17 true (1),
.cycle 14 2 true (2),
.cycle 12 6 true (1),
.cycle 5 11 true (1),
.last 20 (5,false),
.cycle 19 5 false (2),
.cycle 0 27 true (0),
.cycle 12 9 true (1),
.cycle 12 13 true (1),
.cycle 0 17 true (0),
.cycle 12 9 true (1),
.last 23 (5,false)
])
theorem kid12_part776_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid12_part776) = true := by rfl

def kid12_part777 : Audit := .cycle 5 7 true (1)
theorem kid12_part777_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid12_part777) = true := by rfl

def kid12_part778 : Audit := .split 12 (4,true) (byMove [
.cycle 16 11 true (2),
.cycle 9 32 true (1),
.cycle 31 1 false (1),
.cycle 20 1 false (6),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 13 10 true (2),
.cycle 3 55 true (0),
.last 16 (5,false),
.last 15 (5,false),
.cycle 13 17 true (1),
.cycle 18 2 true (2),
.cycle 5 9 true (1),
.cycle 5 15 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.cycle 10 5 true (2),
.cycle 11 2 true (2)
])
theorem kid12_part778_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid12_part778) = true := by rfl

def kid12_part779 : Audit := .split 13 (5,false) (byMove [
.last 32 (4,true),
.last 25 (4,true),
.cycle 22 1 false (-2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid12_part779_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid12_part779) = true := by rfl

def kid12_part780 : Audit := .split 22 (4,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.last 41 (5,false),
.cycle 0 24 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 13 10 true (3),
.cycle 3 20 true (1),
.last 24 (5,false),
.last 23 (5,false),
.cycle 6 17 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 31 true (1),
.last 46 (5,false),
.cycle 11 12 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 38 true (0),
.cycle 10 13 true (3),
.last 23 (5,false)
])
theorem kid12_part780_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid12_part780) = true := by rfl

def kid12_part781 : Audit := .cycle 9 3 true (3)
theorem kid12_part781_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid12_part781) = true := by rfl

def kid12_part782 : Audit := .cycle 6 7 true (2)
theorem kid12_part782_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid12_part782) = true := by rfl

def kid12_part783 : Audit := .cycle 0 13 true (0)
theorem kid12_part783_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid12_part783) = true := by rfl

def kid12_part784 : Audit := .split 12 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 20 (5,false),
.cycle 10 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 10 true (3),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 21 true (1),
.last 20 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.cycle 10 3 true (3),
.last 13 (5,false)
])
theorem kid12_part784_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid12_part784) = true := by rfl

def kid12_part785 : Audit := .split 13 (5,false) (byMove [
.last 24 (4,true),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 19 (4,true),
.last 26 (4,true),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (4,true),
.cycle 10 4 true (3),
.cycle 13 1 true (5)
])
theorem kid12_part785_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid12_part785) = true := by rfl

def kid12_part761 : Audit := .split 11 (5,true) (byMove [(kid12_part762),(kid12_part763),(kid12_part764),(kid12_part765),(kid12_part766),(kid12_part767),(kid12_part768),(kid12_part769),(kid12_part770),(kid12_part771),(kid12_part772),(kid12_part773),(kid12_part774),(kid12_part775),(kid12_part776),(kid12_part777),(kid12_part778),(kid12_part779),(kid12_part780),(kid12_part781),(kid12_part782),(kid12_part783),(kid12_part784),(kid12_part785)])

theorem kid12_part761_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part761) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid12_part762),(kid12_part763),(kid12_part764),(kid12_part765),(kid12_part766),(kid12_part767),(kid12_part768),(kid12_part769),(kid12_part770),(kid12_part771),(kid12_part772),(kid12_part773),(kid12_part774),(kid12_part775),(kid12_part776),(kid12_part777),(kid12_part778),(kid12_part779),(kid12_part780),(kid12_part781),(kid12_part782),(kid12_part783),(kid12_part784),(kid12_part785)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part762_checked

  · exact kid12_part768_checked

  · exact kid12_part774_checked

  · exact kid12_part780_checked

  · exact kid12_part763_checked

  · exact kid12_part769_checked

  · exact kid12_part775_checked

  · exact kid12_part781_checked

  · exact kid12_part764_checked

  · exact kid12_part770_checked

  · exact kid12_part776_checked

  · exact kid12_part782_checked

  · exact kid12_part765_checked

  · exact kid12_part771_checked

  · exact kid12_part777_checked

  · exact kid12_part783_checked

  · exact kid12_part766_checked

  · exact kid12_part772_checked

  · exact kid12_part778_checked

  · exact kid12_part784_checked

  · exact kid12_part767_checked

  · exact kid12_part773_checked

  · exact kid12_part779_checked

  · exact kid12_part785_checked

def kid12_part786 : Audit := .cycle 0 11 true (0)
theorem kid12_part786_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part786) = true := by rfl

def kid12_part787 : Audit := .cycle 1 10 true (1)
theorem kid12_part787_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part787) = true := by rfl

def kid12_part788 : Audit := .cycle 2 9 true (1)
theorem kid12_part788_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part788) = true := by rfl

def kid12_part789 : Audit := .split 24 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 8 18 true (2),
.cycle 67 1 false (3),
.split 25 (5,true) (byMove [
.cycle 55 1 false (3),
.cycle 4 24 true (1),
.cycle 4 26 true (1),
.cycle 6 24 true (2),
.last 27 (5,false),
.last 27 (5,false),
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 3 32 true (1),
.cycle 0 28 true (0),
.last 26 (5,false),
.cycle 0 32 true (0),
.cycle 4 32 true (1),
.cycle 45 5 false (2),
.cycle 0 30 true (0),
.last 27 (5,false),
.last 27 (5,false),
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.cycle 0 28 true (0),
.last 26 (5,false)
]),
.cycle 13 12 true (3),
.cycle 9 16 true (3),
.cycle 7 18 true (2),
.cycle 0 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 11 15 true (3),
.cycle 10 16 true (3),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 14 12 true (3),
.last 35 (5,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 512, 16777216, 128, 256, 32768, 1048580, 512, 16777216, 524288, 1048576, 2097152, 4195328, 2097152, 16777216, 128, 256, 32768, 147456, 512, 16777216, 16777216],[4, 1024, 1024, 1, 32, 16, 16384, 1024, 1024, 4096, 131072, 65536, 1048576, 4194304, 1024, 262144, 8388608, 4194304, 16384, 1024, 1024, 4096, 131072, 65536, 16777216],27478048⟩,
.last 26 (5,false),
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.cycle 0 28 true (0),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 0 43 true (0),
.cycle 10 16 true (3),
.last 26 (5,false)
]),
.cycle 6 24 true (2),
.cycle 23 2 true (5),
.cycle 20 6 true (4),
.cycle 5 20 true (1),
.cycle 5 32 true (1),
.split 25 (5,true) (byMove [
.cycle 151 1 false (19),
.cycle 12 16 true (3),
.cycle 12 18 true (3),
.cycle 8 24 true (2),
.last 27 (5,false),
.last 27 (5,false),
.cycle 6 20 true (2),
.cycle 9 20 true (3),
.cycle 7 24 true (2),
.cycle 5 36 true (1),
.last 27 (5,false),
.last 28 (5,false),
.cycle 20 6 true (4),
.cycle 51 11 false (2),
.cycle 45 5 false (2),
.cycle 5 28 true (1),
.last 27 (5,false),
.last 27 (5,false),
.cycle 6 20 true (2),
.cycle 9 20 true (3),
.cycle 6 28 true (2),
.cycle 12 14 true (3),
.cycle 24 2 true (5),
.last 28 (5,false)
]),
.cycle 0 36 true (0),
.cycle 9 16 true (3),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.cycle 10 16 true (3),
.split 25 (5,true) (byMove [
.last 37 (5,false),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 27 (5,false),
.last 29 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.last 36 (5,false),
.cycle 3 23 true (1),
.last 44 (5,false),
.last 26 (5,false),
.cycle 6 20 true (2),
.last 28 (5,false),
.last 32 (5,false),
.cycle 12 14 true (3),
.cycle 24 2 true (6),
.last 29 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 11 15 true (3),
.cycle 10 16 true (3),
.last 26 (5,false)
])
])
theorem kid12_part789_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part789) = true := by rfl

def kid12_part790 : Audit := .cycle 10 1 true (4)
theorem kid12_part790_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part790) = true := by rfl

def kid12_part792 : Audit := .split 22 (4,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 60 1 false (2),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 13 10 true (3),
.cycle 3 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 12, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 31 true (1),
.last 26 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 38 true (0),
.cycle 10 13 true (3),
.cycle 11 12 true (3)
])
theorem kid12_part792_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part792) = true := by rfl

def kid12_part793 : Audit := .cycle 9 3 true (3)
theorem kid12_part793_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part793) = true := by rfl

def kid12_part794 : Audit := .cycle 6 7 true (2)
theorem kid12_part794_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part794) = true := by rfl

def kid12_part795 : Audit := .cycle 0 13 true (0)
theorem kid12_part795_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part795) = true := by rfl

def kid12_part796 : Audit := .split 12 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 10 true (3),
.cycle 3 10 true (1),
.cycle 10 3 true (4),
.cycle 10 4 true (4),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 21 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.cycle 10 3 true (4),
.cycle 11 2 true (4)
])
theorem kid12_part796_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part796) = true := by rfl

def kid12_part797 : Audit := .split 12 (5,true) (byMove [
.last 23 (4,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 10 3 true (4),
.cycle 23 1 false (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 18 (4,true),
.last 25 (4,true),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (4,true),
.cycle 10 3 true (4),
.cycle 11 2 true (4)
])
theorem kid12_part797_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part797) = true := by rfl

def kid12_part798 : Audit := .cycle 0 12 true (0)
theorem kid12_part798_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part798) = true := by rfl

def kid12_part799 : Audit := .cycle 1 11 true (1)
theorem kid12_part799_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part799) = true := by rfl

def kid12_part800 : Audit := .split 21 (4,true) (byMove [
.cycle 12 11 true (4),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 10 14 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (4),
.cycle 3 19 true (1),
.cycle 10 12 true (4),
.last 34 (5,true),
.cycle 6 16 true (2),
.cycle 20 2 true (6),
.cycle 17 6 true (5),
.cycle 5 30 true (1),
.last 25 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.cycle 10 12 true (4),
.cycle 11 11 true (4)
])
theorem kid12_part800_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part800) = true := by rfl

def kid12_part801 : Audit := .cycle 3 9 true (1)
theorem kid12_part801_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part801) = true := by rfl

def kid12_part802 : Audit := .cycle 10 2 true (4)
theorem kid12_part802_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part802) = true := by rfl

def kid12_part803 : Audit := .cycle 11 1 true (5)
theorem kid12_part803_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part803) = true := by rfl

def kid12_part804 : Audit := .cycle 6 6 true (2)
theorem kid12_part804_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part804) = true := by rfl

def kid12_part805 : Audit := .split 13 (4,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 21 5 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 10 true (4),
.cycle 3 11 true (1),
.cycle 10 4 true (4),
.cycle 6 11 true (2),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 12 6 true (3),
.cycle 5 22 true (1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 29 true (0),
.cycle 10 4 true (4),
.cycle 11 3 true (4)
])
theorem kid12_part805_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part805) = true := by rfl

def kid12_part806 : Audit := .split 17 (4,true) (byMove [
.cycle 13 11 true (3),
.cycle 9 9 true (3),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.cycle 25 8 false (2),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 13 10 true (3),
.cycle 3 15 true (1),
.cycle 14 6 true (3),
.cycle 0 21 true (0),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.cycle 12 6 true (3),
.cycle 5 26 true (1),
.last 22 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 0 33 true (0),
.cycle 10 8 true (3),
.cycle 11 7 true (3)
])
theorem kid12_part806_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part806) = true := by rfl

def kid12_part807 : Audit := .split 24 (4,true) (byMove [
.cycle 0 28 true (0),
.last 27 (5,true),
.last 31 (5,true),
.cycle 8 18 true (2),
.cycle 67 1 false (3),
.last 25 (5,true),
.cycle 13 12 true (3),
.cycle 9 16 true (3),
.cycle 7 18 true (2),
.cycle 0 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.last 25 (5,true),
.cycle 6 24 true (2),
.cycle 23 2 true (5),
.cycle 20 6 true (4),
.cycle 5 20 true (1),
.last 28 (5,true),
.last 25 (5,true),
.cycle 0 36 true (0),
.cycle 9 16 true (3),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.cycle 10 16 true (3),
.last 25 (5,true)
])
theorem kid12_part807_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part807) = true := by rfl

def kid12_part808 : Audit := .split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.last 15 (5,true),
.last 19 (5,true),
.cycle 8 6 true (2),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 12 12 true (3),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (4),
.last 13 (5,true),
.cycle 6 12 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 8 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (4),
.last 13 (5,true)
])
theorem kid12_part808_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part808) = true := by rfl

def kid12_part809 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 9 7 true (3),
.cycle 6 15 true (2),
.cycle 8 6 true (2),
.last 13 (4,true),
.cycle 17 1 false (-1),
.last 24 (4,true),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 49 1 false (9),
.last 17 (4,true),
.last 14 (4,true),
.last 18 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.last 23 (4,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (4)
])
theorem kid12_part809_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part809) = true := by rfl

def kid12_part810 : Audit := .cycle 0 12 true (0)
theorem kid12_part810_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part810) = true := by rfl

def kid12_part811 : Audit := .cycle 1 11 true (1)
theorem kid12_part811_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part811) = true := by rfl

def kid12_part812 : Audit := .cycle 2 10 true (1)
theorem kid12_part812_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part812) = true := by rfl

def kid12_part813 : Audit := .split 25 (4,true) (byMove [
.cycle 0 29 true (0),
.last 28 (5,true),
.last 32 (5,true),
.cycle 8 19 true (2),
.cycle 0 35 true (0),
.last 26 (5,true),
.cycle 14 12 true (4),
.cycle 9 17 true (3),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (4),
.last 26 (5,true),
.cycle 6 25 true (2),
.cycle 24 2 true (6),
.cycle 21 6 true (5),
.cycle 5 21 true (1),
.last 29 (5,true),
.last 26 (5,true),
.cycle 0 37 true (0),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 10 17 true (4),
.last 26 (5,true)
])
theorem kid12_part813_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part813) = true := by rfl

def kid12_part814 : Audit := .cycle 10 2 true (4)
theorem kid12_part814_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part814) = true := by rfl

def kid12_part815 : Audit := .cycle 11 1 true (5)
theorem kid12_part815_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part815) = true := by rfl

def kid12_part791 : Audit := .split 11 (5,false) (byMove [(kid12_part792),(kid12_part793),(kid12_part794),(kid12_part795),(kid12_part796),(kid12_part797),(kid12_part798),(kid12_part799),(kid12_part800),(kid12_part801),(kid12_part802),(kid12_part803),(kid12_part804),(kid12_part805),(kid12_part806),(kid12_part807),(kid12_part808),(kid12_part809),(kid12_part810),(kid12_part811),(kid12_part812),(kid12_part813),(kid12_part814),(kid12_part815)])

theorem kid12_part791_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part791) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part792),(kid12_part793),(kid12_part794),(kid12_part795),(kid12_part796),(kid12_part797),(kid12_part798),(kid12_part799),(kid12_part800),(kid12_part801),(kid12_part802),(kid12_part803),(kid12_part804),(kid12_part805),(kid12_part806),(kid12_part807),(kid12_part808),(kid12_part809),(kid12_part810),(kid12_part811),(kid12_part812),(kid12_part813),(kid12_part814),(kid12_part815)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part792_checked

  · exact kid12_part798_checked

  · exact kid12_part804_checked

  · exact kid12_part810_checked

  · exact kid12_part793_checked

  · exact kid12_part799_checked

  · exact kid12_part805_checked

  · exact kid12_part811_checked

  · exact kid12_part794_checked

  · exact kid12_part800_checked

  · exact kid12_part806_checked

  · exact kid12_part812_checked

  · exact kid12_part795_checked

  · exact kid12_part801_checked

  · exact kid12_part807_checked

  · exact kid12_part813_checked

  · exact kid12_part796_checked

  · exact kid12_part802_checked

  · exact kid12_part808_checked

  · exact kid12_part814_checked

  · exact kid12_part797_checked

  · exact kid12_part803_checked

  · exact kid12_part809_checked

  · exact kid12_part815_checked

def kid12_part695 : Audit := .split 10 (4,false) (byMove [(kid12_part696),(kid12_part697),(kid12_part698),(kid12_part699),(kid12_part700),(kid12_part701),(kid12_part726),(kid12_part727),(kid12_part728),(kid12_part729),(kid12_part730),(kid12_part731),(kid12_part756),(kid12_part757),(kid12_part758),(kid12_part759),(kid12_part760),(kid12_part761),(kid12_part786),(kid12_part787),(kid12_part788),(kid12_part789),(kid12_part790),(kid12_part791)])

theorem kid12_part695_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (kid12_part695) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part696),(kid12_part697),(kid12_part698),(kid12_part699),(kid12_part700),(kid12_part701),(kid12_part726),(kid12_part727),(kid12_part728),(kid12_part729),(kid12_part730),(kid12_part731),(kid12_part756),(kid12_part757),(kid12_part758),(kid12_part759),(kid12_part760),(kid12_part761),(kid12_part786),(kid12_part787),(kid12_part788),(kid12_part789),(kid12_part790),(kid12_part791)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part696_checked

  · exact kid12_part726_checked

  · exact kid12_part756_checked

  · exact kid12_part786_checked

  · exact kid12_part697_checked

  · exact kid12_part727_checked

  · exact kid12_part757_checked

  · exact kid12_part787_checked

  · exact kid12_part698_checked

  · exact kid12_part728_checked

  · exact kid12_part758_checked

  · exact kid12_part788_checked

  · exact kid12_part699_checked

  · exact kid12_part729_checked

  · exact kid12_part759_checked

  · exact kid12_part789_checked

  · exact kid12_part700_checked

  · exact kid12_part730_checked

  · exact kid12_part760_checked

  · exact kid12_part790_checked

  · exact kid12_part701_checked

  · exact kid12_part731_checked

  · exact kid12_part761_checked

  · exact kid12_part791_checked

def kid12_part817 : Audit := .split 21 (5,true) (byMove [
.cycle 11 11 true (2),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.split 22 (4,true) (byMove [
.cycle 39 1 false (3),
.cycle 43 1 false (3),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 12 11 true (2),
.cycle 3 20 true (1),
.last 23 (4,false),
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 6 22 true (2),
.cycle 35 5 false (2),
.cycle 63 1 false (9),
.last 24 (4,false),
.last 24 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 4 34 true (1),
.last 23 (4,false),
.cycle 10 13 true (2)
]),
.cycle 0 25 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (2),
.cycle 3 19 true (1),
.split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 37 (4,true),
.last 24 (4,true),
.cycle 10 13 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.last 34 (4,true),
.cycle 13 10 true (2),
.cycle 22 1 true (6),
.cycle 0 24 true (0),
.cycle 8 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 4 19 true (1),
.last 24 (4,true),
.cycle 0 27 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 38 (4,true),
.cycle 22 1 true (6),
.last 36 (4,true)
]),
.cycle 0 23 true (0),
.cycle 6 16 true (2),
.cycle 20 2 true (4),
.cycle 17 6 true (3),
.cycle 5 30 true (1),
.split 22 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 8 16 true (2),
.last 24 (4,false),
.last 24 (4,false),
.cycle 6 30 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 1, 64],[8, 8, 1, 8, 8, 16, 64],80⟩,
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 24 (4,false),
.cycle 17 6 true (3),
.cycle 45 11 false (2),
.cycle 35 5 false (2),
.cycle 5 18 true (1),
.last 24 (4,false),
.last 24 (4,false),
.cycle 11 12 true (2),
.cycle 9 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.last 24 (4,false),
.cycle 21 2 true (4)
]),
.cycle 33 12 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.split 22 (4,false) (byMove [
.cycle 11 12 true (2),
.cycle 9 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 12 11 true (2),
.cycle 3 20 true (1),
.cycle 22 1 true (6),
.cycle 0 24 true (0),
.cycle 6 17 true (2),
.cycle 20 3 true (4),
.cycle 17 7 true (3),
.last 36 (4,true),
.last 23 (4,true),
.last 24 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.last 37 (4,true),
.cycle 22 1 true (6),
.cycle 10 13 true (2)
]),
.cycle 10 12 true (2)
])
theorem kid12_part817_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid12_part817) = true := by rfl

def kid12_part818 : Audit := .cycle 9 2 true (3)
theorem kid12_part818_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid12_part818) = true := by rfl

def kid12_part819 : Audit := .cycle 6 6 true (2)
theorem kid12_part819_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid12_part819) = true := by rfl

def kid12_part820 : Audit := .cycle 0 12 true (0)
theorem kid12_part820_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid12_part820) = true := by rfl

def kid12_part822 : Audit := .split 23 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 29 1 false (3),
.cycle 33 1 false (3),
.cycle 8 17 true (0),
.cycle 27 1 false (3),
.last 27 (4,false),
.cycle 12 12 true (0),
.cycle 0 27 true (0),
.cycle 30 10 true (2),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 26 (4,false),
.cycle 24 17 true (2),
.cycle 22 2 true (2),
.cycle 19 6 true (1),
.cycle 5 19 true (0),
.cycle 30 1 false (6),
.last 27 (4,false),
.cycle 0 35 true (0),
.cycle 1 37 true (0),
.cycle 2 40 true (0),
.cycle 0 25 true (0),
.last 36 (4,false),
.cycle 24 13 true (2)
])
theorem kid12_part822_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part822) = true := by rfl

def kid12_part823 : Audit := .cycle 1 14 true (1)
theorem kid12_part823_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part823) = true := by rfl

def kid12_part824 : Audit := .cycle 19 5 false (2)
theorem kid12_part824_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part824) = true := by rfl

def kid12_part825 : Audit := .cycle 0 13 true (0)
theorem kid12_part825_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part825) = true := by rfl

def kid12_part826 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.cycle 16 13 false (1),
.cycle 22 1 false (-2),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 13 2 true (1),
.cycle 16 6 false (2),
.last 15 (5,true),
.last 17 (5,true),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 13 1 true (1),
.cycle 16 3 false (0)
])
theorem kid12_part826_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part826) = true := by rfl

def kid12_part827 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 10 true (2),
.cycle 3 19 true (0),
.last 13 (4,false),
.last 14 (4,false),
.cycle 20 5 false (2),
.cycle 21 2 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.last 13 (4,false),
.last 18 (4,false)
])
theorem kid12_part827_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part827) = true := by rfl

def kid12_part828 : Audit := .cycle 0 12 true (0)
theorem kid12_part828_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part828) = true := by rfl

def kid12_part829 : Audit := .cycle 1 11 true (1)
theorem kid12_part829_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part829) = true := by rfl

def kid12_part830 : Audit := .split 21 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 13 true (2),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.cycle 11 11 true (2),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (2),
.cycle 3 19 true (1),
.last 22 (4,false),
.last 23 (4,false),
.cycle 6 16 true (2),
.cycle 20 2 true (4),
.cycle 17 6 true (3),
.cycle 5 30 true (1),
.cycle 7 16 true (2),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.last 22 (4,false),
.cycle 10 12 true (2)
])
theorem kid12_part830_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part830) = true := by rfl

def kid12_part831 : Audit := .cycle 3 9 true (1)
theorem kid12_part831_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part831) = true := by rfl

def kid12_part832 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 19 1 false (1),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 28 1 false (6),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (5,true),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
])
theorem kid12_part832_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part832) = true := by rfl

def kid12_part833 : Audit := .split 13 (4,false) (byMove [
.last 25 (5,true),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 12 2 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 13 1 true (3),
.cycle 10 4 true (3)
])
theorem kid12_part833_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part833) = true := by rfl

def kid12_part834 : Audit := .cycle 6 6 true (2)
theorem kid12_part834_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part834) = true := by rfl

def kid12_part835 : Audit := .split 13 (5,true) (byMove [
.cycle 0 29 true (0),
.cycle 27 13 false (2),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.cycle 25 11 false (1),
.last 29 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 10 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 8 true (2),
.cycle 12 2 true (2),
.cycle 14 6 true (1),
.cycle 5 42 true (0),
.cycle 23 11 false (2),
.last 29 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 29 true (0),
.last 14 (4,false),
.cycle 10 4 true (2)
])
theorem kid12_part835_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part835) = true := by rfl

def kid12_part836 : Audit := .split 15 (5,true) (byMove [
.cycle 12 11 true (1),
.cycle 21 7 false (2),
.cycle 25 11 false (2),
.cycle 0 17 true (0),
.cycle 19 5 false (2),
.last 20 (4,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 10 true (1),
.cycle 3 13 true (1),
.last 16 (4,false),
.last 17 (4,false),
.cycle 12 12 true (1),
.cycle 14 2 true (2),
.cycle 12 6 true (1),
.cycle 5 24 true (1),
.cycle 19 5 false (2),
.last 20 (4,false),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 0 31 true (0),
.last 16 (4,false),
.cycle 12 8 true (1)
])
theorem kid12_part836_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part836) = true := by rfl

def kid12_part837 : Audit := .split 25 (5,true) (byMove [
.cycle 70 11 true (6),
.cycle 35 1 false (7),
.cycle 39 1 false (7),
.cycle 0 31 true (0),
.cycle 33 1 false (7),
.last 29 (4,false),
.cycle 6 20 true (0),
.cycle 31 28 true (4),
.cycle 26 10 true (3),
.cycle 12 14 true (0),
.last 34 (4,false),
.last 29 (4,false),
.cycle 26 24 true (2),
.cycle 24 2 true (2),
.cycle 21 6 true (1),
.cycle 5 40 true (0),
.cycle 51 1 false (7),
.last 29 (4,false),
.cycle 0 56 true (0),
.cycle 1 27 true (0),
.cycle 2 30 true (0),
.cycle 0 40 true (0),
.cycle 5 22 true (0),
.cycle 26 16 true (3)
])
theorem kid12_part837_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part837) = true := by rfl

def kid12_part838 : Audit := .split 13 (4,false) (byMove [
.cycle 19 1 false (5),
.last 23 (5,true),
.cycle 22 1 false (-2),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (1),
.last 15 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.cycle 12 2 true (1),
.last 14 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 28 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 26 (5,true),
.cycle 15 3 false (1),
.last 14 (5,true)
])
theorem kid12_part838_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part838) = true := by rfl

def kid12_part839 : Audit := .split 12 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 20 true (0),
.last 17 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 13 12 true (1),
.cycle 18 2 true (2),
.cycle 23 6 true (1),
.cycle 5 28 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 24 true (0),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 10 4 true (2)
])
theorem kid12_part839_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part839) = true := by rfl

def kid12_part840 : Audit := .cycle 0 12 true (0)
theorem kid12_part840_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part840) = true := by rfl

def kid12_part841 : Audit := .cycle 1 11 true (1)
theorem kid12_part841_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part841) = true := by rfl

def kid12_part842 : Audit := .cycle 2 10 true (1)
theorem kid12_part842_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part842) = true := by rfl

def kid12_part843 : Audit := .split 25 (5,true) (byMove [
.cycle 0 29 true (0),
.cycle 4 25 true (1),
.cycle 4 29 true (1),
.cycle 8 19 true (2),
.cycle 4 23 true (1),
.last 29 (4,false),
.cycle 14 12 true (2),
.cycle 1 45 true (1),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.cycle 0 44 true (0),
.last 28 (4,false),
.cycle 6 25 true (2),
.cycle 24 2 true (4),
.cycle 21 6 true (3),
.cycle 5 21 true (1),
.cycle 13 14 true (2),
.last 29 (4,false),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 11 15 true (2),
.cycle 10 17 true (2)
])
theorem kid12_part843_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part843) = true := by rfl

def kid12_part844 : Audit := .split 12 (4,false) (byMove [
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.last 25 (5,true),
.cycle 11 3 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (5,true),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
])
theorem kid12_part844_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part844) = true := by rfl

def kid12_part845 : Audit := .cycle 10 2 true (3)
theorem kid12_part845_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part845) = true := by rfl

def kid12_part821 : Audit := .split 11 (4,true) (byMove [(kid12_part822),(kid12_part823),(kid12_part824),(kid12_part825),(kid12_part826),(kid12_part827),(kid12_part828),(kid12_part829),(kid12_part830),(kid12_part831),(kid12_part832),(kid12_part833),(kid12_part834),(kid12_part835),(kid12_part836),(kid12_part837),(kid12_part838),(kid12_part839),(kid12_part840),(kid12_part841),(kid12_part842),(kid12_part843),(kid12_part844),(kid12_part845)])

theorem kid12_part821_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid12_part821) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid12_part822),(kid12_part823),(kid12_part824),(kid12_part825),(kid12_part826),(kid12_part827),(kid12_part828),(kid12_part829),(kid12_part830),(kid12_part831),(kid12_part832),(kid12_part833),(kid12_part834),(kid12_part835),(kid12_part836),(kid12_part837),(kid12_part838),(kid12_part839),(kid12_part840),(kid12_part841),(kid12_part842),(kid12_part843),(kid12_part844),(kid12_part845)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part822_checked

  · exact kid12_part828_checked

  · exact kid12_part834_checked

  · exact kid12_part840_checked

  · exact kid12_part823_checked

  · exact kid12_part829_checked

  · exact kid12_part835_checked

  · exact kid12_part841_checked

  · exact kid12_part824_checked

  · exact kid12_part830_checked

  · exact kid12_part836_checked

  · exact kid12_part842_checked

  · exact kid12_part825_checked

  · exact kid12_part831_checked

  · exact kid12_part837_checked

  · exact kid12_part843_checked

  · exact kid12_part826_checked

  · exact kid12_part832_checked

  · exact kid12_part838_checked

  · exact kid12_part844_checked

  · exact kid12_part827_checked

  · exact kid12_part833_checked

  · exact kid12_part839_checked

  · exact kid12_part845_checked

def kid12_part846 : Audit := .split 11 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 1 14 true (1),
.cycle 19 5 false (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 33 1 false (3),
.last 13 (4,false),
.last 17 (4,false),
.cycle 20 5 false (2),
.cycle 23 9 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 48 true (0),
.last 13 (4,false),
.last 15 (4,false)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (4,true),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 11 10 true (2),
.cycle 12 1 true (4),
.cycle 24 1 false (2),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 28 (4,true),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
]),
.cycle 19 1 false (1),
.cycle 6 6 true (2),
.cycle 11 2 true (2),
.cycle 12 6 true (1),
.cycle 5 40 true (0),
.split 12 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 16 true (0),
.cycle 30 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,false),
.last 15 (4,false),
.cycle 6 40 true (0),
.last 16 (4,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 13 6 true (1),
.cycle 21 11 false (2),
.cycle 24 5 false (3),
.cycle 29 1 false (1),
.last 13 (4,false),
.last 15 (4,false),
.cycle 11 12 true (2),
.cycle 9 4 true (2),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 27 true (0),
.split 12 (4,false) (byMove [
.cycle 11 12 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 11 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 10 4 true (3),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 11 7 true (2),
.last 26 (4,true),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 27 (4,true),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
]),
.cycle 10 2 true (3)
])
theorem kid12_part846_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid12_part846) = true := by rfl

def kid12_part847 : Audit := .cycle 0 11 true (0)
theorem kid12_part847_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid12_part847) = true := by rfl

def kid12_part848 : Audit := .cycle 1 10 true (1)
theorem kid12_part848_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid12_part848) = true := by rfl

def kid12_part849 : Audit := .split 20 (5,true) (byMove [
.cycle 11 11 true (3),
.cycle 9 12 true (3),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 51 1 false (3),
.cycle 9 13 true (3),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 11 11 true (3),
.cycle 3 19 true (1),
.last 22 (4,false),
.cycle 7 29 true (2),
.cycle 6 16 true (2),
.cycle 6 21 true (2),
.cycle 41 5 false (2),
.cycle 75 1 false (11),
.last 23 (4,false),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 4 33 true (1),
.last 22 (4,false),
.cycle 10 12 true (3)
]),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 36 (4,true),
.last 23 (4,true),
.cycle 10 12 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 33 (4,true),
.cycle 12 10 true (3),
.cycle 21 1 true (7),
.last 35 (4,true),
.cycle 8 14 true (2),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (4,true),
.cycle 7 16 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 37 (4,true),
.cycle 21 1 true (7),
.cycle 10 12 true (3)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 64, 4, 64],[4, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.cycle 16 6 true (4),
.cycle 5 29 true (1),
.split 21 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 7 17 true (2),
.cycle 7 19 true (2),
.cycle 8 15 true (2),
.last 23 (4,false),
.last 23 (4,false),
.cycle 6 29 true (2),
.cycle 9 13 true (3),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 23 (4,false),
.cycle 16 6 true (4),
.cycle 47 11 false (2),
.cycle 41 5 false (2),
.cycle 5 17 true (1),
.last 23 (4,false),
.last 23 (4,false),
.cycle 11 12 true (3),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 20 2 true (5)
]),
.cycle 36 7 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 0 36 true (0),
.split 21 (4,false) (byMove [
.cycle 11 12 true (3),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 11 11 true (3),
.cycle 3 19 true (1),
.cycle 21 1 true (7),
.last 34 (4,true),
.cycle 6 16 true (2),
.cycle 19 3 true (5),
.cycle 16 7 true (4),
.last 35 (4,true),
.last 22 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.last 36 (4,true),
.cycle 21 1 true (7),
.cycle 10 12 true (3)
]),
.cycle 10 11 true (3)
])
theorem kid12_part849_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid12_part849) = true := by rfl

def kid12_part850 : Audit := .cycle 3 8 true (1)
theorem kid12_part850_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid12_part850) = true := by rfl

def kid12_part852 : Audit := .cycle 0 12 true (0)
theorem kid12_part852_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part852) = true := by rfl

def kid12_part853 : Audit := .cycle 1 11 true (1)
theorem kid12_part853_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part853) = true := by rfl

def kid12_part854 : Audit := .cycle 2 10 true (1)
theorem kid12_part854_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part854) = true := by rfl

def kid12_part855 : Audit := .split 25 (5,true) (byMove [
.cycle 0 29 true (0),
.last 28 (4,true),
.last 32 (4,true),
.cycle 8 19 true (2),
.last 26 (4,true),
.cycle 57 1 false (1),
.cycle 14 12 true (2),
.cycle 1 45 true (1),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 3 37 true (1),
.cycle 6 25 true (2),
.cycle 24 2 true (4),
.cycle 21 6 true (3),
.cycle 5 21 true (1),
.last 26 (4,true),
.last 29 (4,true),
.cycle 0 37 true (0),
.cycle 9 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 10 17 true (2)
])
theorem kid12_part855_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part855) = true := by rfl

def kid12_part856 : Audit := .split 13 (4,true) (byMove [
.last 25 (5,true),
.cycle 1 18 true (1),
.cycle 23 7 false (3),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.cycle 26 1 false (2),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 12 2 true (3),
.cycle 10 4 true (3)
])
theorem kid12_part856_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part856) = true := by rfl

def kid12_part857 : Audit := .cycle 10 2 true (4)
theorem kid12_part857_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part857) = true := by rfl

def kid12_part858 : Audit := .cycle 0 12 true (0)
theorem kid12_part858_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part858) = true := by rfl

def kid12_part859 : Audit := .cycle 1 11 true (1)
theorem kid12_part859_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part859) = true := by rfl

def kid12_part860 : Audit := .split 22 (5,true) (byMove [
.cycle 0 26 true (0),
.last 25 (4,true),
.last 29 (4,true),
.cycle 8 16 true (2),
.last 23 (4,true),
.cycle 59 1 false (3),
.cycle 12 12 true (3),
.cycle 9 14 true (3),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 4, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 6 22 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 18 true (1),
.last 23 (4,true),
.last 26 (4,true),
.cycle 0 34 true (0),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 10 14 true (3)
])
theorem kid12_part860_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part860) = true := by rfl

def kid12_part861 : Audit := .split 20 (5,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 12 true (3),
.cycle 6 16 true (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 12 10 true (3),
.cycle 3 18 true (1),
.cycle 11 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 8, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.cycle 16 6 true (4),
.cycle 5 29 true (1),
.last 21 (4,true),
.last 24 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 0 36 true (0),
.cycle 3 19 true (1),
.cycle 10 11 true (3)
])
theorem kid12_part861_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part861) = true := by rfl

def kid12_part862 : Audit := .cycle 11 1 true (5)
theorem kid12_part862_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part862) = true := by rfl

def kid12_part863 : Audit := .cycle 10 2 true (4)
theorem kid12_part863_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part863) = true := by rfl

def kid12_part864 : Audit := .cycle 8 4 true (2)
theorem kid12_part864_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part864) = true := by rfl

def kid12_part865 : Audit := .cycle 6 8 true (2)
theorem kid12_part865_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part865) = true := by rfl

def kid12_part866 : Audit := .cycle 0 14 true (0)
theorem kid12_part866_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part866) = true := by rfl

def kid12_part867 : Audit := .cycle 4 8 true (1)
theorem kid12_part867_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part867) = true := by rfl

def kid12_part868 : Audit := .split 13 (4,true) (byMove [
.last 31 (5,true),
.cycle 0 20 true (0),
.last 27 (5,true),
.last 17 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.cycle 40 1 false (8),
.last 14 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 19 (5,true),
.last 26 (5,true),
.cycle 14 3 true (4),
.last 14 (5,true)
])
theorem kid12_part868_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part868) = true := by rfl

def kid12_part869 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.last 15 (5,true),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (5,true),
.last 22 (5,true),
.cycle 11 3 true (4),
.cycle 10 4 true (4),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (5,true),
.last 15 (5,true),
.cycle 10 4 true (4)
])
theorem kid12_part869_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part869) = true := by rfl

def kid12_part870 : Audit := .cycle 0 12 true (0)
theorem kid12_part870_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part870) = true := by rfl

def kid12_part871 : Audit := .cycle 1 11 true (1)
theorem kid12_part871_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part871) = true := by rfl

def kid12_part872 : Audit := .cycle 2 10 true (1)
theorem kid12_part872_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part872) = true := by rfl

def kid12_part873 : Audit := .split 26 (5,true) (byMove [
.cycle 5 41 true (1),
.last 29 (4,true),
.last 33 (4,true),
.cycle 0 32 true (0),
.last 27 (4,true),
.cycle 0 75 true (0),
.cycle 6 21 true (2),
.cycle 1 28 true (1),
.cycle 27 10 true (6),
.cycle 13 14 true (3),
.last 27 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 8, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 6 31 true (2),
.cycle 25 2 true (5),
.cycle 22 6 true (4),
.cycle 5 41 true (1),
.last 27 (4,true),
.last 30 (4,true),
.cycle 6 21 true (2),
.cycle 1 28 true (1),
.cycle 2 31 true (1),
.cycle 0 41 true (0),
.last 27 (4,true),
.cycle 10 19 true (3)
])
theorem kid12_part873_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part873) = true := by rfl

def kid12_part874 : Audit := .cycle 11 1 true (5)
theorem kid12_part874_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part874) = true := by rfl

def kid12_part875 : Audit := .cycle 10 2 true (4)
theorem kid12_part875_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part875) = true := by rfl

def kid12_part851 : Audit := .split 11 (4,false) (byMove [(kid12_part852),(kid12_part853),(kid12_part854),(kid12_part855),(kid12_part856),(kid12_part857),(kid12_part858),(kid12_part859),(kid12_part860),(kid12_part861),(kid12_part862),(kid12_part863),(kid12_part864),(kid12_part865),(kid12_part866),(kid12_part867),(kid12_part868),(kid12_part869),(kid12_part870),(kid12_part871),(kid12_part872),(kid12_part873),(kid12_part874),(kid12_part875)])

theorem kid12_part851_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid12_part851) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part852),(kid12_part853),(kid12_part854),(kid12_part855),(kid12_part856),(kid12_part857),(kid12_part858),(kid12_part859),(kid12_part860),(kid12_part861),(kid12_part862),(kid12_part863),(kid12_part864),(kid12_part865),(kid12_part866),(kid12_part867),(kid12_part868),(kid12_part869),(kid12_part870),(kid12_part871),(kid12_part872),(kid12_part873),(kid12_part874),(kid12_part875)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part852_checked

  · exact kid12_part858_checked

  · exact kid12_part864_checked

  · exact kid12_part870_checked

  · exact kid12_part853_checked

  · exact kid12_part859_checked

  · exact kid12_part865_checked

  · exact kid12_part871_checked

  · exact kid12_part854_checked

  · exact kid12_part860_checked

  · exact kid12_part866_checked

  · exact kid12_part872_checked

  · exact kid12_part855_checked

  · exact kid12_part861_checked

  · exact kid12_part867_checked

  · exact kid12_part873_checked

  · exact kid12_part856_checked

  · exact kid12_part862_checked

  · exact kid12_part868_checked

  · exact kid12_part874_checked

  · exact kid12_part857_checked

  · exact kid12_part863_checked

  · exact kid12_part869_checked

  · exact kid12_part875_checked

def kid12_part876 : Audit := .cycle 10 1 true (4)
theorem kid12_part876_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid12_part876) = true := by rfl

def kid12_part877 : Audit := .cycle 6 5 true (2)
theorem kid12_part877_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid12_part877) = true := by rfl

def kid12_part878 : Audit := .split 12 (5,true) (byMove [
.cycle 11 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 29 1 false (3),
.cycle 1 18 true (1),
.cycle 23 7 false (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 11 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 6 11 true (2),
.cycle 6 8 true (2),
.cycle 27 13 false (2),
.cycle 21 5 false (2),
.cycle 35 1 false (7),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 4 25 true (1),
.last 14 (4,false),
.cycle 10 4 true (3)
]),
.cycle 17 12 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (4,true),
.last 15 (4,true),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (4,true),
.cycle 11 10 true (3),
.cycle 13 1 true (5),
.cycle 6 11 true (2),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.last 17 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (4,true),
.cycle 13 1 true (5),
.cycle 10 4 true (3)
]),
.cycle 6 10 true (2),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 11 6 true (2),
.cycle 5 21 true (1),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 11 36 true (1),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 6 21 true (2),
.cycle 9 5 true (3),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 11 6 true (2),
.cycle 25 11 false (2),
.cycle 21 5 false (2),
.cycle 5 9 true (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 11 12 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 12 2 true (3)
]),
.cycle 17 10 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.split 13 (4,false) (byMove [
.cycle 11 12 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 11 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 6 11 true (2),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.cycle 11 7 true (3),
.last 27 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 28 (4,true),
.cycle 13 1 true (5),
.cycle 10 4 true (3)
]),
.cycle 10 3 true (3)
])
theorem kid12_part878_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid12_part878) = true := by rfl

def kid12_part879 : Audit := .split 16 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.split 17 (4,true) (byMove [
.cycle 33 1 false (3),
.cycle 29 7 false (2),
.cycle 31 11 false (2),
.cycle 0 19 true (0),
.last 19 (4,false),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 11 true (2),
.cycle 3 15 true (1),
.last 18 (4,false),
.cycle 0 21 true (0),
.cycle 6 12 true (2),
.cycle 35 17 false (2),
.cycle 25 5 false (2),
.cycle 39 1 false (7),
.last 19 (4,false),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 4 29 true (1),
.last 18 (4,false),
.cycle 10 8 true (2)
]),
.cycle 0 29 false (4),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 12 10 true (2),
.cycle 3 14 true (1),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 32 (4,true),
.last 19 (4,true),
.cycle 10 8 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (4,true),
.cycle 12 10 true (2),
.cycle 17 1 true (5),
.cycle 0 21 true (0),
.cycle 8 10 true (2),
.cycle 6 14 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (4,true),
.last 25 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 33 (4,true),
.cycle 17 1 true (5),
.cycle 13 6 true (2)
]),
.cycle 0 20 true (0),
.cycle 6 11 true (2),
.cycle 15 2 true (3),
.cycle 11 6 true (2),
.cycle 5 25 true (1),
.split 17 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 29 7 false (2),
.cycle 31 11 false (2),
.cycle 8 11 true (2),
.last 19 (4,false),
.last 19 (4,false),
.cycle 6 25 true (2),
.cycle 13 7 true (2),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.last 19 (4,false),
.last 19 (4,false),
.cycle 12 6 true (2),
.cycle 29 11 false (2),
.cycle 25 5 false (2),
.cycle 5 13 true (1),
.last 19 (4,false),
.last 19 (4,false),
.cycle 12 12 true (2),
.cycle 9 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.last 19 (4,false),
.cycle 16 2 true (3)
]),
.cycle 20 10 true (-3),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 32 true (0),
.split 17 (4,false) (byMove [
.cycle 12 12 true (2),
.cycle 9 9 true (2),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 11 true (2),
.cycle 3 15 true (1),
.cycle 17 1 true (5),
.cycle 0 21 true (0),
.cycle 6 12 true (2),
.cycle 15 3 true (3),
.cycle 11 7 true (2),
.last 31 (4,true),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.last 32 (4,true),
.cycle 17 1 true (5),
.cycle 10 8 true (2)
]),
.cycle 10 7 true (2)
])
theorem kid12_part879_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid12_part879) = true := by rfl

def kid12_part880 : Audit := .split 23 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 5 21 true (1),
.cycle 5 25 true (1),
.cycle 8 17 true (2),
.split 24 (4,true) (byMove [
.cycle 41 1 false (3),
.cycle 0 31 true (0),
.cycle 0 33 true (0),
.cycle 6 23 true (2),
.last 26 (4,false),
.last 26 (4,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 3 31 true (1),
.last 25 (4,false),
.cycle 4 31 true (1),
.cycle 5 25 true (1),
.cycle 0 39 true (0),
.cycle 37 5 false (2),
.cycle 0 29 true (0),
.last 26 (4,false),
.last 26 (4,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 4 21 true (1),
.last 25 (4,false),
.cycle 5 21 true (1)
]),
.cycle 50 1 false (0),
.cycle 12 12 true (2),
.cycle 1 41 true (1),
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.split 24 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 11 15 true (2),
.last 25 (4,false),
.cycle 10 15 true (2),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 13 12 true (2),
.last 34 (4,false),
.last 25 (4,false),
.last 34 (4,false),
.cycle 8 17 true (2),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.cycle 4 21 true (1),
.last 25 (4,false),
.cycle 5 21 true (1),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 0 42 true (0),
.last 25 (4,false),
.last 42 (4,false)
]),
.cycle 4 31 true (1),
.cycle 6 23 true (2),
.cycle 22 2 true (4),
.cycle 19 6 true (3),
.cycle 5 19 true (1),
.split 24 (4,true) (byMove [
.cycle 81 1 false (13),
.cycle 5 31 true (1),
.cycle 5 35 true (1),
.cycle 8 23 true (2),
.last 26 (4,false),
.last 26 (4,false),
.cycle 6 19 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 8, 1, 8, 8, 16, 64],80⟩,
.cycle 7 23 true (2),
.cycle 5 35 true (1),
.last 27 (4,false),
.last 26 (4,false),
.cycle 19 6 true (3),
.cycle 47 11 false (2),
.cycle 37 5 false (2),
.cycle 5 27 true (1),
.last 26 (4,false),
.last 26 (4,false),
.cycle 6 19 true (2),
.cycle 9 19 true (2),
.cycle 6 27 true (2),
.cycle 11 14 true (2),
.last 27 (4,false),
.cycle 23 2 true (4)
]),
.cycle 37 1 false (-1),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.split 24 (4,true) (byMove [
.last 36 (4,false),
.cycle 9 16 true (2),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.last 28 (4,false),
.last 26 (4,false),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.last 35 (4,false),
.cycle 3 22 true (1),
.last 25 (4,false),
.cycle 4 22 true (1),
.cycle 6 19 true (2),
.last 27 (4,false),
.last 31 (4,false),
.cycle 11 14 true (2),
.last 28 (4,false),
.cycle 23 2 true (5),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 11 15 true (2),
.last 25 (4,false),
.cycle 10 15 true (2)
]),
.cycle 10 15 true (2)
])
theorem kid12_part880_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid12_part880) = true := by rfl

def kid12_part882 : Audit := .cycle 0 15 true (0)
theorem kid12_part882_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid12_part882) = true := by rfl

def kid12_part883 : Audit := .split 30 (5,true) (byMove [
.cycle 5 45 true (1),
.cycle 9 36 true (1),
.cycle 6 44 true (1),
.cycle 0 36 true (0),
.cycle 0 48 true (0),
.cycle 15 24 true (-1),
.cycle 6 25 true (1),
.cycle 1 32 true (1),
.cycle 31 10 true (4),
.cycle 17 14 true (1),
.cycle 0 35 true (0),
.last 34 (4,false),
.cycle 5 104 true (1),
.cycle 29 2 true (3),
.cycle 26 6 true (2),
.cycle 5 45 true (1),
.cycle 11 32 true (1),
.last 46 (4,false),
.cycle 0 68 true (0),
.cycle 1 32 true (1),
.cycle 2 35 true (1),
.cycle 0 45 true (0),
.last 49 (4,false),
.cycle 5 80 true (1)
])
theorem kid12_part883_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid12_part883) = true := by rfl

def kid12_part884 : Audit := .cycle 19 5 false (2)
theorem kid12_part884_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid12_part884) = true := by rfl

def kid12_part885 : Audit := .cycle 8 5 true (2)
theorem kid12_part885_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid12_part885) = true := by rfl

def kid12_part886 : Audit := .split 13 (4,false) (byMove [
.cycle 16 1 false (2),
.last 27 (5,true),
.cycle 22 1 false (-2),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 14 (5,true),
.cycle 0 30 true (0),
.cycle 0 17 true (0),
.last 23 (5,true),
.cycle 25 1 false (1),
.cycle 17 1 true (3),
.last 16 (5,true),
.cycle 16 6 false (2),
.last 15 (5,true),
.last 17 (5,true),
.cycle 17 1 false (3),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 49 (5,true),
.cycle 0 17 true (0),
.last 22 (5,true),
.cycle 0 19 true (0),
.cycle 21 1 true (-1),
.cycle 16 3 false (0)
])
theorem kid12_part886_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid12_part886) = true := by rfl

def kid12_part887 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 9 14 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 16 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 0 23 true (0),
.last 13 (4,false),
.last 14 (4,false),
.cycle 20 5 false (2),
.cycle 21 2 true (0),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 18 (4,false)
])
theorem kid12_part887_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid12_part887) = true := by rfl

def kid12_part888 : Audit := .split 23 (5,true) (byMove [
.cycle 0 27 true (0),
.cycle 6 21 true (2),
.cycle 6 25 true (2),
.cycle 8 17 true (2),
.cycle 8 17 true (2),
.last 27 (4,false),
.cycle 12 12 true (2),
.cycle 1 41 true (1),
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 26 (4,false),
.cycle 6 23 true (2),
.cycle 22 2 true (4),
.cycle 19 6 true (3),
.cycle 5 19 true (1),
.cycle 6 19 true (2),
.last 27 (4,false),
.cycle 0 35 true (0),
.cycle 9 15 true (2),
.cycle 6 19 true (2),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 10 15 true (2)
])
theorem kid12_part888_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid12_part888) = true := by rfl

def kid12_part889 : Audit := .cycle 9 3 true (3)
theorem kid12_part889_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid12_part889) = true := by rfl

def kid12_part890 : Audit := .cycle 7 5 true (2)
theorem kid12_part890_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid12_part890) = true := by rfl

def kid12_part891 : Audit := .cycle 0 13 true (0)
theorem kid12_part891_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid12_part891) = true := by rfl

def kid12_part892 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 13 1 true (5),
.last 16 (5,true),
.cycle 8 6 true (2),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.last 21 (5,true),
.cycle 33 1 false (7),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 29 (5,true),
.cycle 13 1 true (5),
.cycle 10 4 true (3)
])
theorem kid12_part892_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid12_part892) = true := by rfl

def kid12_part893 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 33 true (0),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 17 true (2),
.cycle 3 19 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 17 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 42 true (0),
.last 13 (4,false),
.cycle 10 3 true (3)
])
theorem kid12_part893_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid12_part893) = true := by rfl

def kid12_part894 : Audit := .split 16 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 8 true (2),
.cycle 6 12 true (2),
.cycle 0 18 true (0),
.cycle 6 12 true (2),
.last 27 (4,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 12 10 true (2),
.cycle 3 14 true (1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 6 11 true (2),
.cycle 15 2 true (3),
.cycle 12 6 true (2),
.cycle 5 25 true (1),
.cycle 11 6 true (2),
.last 27 (4,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 0 32 true (0),
.last 17 (4,false),
.cycle 10 7 true (2)
])
theorem kid12_part894_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid12_part894) = true := by rfl

def kid12_part895 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 27 15 false (2),
.cycle 23 7 false (2),
.cycle 8 7 true (2),
.cycle 25 11 false (1),
.last 27 (4,false),
.cycle 12 12 true (2),
.cycle 1 23 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 6 11 true (2),
.last 16 (4,false),
.cycle 6 13 true (2),
.cycle 12 2 true (2),
.cycle 14 6 true (1),
.cycle 5 9 true (1),
.cycle 23 11 false (2),
.last 27 (4,false),
.cycle 0 25 true (0),
.cycle 9 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 17 (4,false),
.cycle 10 5 true (2)
])
theorem kid12_part895_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid12_part895) = true := by rfl

def kid12_part896 : Audit := .split 15 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 21 7 false (2),
.cycle 25 11 false (2),
.cycle 8 9 true (1),
.cycle 19 5 false (2),
.last 20 (4,false),
.cycle 12 12 true (1),
.cycle 1 35 true (1),
.cycle 12 11 true (1),
.cycle 0 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,false),
.cycle 12 17 true (1),
.cycle 14 2 true (2),
.cycle 12 6 true (1),
.cycle 5 11 true (1),
.cycle 19 5 false (2),
.last 20 (4,false),
.cycle 0 27 true (0),
.cycle 12 9 true (1),
.cycle 12 13 true (1),
.cycle 0 17 true (0),
.last 23 (4,false),
.cycle 12 9 true (1)
])
theorem kid12_part896_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid12_part896) = true := by rfl

def kid12_part897 : Audit := .cycle 5 7 true (1)
theorem kid12_part897_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid12_part897) = true := by rfl

def kid12_part898 : Audit := .split 13 (4,false) (byMove [
.last 32 (5,true),
.last 25 (5,true),
.cycle 22 1 false (-2),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.last 14 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.cycle 15 1 false (-1),
.last 14 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 5 9 true (1),
.cycle 15 3 false (1),
.last 14 (5,true)
])
theorem kid12_part898_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid12_part898) = true := by rfl

def kid12_part899 : Audit := .split 12 (5,true) (byMove [
.cycle 16 11 true (2),
.cycle 9 32 true (1),
.cycle 31 1 false (1),
.cycle 20 1 false (6),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 13 10 true (2),
.cycle 3 55 true (0),
.last 15 (4,false),
.last 16 (4,false),
.cycle 13 17 true (1),
.cycle 18 2 true (2),
.cycle 5 9 true (1),
.cycle 5 15 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.cycle 0 27 true (0),
.cycle 11 2 true (2),
.cycle 10 5 true (2)
])
theorem kid12_part899_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid12_part899) = true := by rfl

def kid12_part900 : Audit := .split 22 (5,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.last 41 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 13 10 true (3),
.cycle 3 20 true (1),
.last 23 (4,false),
.last 24 (4,false),
.cycle 6 17 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 31 true (1),
.cycle 11 12 true (3),
.last 46 (4,false),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 38 true (0),
.last 23 (4,false),
.cycle 10 13 true (3)
])
theorem kid12_part900_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid12_part900) = true := by rfl

def kid12_part901 : Audit := .cycle 9 3 true (3)
theorem kid12_part901_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid12_part901) = true := by rfl

def kid12_part902 : Audit := .cycle 6 7 true (2)
theorem kid12_part902_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid12_part902) = true := by rfl

def kid12_part903 : Audit := .cycle 0 13 true (0)
theorem kid12_part903_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid12_part903) = true := by rfl

def kid12_part904 : Audit := .split 13 (4,false) (byMove [
.last 24 (5,true),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.last 16 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 19 (5,true),
.last 26 (5,true),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 27 (5,true),
.cycle 13 1 true (5),
.cycle 10 4 true (3)
])
theorem kid12_part904_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid12_part904) = true := by rfl

def kid12_part905 : Audit := .split 12 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (3),
.last 20 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 10 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 21 true (1),
.cycle 11 2 true (3),
.last 20 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.last 13 (4,false),
.cycle 10 3 true (3)
])
theorem kid12_part905_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid12_part905) = true := by rfl

def kid12_part881 : Audit := .split 11 (4,true) (byMove [(kid12_part882),(kid12_part883),(kid12_part884),(kid12_part885),(kid12_part886),(kid12_part887),(kid12_part888),(kid12_part889),(kid12_part890),(kid12_part891),(kid12_part892),(kid12_part893),(kid12_part894),(kid12_part895),(kid12_part896),(kid12_part897),(kid12_part898),(kid12_part899),(kid12_part900),(kid12_part901),(kid12_part902),(kid12_part903),(kid12_part904),(kid12_part905)])

theorem kid12_part881_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid12_part881) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid12_part882),(kid12_part883),(kid12_part884),(kid12_part885),(kid12_part886),(kid12_part887),(kid12_part888),(kid12_part889),(kid12_part890),(kid12_part891),(kid12_part892),(kid12_part893),(kid12_part894),(kid12_part895),(kid12_part896),(kid12_part897),(kid12_part898),(kid12_part899),(kid12_part900),(kid12_part901),(kid12_part902),(kid12_part903),(kid12_part904),(kid12_part905)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part882_checked

  · exact kid12_part888_checked

  · exact kid12_part894_checked

  · exact kid12_part900_checked

  · exact kid12_part883_checked

  · exact kid12_part889_checked

  · exact kid12_part895_checked

  · exact kid12_part901_checked

  · exact kid12_part884_checked

  · exact kid12_part890_checked

  · exact kid12_part896_checked

  · exact kid12_part902_checked

  · exact kid12_part885_checked

  · exact kid12_part891_checked

  · exact kid12_part897_checked

  · exact kid12_part903_checked

  · exact kid12_part886_checked

  · exact kid12_part892_checked

  · exact kid12_part898_checked

  · exact kid12_part904_checked

  · exact kid12_part887_checked

  · exact kid12_part893_checked

  · exact kid12_part899_checked

  · exact kid12_part905_checked

def kid12_part906 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 36 true (1),
.cycle 19 5 false (2),
.cycle 8 5 true (2),
.split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.last 27 (4,false),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.last 13 (4,false),
.last 15 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 42 1 false (4),
.last 13 (4,false),
.last 17 (4,false),
.cycle 20 5 false (2),
.cycle 23 9 false (1),
.cycle 8 7 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 15 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.last 15 (4,false)
]),
.cycle 15 1 false (-1),
.cycle 11 12 true (2),
.cycle 9 3 true (3),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 34 true (0),
.last 13 (4,false),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 12 true (2),
.last 22 (4,false),
.last 13 (4,false),
.last 33 (4,false),
.cycle 8 5 true (2),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 13 (4,false),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 30 true (0),
.last 13 (4,false),
.cycle 10 3 true (3)
]),
.cycle 33 1 false (7),
.cycle 6 11 true (2),
.cycle 11 2 true (2),
.cycle 12 6 true (1),
.cycle 5 7 true (1),
.split 12 (4,true) (byMove [
.cycle 0 25 true (0),
.last 33 (4,false),
.cycle 30 1 false (0),
.cycle 20 1 false (6),
.last 13 (4,false),
.last 15 (4,false),
.cycle 6 7 true (2),
.last 19 (4,false),
.cycle 7 11 true (2),
.cycle 0 37 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 13 6 true (1),
.cycle 21 11 false (2),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.last 13 (4,false),
.last 15 (4,false),
.cycle 6 7 true (2),
.cycle 9 7 true (2),
.cycle 6 15 true (2),
.cycle 11 14 true (2),
.last 15 (4,false),
.cycle 11 2 true (2)
]),
.cycle 15 1 false (-1),
.cycle 0 23 true (0),
.cycle 9 3 true (3),
.cycle 6 7 true (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.last 24 (4,false),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 18 (4,false),
.cycle 6 7 true (2),
.last 15 (4,false),
.last 19 (4,false),
.cycle 11 14 true (2),
.last 15 (4,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 15 true (3),
.last 13 (4,false),
.cycle 10 3 true (3)
]),
.cycle 10 3 true (3)
])
theorem kid12_part906_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid12_part906) = true := by rfl

def kid12_part907 : Audit := .cycle 0 11 true (0)
theorem kid12_part907_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid12_part907) = true := by rfl

def kid12_part908 : Audit := .cycle 1 10 true (1)
theorem kid12_part908_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid12_part908) = true := by rfl

def kid12_part909 : Audit := .cycle 2 9 true (1)
theorem kid12_part909_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid12_part909) = true := by rfl

def kid12_part910 : Audit := .split 24 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 8 18 true (2),
.split 25 (4,true) (byMove [
.cycle 55 1 false (3),
.cycle 4 24 true (1),
.cycle 4 26 true (1),
.cycle 6 24 true (2),
.last 27 (4,false),
.last 27 (4,false),
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 3 32 true (1),
.last 26 (4,false),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 4 32 true (1),
.cycle 45 5 false (2),
.cycle 0 30 true (0),
.last 27 (4,false),
.last 27 (4,false),
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.last 26 (4,false),
.cycle 0 28 true (0)
]),
.cycle 67 1 false (3),
.cycle 13 12 true (3),
.cycle 9 16 true (3),
.cycle 7 18 true (2),
.cycle 0 26 true (0),
.split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 11 15 true (3),
.last 26 (4,false),
.cycle 10 16 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 14 12 true (3),
.last 35 (4,false),
.last 26 (4,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 16777216, 512, 128, 256, 32768, 1048580, 16777216, 512, 524288, 1048576, 2097152, 8390656, 16777216, 2097152, 128, 256, 32768, 81920, 16777216, 512, 16777216],[4, 2048, 2048, 1, 32, 16, 16384, 2048, 2048, 4096, 131072, 65536, 1048576, 8388608, 2048, 262144, 8388608, 4194304, 16384, 2048, 2048, 4096, 131072, 65536, 16777216],23282704⟩,
.cycle 8 18 true (2),
.cycle 6 22 true (2),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.last 26 (4,false),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 0 43 true (0),
.last 26 (4,false),
.cycle 10 16 true (3)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 64, 8, 64],[4, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 6 24 true (2),
.cycle 23 2 true (5),
.cycle 20 6 true (4),
.cycle 5 20 true (1),
.split 25 (4,true) (byMove [
.cycle 151 1 false (19),
.cycle 12 16 true (3),
.cycle 12 18 true (3),
.cycle 8 24 true (2),
.last 27 (4,false),
.last 27 (4,false),
.cycle 6 20 true (2),
.cycle 9 20 true (3),
.cycle 7 24 true (2),
.cycle 5 36 true (1),
.last 28 (4,false),
.last 27 (4,false),
.cycle 20 6 true (4),
.cycle 51 11 false (2),
.cycle 45 5 false (2),
.cycle 5 28 true (1),
.last 27 (4,false),
.last 27 (4,false),
.cycle 6 20 true (2),
.cycle 9 20 true (3),
.cycle 6 28 true (2),
.cycle 12 14 true (3),
.last 28 (4,false),
.cycle 24 2 true (5)
]),
.cycle 5 32 true (1),
.cycle 0 36 true (0),
.cycle 9 16 true (3),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.split 25 (4,true) (byMove [
.last 37 (4,false),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 29 (4,false),
.last 27 (4,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.last 36 (4,false),
.cycle 3 23 true (1),
.last 26 (4,false),
.last 44 (4,false),
.cycle 6 20 true (2),
.last 28 (4,false),
.last 32 (4,false),
.cycle 12 14 true (3),
.last 29 (4,false),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 11 15 true (3),
.last 26 (4,false),
.cycle 10 16 true (3)
]),
.cycle 10 16 true (3)
])
theorem kid12_part910_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid12_part910) = true := by rfl

def kid12_part912 : Audit := .split 22 (5,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 14 true (3),
.cycle 6 18 true (2),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 60 1 false (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 13 10 true (3),
.cycle 3 20 true (1),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 12, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 6 17 true (2),
.cycle 21 2 true (5),
.cycle 18 6 true (4),
.cycle 5 31 true (1),
.last 23 (4,true),
.last 26 (4,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 0 38 true (0),
.cycle 11 12 true (3),
.cycle 10 13 true (3)
])
theorem kid12_part912_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid12_part912) = true := by rfl

def kid12_part913 : Audit := .cycle 9 3 true (3)
theorem kid12_part913_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid12_part913) = true := by rfl

def kid12_part914 : Audit := .cycle 6 7 true (2)
theorem kid12_part914_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid12_part914) = true := by rfl

def kid12_part915 : Audit := .cycle 0 13 true (0)
theorem kid12_part915_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid12_part915) = true := by rfl

def kid12_part916 : Audit := .split 12 (4,true) (byMove [
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 23 1 false (1),
.cycle 10 3 true (4),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.last 25 (5,true),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 26 (5,true),
.cycle 11 2 true (4),
.cycle 10 3 true (4)
])
theorem kid12_part916_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid12_part916) = true := by rfl

def kid12_part917 : Audit := .split 12 (5,true) (byMove [
.cycle 12 11 true (2),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 12 10 true (3),
.cycle 3 10 true (1),
.cycle 10 4 true (4),
.cycle 10 3 true (4),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 21 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 28 true (0),
.cycle 11 2 true (4),
.cycle 10 3 true (4)
])
theorem kid12_part917_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid12_part917) = true := by rfl

def kid12_part918 : Audit := .cycle 0 12 true (0)
theorem kid12_part918_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid12_part918) = true := by rfl

def kid12_part919 : Audit := .cycle 1 11 true (1)
theorem kid12_part919_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid12_part919) = true := by rfl

def kid12_part920 : Audit := .split 21 (5,true) (byMove [
.cycle 12 11 true (4),
.cycle 9 13 true (3),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 10 14 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 12 10 true (4),
.cycle 3 19 true (1),
.last 34 (4,true),
.cycle 10 12 true (4),
.cycle 6 16 true (2),
.cycle 20 2 true (6),
.cycle 17 6 true (5),
.cycle 5 30 true (1),
.last 22 (4,true),
.last 25 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 0 37 true (0),
.cycle 11 11 true (4),
.cycle 10 12 true (4)
])
theorem kid12_part920_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid12_part920) = true := by rfl

def kid12_part921 : Audit := .cycle 3 9 true (1)
theorem kid12_part921_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid12_part921) = true := by rfl

def kid12_part922 : Audit := .cycle 11 1 true (5)
theorem kid12_part922_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid12_part922) = true := by rfl

def kid12_part923 : Audit := .cycle 10 2 true (4)
theorem kid12_part923_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid12_part923) = true := by rfl

def kid12_part924 : Audit := .cycle 6 6 true (2)
theorem kid12_part924_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid12_part924) = true := by rfl

def kid12_part925 : Audit := .split 13 (5,true) (byMove [
.cycle 12 11 true (3),
.cycle 9 5 true (3),
.cycle 6 9 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 21 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 10 true (4),
.cycle 3 11 true (1),
.cycle 6 11 true (2),
.cycle 10 4 true (4),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 12 6 true (3),
.cycle 5 22 true (1),
.last 14 (4,true),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 29 true (0),
.cycle 11 3 true (4),
.cycle 10 4 true (4)
])
theorem kid12_part925_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid12_part925) = true := by rfl

def kid12_part926 : Audit := .split 17 (5,true) (byMove [
.cycle 13 11 true (3),
.cycle 9 9 true (3),
.cycle 6 13 true (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 25 8 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 13 10 true (3),
.cycle 3 15 true (1),
.cycle 0 21 true (0),
.cycle 14 6 true (3),
.cycle 6 12 true (2),
.cycle 16 2 true (4),
.cycle 12 6 true (3),
.cycle 5 26 true (1),
.last 18 (4,true),
.last 22 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 0 33 true (0),
.cycle 11 7 true (3),
.cycle 10 8 true (3)
])
theorem kid12_part926_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid12_part926) = true := by rfl

def kid12_part927 : Audit := .split 24 (5,true) (byMove [
.cycle 0 28 true (0),
.last 27 (4,true),
.last 31 (4,true),
.cycle 8 18 true (2),
.last 25 (4,true),
.cycle 67 1 false (3),
.cycle 13 12 true (3),
.cycle 9 16 true (3),
.cycle 7 18 true (2),
.cycle 0 26 true (0),
.last 25 (4,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 36, 16, 64],[4, 32, 32, 1, 64, 32, 64],64⟩,
.cycle 6 24 true (2),
.cycle 23 2 true (5),
.cycle 20 6 true (4),
.cycle 5 20 true (1),
.last 25 (4,true),
.last 28 (4,true),
.cycle 0 36 true (0),
.cycle 9 16 true (3),
.cycle 6 20 true (2),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 10 16 true (3)
])
theorem kid12_part927_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid12_part927) = true := by rfl

def kid12_part928 : Audit := .split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 9 7 true (3),
.cycle 6 15 true (2),
.cycle 8 6 true (2),
.cycle 17 1 false (-1),
.last 13 (5,true),
.last 24 (5,true),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 49 1 false (9),
.last 13 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.last 18 (5,true),
.cycle 5 8 true (1),
.cycle 17 1 false (-1),
.last 13 (5,true),
.last 23 (5,true),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.last 13 (5,true)
])
theorem kid12_part928_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid12_part928) = true := by rfl

def kid12_part929 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 15 (4,true),
.last 19 (4,true),
.cycle 8 6 true (2),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 12 12 true (3),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 4 true (4),
.cycle 6 12 true (2),
.cycle 12 2 true (3),
.cycle 12 6 true (2),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 24 true (0),
.cycle 9 4 true (3),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 4 true (4)
])
theorem kid12_part929_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid12_part929) = true := by rfl

def kid12_part930 : Audit := .cycle 0 12 true (0)
theorem kid12_part930_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid12_part930) = true := by rfl

def kid12_part931 : Audit := .cycle 1 11 true (1)
theorem kid12_part931_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid12_part931) = true := by rfl

def kid12_part932 : Audit := .cycle 2 10 true (1)
theorem kid12_part932_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid12_part932) = true := by rfl

def kid12_part933 : Audit := .split 25 (5,true) (byMove [
.cycle 0 29 true (0),
.last 28 (4,true),
.last 32 (4,true),
.cycle 8 19 true (2),
.last 26 (4,true),
.cycle 0 35 true (0),
.cycle 14 12 true (4),
.cycle 9 17 true (3),
.cycle 7 19 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 10 17 true (4),
.cycle 6 25 true (2),
.cycle 24 2 true (6),
.cycle 21 6 true (5),
.cycle 5 21 true (1),
.last 26 (4,true),
.last 29 (4,true),
.cycle 0 37 true (0),
.cycle 9 17 true (3),
.cycle 6 21 true (2),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 10 17 true (4)
])
theorem kid12_part933_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid12_part933) = true := by rfl

def kid12_part934 : Audit := .cycle 11 1 true (5)
theorem kid12_part934_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid12_part934) = true := by rfl

def kid12_part935 : Audit := .cycle 10 2 true (4)
theorem kid12_part935_checked : zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid12_part935) = true := by rfl

def kid12_part911 : Audit := .split 11 (4,false) (byMove [(kid12_part912),(kid12_part913),(kid12_part914),(kid12_part915),(kid12_part916),(kid12_part917),(kid12_part918),(kid12_part919),(kid12_part920),(kid12_part921),(kid12_part922),(kid12_part923),(kid12_part924),(kid12_part925),(kid12_part926),(kid12_part927),(kid12_part928),(kid12_part929),(kid12_part930),(kid12_part931),(kid12_part932),(kid12_part933),(kid12_part934),(kid12_part935)])

theorem kid12_part911_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid12_part911) = true := by

  change (zipQueryOK 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid12_part912),(kid12_part913),(kid12_part914),(kid12_part915),(kid12_part916),(kid12_part917),(kid12_part918),(kid12_part919),(kid12_part920),(kid12_part921),(kid12_part922),(kid12_part923),(kid12_part924),(kid12_part925),(kid12_part926),(kid12_part927),(kid12_part928),(kid12_part929),(kid12_part930),(kid12_part931),(kid12_part932),(kid12_part933),(kid12_part934),(kid12_part935)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part912_checked

  · exact kid12_part918_checked

  · exact kid12_part924_checked

  · exact kid12_part930_checked

  · exact kid12_part913_checked

  · exact kid12_part919_checked

  · exact kid12_part925_checked

  · exact kid12_part931_checked

  · exact kid12_part914_checked

  · exact kid12_part920_checked

  · exact kid12_part926_checked

  · exact kid12_part932_checked

  · exact kid12_part915_checked

  · exact kid12_part921_checked

  · exact kid12_part927_checked

  · exact kid12_part933_checked

  · exact kid12_part916_checked

  · exact kid12_part922_checked

  · exact kid12_part928_checked

  · exact kid12_part934_checked

  · exact kid12_part917_checked

  · exact kid12_part923_checked

  · exact kid12_part929_checked

  · exact kid12_part935_checked

def kid12_part936 : Audit := .cycle 10 1 true (4)
theorem kid12_part936_checked : zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid12_part936) = true := by rfl

def kid12_part816 : Audit := .split 10 (5,false) (byMove [(kid12_part817),(kid12_part818),(kid12_part819),(kid12_part820),(kid12_part821),(kid12_part846),(kid12_part847),(kid12_part848),(kid12_part849),(kid12_part850),(kid12_part851),(kid12_part876),(kid12_part877),(kid12_part878),(kid12_part879),(kid12_part880),(kid12_part881),(kid12_part906),(kid12_part907),(kid12_part908),(kid12_part909),(kid12_part910),(kid12_part911),(kid12_part936)])

theorem kid12_part816_checked : zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (kid12_part816) = true := by

  change (zipQueryOK 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 2354 (refine (refine (childRC ⟨true,false,0⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid12_part817),(kid12_part818),(kid12_part819),(kid12_part820),(kid12_part821),(kid12_part846),(kid12_part847),(kid12_part848),(kid12_part849),(kid12_part850),(kid12_part851),(kid12_part876),(kid12_part877),(kid12_part878),(kid12_part879),(kid12_part880),(kid12_part881),(kid12_part906),(kid12_part907),(kid12_part908),(kid12_part909),(kid12_part910),(kid12_part911),(kid12_part936)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part817_checked

  · exact kid12_part847_checked

  · exact kid12_part877_checked

  · exact kid12_part907_checked

  · exact kid12_part818_checked

  · exact kid12_part848_checked

  · exact kid12_part878_checked

  · exact kid12_part908_checked

  · exact kid12_part819_checked

  · exact kid12_part849_checked

  · exact kid12_part879_checked

  · exact kid12_part909_checked

  · exact kid12_part820_checked

  · exact kid12_part850_checked

  · exact kid12_part880_checked

  · exact kid12_part910_checked

  · exact kid12_part821_checked

  · exact kid12_part851_checked

  · exact kid12_part881_checked

  · exact kid12_part911_checked

  · exact kid12_part846_checked

  · exact kid12_part876_checked

  · exact kid12_part906_checked

  · exact kid12_part936_checked

def kid12 : Audit := .split 9 (1,true) (byMove [(kid12_part1),(kid12_part2),(kid12_part3),(kid12_part4),(kid12_part5),(kid12_part102),(kid12_part199),(kid12_part200),(kid12_part201),(kid12_part202),(kid12_part203),(kid12_part324),(kid12_part445),(kid12_part446),(kid12_part447),(kid12_part448),(kid12_part449),(kid12_part570),(kid12_part691),(kid12_part692),(kid12_part693),(kid12_part694),(kid12_part695),(kid12_part816)])

theorem check12 : zipCheck 2354 (childRC ⟨true,false,0⟩) (kid12) = true := by

  change (zipQueryOK 2354 (childRC ⟨true,false,0⟩) 9 (1,true) && allMoves (fun mv => zipCheck 2354 (refine (childRC ⟨true,false,0⟩) (1,true) (some mv)) (byMove [(kid12_part1),(kid12_part2),(kid12_part3),(kid12_part4),(kid12_part5),(kid12_part102),(kid12_part199),(kid12_part200),(kid12_part201),(kid12_part202),(kid12_part203),(kid12_part324),(kid12_part445),(kid12_part446),(kid12_part447),(kid12_part448),(kid12_part449),(kid12_part570),(kid12_part691),(kid12_part692),(kid12_part693),(kid12_part694),(kid12_part695),(kid12_part816)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid12_part1_checked

  · exact kid12_part199_checked

  · exact kid12_part445_checked

  · exact kid12_part691_checked

  · exact kid12_part2_checked

  · exact kid12_part200_checked

  · exact kid12_part446_checked

  · exact kid12_part692_checked

  · exact kid12_part3_checked

  · exact kid12_part201_checked

  · exact kid12_part447_checked

  · exact kid12_part693_checked

  · exact kid12_part4_checked

  · exact kid12_part202_checked

  · exact kid12_part448_checked

  · exact kid12_part694_checked

  · exact kid12_part5_checked

  · exact kid12_part203_checked

  · exact kid12_part449_checked

  · exact kid12_part695_checked

  · exact kid12_part102_checked

  · exact kid12_part324_checked

  · exact kid12_part570_checked

  · exact kid12_part816_checked

end BB6.Agent11Raw39RC
