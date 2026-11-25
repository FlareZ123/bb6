import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid14_part1 : Audit := .cycle 1 12 true (1)
theorem kid14_part1_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,0⟩)) (kid14_part1) = true := by rfl

def kid14_part2 : Audit := .cycle 0 12 true (0)
theorem kid14_part2_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,1⟩)) (kid14_part2) = true := by rfl

def kid14_part3 : Audit := .cycle 17 1 false (1)
theorem kid14_part3_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,2⟩)) (kid14_part3) = true := by rfl

def kid14_part4 : Audit := .cycle 0 15 true (0)
theorem kid14_part4_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,3⟩)) (kid14_part4) = true := by rfl

def kid14_part6 : Audit := .cycle 0 14 true (0)
theorem kid14_part6_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part6) = true := by rfl

def kid14_part7 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.cycle 17 9 false (1),
.cycle 0 18 true (-1),
.cycle 18 9 false (1),
.split 17 (5,true) (byMove [
.cycle 0 18 true (-1),
.cycle 18 9 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 9 false (1),
.last 18 (5,false),
.cycle 0 18 true (-1),
.cycle 18 9 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 9 false (3),
.last 18 (5,false),
.cycle 19 9 false (1),
.last 21 (5,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 0 22 true (-1),
.last 18 (5,false),
.cycle 28 9 false (2),
.cycle 1 17 true (-1),
.cycle 18 9 false (3),
.cycle 1 20 true (-1),
.cycle 0 22 true (-1),
.last 18 (5,false)
]),
.cycle 0 17 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 64, 64],[2, 15, 15, 1, 2, 64, 64],96⟩,
.cycle 19 9 false (3),
.cycle 17 9 false (3),
.cycle 1 17 true (-1),
.split 17 (5,false) (byMove [
.cycle 28 9 false (2),
.cycle 1 17 true (-1),
.cycle 18 9 false (3),
.cycle 1 20 true (-1),
.cycle 0 22 true (-1),
.last 19 (5,true),
.cycle 0 18 true (-1),
.cycle 1 56 true (-1),
.cycle 21 9 false (3),
.cycle 19 9 false (3),
.last 93 (5,true),
.cycle 17 1 true (3),
.cycle 24 9 false (2),
.cycle 14 4 true (2),
.cycle 0 20 true (-1),
.cycle 18 9 false (3),
.cycle 23 9 false (3),
.last 19 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 1, 64],[2, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 1 17 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 4, 64],[2, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 1 20 true (-1),
.cycle 0 22 true (-1),
.cycle 17 1 true (3)
]),
.cycle 17 9 false (2),
.cycle 1 20 true (-1),
.cycle 17 9 false (1),
.cycle 1 18 true (-1),
.cycle 1 22 true (-1),
.split 17 (5,true) (byMove [
.cycle 13 5 false (3),
.cycle 0 21 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 9 false (1),
.last 18 (5,false),
.cycle 1 18 true (-1),
.cycle 0 21 true (-1),
.cycle 18 9 false (2),
.cycle 0 19 true (-1),
.last 19 (5,false),
.last 19 (5,false),
.cycle 19 9 false (1),
.last 21 (5,false),
.cycle 1 20 true (-1),
.cycle 18 1 false (0),
.cycle 1 22 true (-1),
.last 18 (5,false),
.cycle 28 9 false (2),
.cycle 18 9 false (2),
.last 20 (5,false),
.cycle 0 19 true (-1),
.cycle 16 2 true (1),
.last 19 (5,false)
]),
.cycle 27 4 true (1),
.cycle 26 9 false (2),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.cycle 18 9 false (2),
.split 17 (5,false) (byMove [
.cycle 28 9 false (2),
.cycle 18 9 false (2),
.cycle 21 9 false (1),
.cycle 0 19 true (-1),
.cycle 16 2 true (2),
.last 18 (5,true),
.cycle 0 18 true (-1),
.cycle 36 9 false (2),
.cycle 37 9 false (3),
.cycle 3 15 true (-1),
.cycle 28 9 false (2),
.cycle 17 1 true (3),
.cycle 23 9 false (2),
.cycle 18 9 false (2),
.cycle 21 9 false (1),
.cycle 1 19 true (-1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 36 true (-1),
.cycle 27 4 true (1),
.cycle 26 9 false (2),
.cycle 1 20 true (-1),
.cycle 16 7 true (1),
.cycle 17 1 true (3)
])
])
theorem kid14_part7_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part7) = true := by rfl

def kid14_part8 : Audit := .cycle 13 1 false (-1)
theorem kid14_part8_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part8) = true := by rfl

def kid14_part9 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.last 16 (5,false),
.cycle 20 1 false (-2),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.last 16 (5,false)
]),
.cycle 0 15 true (0),
.cycle 0 30 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 1 18 true (0),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 32 1 false (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 25 1 false (-1),
.cycle 12 4 true (2),
.cycle 0 18 true (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 0 30 true (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.cycle 15 1 true (3)
]),
.cycle 19 1 false (-1),
.cycle 1 18 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 11 5 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 0 19 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 20 1 false (-2),
.last 19 (5,false),
.cycle 1 18 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 14 2 true (1),
.last 17 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 0 17 true (0),
.split 15 (5,false) (byMove [
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 14 2 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 0 31 true (0),
.cycle 0 34 true (0),
.cycle 3 13 true (0),
.cycle 1 19 true (0),
.cycle 15 1 true (3),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 1 17 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.cycle 15 1 true (3)
])
])
theorem kid14_part9_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part9) = true := by rfl

def kid14_part10 : Audit := .split 10 (4,true) (byMove [
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
.cycle 0 16 true (-1),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 15 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 9 3 false (1),
.last 15 (5,true)
]),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 15 1 false (1),
.cycle 24 1 false (4),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 12 1 false (2),
.last 13 (5,true),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 1 17 true (0),
.cycle 1 15 true (0),
.cycle 0 14 true (0),
.cycle 17 1 false (1),
.cycle 15 3 true (3),
.last 13 (5,true)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.last 19 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.last 19 (5,true),
.cycle 13 1 false (-1),
.last 17 (5,true),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.last 17 (5,true),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.cycle 1 19 true (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 19 true (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 7 6 true (0),
.cycle 0 31 true (0),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.cycle 9 4 true (0),
.last 13 (5,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 1 17 true (0),
.cycle 1 15 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.cycle 15 3 true (3),
.last 13 (5,true)
])
])
theorem kid14_part10_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part10) = true := by rfl

def kid14_part12 : Audit := .cycle 0 11 false (3)
theorem kid14_part12_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part12) = true := by rfl

def kid14_part13 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 24 (4,true),
.cycle 0 32 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 0 40 true (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.last 26 (4,true),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 24 (4,true),
.cycle 0 32 true (-2),
.cycle 12 9 false (1),
.last 26 (4,true),
.cycle 9 12 false (1),
.last 26 (4,true)
])
theorem kid14_part13_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part13) = true := by rfl

def kid14_part14 : Audit := .cycle 12 1 false (0)
theorem kid14_part14_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part14) = true := by rfl

def kid14_part15 : Audit := .cycle 11 1 false (-1)
theorem kid14_part15_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part15) = true := by rfl

def kid14_part16 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 13 false (3),
.cycle 0 34 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 19 1 true (1),
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
.last 18 (4,true)
])
theorem kid14_part16_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part16) = true := by rfl

def kid14_part17 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.cycle 1 25 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 16 1 true (2),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 0 18 true (-1),
.cycle 9 3 false (1),
.cycle 20 1 true (-2)
])
theorem kid14_part17_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part17) = true := by rfl

def kid14_part18 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 24 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 1 18 true (0),
.last 17 (5,false),
.cycle 1 16 true (0),
.last 17 (5,false),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 0 17 true (0),
.last 15 (5,false)
])
theorem kid14_part18_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part18) = true := by rfl

def kid14_part19 : Audit := .cycle 0 14 true (0)
theorem kid14_part19_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part19) = true := by rfl

def kid14_part20 : Audit := .cycle 12 1 false (2)
theorem kid14_part20_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part20) = true := by rfl

def kid14_part21 : Audit := .cycle 11 1 false (1)
theorem kid14_part21_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part21) = true := by rfl

def kid14_part22 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.cycle 17 1 true (3),
.cycle 11 5 false (1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 11 9 false (2),
.last 18 (4,true),
.cycle 9 4 true (0),
.cycle 17 1 true (3)
])
theorem kid14_part22_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part22) = true := by rfl

def kid14_part23 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 11 10 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 11 2 true (1),
.cycle 14 1 true (4),
.cycle 11 5 false (1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 24 (4,true),
.last 15 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part23_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part23) = true := by rfl

def kid14_part24 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.last 22 (4,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 true (-3),
.cycle 10 8 true (-3),
.cycle 11 5 false (0),
.last 18 (4,true),
.last 21 (4,true),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.last 22 (4,true),
.cycle 12 9 false (0),
.last 21 (4,true),
.cycle 9 7 false (1),
.last 22 (4,true)
])
theorem kid14_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part24) = true := by rfl

def kid14_part25 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 false (3),
.last 23 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 18 true (-1),
.last 23 (5,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 11 3 false (0),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 18 true (-1),
.cycle 1 13 false (3),
.last 22 (5,false),
.cycle 0 20 true (-1),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid14_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part25) = true := by rfl

def kid14_part26 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.last 19 (5,false),
.cycle 0 18 true (-1),
.last 19 (5,false),
.cycle 0 20 true (-1),
.cycle 0 17 true (-1),
.last 26 (5,false),
.last 26 (5,false),
.last 24 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 1 20 true (-1),
.last 19 (5,false),
.cycle 1 18 true (-1),
.last 19 (5,false),
.cycle 1 20 true (-1),
.cycle 28 4 true (1),
.last 29 (5,false),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.last 21 (5,false),
.last 17 (5,false)
])
theorem kid14_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part26) = true := by rfl

def kid14_part27 : Audit := .cycle 11 1 false (-1)
theorem kid14_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part27) = true := by rfl

def kid14_part28 : Audit := .split 12 (5,false) (byMove [
.last 20 (4,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 21 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 25 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.last 25 (4,true),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid14_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part28) = true := by rfl

def kid14_part29 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.last 18 (4,true),
.cycle 16 1 false (0),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 0 16 true (-1),
.last 22 (4,true),
.last 13 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid14_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part29) = true := by rfl

def kid14_part30 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.last 18 (5,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 24 (5,false),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 16 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.last 23 (5,false),
.cycle 1 16 true (0),
.last 18 (5,false),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 0 17 true (0),
.last 15 (5,false)
])
theorem kid14_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part30) = true := by rfl

def kid14_part31 : Audit := .cycle 0 14 true (0)
theorem kid14_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part31) = true := by rfl

def kid14_part32 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 false (3),
.cycle 11 10 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 18 2 false (0),
.cycle 19 1 false (-1),
.last 23 (4,true),
.cycle 1 23 true (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 18 2 true (-1),
.last 24 (4,true),
.cycle 16 5 false (2),
.last 22 (4,true),
.last 25 (4,true),
.cycle 20 1 false (-2),
.cycle 18 2 false (0),
.cycle 19 1 false (-1),
.last 23 (4,true),
.cycle 1 23 true (-1),
.cycle 11 9 false (2),
.last 25 (4,true),
.cycle 9 11 false (2),
.last 24 (4,true)
])
theorem kid14_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part32) = true := by rfl

def kid14_part33 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.last 19 (5,false),
.cycle 0 18 true (0),
.last 19 (5,false),
.cycle 1 20 true (0),
.cycle 0 17 true (0),
.last 26 (5,false),
.last 26 (5,false),
.last 24 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 1 20 true (0),
.last 19 (5,false),
.cycle 1 18 true (0),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 1 21 true (0),
.last 17 (5,false)
])
theorem kid14_part33_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part33) = true := by rfl

def kid14_part34 : Audit := .cycle 9 2 true (0)
theorem kid14_part34_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part34) = true := by rfl

def kid14_part35 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.last 18 (4,true),
.cycle 16 1 false (-2),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 7 6 true (0),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 20 1 false (0),
.cycle 11 2 true (1),
.cycle 14 1 true (4),
.cycle 13 5 false (1),
.last 18 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.cycle 16 3 true (2),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.last 15 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part35_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part35) = true := by rfl

def kid14_part11 : Audit := .split 10 (5,true) (byMove [(kid14_part12),(kid14_part13),(kid14_part14),(kid14_part15),(kid14_part16),(kid14_part17),(kid14_part18),(kid14_part19),(kid14_part20),(kid14_part21),(kid14_part22),(kid14_part23),(kid14_part24),(kid14_part25),(kid14_part26),(kid14_part27),(kid14_part28),(kid14_part29),(kid14_part30),(kid14_part31),(kid14_part32),(kid14_part33),(kid14_part34),(kid14_part35)])

theorem kid14_part11_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part11) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part12),(kid14_part13),(kid14_part14),(kid14_part15),(kid14_part16),(kid14_part17),(kid14_part18),(kid14_part19),(kid14_part20),(kid14_part21),(kid14_part22),(kid14_part23),(kid14_part24),(kid14_part25),(kid14_part26),(kid14_part27),(kid14_part28),(kid14_part29),(kid14_part30),(kid14_part31),(kid14_part32),(kid14_part33),(kid14_part34),(kid14_part35)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part12_checked

  · exact kid14_part18_checked

  · exact kid14_part24_checked

  · exact kid14_part30_checked

  · exact kid14_part13_checked

  · exact kid14_part19_checked

  · exact kid14_part25_checked

  · exact kid14_part31_checked

  · exact kid14_part14_checked

  · exact kid14_part20_checked

  · exact kid14_part26_checked

  · exact kid14_part32_checked

  · exact kid14_part15_checked

  · exact kid14_part21_checked

  · exact kid14_part27_checked

  · exact kid14_part33_checked

  · exact kid14_part16_checked

  · exact kid14_part22_checked

  · exact kid14_part28_checked

  · exact kid14_part34_checked

  · exact kid14_part17_checked

  · exact kid14_part23_checked

  · exact kid14_part29_checked

  · exact kid14_part35_checked

def kid14_part36 : Audit := .cycle 7 4 true (1)
theorem kid14_part36_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part36) = true := by rfl

def kid14_part37 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 1 13 true (1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 0 17 true (-1),
.cycle 30 1 false (0),
.cycle 0 15 true (0),
.cycle 14 14 true (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1),
.cycle 15 8 false (1),
.cycle 1 17 true (-1),
.cycle 0 22 true (-2),
.cycle 1 15 true (0),
.cycle 0 32 true (-2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 1 13 true (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (9),
.cycle 1 28 true (0),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 7 8 true (1),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3)
]),
.cycle 15 7 false (1),
.cycle 1 19 true (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 0 17 true (0),
.split 13 (5,false) (byMove [
.last 18 (5,true),
.cycle 0 28 true (-1),
.cycle 0 19 true (-1),
.cycle 23 1 false (-1),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.last 14 (5,true),
.cycle 15 8 false (1),
.cycle 21 4 false (2),
.last 26 (5,true),
.cycle 23 1 false (-1),
.last 36 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.last 16 (5,true),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 28 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3)
])
])
theorem kid14_part37_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part37) = true := by rfl

def kid14_part38 : Audit := .cycle 0 12 true (0)
theorem kid14_part38_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part38) = true := by rfl

def kid14_part39 : Audit := .cycle 17 1 false (1)
theorem kid14_part39_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part39) = true := by rfl

def kid14_part40 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 13 1 true (3),
.cycle 12 1 true (2),
.cycle 16 7 false (0),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 3 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 30 1 true (4),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 13 1 true (3),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (5,true),
.last 25 (5,true),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.cycle 7 7 true (1),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.last 23 (5,true),
.cycle 10 3 true (2),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
]),
.cycle 7 6 true (1),
.cycle 1 21 true (-1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.split 12 (5,false) (byMove [
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 19 (5,true),
.cycle 9 4 true (1),
.last 14 (5,true),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 13 (5,true),
.cycle 16 7 false (0),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 16 3 false (0),
.last 14 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 18 (5,true),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 8 5 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
])
theorem kid14_part40_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part40) = true := by rfl

def kid14_part42 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 26 true (-2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 0 19 false (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 20 9 false (0),
.cycle 1 33 true (-2),
.cycle 21 7 false (2),
.cycle 1 16 true (1),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1)
])
theorem kid14_part42_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part42) = true := by rfl

def kid14_part43 : Audit := .cycle 0 14 true (0)
theorem kid14_part43_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part43) = true := by rfl

def kid14_part44 : Audit := .cycle 21 1 false (1)
theorem kid14_part44_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part44) = true := by rfl

def kid14_part45 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 20 1 false (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 35 1 false (1),
.cycle 27 1 false (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 1 20 true (0),
.cycle 22 1 false (0),
.cycle 1 20 true (0),
.cycle 20 1 false (0),
.cycle 1 18 true (0),
.last 19 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 1 21 true (0),
.cycle 0 19 true (0)
])
theorem kid14_part45_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part45) = true := by rfl

def kid14_part46 : Audit := .cycle 9 2 true (1)
theorem kid14_part46_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part46) = true := by rfl

def kid14_part47 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 9 4 true (0),
.cycle 11 2 true (0)
])
theorem kid14_part47_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part47) = true := by rfl

def kid14_part48 : Audit := .cycle 1 11 true (1)
theorem kid14_part48_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part48) = true := by rfl

def kid14_part49 : Audit := .cycle 0 14 true (0)
theorem kid14_part49_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part49) = true := by rfl

def kid14_part50 : Audit := .cycle 39 1 false (7)
theorem kid14_part50_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part50) = true := by rfl

def kid14_part51 : Audit := .cycle 0 12 true (0)
theorem kid14_part51_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part51) = true := by rfl

def kid14_part52 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 2 true (2),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 30 2 true (4),
.cycle 1 24 true (0),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 7 6 true (1),
.cycle 1 21 true (-1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part52_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part52) = true := by rfl

def kid14_part53 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 13 1 true (3),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 true (5),
.cycle 1 24 true (0),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 11 2 true (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
theorem kid14_part53_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part53) = true := by rfl

def kid14_part54 : Audit := .split 14 (4,true) (byMove [
.cycle 1 19 true (-1),
.cycle 21 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.cycle 15 5 false (-1),
.cycle 15 5 false (2),
.cycle 27 5 false (5),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 15 5 false (1),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 17 5 false (2),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 15 5 false (-1),
.cycle 11 4 true (0),
.cycle 1 20 true (0),
.cycle 1 17 true (0),
.cycle 18 5 false (2),
.last 16 (5,true),
.cycle 17 5 false (1)
])
theorem kid14_part54_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part54) = true := by rfl

def kid14_part55 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 15 (5,true),
.cycle 10 4 true (1),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 12 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 15 12 true (-2)
])
theorem kid14_part55_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part55) = true := by rfl

def kid14_part56 : Audit := .cycle 1 13 true (1)
theorem kid14_part56_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part56) = true := by rfl

def kid14_part57 : Audit := .cycle 18 1 false (0)
theorem kid14_part57_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part57) = true := by rfl

def kid14_part58 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (4,true),
.cycle 9 4 true (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 3 true (3),
.last 16 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid14_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part58) = true := by rfl

def kid14_part59 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.last 13 (4,true),
.cycle 16 1 false (4),
.cycle 17 1 false (-1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 16 1 false (0),
.last 14 (4,true),
.cycle 5 8 true (0),
.last 13 (4,true),
.cycle 14 3 true (2)
])
theorem kid14_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part59) = true := by rfl

def kid14_part60 : Audit := .cycle 1 11 true (1)
theorem kid14_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part60) = true := by rfl

def kid14_part61 : Audit := .cycle 7 4 true (1)
theorem kid14_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part61) = true := by rfl

def kid14_part62 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 2 13 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 2 13 true (1),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.cycle 1 19 true (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 13 true (1),
.cycle 2 12 true (1)
])
theorem kid14_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part62) = true := by rfl

def kid14_part63 : Audit := .cycle 0 12 true (0)
theorem kid14_part63_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part63) = true := by rfl

def kid14_part64 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 13 2 true (1),
.cycle 0 13 true (0),
.cycle 13 2 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 2 true (4),
.cycle 3 9 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part64_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part64) = true := by rfl

def kid14_part65 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 14 1 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 true (5),
.cycle 3 9 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
theorem kid14_part65_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part65) = true := by rfl

def kid14_part41 : Audit := .split 10 (5,false) (byMove [(kid14_part42),(kid14_part43),(kid14_part44),(kid14_part45),(kid14_part46),(kid14_part47),(kid14_part48),(kid14_part49),(kid14_part50),(kid14_part51),(kid14_part52),(kid14_part53),(kid14_part54),(kid14_part55),(kid14_part56),(kid14_part57),(kid14_part58),(kid14_part59),(kid14_part60),(kid14_part61),(kid14_part62),(kid14_part63),(kid14_part64),(kid14_part65)])

theorem kid14_part41_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part41) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part42),(kid14_part43),(kid14_part44),(kid14_part45),(kid14_part46),(kid14_part47),(kid14_part48),(kid14_part49),(kid14_part50),(kid14_part51),(kid14_part52),(kid14_part53),(kid14_part54),(kid14_part55),(kid14_part56),(kid14_part57),(kid14_part58),(kid14_part59),(kid14_part60),(kid14_part61),(kid14_part62),(kid14_part63),(kid14_part64),(kid14_part65)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part42_checked

  · exact kid14_part48_checked

  · exact kid14_part54_checked

  · exact kid14_part60_checked

  · exact kid14_part43_checked

  · exact kid14_part49_checked

  · exact kid14_part55_checked

  · exact kid14_part61_checked

  · exact kid14_part44_checked

  · exact kid14_part50_checked

  · exact kid14_part56_checked

  · exact kid14_part62_checked

  · exact kid14_part45_checked

  · exact kid14_part51_checked

  · exact kid14_part57_checked

  · exact kid14_part63_checked

  · exact kid14_part46_checked

  · exact kid14_part52_checked

  · exact kid14_part58_checked

  · exact kid14_part64_checked

  · exact kid14_part47_checked

  · exact kid14_part53_checked

  · exact kid14_part59_checked

  · exact kid14_part65_checked

def kid14_part66 : Audit := .cycle 11 4 false (1)
theorem kid14_part66_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part66) = true := by rfl

def kid14_part67 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.cycle 23 1 false (-1),
.cycle 0 18 true (-1),
.cycle 17 4 false (1),
.split 17 (5,true) (byMove [
.cycle 0 18 true (-1),
.last 30 (5,false),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 22 (5,false),
.last 18 (5,false),
.cycle 0 18 true (-1),
.last 30 (5,false),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 22 (5,false),
.last 18 (5,false),
.last 25 (5,false),
.last 21 (5,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.last 22 (5,false),
.last 18 (5,false),
.last 34 (5,false),
.cycle 1 17 true (-1),
.last 29 (5,false),
.cycle 1 20 true (-1),
.cycle 1 22 true (-1),
.last 18 (5,false)
]),
.cycle 0 17 true (-1),
.cycle 0 32 true (-1),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 14 4 true (2),
.split 17 (5,false) (byMove [
.cycle 11 26 true (-1),
.cycle 1 17 true (-1),
.cycle 31 1 false (1),
.cycle 1 20 true (-1),
.cycle 1 22 true (-1),
.last 19 (5,true),
.cycle 0 18 true (-1),
.cycle 14 17 true (2),
.cycle 0 44 true (-1),
.cycle 30 1 false (2),
.cycle 14 5 true (2),
.cycle 17 1 true (3),
.cycle 20 8 false (2),
.cycle 14 4 true (2),
.cycle 0 20 true (-1),
.cycle 28 1 false (0),
.cycle 25 5 false (1),
.last 19 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 1, 64],[2, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 1 17 true (-1),
.cycle 0 32 true (-1),
.cycle 1 20 true (-1),
.cycle 1 22 true (-1),
.cycle 17 1 true (3)
]),
.cycle 18 7 false (2),
.cycle 1 20 true (-1),
.cycle 14 11 false (3),
.cycle 1 18 true (-1),
.cycle 17 4 false (1),
.split 17 (5,true) (byMove [
.cycle 14 5 false (3),
.cycle 0 21 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 22 (5,false),
.last 18 (5,false),
.cycle 1 18 true (-1),
.cycle 0 21 true (-1),
.last 23 (5,false),
.cycle 0 19 true (-1),
.last 19 (5,false),
.last 19 (5,false),
.last 25 (5,false),
.last 21 (5,false),
.cycle 1 20 true (-1),
.cycle 18 1 false (0),
.last 22 (5,false),
.last 18 (5,false),
.last 34 (5,false),
.last 24 (5,false),
.last 20 (5,false),
.cycle 0 19 true (-1),
.cycle 16 2 true (1),
.last 19 (5,false)
]),
.cycle 27 4 true (1),
.cycle 11 22 true (-1),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.cycle 9 15 false (3),
.split 17 (5,false) (byMove [
.cycle 11 26 true (-1),
.cycle 14 15 false (3),
.cycle 18 6 false (2),
.cycle 0 19 true (-1),
.cycle 16 2 true (2),
.last 18 (5,true),
.cycle 0 18 true (-1),
.cycle 14 17 true (2),
.cycle 1 46 true (-1),
.cycle 3 15 true (-1),
.cycle 14 5 true (2),
.cycle 17 1 true (3),
.cycle 20 8 false (2),
.cycle 10 15 false (3),
.cycle 18 6 false (2),
.cycle 1 19 true (-1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 13 24 true (1),
.cycle 27 4 true (1),
.cycle 11 22 true (-1),
.cycle 1 20 true (-1),
.last 24 (5,true),
.cycle 17 1 true (3)
])
])
theorem kid14_part67_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part67) = true := by rfl

def kid14_part68 : Audit := .cycle 10 6 true (-2)
theorem kid14_part68_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part68) = true := by rfl

def kid14_part69 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.last 16 (5,false),
.cycle 20 1 false (-2),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.cycle 1 18 true (0),
.last 16 (5,false)
]),
.cycle 0 15 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.cycle 1 18 true (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 32 1 false (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 25 1 false (-1),
.cycle 12 4 true (2),
.cycle 0 18 true (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 30 1 false (0),
.cycle 1 18 true (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3)
]),
.cycle 19 1 false (-1),
.cycle 1 18 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 12 5 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 0 19 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 20 1 false (-2),
.last 19 (5,false),
.cycle 1 18 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 14 2 true (1),
.last 17 (5,false)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 1 17 true (0),
.split 15 (5,false) (byMove [
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.cycle 14 2 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 2, 64],[2, 15, 15, 1, 32, 64, 64],64⟩,
.cycle 1 34 true (0),
.cycle 3 13 true (0),
.cycle 4 13 true (0),
.cycle 15 1 true (3),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 1 17 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3)
])
])
theorem kid14_part69_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part69) = true := by rfl

def kid14_part70 : Audit := .split 10 (4,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 30 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 22 (5,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 13 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 21 (5,true),
.last 15 (5,true),
.last 27 (5,true),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 12 1 false (2),
.split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 12 1 false (2),
.last 12 (5,false),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 17 1 false (1),
.last 16 (5,false),
.last 12 (5,false)
]),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.last 19 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 19 (5,true),
.cycle 13 1 false (-1),
.last 17 (5,true),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 21 (5,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.last 17 (5,true),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 7 6 true (0),
.cycle 14 3 true (2),
.split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.last 13 (5,false),
.last 13 (5,false),
.cycle 7 6 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.last 23 (5,false),
.last 12 (5,false),
.cycle 15 1 false (-1),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 17 (5,false),
.cycle 10 2 true (0),
.last 13 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.last 16 (5,false),
.last 12 (5,false)
])
])
theorem kid14_part70_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part70) = true := by rfl

def kid14_part72 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 22 true (-2),
.last 17 (5,false),
.cycle 0 20 true (-1),
.last 17 (5,false),
.cycle 0 16 false (3),
.cycle 0 19 true (-1),
.cycle 0 18 true (-1),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 0 22 true (-2),
.last 17 (5,false),
.cycle 0 20 true (-1),
.last 17 (5,false),
.cycle 10 5 false (1),
.cycle 12 19 true (0),
.cycle 0 18 true (-1),
.cycle 2 13 false (3),
.cycle 1 23 true (-1),
.cycle 12 6 true (-1),
.last 15 (5,false)
])
theorem kid14_part72_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part72) = true := by rfl

def kid14_part73 : Audit := .split 18 (5,false) (byMove [
.last 22 (4,true),
.cycle 11 16 false (3),
.cycle 23 1 false (-3),
.cycle 25 1 false (-3),
.last 19 (4,true),
.cycle 29 1 false (-3),
.last 22 (4,true),
.cycle 12 8 true (0),
.last 28 (4,true),
.cycle 13 6 true (0),
.last 19 (4,true),
.cycle 1 19 false (3),
.cycle 20 5 false (0),
.last 29 (4,true),
.last 27 (4,true),
.cycle 25 1 false (-3),
.last 19 (4,true),
.last 26 (4,true),
.last 22 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.cycle 7 28 false (3),
.last 19 (4,true),
.last 31 (4,true)
])
theorem kid14_part73_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part73) = true := by rfl

def kid14_part74 : Audit := .cycle 12 1 false (0)
theorem kid14_part74_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part74) = true := by rfl

def kid14_part75 : Audit := .cycle 11 1 false (-1)
theorem kid14_part75_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part75) = true := by rfl

def kid14_part76 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 11 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 11 8 true (-2),
.cycle 11 3 false (-1),
.cycle 11 6 true (-2),
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
theorem kid14_part76_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part76) = true := by rfl

def kid14_part77 : Audit := .split 11 (5,false) (byMove [
.last 24 (4,true),
.cycle 18 16 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 16 3 false (2),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 18 1 true (2),
.cycle 11 5 false (-1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.last 20 (4,true),
.cycle 7 14 false (3),
.cycle 9 3 false (1),
.cycle 27 1 true (-3)
])
theorem kid14_part77_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part77) = true := by rfl

def kid14_part78 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 24 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 1 18 true (0),
.last 17 (5,false),
.cycle 1 16 true (0),
.last 17 (5,false),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 1 17 true (0),
.last 15 (5,false)
])
theorem kid14_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part78) = true := by rfl

def kid14_part79 : Audit := .split 18 (5,false) (byMove [
.last 22 (4,true),
.cycle 11 16 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.last 22 (4,true),
.cycle 11 8 true (0),
.cycle 16 3 false (2),
.cycle 13 6 true (0),
.last 19 (4,true),
.last 22 (4,true),
.cycle 14 5 false (3),
.last 21 (4,true),
.last 24 (4,true),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.last 22 (4,true),
.cycle 15 4 false (3),
.last 20 (4,true),
.cycle 7 14 true (0),
.last 19 (4,true),
.last 22 (4,true)
])
theorem kid14_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part79) = true := by rfl

def kid14_part80 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.last 20 (4,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.last 20 (4,true),
.cycle 11 3 false (1),
.last 18 (4,true),
.last 14 (4,true),
.cycle 16 1 false (2),
.cycle 11 5 false (1),
.last 16 (4,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.cycle 11 4 false (1),
.last 15 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.cycle 0 36 true (-2)
])
theorem kid14_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part80) = true := by rfl

def kid14_part81 : Audit := .split 16 (5,false) (byMove [
.last 20 (4,true),
.cycle 11 16 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.last 20 (4,true),
.cycle 11 8 true (0),
.cycle 14 3 false (2),
.cycle 11 6 true (0),
.last 17 (4,true),
.cycle 18 1 false (2),
.cycle 12 5 false (3),
.last 19 (4,true),
.last 22 (4,true),
.cycle 17 1 false (-1),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.last 20 (4,true),
.cycle 13 4 false (3),
.last 18 (4,true),
.cycle 7 12 true (0),
.last 17 (4,true),
.cycle 13 9 false (3)
])
theorem kid14_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part81) = true := by rfl

def kid14_part82 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.last 21 (5,false),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.cycle 11 3 false (1),
.last 18 (5,false),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 11 4 true (1),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.last 18 (5,false),
.cycle 15 3 true (3),
.last 12 (5,false)
])
theorem kid14_part82_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part82) = true := by rfl

def kid14_part83 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 12 3 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 1 true (4),
.cycle 12 5 false (2),
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 2 false (2),
.cycle 12 1 false (2),
.cycle 1 13 true (0),
.cycle 12 4 false (3),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part83_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part83) = true := by rfl

def kid14_part84 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.cycle 11 16 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.cycle 11 8 true (-3),
.cycle 13 3 false (-1),
.cycle 11 6 true (-3),
.last 16 (4,true),
.cycle 10 6 false (0),
.cycle 11 5 false (0),
.last 18 (4,true),
.last 21 (4,true),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.last 19 (4,true),
.cycle 12 4 false (0),
.last 17 (4,true),
.cycle 7 11 false (3),
.last 16 (4,true),
.cycle 12 6 false (0)
])
theorem kid14_part84_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part84) = true := by rfl

def kid14_part85 : Audit := .split 13 (4,true) (byMove [
.last 22 (5,false),
.last 23 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 0 20 true (-1),
.last 20 (5,false),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 11 3 false (0),
.last 20 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 12 4 true (-1),
.cycle 0 20 true (-1),
.last 20 (5,false),
.last 20 (5,false),
.cycle 9 5 false (1),
.last 14 (5,false)
])
theorem kid14_part85_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part85) = true := by rfl

def kid14_part86 : Audit := .split 16 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.last 19 (5,false),
.cycle 0 18 true (-1),
.last 19 (5,false),
.cycle 0 20 true (-1),
.cycle 0 17 true (-1),
.last 26 (5,false),
.last 26 (5,false),
.last 24 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 1 20 true (-1),
.last 19 (5,false),
.cycle 1 18 true (-1),
.last 19 (5,false),
.cycle 1 20 true (-1),
.cycle 28 4 true (1),
.last 29 (5,false),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.last 21 (5,false),
.last 17 (5,false)
])
theorem kid14_part86_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part86) = true := by rfl

def kid14_part87 : Audit := .cycle 11 1 false (-1)
theorem kid14_part87_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part87) = true := by rfl

def kid14_part88 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 17 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 21 (4,true),
.cycle 17 8 true (-2),
.cycle 11 3 false (-1),
.cycle 15 6 true (-2),
.last 13 (4,true),
.cycle 10 3 false (0),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 25 (4,true),
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
theorem kid14_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part88) = true := by rfl

def kid14_part89 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 20 (4,true),
.last 18 (4,true),
.cycle 11 3 false (0),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 11 4 false (0),
.last 13 (4,true),
.last 16 (4,true),
.last 12 (4,true),
.cycle 10 3 false (0)
])
theorem kid14_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part89) = true := by rfl

def kid14_part90 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (0),
.last 18 (5,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 24 (5,false),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 16 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.last 23 (5,false),
.cycle 1 16 true (0),
.last 18 (5,false),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 1 17 true (0),
.last 15 (5,false)
])
theorem kid14_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part90) = true := by rfl

def kid14_part91 : Audit := .split 14 (5,false) (byMove [
.last 18 (4,true),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 11 6 true (-2),
.last 15 (4,true),
.last 18 (4,true),
.cycle 11 5 false (1),
.last 17 (4,true),
.last 20 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 11 4 false (1),
.last 16 (4,true),
.cycle 7 10 false (3),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid14_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part91) = true := by rfl

def kid14_part92 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 11 3 false (1),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 21 (5,false),
.cycle 1 21 true (0),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid14_part92_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part92) = true := by rfl

def kid14_part93 : Audit := .cycle 7 6 true (0)
theorem kid14_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part93) = true := by rfl

def kid14_part94 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 22 true (-1),
.last 14 (5,false),
.cycle 0 18 true (0),
.last 14 (5,false),
.cycle 9 4 true (0),
.cycle 7 6 true (0),
.last 24 (5,false),
.cycle 0 14 true (0),
.last 19 (5,false),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.cycle 1 22 true (-1),
.last 14 (5,false),
.cycle 1 18 true (0),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 11 4 true (1),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.cycle 15 3 true (3),
.last 12 (5,false)
])
theorem kid14_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part94) = true := by rfl

def kid14_part95 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 13 16 false (1),
.last 14 (4,true),
.cycle 7 8 true (0),
.last 13 (4,true),
.cycle 11 2 true (1),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 8 22 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 1 true (4),
.last 16 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 5 8 true (0),
.last 13 (4,true),
.cycle 14 3 true (2),
.cycle 1 13 true (0),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part95_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part95) = true := by rfl

def kid14_part71 : Audit := .split 10 (5,true) (byMove [(kid14_part72),(kid14_part73),(kid14_part74),(kid14_part75),(kid14_part76),(kid14_part77),(kid14_part78),(kid14_part79),(kid14_part80),(kid14_part81),(kid14_part82),(kid14_part83),(kid14_part84),(kid14_part85),(kid14_part86),(kid14_part87),(kid14_part88),(kid14_part89),(kid14_part90),(kid14_part91),(kid14_part92),(kid14_part93),(kid14_part94),(kid14_part95)])

theorem kid14_part71_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part71) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part72),(kid14_part73),(kid14_part74),(kid14_part75),(kid14_part76),(kid14_part77),(kid14_part78),(kid14_part79),(kid14_part80),(kid14_part81),(kid14_part82),(kid14_part83),(kid14_part84),(kid14_part85),(kid14_part86),(kid14_part87),(kid14_part88),(kid14_part89),(kid14_part90),(kid14_part91),(kid14_part92),(kid14_part93),(kid14_part94),(kid14_part95)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part72_checked

  · exact kid14_part78_checked

  · exact kid14_part84_checked

  · exact kid14_part90_checked

  · exact kid14_part73_checked

  · exact kid14_part79_checked

  · exact kid14_part85_checked

  · exact kid14_part91_checked

  · exact kid14_part74_checked

  · exact kid14_part80_checked

  · exact kid14_part86_checked

  · exact kid14_part92_checked

  · exact kid14_part75_checked

  · exact kid14_part81_checked

  · exact kid14_part87_checked

  · exact kid14_part93_checked

  · exact kid14_part76_checked

  · exact kid14_part82_checked

  · exact kid14_part88_checked

  · exact kid14_part94_checked

  · exact kid14_part77_checked

  · exact kid14_part83_checked

  · exact kid14_part89_checked

  · exact kid14_part95_checked

def kid14_part96 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.cycle 0 20 true (-1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.last 28 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (-1),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 20 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.cycle 0 20 true (-1),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.last 27 (5,false),
.cycle 1 24 true (0),
.cycle 9 6 true (0),
.last 15 (5,false)
]),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 1 15 true (1),
.split 14 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 1 24 true (0),
.cycle 9 6 true (1),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true),
.cycle 15 9 false (2),
.cycle 12 4 true (1),
.cycle 1 17 true (1),
.cycle 26 1 false (0),
.cycle 11 6 true (1),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true)
]),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.cycle 13 12 false (1),
.split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.last 26 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 20 (5,false),
.last 15 (5,false),
.cycle 1 20 true (0),
.last 26 (5,false),
.cycle 0 24 true (0),
.last 24 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.last 20 (5,false),
.last 15 (5,false),
.cycle 1 20 true (0),
.last 22 (5,false),
.last 17 (5,false),
.cycle 7 10 true (0),
.cycle 13 2 true (0),
.last 16 (5,false)
]),
.cycle 10 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.split 14 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 15 12 true (-2),
.cycle 0 24 true (-1),
.cycle 7 10 true (1),
.cycle 13 2 true (1),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true),
.cycle 16 9 false (2),
.cycle 15 12 true (-2),
.cycle 15 7 false (1),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 11 4 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true)
])
])
theorem kid14_part96_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part96) = true := by rfl

def kid14_part97 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 15 false (3),
.split 13 (5,true) (byMove [
.cycle 1 14 true (0),
.cycle 0 17 true (-1),
.cycle 1 15 false (3),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 15 8 false (1),
.cycle 1 17 true (-1),
.cycle 0 22 true (-2),
.cycle 1 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 20 true (1),
.cycle 0 27 true (0),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 16 13 false (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 16 13 false (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3)
]),
.cycle 18 7 false (0),
.cycle 1 29 true (-2),
.cycle 19 5 false (2),
.cycle 1 14 true (1),
.cycle 13 8 false (1),
.split 13 (5,true) (byMove [
.cycle 15 5 false (2),
.cycle 0 28 true (-1),
.cycle 0 19 true (-1),
.cycle 23 1 false (-1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 15 (5,false),
.cycle 15 8 false (1),
.last 28 (5,false),
.cycle 1 29 true (-2),
.cycle 23 1 false (-1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.last 17 (5,false),
.last 19 (5,false),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 22 7 false (2),
.cycle 1 21 false (3),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 28 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 16 13 false (2),
.cycle 22 7 false (2),
.cycle 14 9 false (2),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3)
])
])
theorem kid14_part97_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part97) = true := by rfl

def kid14_part98 : Audit := .cycle 0 12 true (0)
theorem kid14_part98_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part98) = true := by rfl

def kid14_part99 : Audit := .cycle 4 6 true (1)
theorem kid14_part99_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part99) = true := by rfl

def kid14_part100 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 21 5 false (1),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.cycle 15 1 true (-1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 15 1 true (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 13 1 true (3),
.last 13 (5,false),
.last 17 (5,false),
.last 30 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 13 3 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 true (4),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.last 34 (5,true),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 3 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
]),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.split 12 (5,true) (byMove [
.cycle 19 5 false (2),
.cycle 13 10 true (-2),
.last 15 (5,false),
.cycle 7 8 true (1),
.last 20 (5,false),
.last 15 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.cycle 13 10 true (-2),
.last 15 (5,false),
.cycle 5 8 true (1),
.cycle 13 3 false (1),
.last 15 (5,false),
.cycle 1 13 true (1),
.last 26 (5,false),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 17 14 true (-2),
.cycle 23 1 true (-1),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.last 34 (5,true),
.last 22 (5,true),
.last 26 (5,true),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
])
theorem kid14_part100_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part100) = true := by rfl

def kid14_part102 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 26 true (-2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 19 false (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 20 9 false (0),
.cycle 1 33 true (-2),
.cycle 21 7 false (2),
.cycle 1 16 true (1),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1)
])
theorem kid14_part102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part102) = true := by rfl

def kid14_part103 : Audit := .cycle 11 8 true (-2)
theorem kid14_part103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part103) = true := by rfl

def kid14_part104 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 3 false (2),
.cycle 15 1 false (1),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 19 3 false (1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 19 3 false (1),
.cycle 1 21 true (0),
.cycle 9 4 true (0),
.cycle 13 3 false (1)
])
theorem kid14_part104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part104) = true := by rfl

def kid14_part105 : Audit := .cycle 7 6 true (1)
theorem kid14_part105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part105) = true := by rfl

def kid14_part106 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 22 true (-1),
.cycle 17 1 false (-1),
.cycle 0 18 true (0),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 1 22 true (-1),
.cycle 12 8 true (-2),
.cycle 1 18 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 11 4 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.cycle 10 2 true (1)
])
theorem kid14_part106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part106) = true := by rfl

def kid14_part107 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 18 (4,true),
.cycle 17 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 13 3 true (3),
.cycle 15 1 false (1),
.cycle 13 6 false (1),
.last 18 (4,true),
.cycle 12 8 true (-2),
.last 16 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 13 3 true (3),
.cycle 10 2 true (1)
])
theorem kid14_part107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part107) = true := by rfl

def kid14_part108 : Audit := .cycle 1 11 true (1)
theorem kid14_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part108) = true := by rfl

def kid14_part109 : Audit := .cycle 0 14 true (0)
theorem kid14_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part109) = true := by rfl

def kid14_part110 : Audit := .cycle 8 16 true (1)
theorem kid14_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part110) = true := by rfl

def kid14_part111 : Audit := .cycle 0 12 true (0)
theorem kid14_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part111) = true := by rfl

def kid14_part112 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (2),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 17 10 false (1),
.cycle 1 33 true (-2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part112) = true := by rfl

def kid14_part113 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
theorem kid14_part113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part113) = true := by rfl

def kid14_part114 : Audit := .split 14 (4,true) (byMove [
.cycle 1 19 true (-1),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.cycle 17 5 false (-1),
.cycle 16 5 false (2),
.cycle 26 5 false (5),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.last 16 (5,true),
.cycle 17 5 false (1),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 18 5 false (2),
.cycle 15 1 false (-1),
.last 16 (5,true),
.cycle 17 5 false (-1),
.cycle 12 4 true (0),
.cycle 1 20 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.last 16 (5,true),
.cycle 15 5 false (1)
])
theorem kid14_part114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part114) = true := by rfl

def kid14_part115 : Audit := .cycle 11 8 true (-2)
theorem kid14_part115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part115) = true := by rfl

def kid14_part116 : Audit := .split 12 (4,true) (byMove [
.cycle 1 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 20 (5,true),
.cycle 15 3 false (1),
.cycle 26 3 false (4),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 14 (5,true),
.cycle 18 3 false (2),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 14 (5,true),
.last 20 (5,true),
.cycle 11 4 true (0),
.cycle 1 18 true (0),
.cycle 1 15 true (0),
.cycle 17 3 false (1),
.last 14 (5,true),
.cycle 13 3 false (1)
])
theorem kid14_part116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part116) = true := by rfl

def kid14_part117 : Audit := .cycle 5 6 true (1)
theorem kid14_part117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part117) = true := by rfl

def kid14_part118 : Audit := .split 11 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 12 4 true (2),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 20 3 false (0),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 13 4 true (1),
.cycle 1 20 true (0),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 12 4 true (2),
.last 12 (5,true)
])
theorem kid14_part118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part118) = true := by rfl

def kid14_part119 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 23 1 false (5),
.cycle 13 6 false (1),
.last 23 (4,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 12 3 true (2)
])
theorem kid14_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part119) = true := by rfl

def kid14_part120 : Audit := .cycle 1 11 true (1)
theorem kid14_part120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part120) = true := by rfl

def kid14_part121 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.cycle 0 20 true (-1),
.last 14 (5,true),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 15 (5,true),
.cycle 7 8 true (1),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 11 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 10 4 true (1)
])
theorem kid14_part121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part121) = true := by rfl

def kid14_part122 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 2 15 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 2 13 true (1),
.cycle 2 12 true (1),
.cycle 18 7 false (0),
.cycle 1 29 true (-2),
.cycle 19 5 false (2),
.cycle 1 14 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 13 true (1),
.cycle 2 12 true (1)
])
theorem kid14_part122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part122) = true := by rfl

def kid14_part123 : Audit := .cycle 0 12 true (0)
theorem kid14_part123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part123) = true := by rfl

def kid14_part124 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 21 5 false (1),
.cycle 15 2 true (-1),
.cycle 0 13 true (0),
.cycle 15 2 true (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 2 true (4),
.cycle 3 9 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part124) = true := by rfl

def kid14_part125 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 true (5),
.cycle 3 9 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4),
.last 15 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 13 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (5),
.cycle 12 1 true (4)
])
theorem kid14_part125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part125) = true := by rfl

def kid14_part101 : Audit := .split 10 (5,false) (byMove [(kid14_part102),(kid14_part103),(kid14_part104),(kid14_part105),(kid14_part106),(kid14_part107),(kid14_part108),(kid14_part109),(kid14_part110),(kid14_part111),(kid14_part112),(kid14_part113),(kid14_part114),(kid14_part115),(kid14_part116),(kid14_part117),(kid14_part118),(kid14_part119),(kid14_part120),(kid14_part121),(kid14_part122),(kid14_part123),(kid14_part124),(kid14_part125)])

theorem kid14_part101_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part101) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part102),(kid14_part103),(kid14_part104),(kid14_part105),(kid14_part106),(kid14_part107),(kid14_part108),(kid14_part109),(kid14_part110),(kid14_part111),(kid14_part112),(kid14_part113),(kid14_part114),(kid14_part115),(kid14_part116),(kid14_part117),(kid14_part118),(kid14_part119),(kid14_part120),(kid14_part121),(kid14_part122),(kid14_part123),(kid14_part124),(kid14_part125)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part102_checked

  · exact kid14_part108_checked

  · exact kid14_part114_checked

  · exact kid14_part120_checked

  · exact kid14_part103_checked

  · exact kid14_part109_checked

  · exact kid14_part115_checked

  · exact kid14_part121_checked

  · exact kid14_part104_checked

  · exact kid14_part110_checked

  · exact kid14_part116_checked

  · exact kid14_part122_checked

  · exact kid14_part105_checked

  · exact kid14_part111_checked

  · exact kid14_part117_checked

  · exact kid14_part123_checked

  · exact kid14_part106_checked

  · exact kid14_part112_checked

  · exact kid14_part118_checked

  · exact kid14_part124_checked

  · exact kid14_part107_checked

  · exact kid14_part113_checked

  · exact kid14_part119_checked

  · exact kid14_part125_checked

def kid14_part5 : Audit := .split 9 (4,false) (byMove [(kid14_part6),(kid14_part7),(kid14_part8),(kid14_part9),(kid14_part10),(kid14_part11),(kid14_part36),(kid14_part37),(kid14_part38),(kid14_part39),(kid14_part40),(kid14_part41),(kid14_part66),(kid14_part67),(kid14_part68),(kid14_part69),(kid14_part70),(kid14_part71),(kid14_part96),(kid14_part97),(kid14_part98),(kid14_part99),(kid14_part100),(kid14_part101)])

theorem kid14_part5_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (kid14_part5) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid14_part6),(kid14_part7),(kid14_part8),(kid14_part9),(kid14_part10),(kid14_part11),(kid14_part36),(kid14_part37),(kid14_part38),(kid14_part39),(kid14_part40),(kid14_part41),(kid14_part66),(kid14_part67),(kid14_part68),(kid14_part69),(kid14_part70),(kid14_part71),(kid14_part96),(kid14_part97),(kid14_part98),(kid14_part99),(kid14_part100),(kid14_part101)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part6_checked

  · exact kid14_part36_checked

  · exact kid14_part66_checked

  · exact kid14_part96_checked

  · exact kid14_part7_checked

  · exact kid14_part37_checked

  · exact kid14_part67_checked

  · exact kid14_part97_checked

  · exact kid14_part8_checked

  · exact kid14_part38_checked

  · exact kid14_part68_checked

  · exact kid14_part98_checked

  · exact kid14_part9_checked

  · exact kid14_part39_checked

  · exact kid14_part69_checked

  · exact kid14_part99_checked

  · exact kid14_part10_checked

  · exact kid14_part40_checked

  · exact kid14_part70_checked

  · exact kid14_part100_checked

  · exact kid14_part11_checked

  · exact kid14_part41_checked

  · exact kid14_part71_checked

  · exact kid14_part101_checked

def kid14_part127 : Audit := .cycle 0 14 true (0)
theorem kid14_part127_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part127) = true := by rfl

def kid14_part128 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.cycle 17 9 false (1),
.cycle 0 18 true (-1),
.split 17 (4,true) (byMove [
.cycle 0 18 true (-1),
.cycle 18 9 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 18 9 false (1),
.cycle 0 18 true (-1),
.cycle 18 9 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 18 9 false (3),
.cycle 19 9 false (1),
.last 21 (4,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 0 22 true (-1),
.cycle 28 9 false (2),
.cycle 1 17 true (-1),
.cycle 18 9 false (3),
.cycle 1 20 true (-1),
.last 18 (4,false),
.cycle 0 22 true (-1)
]),
.cycle 18 9 false (1),
.cycle 0 17 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 2, 64],80⟩,
.cycle 19 9 false (3),
.cycle 17 9 false (3),
.split 17 (4,false) (byMove [
.cycle 28 9 false (2),
.cycle 1 17 true (-1),
.cycle 18 9 false (3),
.cycle 1 20 true (-1),
.last 19 (4,true),
.cycle 0 22 true (-1),
.cycle 0 18 true (-1),
.cycle 1 56 true (-1),
.cycle 21 9 false (3),
.cycle 19 9 false (3),
.cycle 17 1 true (3),
.last 93 (4,true),
.cycle 24 9 false (2),
.cycle 14 4 true (2),
.cycle 0 20 true (-1),
.cycle 18 9 false (3),
.last 19 (4,true),
.cycle 23 9 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 1, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.cycle 1 17 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 4, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.cycle 1 20 true (-1),
.cycle 17 1 true (3),
.cycle 0 22 true (-1)
]),
.cycle 1 17 true (-1),
.cycle 17 9 false (2),
.cycle 1 20 true (-1),
.cycle 17 9 false (1),
.cycle 1 18 true (-1),
.split 17 (4,true) (byMove [
.cycle 13 5 false (3),
.cycle 0 21 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 18 9 false (1),
.cycle 1 18 true (-1),
.cycle 0 21 true (-1),
.cycle 18 9 false (2),
.cycle 0 19 true (-1),
.last 19 (4,false),
.last 19 (4,false),
.cycle 19 9 false (1),
.last 21 (4,false),
.cycle 1 20 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 1 22 true (-1),
.cycle 28 9 false (2),
.cycle 18 9 false (2),
.last 20 (4,false),
.cycle 0 19 true (-1),
.last 19 (4,false),
.cycle 16 2 true (1)
]),
.cycle 1 22 true (-1),
.cycle 27 4 true (1),
.cycle 26 9 false (2),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.split 17 (4,false) (byMove [
.cycle 28 9 false (2),
.cycle 18 9 false (2),
.cycle 21 9 false (1),
.cycle 0 19 true (-1),
.last 18 (4,true),
.cycle 16 2 true (2),
.cycle 0 18 true (-1),
.cycle 36 9 false (2),
.cycle 37 9 false (3),
.cycle 3 15 true (-1),
.cycle 17 1 true (3),
.cycle 28 9 false (2),
.cycle 23 9 false (2),
.cycle 18 9 false (2),
.cycle 21 9 false (1),
.cycle 1 19 true (-1),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 36 true (-1),
.cycle 27 4 true (1),
.cycle 26 9 false (2),
.cycle 1 20 true (-1),
.cycle 17 1 true (3),
.cycle 16 7 true (1)
]),
.cycle 18 9 false (2)
])
theorem kid14_part128_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part128) = true := by rfl

def kid14_part129 : Audit := .cycle 13 1 false (-1)
theorem kid14_part129_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part129) = true := by rfl

def kid14_part130 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 17 1 false (1),
.cycle 20 1 false (-2),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 0 18 true (0)
]),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 0 30 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.last 17 (4,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 32 1 false (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 24 1 false (0),
.cycle 25 1 false (-1),
.cycle 12 4 true (2),
.cycle 0 18 true (0),
.cycle 22 1 false (0),
.last 17 (4,true),
.cycle 22 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 0 30 true (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3),
.cycle 0 18 true (0)
]),
.cycle 1 18 true (0),
.cycle 19 1 false (-1),
.cycle 1 18 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.split 15 (4,true) (byMove [
.cycle 11 5 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 0 19 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.last 17 (4,false),
.last 17 (4,false),
.cycle 20 1 false (-2),
.last 19 (4,false),
.cycle 1 18 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.last 18 (4,false),
.cycle 0 17 true (0),
.last 17 (4,false),
.cycle 14 2 true (1)
]),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.split 15 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.cycle 0 31 true (0),
.cycle 0 34 true (0),
.cycle 3 13 true (0),
.cycle 15 1 true (3),
.cycle 1 19 true (0),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 1 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3),
.cycle 0 18 true (0)
]),
.cycle 0 17 true (0)
])
theorem kid14_part130_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part130) = true := by rfl

def kid14_part132 : Audit := .cycle 0 11 false (3)
theorem kid14_part132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part132) = true := by rfl

def kid14_part133 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 false (3),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 24 (5,true),
.cycle 0 32 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 40 true (-2),
.cycle 19 2 true (-2),
.cycle 17 5 false (1),
.last 23 (5,true),
.last 26 (5,true),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 24 (5,true),
.cycle 0 32 true (-2),
.cycle 12 9 false (1),
.last 26 (5,true),
.last 26 (5,true),
.cycle 9 12 false (1)
])
theorem kid14_part133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part133) = true := by rfl

def kid14_part134 : Audit := .cycle 12 1 false (0)
theorem kid14_part134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part134) = true := by rfl

def kid14_part135 : Audit := .cycle 11 1 false (-1)
theorem kid14_part135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part135) = true := by rfl

def kid14_part136 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 16 true (-1),
.cycle 1 25 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 16 1 true (2),
.cycle 11 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 16 true (-1),
.cycle 1 11 false (3),
.cycle 11 9 false (1),
.cycle 0 18 true (-1),
.cycle 20 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid14_part136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part136) = true := by rfl

def kid14_part137 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 13 false (3),
.cycle 0 34 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 19 1 true (1),
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
.last 18 (5,true),
.cycle 9 4 false (1)
])
theorem kid14_part137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part137) = true := by rfl

def kid14_part138 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 17 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.last 24 (4,false),
.last 24 (4,false),
.last 22 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 1 18 true (0),
.last 17 (4,false),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 0 17 true (0)
])
theorem kid14_part138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part138) = true := by rfl

def kid14_part139 : Audit := .cycle 0 14 true (0)
theorem kid14_part139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part139) = true := by rfl

def kid14_part140 : Audit := .cycle 12 1 false (2)
theorem kid14_part140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part140) = true := by rfl

def kid14_part141 : Audit := .cycle 11 1 false (1)
theorem kid14_part141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part141) = true := by rfl

def kid14_part142 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 11 10 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.last 20 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 14 1 true (4),
.cycle 11 2 true (1),
.cycle 11 5 false (1),
.last 14 (5,true),
.last 24 (5,true),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 24 (5,true),
.cycle 14 1 true (4),
.last 15 (5,true)
])
theorem kid14_part142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part142) = true := by rfl

def kid14_part143 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 17 1 true (3),
.cycle 11 2 true (0),
.cycle 11 5 false (1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 11 9 false (2),
.last 18 (5,true),
.cycle 17 1 true (3),
.cycle 9 4 true (0)
])
theorem kid14_part143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part143) = true := by rfl

def kid14_part144 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.last 22 (5,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 10 8 true (-3),
.cycle 14 2 true (-3),
.cycle 11 5 false (0),
.last 18 (5,true),
.last 21 (5,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.last 22 (5,true),
.cycle 12 9 false (0),
.last 21 (5,true),
.last 22 (5,true),
.cycle 9 7 false (1)
])
theorem kid14_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part144) = true := by rfl

def kid14_part145 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 false (3),
.last 23 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 18 true (-1),
.last 23 (4,false),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 0 18 true (-1),
.cycle 1 13 false (3),
.last 22 (4,false),
.cycle 0 20 true (-1),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid14_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part145) = true := by rfl

def kid14_part146 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.last 19 (4,false),
.cycle 0 18 true (-1),
.cycle 0 20 true (-1),
.last 19 (4,false),
.cycle 0 17 true (-1),
.last 26 (4,false),
.last 26 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.cycle 1 20 true (-1),
.last 19 (4,false),
.cycle 1 18 true (-1),
.cycle 1 20 true (-1),
.last 19 (4,false),
.cycle 28 4 true (1),
.last 29 (4,false),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.last 17 (4,false),
.last 21 (4,false)
])
theorem kid14_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part146) = true := by rfl

def kid14_part147 : Audit := .cycle 11 1 false (-1)
theorem kid14_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part147) = true := by rfl

def kid14_part148 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 16 true (-1),
.last 18 (5,true),
.cycle 16 1 false (0),
.last 16 (5,true),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 16 true (-1),
.last 22 (5,true),
.last 13 (5,true),
.last 16 (5,true),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid14_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part148) = true := by rfl

def kid14_part149 : Audit := .split 12 (4,false) (byMove [
.last 20 (5,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 21 (5,true),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 25 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.last 15 (5,true),
.last 18 (5,true),
.last 25 (5,true),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid14_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part149) = true := by rfl

def kid14_part150 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 18 (4,false),
.cycle 0 15 true (0),
.last 24 (4,false),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.last 23 (4,false),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.last 18 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 0 17 true (0)
])
theorem kid14_part150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part150) = true := by rfl

def kid14_part151 : Audit := .cycle 0 14 true (0)
theorem kid14_part151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part151) = true := by rfl

def kid14_part152 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 false (3),
.cycle 11 10 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 2 false (0),
.last 23 (5,true),
.cycle 1 23 true (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 24 (5,true),
.cycle 18 2 true (-1),
.cycle 16 5 false (2),
.last 22 (5,true),
.last 25 (5,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 2 false (0),
.last 23 (5,true),
.cycle 1 23 true (-1),
.cycle 11 9 false (2),
.last 25 (5,true),
.last 24 (5,true),
.cycle 9 11 false (2)
])
theorem kid14_part152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part152) = true := by rfl

def kid14_part153 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 1 20 true (0),
.last 19 (4,false),
.cycle 0 17 true (0),
.last 26 (4,false),
.last 26 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.cycle 1 20 true (0),
.last 19 (4,false),
.cycle 1 18 true (0),
.cycle 0 19 true (0),
.last 19 (4,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.last 17 (4,false),
.cycle 1 21 true (0)
])
theorem kid14_part153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part153) = true := by rfl

def kid14_part154 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 18 (5,true),
.cycle 16 1 false (-2),
.last 16 (5,true),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 7 6 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 20 1 false (0),
.cycle 14 1 true (4),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.last 18 (5,true),
.last 20 (5,true),
.last 16 (5,true),
.cycle 16 3 true (2),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.cycle 14 1 true (4),
.last 15 (5,true)
])
theorem kid14_part154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part154) = true := by rfl

def kid14_part155 : Audit := .cycle 9 2 true (0)
theorem kid14_part155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part155) = true := by rfl

def kid14_part131 : Audit := .split 10 (4,true) (byMove [(kid14_part132),(kid14_part133),(kid14_part134),(kid14_part135),(kid14_part136),(kid14_part137),(kid14_part138),(kid14_part139),(kid14_part140),(kid14_part141),(kid14_part142),(kid14_part143),(kid14_part144),(kid14_part145),(kid14_part146),(kid14_part147),(kid14_part148),(kid14_part149),(kid14_part150),(kid14_part151),(kid14_part152),(kid14_part153),(kid14_part154),(kid14_part155)])

theorem kid14_part131_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part131) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part132),(kid14_part133),(kid14_part134),(kid14_part135),(kid14_part136),(kid14_part137),(kid14_part138),(kid14_part139),(kid14_part140),(kid14_part141),(kid14_part142),(kid14_part143),(kid14_part144),(kid14_part145),(kid14_part146),(kid14_part147),(kid14_part148),(kid14_part149),(kid14_part150),(kid14_part151),(kid14_part152),(kid14_part153),(kid14_part154),(kid14_part155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part132_checked

  · exact kid14_part138_checked

  · exact kid14_part144_checked

  · exact kid14_part150_checked

  · exact kid14_part133_checked

  · exact kid14_part139_checked

  · exact kid14_part145_checked

  · exact kid14_part151_checked

  · exact kid14_part134_checked

  · exact kid14_part140_checked

  · exact kid14_part146_checked

  · exact kid14_part152_checked

  · exact kid14_part135_checked

  · exact kid14_part141_checked

  · exact kid14_part147_checked

  · exact kid14_part153_checked

  · exact kid14_part136_checked

  · exact kid14_part142_checked

  · exact kid14_part148_checked

  · exact kid14_part154_checked

  · exact kid14_part137_checked

  · exact kid14_part143_checked

  · exact kid14_part149_checked

  · exact kid14_part155_checked

def kid14_part156 : Audit := .split 10 (5,true) (byMove [
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
.cycle 0 16 true (-1),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 15 (4,true),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-1),
.cycle 1 11 false (3),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.last 15 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 24 1 false (4),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.last 13 (4,true),
.cycle 12 1 false (2),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 1 17 true (0),
.cycle 1 15 true (0),
.cycle 0 14 true (0),
.cycle 17 1 false (1),
.last 13 (4,true),
.cycle 15 3 true (3)
]),
.cycle 11 1 false (1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.last 19 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-1),
.last 19 (4,true),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 16 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.last 17 (4,true),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.cycle 1 19 true (0),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 19 true (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 7 6 true (0),
.cycle 0 31 true (0),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.last 13 (4,true),
.cycle 9 4 true (0),
.cycle 15 1 false (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 17 true (0),
.cycle 1 15 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.last 13 (4,true),
.cycle 15 3 true (3)
]),
.cycle 9 2 true (0)
])
theorem kid14_part156_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part156) = true := by rfl

def kid14_part157 : Audit := .cycle 7 4 true (1)
theorem kid14_part157_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part157) = true := by rfl

def kid14_part158 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.cycle 0 17 true (-1),
.cycle 30 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 14 14 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 1 true (1),
.cycle 1 14 true (1),
.cycle 15 8 false (1),
.cycle 1 17 true (-1),
.cycle 0 22 true (-2),
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 0 32 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 1 14 true (1)
]),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 51 1 false (9),
.cycle 1 28 true (0),
.cycle 13 1 true (3),
.cycle 1 14 true (1),
.cycle 7 8 true (1),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 13 true (1),
.cycle 15 7 false (1),
.cycle 1 19 true (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.split 13 (4,false) (byMove [
.last 18 (4,true),
.cycle 0 28 true (-1),
.cycle 0 19 true (-1),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 14 5 false (0),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (1),
.cycle 15 8 false (1),
.cycle 21 4 false (2),
.last 26 (4,true),
.cycle 23 1 false (-1),
.last 14 (4,true),
.last 36 (4,true),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 28 true (1),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 13 true (1)
])
theorem kid14_part158_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part158) = true := by rfl

def kid14_part159 : Audit := .cycle 0 12 true (0)
theorem kid14_part159_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part159) = true := by rfl

def kid14_part160 : Audit := .cycle 17 1 false (1)
theorem kid14_part160_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part160) = true := by rfl

def kid14_part162 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 26 true (-2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 19 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.cycle 20 9 false (0),
.cycle 1 33 true (-2),
.cycle 21 7 false (2),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0)
])
theorem kid14_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part162) = true := by rfl

def kid14_part163 : Audit := .cycle 0 14 true (0)
theorem kid14_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part163) = true := by rfl

def kid14_part164 : Audit := .cycle 21 1 false (1)
theorem kid14_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part164) = true := by rfl

def kid14_part165 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 20 1 false (0),
.cycle 0 17 true (0),
.cycle 35 1 false (1),
.cycle 27 1 false (1),
.cycle 25 1 false (1),
.cycle 1 20 true (0),
.cycle 27 1 false (1),
.cycle 22 1 false (0),
.cycle 1 20 true (0),
.cycle 20 1 false (0),
.cycle 1 18 true (0),
.last 17 (4,true),
.last 19 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 1 21 true (0)
])
theorem kid14_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part165) = true := by rfl

def kid14_part166 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (2),
.cycle 17 1 false (-1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 18 (5,true),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
])
theorem kid14_part166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part166) = true := by rfl

def kid14_part167 : Audit := .cycle 9 2 true (1)
theorem kid14_part167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part167) = true := by rfl

def kid14_part168 : Audit := .cycle 1 11 true (1)
theorem kid14_part168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part168) = true := by rfl

def kid14_part169 : Audit := .cycle 0 14 true (0)
theorem kid14_part169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part169) = true := by rfl

def kid14_part170 : Audit := .cycle 39 1 false (7)
theorem kid14_part170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part170) = true := by rfl

def kid14_part171 : Audit := .cycle 0 12 true (0)
theorem kid14_part171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part171) = true := by rfl

def kid14_part172 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 13 1 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 true (5),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
])
theorem kid14_part172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part172) = true := by rfl

def kid14_part173 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 2 true (2),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 30 2 true (4),
.cycle 1 24 true (0),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 7 6 true (1),
.cycle 1 21 true (-1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part173) = true := by rfl

def kid14_part174 : Audit := .split 14 (5,true) (byMove [
.cycle 1 19 true (-1),
.cycle 21 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (0),
.cycle 15 5 false (2),
.cycle 27 5 false (5),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 15 5 false (1),
.last 16 (4,true),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 17 5 false (2),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.last 16 (4,true),
.cycle 11 4 true (0),
.cycle 1 20 true (0),
.cycle 1 17 true (0),
.cycle 18 5 false (2),
.cycle 17 5 false (1),
.last 16 (4,true)
])
theorem kid14_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part174) = true := by rfl

def kid14_part175 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.last 14 (4,true),
.cycle 14 5 false (0),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 10 4 true (1),
.last 15 (4,true),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 12 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 15 12 true (-2),
.last 15 (4,true)
])
theorem kid14_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part175) = true := by rfl

def kid14_part176 : Audit := .cycle 1 13 true (1)
theorem kid14_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part176) = true := by rfl

def kid14_part177 : Audit := .cycle 18 1 false (0)
theorem kid14_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part177) = true := by rfl

def kid14_part178 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
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
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.last 13 (5,true)
])
theorem kid14_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part178) = true := by rfl

def kid14_part179 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (5,true),
.last 14 (5,true),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.cycle 13 3 true (3),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid14_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part179) = true := by rfl

def kid14_part180 : Audit := .cycle 1 11 true (1)
theorem kid14_part180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part180) = true := by rfl

def kid14_part181 : Audit := .cycle 7 4 true (1)
theorem kid14_part181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part181) = true := by rfl

def kid14_part182 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 2 12 true (1),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 2 12 true (1),
.cycle 2 13 true (1),
.cycle 15 7 false (1),
.cycle 1 19 true (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 16 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.cycle 2 13 true (1)
])
theorem kid14_part182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part182) = true := by rfl

def kid14_part183 : Audit := .cycle 0 12 true (0)
theorem kid14_part183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part183) = true := by rfl

def kid14_part184 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 14 1 true (2),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 true (5),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 15 3 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
])
theorem kid14_part184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part184) = true := by rfl

def kid14_part185 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 13 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 2 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 2 true (4),
.cycle 3 9 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part185) = true := by rfl

def kid14_part161 : Audit := .split 10 (4,false) (byMove [(kid14_part162),(kid14_part163),(kid14_part164),(kid14_part165),(kid14_part166),(kid14_part167),(kid14_part168),(kid14_part169),(kid14_part170),(kid14_part171),(kid14_part172),(kid14_part173),(kid14_part174),(kid14_part175),(kid14_part176),(kid14_part177),(kid14_part178),(kid14_part179),(kid14_part180),(kid14_part181),(kid14_part182),(kid14_part183),(kid14_part184),(kid14_part185)])

theorem kid14_part161_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part161) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part162),(kid14_part163),(kid14_part164),(kid14_part165),(kid14_part166),(kid14_part167),(kid14_part168),(kid14_part169),(kid14_part170),(kid14_part171),(kid14_part172),(kid14_part173),(kid14_part174),(kid14_part175),(kid14_part176),(kid14_part177),(kid14_part178),(kid14_part179),(kid14_part180),(kid14_part181),(kid14_part182),(kid14_part183),(kid14_part184),(kid14_part185)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part162_checked

  · exact kid14_part168_checked

  · exact kid14_part174_checked

  · exact kid14_part180_checked

  · exact kid14_part163_checked

  · exact kid14_part169_checked

  · exact kid14_part175_checked

  · exact kid14_part181_checked

  · exact kid14_part164_checked

  · exact kid14_part170_checked

  · exact kid14_part176_checked

  · exact kid14_part182_checked

  · exact kid14_part165_checked

  · exact kid14_part171_checked

  · exact kid14_part177_checked

  · exact kid14_part183_checked

  · exact kid14_part166_checked

  · exact kid14_part172_checked

  · exact kid14_part178_checked

  · exact kid14_part184_checked

  · exact kid14_part167_checked

  · exact kid14_part173_checked

  · exact kid14_part179_checked

  · exact kid14_part185_checked

def kid14_part186 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 13 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 13 1 true (3),
.cycle 16 7 false (0),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (4,true),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 13 1 true (3)
]),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 30 1 true (4),
.cycle 1 24 true (0),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (4,true),
.last 25 (4,true),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.cycle 7 7 true (1),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.last 23 (4,true),
.last 16 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
]),
.cycle 12 1 true (4),
.cycle 7 6 true (1),
.cycle 1 21 true (-1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 19 (4,true),
.last 14 (4,true),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (2),
.cycle 16 7 false (0),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 14 (4,true),
.cycle 16 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 18 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 8 5 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
]),
.cycle 12 1 true (4)
])
theorem kid14_part186_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part186) = true := by rfl

def kid14_part187 : Audit := .cycle 11 4 false (1)
theorem kid14_part187_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part187) = true := by rfl

def kid14_part188 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.cycle 23 1 false (-1),
.cycle 0 18 true (-1),
.split 17 (4,true) (byMove [
.cycle 0 18 true (-1),
.last 30 (4,false),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 18 (4,false),
.last 22 (4,false),
.cycle 0 18 true (-1),
.last 30 (4,false),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.last 22 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.last 22 (4,false),
.last 34 (4,false),
.cycle 1 17 true (-1),
.last 29 (4,false),
.cycle 1 20 true (-1),
.last 18 (4,false),
.cycle 1 22 true (-1)
]),
.cycle 17 4 false (1),
.cycle 0 17 true (-1),
.cycle 0 32 true (-1),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.split 17 (4,false) (byMove [
.cycle 11 26 true (-1),
.cycle 1 17 true (-1),
.cycle 31 1 false (1),
.cycle 1 20 true (-1),
.last 19 (4,true),
.cycle 1 22 true (-1),
.cycle 0 18 true (-1),
.cycle 14 17 true (2),
.cycle 0 44 true (-1),
.cycle 30 1 false (2),
.cycle 17 1 true (3),
.cycle 14 5 true (2),
.cycle 20 8 false (2),
.cycle 14 4 true (2),
.cycle 0 20 true (-1),
.cycle 28 1 false (0),
.last 19 (4,true),
.cycle 25 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 1, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.cycle 1 17 true (-1),
.cycle 0 32 true (-1),
.cycle 1 20 true (-1),
.cycle 17 1 true (3),
.cycle 1 22 true (-1)
]),
.cycle 14 4 true (2),
.cycle 18 7 false (2),
.cycle 1 20 true (-1),
.cycle 14 11 false (3),
.cycle 1 18 true (-1),
.split 17 (4,true) (byMove [
.cycle 14 5 false (3),
.cycle 0 21 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 18 (4,false),
.last 22 (4,false),
.cycle 1 18 true (-1),
.cycle 0 21 true (-1),
.last 23 (4,false),
.cycle 0 19 true (-1),
.last 19 (4,false),
.last 19 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.cycle 1 20 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.last 22 (4,false),
.last 34 (4,false),
.last 24 (4,false),
.last 20 (4,false),
.cycle 0 19 true (-1),
.last 19 (4,false),
.cycle 16 2 true (1)
]),
.cycle 17 4 false (1),
.cycle 27 4 true (1),
.cycle 11 22 true (-1),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.split 17 (4,false) (byMove [
.cycle 11 26 true (-1),
.cycle 14 15 false (3),
.cycle 18 6 false (2),
.cycle 0 19 true (-1),
.last 18 (4,true),
.cycle 16 2 true (2),
.cycle 0 18 true (-1),
.cycle 14 17 true (2),
.cycle 1 46 true (-1),
.cycle 3 15 true (-1),
.cycle 17 1 true (3),
.cycle 14 5 true (2),
.cycle 20 8 false (2),
.cycle 10 15 false (3),
.cycle 18 6 false (2),
.cycle 1 19 true (-1),
.last 18 (4,true),
.last 19 (4,true),
.cycle 13 24 true (1),
.cycle 27 4 true (1),
.cycle 11 22 true (-1),
.cycle 1 20 true (-1),
.cycle 17 1 true (3),
.last 24 (4,true)
]),
.cycle 9 15 false (3)
])
theorem kid14_part188_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part188) = true := by rfl

def kid14_part189 : Audit := .cycle 10 6 true (-2)
theorem kid14_part189_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part189) = true := by rfl

def kid14_part190 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 17 1 false (1),
.cycle 20 1 false (-2),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 1 18 true (0)
]),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (0),
.cycle 1 18 true (0),
.last 17 (4,true),
.cycle 1 18 true (0),
.cycle 0 16 true (0),
.cycle 32 1 false (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 24 1 false (0),
.cycle 25 1 false (-1),
.cycle 12 4 true (2),
.cycle 0 18 true (0),
.cycle 22 1 false (0),
.last 17 (4,true),
.cycle 22 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 30 1 false (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3),
.cycle 1 18 true (0)
]),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 1 18 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.split 15 (4,true) (byMove [
.cycle 12 5 false (3),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 0 19 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.last 17 (4,false),
.last 17 (4,false),
.cycle 20 1 false (-2),
.last 19 (4,false),
.cycle 1 18 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.last 18 (4,false),
.cycle 0 17 true (0),
.last 17 (4,false),
.cycle 14 2 true (1)
]),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.split 15 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 2, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.cycle 1 34 true (0),
.cycle 3 13 true (0),
.cycle 15 1 true (3),
.cycle 4 13 true (0),
.cycle 25 1 false (-1),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 1 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 15 1 true (3),
.cycle 1 18 true (0)
]),
.cycle 1 17 true (0)
])
theorem kid14_part190_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part190) = true := by rfl

def kid14_part192 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 22 true (-2),
.last 17 (4,false),
.cycle 0 20 true (-1),
.cycle 0 16 false (3),
.last 17 (4,false),
.cycle 0 19 true (-1),
.cycle 0 18 true (-1),
.last 24 (4,false),
.last 22 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 0 22 true (-2),
.last 17 (4,false),
.cycle 0 20 true (-1),
.cycle 10 5 false (1),
.last 17 (4,false),
.cycle 12 19 true (0),
.cycle 0 18 true (-1),
.cycle 2 13 false (3),
.cycle 1 23 true (-1),
.last 15 (4,false),
.cycle 12 6 true (-1)
])
theorem kid14_part192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part192) = true := by rfl

def kid14_part193 : Audit := .split 18 (4,false) (byMove [
.last 22 (5,true),
.cycle 11 16 false (3),
.cycle 23 1 false (-3),
.cycle 25 1 false (-3),
.cycle 29 1 false (-3),
.last 19 (5,true),
.last 22 (5,true),
.cycle 12 8 true (0),
.last 28 (5,true),
.cycle 13 6 true (0),
.cycle 1 19 false (3),
.last 19 (5,true),
.cycle 20 5 false (0),
.last 29 (5,true),
.last 27 (5,true),
.cycle 25 1 false (-3),
.last 26 (5,true),
.last 19 (5,true),
.last 22 (5,true),
.last 21 (5,true),
.last 20 (5,true),
.cycle 7 28 false (3),
.last 31 (5,true),
.last 19 (5,true)
])
theorem kid14_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part193) = true := by rfl

def kid14_part194 : Audit := .cycle 12 1 false (0)
theorem kid14_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part194) = true := by rfl

def kid14_part195 : Audit := .cycle 11 1 false (-1)
theorem kid14_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part195) = true := by rfl

def kid14_part196 : Audit := .split 11 (4,false) (byMove [
.last 24 (5,true),
.cycle 18 16 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 20 (5,true),
.last 14 (5,true),
.cycle 16 3 false (2),
.cycle 12 1 false (0),
.cycle 18 1 true (2),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 24 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.last 20 (5,true),
.cycle 7 14 false (3),
.cycle 27 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid14_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part196) = true := by rfl

def kid14_part197 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 11 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 11 8 true (-2),
.cycle 11 3 false (-1),
.cycle 11 6 true (-2),
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
theorem kid14_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part197) = true := by rfl

def kid14_part198 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 17 (4,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.last 24 (4,false),
.last 24 (4,false),
.last 22 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 1 18 true (0),
.last 17 (4,false),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 1 17 true (0)
])
theorem kid14_part198_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part198) = true := by rfl

def kid14_part199 : Audit := .split 18 (4,false) (byMove [
.last 22 (5,true),
.cycle 11 16 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 2 false (1),
.last 22 (5,true),
.cycle 11 8 true (0),
.cycle 16 3 false (2),
.cycle 13 6 true (0),
.last 22 (5,true),
.last 19 (5,true),
.cycle 14 5 false (3),
.last 21 (5,true),
.last 24 (5,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 2 false (1),
.last 22 (5,true),
.cycle 15 4 false (3),
.last 20 (5,true),
.cycle 7 14 true (0),
.last 22 (5,true),
.last 19 (5,true)
])
theorem kid14_part199_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part199) = true := by rfl

def kid14_part200 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.last 20 (5,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 0 18 true (-1),
.last 20 (5,true),
.cycle 11 3 false (1),
.last 18 (5,true),
.cycle 16 1 false (2),
.last 14 (5,true),
.cycle 11 5 false (1),
.last 16 (5,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 0 18 true (-1),
.cycle 11 4 false (1),
.last 15 (5,true),
.last 18 (5,true),
.cycle 0 36 true (-2),
.last 14 (5,true)
])
theorem kid14_part200_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part200) = true := by rfl

def kid14_part201 : Audit := .split 16 (4,false) (byMove [
.last 20 (5,true),
.cycle 11 16 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.last 20 (5,true),
.cycle 11 8 true (0),
.cycle 14 3 false (2),
.cycle 11 6 true (0),
.cycle 18 1 false (2),
.last 17 (5,true),
.cycle 12 5 false (3),
.last 19 (5,true),
.last 22 (5,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.last 20 (5,true),
.cycle 13 4 false (3),
.last 18 (5,true),
.cycle 7 12 true (0),
.cycle 13 9 false (3),
.last 17 (5,true)
])
theorem kid14_part201_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part201) = true := by rfl

def kid14_part202 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 12 3 false (3),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 13 (5,true),
.cycle 12 5 false (2),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 1 13 true (0),
.cycle 12 4 false (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 13 (5,true)
])
theorem kid14_part202_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part202) = true := by rfl

def kid14_part203 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 21 (4,false),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.last 24 (4,false),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 11 3 false (1),
.last 18 (4,false),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 11 4 true (1),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.last 18 (4,false),
.last 12 (4,false),
.cycle 15 3 true (3)
])
theorem kid14_part203_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part203) = true := by rfl

def kid14_part204 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.cycle 11 16 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.cycle 11 8 true (-3),
.cycle 13 3 false (-1),
.cycle 11 6 true (-3),
.cycle 10 6 false (0),
.last 16 (5,true),
.cycle 11 5 false (0),
.last 18 (5,true),
.last 21 (5,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 19 (5,true),
.cycle 12 4 false (0),
.last 17 (5,true),
.cycle 7 11 false (3),
.cycle 12 6 false (0),
.last 16 (5,true)
])
theorem kid14_part204_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part204) = true := by rfl

def kid14_part205 : Audit := .split 13 (5,true) (byMove [
.last 22 (4,false),
.last 23 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 20 true (-1),
.last 20 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 20 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 4 true (-1),
.cycle 0 20 true (-1),
.last 20 (4,false),
.last 20 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid14_part205_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part205) = true := by rfl

def kid14_part206 : Audit := .split 16 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 0 20 true (-1),
.last 19 (4,false),
.cycle 0 18 true (-1),
.cycle 0 20 true (-1),
.last 19 (4,false),
.cycle 0 17 true (-1),
.last 26 (4,false),
.last 26 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.cycle 1 20 true (-1),
.last 19 (4,false),
.cycle 1 18 true (-1),
.cycle 1 20 true (-1),
.last 19 (4,false),
.cycle 28 4 true (1),
.last 29 (4,false),
.cycle 2 15 true (-1),
.cycle 1 19 true (-1),
.last 17 (4,false),
.last 21 (4,false)
])
theorem kid14_part206_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part206) = true := by rfl

def kid14_part207 : Audit := .cycle 11 1 false (-1)
theorem kid14_part207_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part207) = true := by rfl

def kid14_part208 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 11 3 false (0),
.last 16 (5,true),
.cycle 10 2 true (-1),
.last 12 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 24 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 11 4 false (0),
.last 13 (5,true),
.last 16 (5,true),
.cycle 10 3 false (0),
.last 12 (5,true)
])
theorem kid14_part208_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part208) = true := by rfl

def kid14_part209 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 17 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 21 (5,true),
.cycle 17 8 true (-2),
.cycle 11 3 false (-1),
.cycle 15 6 true (-2),
.cycle 10 3 false (0),
.last 13 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 25 (5,true),
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
theorem kid14_part209_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part209) = true := by rfl

def kid14_part210 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (0),
.last 18 (4,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 18 (4,false),
.cycle 0 15 true (0),
.last 24 (4,false),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.last 23 (4,false),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.last 18 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 1 17 true (0)
])
theorem kid14_part210_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part210) = true := by rfl

def kid14_part211 : Audit := .split 14 (4,false) (byMove [
.last 18 (5,true),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 11 6 true (-2),
.last 18 (5,true),
.last 15 (5,true),
.cycle 11 5 false (1),
.last 17 (5,true),
.last 20 (5,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 18 (5,true),
.cycle 11 4 false (1),
.last 16 (5,true),
.cycle 7 10 false (3),
.last 18 (5,true),
.last 15 (5,true)
])
theorem kid14_part211_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part211) = true := by rfl

def kid14_part212 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 22 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 11 3 false (1),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 21 (4,false),
.cycle 1 21 true (0),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid14_part212_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part212) = true := by rfl

def kid14_part213 : Audit := .cycle 7 6 true (0)
theorem kid14_part213_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part213) = true := by rfl

def kid14_part214 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 13 16 false (1),
.last 14 (5,true),
.cycle 7 8 true (0),
.cycle 11 2 true (1),
.last 13 (5,true),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 8 22 true (0),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 13 (5,true),
.last 16 (5,true),
.last 19 (5,true),
.last 14 (5,true),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.last 13 (5,true),
.cycle 1 13 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 14 1 true (4),
.last 13 (5,true)
])
theorem kid14_part214_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part214) = true := by rfl

def kid14_part215 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 22 true (-1),
.last 14 (4,false),
.cycle 0 18 true (0),
.cycle 9 4 true (0),
.last 14 (4,false),
.cycle 7 6 true (0),
.last 24 (4,false),
.cycle 0 14 true (0),
.last 19 (4,false),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 22 true (-1),
.last 14 (4,false),
.cycle 1 18 true (0),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 11 4 true (1),
.cycle 1 14 true (0),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.last 12 (4,false),
.cycle 15 3 true (3)
])
theorem kid14_part215_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part215) = true := by rfl

def kid14_part191 : Audit := .split 10 (4,true) (byMove [(kid14_part192),(kid14_part193),(kid14_part194),(kid14_part195),(kid14_part196),(kid14_part197),(kid14_part198),(kid14_part199),(kid14_part200),(kid14_part201),(kid14_part202),(kid14_part203),(kid14_part204),(kid14_part205),(kid14_part206),(kid14_part207),(kid14_part208),(kid14_part209),(kid14_part210),(kid14_part211),(kid14_part212),(kid14_part213),(kid14_part214),(kid14_part215)])

theorem kid14_part191_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part191) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part192),(kid14_part193),(kid14_part194),(kid14_part195),(kid14_part196),(kid14_part197),(kid14_part198),(kid14_part199),(kid14_part200),(kid14_part201),(kid14_part202),(kid14_part203),(kid14_part204),(kid14_part205),(kid14_part206),(kid14_part207),(kid14_part208),(kid14_part209),(kid14_part210),(kid14_part211),(kid14_part212),(kid14_part213),(kid14_part214),(kid14_part215)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part192_checked

  · exact kid14_part198_checked

  · exact kid14_part204_checked

  · exact kid14_part210_checked

  · exact kid14_part193_checked

  · exact kid14_part199_checked

  · exact kid14_part205_checked

  · exact kid14_part211_checked

  · exact kid14_part194_checked

  · exact kid14_part200_checked

  · exact kid14_part206_checked

  · exact kid14_part212_checked

  · exact kid14_part195_checked

  · exact kid14_part201_checked

  · exact kid14_part207_checked

  · exact kid14_part213_checked

  · exact kid14_part196_checked

  · exact kid14_part202_checked

  · exact kid14_part208_checked

  · exact kid14_part214_checked

  · exact kid14_part197_checked

  · exact kid14_part203_checked

  · exact kid14_part209_checked

  · exact kid14_part215_checked

def kid14_part216 : Audit := .split 10 (5,true) (byMove [
.cycle 1 15 false (3),
.cycle 0 30 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 22 (4,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 21 (4,true),
.last 15 (4,true),
.last 27 (4,true),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 12 1 false (2),
.last 12 (4,false),
.cycle 12 1 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.last 16 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 17 1 false (1),
.last 12 (4,false),
.last 16 (4,false)
]),
.cycle 12 1 false (2),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.last 19 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.last 19 (4,true),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 10 2 true (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.last 21 (4,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.last 17 (4,true),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 7 6 true (0),
.split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 17 (4,false),
.last 13 (4,false),
.last 13 (4,false),
.cycle 7 6 true (0),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 18 1 false (0),
.last 12 (4,false),
.last 23 (4,false),
.cycle 15 1 false (-1),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 17 (4,false),
.last 13 (4,false),
.cycle 10 2 true (0),
.last 16 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 4 8 true (0),
.last 12 (4,false),
.last 16 (4,false)
]),
.cycle 14 3 true (2)
])
theorem kid14_part216_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part216) = true := by rfl

def kid14_part217 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.last 28 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.last 20 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.last 27 (4,false),
.cycle 1 24 true (0),
.last 15 (4,false),
.cycle 9 6 true (0)
]),
.cycle 0 20 true (-1),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.split 14 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 1 24 true (0),
.last 16 (4,true),
.cycle 9 6 true (1),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0),
.cycle 15 9 false (2),
.cycle 12 4 true (1),
.cycle 1 17 true (1),
.cycle 26 1 false (0),
.last 16 (4,true),
.cycle 11 6 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0)
]),
.cycle 1 15 true (1),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.last 26 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 20 (4,false),
.cycle 1 20 true (0),
.last 26 (4,false),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 16 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 20 (4,false),
.cycle 1 20 true (0),
.last 22 (4,false),
.last 17 (4,false),
.cycle 7 10 true (0),
.last 16 (4,false),
.cycle 13 2 true (0)
]),
.cycle 13 12 false (1),
.cycle 10 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.split 14 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 15 12 true (-2),
.cycle 0 24 true (-1),
.cycle 7 10 true (1),
.last 15 (4,true),
.cycle 13 2 true (1),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0),
.cycle 16 9 false (2),
.cycle 15 12 true (-2),
.cycle 15 7 false (1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 11 4 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0)
]),
.cycle 1 15 true (1)
])
theorem kid14_part217_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part217) = true := by rfl

def kid14_part218 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 0 17 true (-1),
.cycle 1 15 false (3),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 1 14 true (1),
.cycle 15 8 false (1),
.cycle 1 17 true (-1),
.cycle 0 22 true (-2),
.cycle 1 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 1 14 true (1)
]),
.cycle 1 15 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 20 true (1),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 1 14 true (1),
.cycle 16 13 false (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (4,true),
.cycle 16 13 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 13 true (1),
.cycle 18 7 false (0),
.cycle 1 29 true (-2),
.cycle 19 5 false (2),
.cycle 1 14 true (1),
.split 13 (4,true) (byMove [
.cycle 15 5 false (2),
.cycle 0 28 true (-1),
.cycle 0 19 true (-1),
.cycle 23 1 false (-1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 15 8 false (1),
.last 28 (4,false),
.cycle 1 29 true (-2),
.cycle 23 1 false (-1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.last 17 (4,false),
.last 19 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 12 2 true (1)
]),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 22 7 false (2),
.cycle 1 21 false (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 1 28 true (1),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1),
.cycle 16 13 false (2),
.cycle 22 7 false (2),
.cycle 14 9 false (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 13 true (1)
])
theorem kid14_part218_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part218) = true := by rfl

def kid14_part219 : Audit := .cycle 0 12 true (0)
theorem kid14_part219_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part219) = true := by rfl

def kid14_part220 : Audit := .cycle 4 6 true (1)
theorem kid14_part220_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part220) = true := by rfl

def kid14_part222 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 26 true (-2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 19 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.cycle 20 9 false (0),
.cycle 1 33 true (-2),
.cycle 21 7 false (2),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.cycle 1 17 true (1)
])
theorem kid14_part222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part222) = true := by rfl

def kid14_part223 : Audit := .cycle 11 8 true (-2)
theorem kid14_part223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part223) = true := by rfl

def kid14_part224 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 3 false (2),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 19 3 false (1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 19 3 false (1),
.cycle 1 21 true (0),
.cycle 13 3 false (1),
.cycle 9 4 true (0)
])
theorem kid14_part224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part224) = true := by rfl

def kid14_part225 : Audit := .cycle 7 6 true (1)
theorem kid14_part225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part225) = true := by rfl

def kid14_part226 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.last 18 (5,true),
.cycle 17 1 false (-1),
.last 16 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 13 3 true (3),
.cycle 13 6 false (1),
.last 18 (5,true),
.cycle 12 8 true (-2),
.last 16 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 2 true (1),
.cycle 13 3 true (3)
])
theorem kid14_part226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part226) = true := by rfl

def kid14_part227 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 22 true (-1),
.cycle 17 1 false (-1),
.cycle 0 18 true (0),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 4 true (1),
.last 13 (4,true),
.cycle 13 6 false (1),
.cycle 1 22 true (-1),
.cycle 12 8 true (-2),
.cycle 1 18 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 11 4 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 2 true (1),
.last 13 (4,true)
])
theorem kid14_part227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part227) = true := by rfl

def kid14_part228 : Audit := .cycle 1 11 true (1)
theorem kid14_part228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part228) = true := by rfl

def kid14_part229 : Audit := .cycle 0 14 true (0)
theorem kid14_part229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part229) = true := by rfl

def kid14_part230 : Audit := .cycle 8 16 true (1)
theorem kid14_part230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part230) = true := by rfl

def kid14_part231 : Audit := .cycle 0 12 true (0)
theorem kid14_part231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part231) = true := by rfl

def kid14_part232 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.cycle 13 1 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 2 true (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
])
theorem kid14_part232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part232) = true := by rfl

def kid14_part233 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (2),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 17 10 false (1),
.cycle 1 33 true (-2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 10 2 true (2),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part233) = true := by rfl

def kid14_part234 : Audit := .split 14 (5,true) (byMove [
.cycle 1 19 true (-1),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 5 false (-1),
.cycle 15 5 false (0),
.cycle 16 5 false (2),
.cycle 26 5 false (5),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 17 5 false (1),
.last 16 (4,true),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 18 5 false (2),
.cycle 15 1 false (-1),
.cycle 17 5 false (-1),
.last 16 (4,true),
.cycle 12 4 true (0),
.cycle 1 20 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.cycle 15 5 false (1),
.last 16 (4,true)
])
theorem kid14_part234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part234) = true := by rfl

def kid14_part235 : Audit := .cycle 11 8 true (-2)
theorem kid14_part235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part235) = true := by rfl

def kid14_part236 : Audit := .split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.cycle 13 3 false (0),
.cycle 15 3 false (1),
.cycle 26 3 false (4),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 18 3 false (2),
.last 14 (4,true),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 11 4 true (0),
.cycle 1 18 true (0),
.cycle 1 15 true (0),
.cycle 17 3 false (1),
.cycle 13 3 false (1),
.last 14 (4,true)
])
theorem kid14_part236_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part236) = true := by rfl

def kid14_part237 : Audit := .cycle 5 6 true (1)
theorem kid14_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part237) = true := by rfl

def kid14_part238 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 23 1 false (5),
.last 12 (5,true),
.cycle 13 6 false (1),
.last 23 (5,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 12 3 true (2),
.last 12 (5,true)
])
theorem kid14_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part238) = true := by rfl

def kid14_part239 : Audit := .split 11 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 12 4 true (2),
.cycle 13 6 false (1),
.cycle 20 3 false (0),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 13 4 true (1),
.cycle 1 20 true (0),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 12 4 true (2)
])
theorem kid14_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part239) = true := by rfl

def kid14_part240 : Audit := .cycle 1 11 true (1)
theorem kid14_part240_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part240) = true := by rfl

def kid14_part241 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 24 true (-1),
.cycle 0 20 true (-1),
.cycle 0 20 true (0),
.last 14 (4,true),
.cycle 0 20 true (-1),
.cycle 7 8 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 7 8 true (1),
.last 15 (4,true),
.cycle 15 8 false (1),
.cycle 1 24 true (-1),
.cycle 14 10 true (-2),
.cycle 1 20 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 11 4 true (1),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 10 4 true (1),
.last 15 (4,true)
])
theorem kid14_part241_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part241) = true := by rfl

def kid14_part242 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 15 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 2 13 true (1),
.cycle 18 7 false (0),
.cycle 1 29 true (-2),
.cycle 19 5 false (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.cycle 2 13 true (1)
])
theorem kid14_part242_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part242) = true := by rfl

def kid14_part243 : Audit := .cycle 0 12 true (0)
theorem kid14_part243_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part243) = true := by rfl

def kid14_part244 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 15 1 true (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 true (5),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.last 15 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
])
theorem kid14_part244_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part244) = true := by rfl

def kid14_part245 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 21 5 false (1),
.cycle 15 2 true (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 2 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 2 true (4),
.cycle 3 9 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part245_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part245) = true := by rfl

def kid14_part221 : Audit := .split 10 (4,false) (byMove [(kid14_part222),(kid14_part223),(kid14_part224),(kid14_part225),(kid14_part226),(kid14_part227),(kid14_part228),(kid14_part229),(kid14_part230),(kid14_part231),(kid14_part232),(kid14_part233),(kid14_part234),(kid14_part235),(kid14_part236),(kid14_part237),(kid14_part238),(kid14_part239),(kid14_part240),(kid14_part241),(kid14_part242),(kid14_part243),(kid14_part244),(kid14_part245)])

theorem kid14_part221_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part221) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part222),(kid14_part223),(kid14_part224),(kid14_part225),(kid14_part226),(kid14_part227),(kid14_part228),(kid14_part229),(kid14_part230),(kid14_part231),(kid14_part232),(kid14_part233),(kid14_part234),(kid14_part235),(kid14_part236),(kid14_part237),(kid14_part238),(kid14_part239),(kid14_part240),(kid14_part241),(kid14_part242),(kid14_part243),(kid14_part244),(kid14_part245)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part222_checked

  · exact kid14_part228_checked

  · exact kid14_part234_checked

  · exact kid14_part240_checked

  · exact kid14_part223_checked

  · exact kid14_part229_checked

  · exact kid14_part235_checked

  · exact kid14_part241_checked

  · exact kid14_part224_checked

  · exact kid14_part230_checked

  · exact kid14_part236_checked

  · exact kid14_part242_checked

  · exact kid14_part225_checked

  · exact kid14_part231_checked

  · exact kid14_part237_checked

  · exact kid14_part243_checked

  · exact kid14_part226_checked

  · exact kid14_part232_checked

  · exact kid14_part238_checked

  · exact kid14_part244_checked

  · exact kid14_part227_checked

  · exact kid14_part233_checked

  · exact kid14_part239_checked

  · exact kid14_part245_checked

def kid14_part246 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 21 5 false (1),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 13 1 true (3),
.last 17 (4,false),
.last 30 (4,false),
.last 15 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 13 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 13 1 true (3)
]),
.cycle 15 1 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 true (4),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.last 34 (4,true),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
]),
.cycle 12 1 true (4),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 19 5 false (2),
.cycle 13 10 true (-2),
.last 15 (4,false),
.cycle 7 8 true (1),
.last 15 (4,false),
.last 20 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 14 1 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 13 10 true (-2),
.last 15 (4,false),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 13 3 false (1),
.cycle 1 13 true (1),
.last 26 (4,false),
.last 21 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 11 2 true (2)
]),
.cycle 13 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 17 14 true (-2),
.cycle 23 1 true (-1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5),
.last 34 (4,true),
.last 22 (4,true),
.last 26 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 13 1 true (5)
]),
.cycle 12 1 true (4)
])
theorem kid14_part246_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part246) = true := by rfl

def kid14_part126 : Audit := .split 9 (5,false) (byMove [(kid14_part127),(kid14_part128),(kid14_part129),(kid14_part130),(kid14_part131),(kid14_part156),(kid14_part157),(kid14_part158),(kid14_part159),(kid14_part160),(kid14_part161),(kid14_part186),(kid14_part187),(kid14_part188),(kid14_part189),(kid14_part190),(kid14_part191),(kid14_part216),(kid14_part217),(kid14_part218),(kid14_part219),(kid14_part220),(kid14_part221),(kid14_part246)])

theorem kid14_part126_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (kid14_part126) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid14_part127),(kid14_part128),(kid14_part129),(kid14_part130),(kid14_part131),(kid14_part156),(kid14_part157),(kid14_part158),(kid14_part159),(kid14_part160),(kid14_part161),(kid14_part186),(kid14_part187),(kid14_part188),(kid14_part189),(kid14_part190),(kid14_part191),(kid14_part216),(kid14_part217),(kid14_part218),(kid14_part219),(kid14_part220),(kid14_part221),(kid14_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part127_checked

  · exact kid14_part157_checked

  · exact kid14_part187_checked

  · exact kid14_part217_checked

  · exact kid14_part128_checked

  · exact kid14_part158_checked

  · exact kid14_part188_checked

  · exact kid14_part218_checked

  · exact kid14_part129_checked

  · exact kid14_part159_checked

  · exact kid14_part189_checked

  · exact kid14_part219_checked

  · exact kid14_part130_checked

  · exact kid14_part160_checked

  · exact kid14_part190_checked

  · exact kid14_part220_checked

  · exact kid14_part131_checked

  · exact kid14_part161_checked

  · exact kid14_part191_checked

  · exact kid14_part221_checked

  · exact kid14_part156_checked

  · exact kid14_part186_checked

  · exact kid14_part216_checked

  · exact kid14_part246_checked

def kid14_part247 : Audit := .cycle 1 9 true (1)
theorem kid14_part247_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,0⟩)) (kid14_part247) = true := by rfl

def kid14_part248 : Audit := .cycle 0 12 true (0)
theorem kid14_part248_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,1⟩)) (kid14_part248) = true := by rfl

def kid14_part249 : Audit := .cycle 25 1 false (7)
theorem kid14_part249_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,2⟩)) (kid14_part249) = true := by rfl

def kid14_part250 : Audit := .cycle 0 10 true (0)
theorem kid14_part250_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,3⟩)) (kid14_part250) = true := by rfl

def kid14_part252 : Audit := .cycle 0 10 true (0)
theorem kid14_part252_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part252) = true := by rfl

def kid14_part253 : Audit := .cycle 1 9 true (1)
theorem kid14_part253_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part253) = true := by rfl

def kid14_part254 : Audit := .cycle 20 1 false (2)
theorem kid14_part254_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part254) = true := by rfl

def kid14_part255 : Audit := .cycle 17 1 false (1)
theorem kid14_part255_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part255) = true := by rfl

def kid14_part256 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 10 2 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (9),
.cycle 1 24 true (0),
.cycle 10 2 true (2),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 5 false (1),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 10 5 true (0),
.cycle 0 24 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 13 6 false (1),
.last 25 (5,true),
.last 26 (5,true),
.cycle 19 1 false (-1),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 16 (5,true),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.cycle 13 4 false (1),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (2),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 14 true (2),
.cycle 3 9 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3)
])
])
theorem kid14_part256_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part256) = true := by rfl

def kid14_part258 : Audit := .cycle 0 11 true (0)
theorem kid14_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part258) = true := by rfl

def kid14_part259 : Audit := .cycle 1 10 true (1)
theorem kid14_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part259) = true := by rfl

def kid14_part260 : Audit := .cycle 21 1 false (1)
theorem kid14_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part260) = true := by rfl

def kid14_part261 : Audit := .cycle 1 13 true (0)
theorem kid14_part261_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part261) = true := by rfl

def kid14_part262 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 14 (5,true)
])
theorem kid14_part262_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part262) = true := by rfl

def kid14_part263 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 15 (4,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid14_part263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part263) = true := by rfl

def kid14_part264 : Audit := .cycle 0 11 true (0)
theorem kid14_part264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part264) = true := by rfl

def kid14_part265 : Audit := .cycle 1 10 true (1)
theorem kid14_part265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part265) = true := by rfl

def kid14_part266 : Audit := .cycle 1 24 true (0)
theorem kid14_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part266) = true := by rfl

def kid14_part267 : Audit := .cycle 20 1 false (2)
theorem kid14_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part267) = true := by rfl

def kid14_part268 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 10 2 true (2),
.cycle 7 6 true (2),
.cycle 11 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2)
])
theorem kid14_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part268) = true := by rfl

def kid14_part269 : Audit := .cycle 10 1 true (2)
theorem kid14_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part269) = true := by rfl

def kid14_part270 : Audit := .cycle 17 5 false (1)
theorem kid14_part270_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part270) = true := by rfl

def kid14_part271 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 11 16 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 20 true (1),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 10 4 true (1),
.cycle 11 24 true (-2),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (5,true),
.cycle 15 12 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 1 18 true (1)
])
theorem kid14_part271_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part271) = true := by rfl

def kid14_part272 : Audit := .cycle 0 13 true (0)
theorem kid14_part272_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part272) = true := by rfl

def kid14_part273 : Audit := .cycle 18 1 false (0)
theorem kid14_part273_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part273) = true := by rfl

def kid14_part274 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 24 true (-1),
.cycle 15 1 false (1),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 38 1 false (8),
.cycle 0 13 true (0),
.cycle 14 3 false (0),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 18 7 false (2),
.cycle 0 24 true (-2),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid14_part274_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part274) = true := by rfl

def kid14_part275 : Audit := .split 12 (5,true) (byMove [
.last 22 (4,false),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 1 16 true (0),
.cycle 15 1 false (1),
.cycle 1 14 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.last 18 (4,false),
.cycle 1 14 true (0),
.last 15 (4,false),
.cycle 13 3 true (1)
])
theorem kid14_part275_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part275) = true := by rfl

def kid14_part276 : Audit := .cycle 0 11 true (0)
theorem kid14_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part276) = true := by rfl

def kid14_part277 : Audit := .cycle 1 10 true (1)
theorem kid14_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part277) = true := by rfl

def kid14_part278 : Audit := .cycle 2 9 true (1)
theorem kid14_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part278) = true := by rfl

def kid14_part279 : Audit := .cycle 1 13 true (1)
theorem kid14_part279_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part279) = true := by rfl

def kid14_part280 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 19 19 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2)
])
theorem kid14_part280_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part280) = true := by rfl

def kid14_part281 : Audit := .cycle 10 1 true (2)
theorem kid14_part281_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part281) = true := by rfl

def kid14_part257 : Audit := .split 10 (5,false) (byMove [(kid14_part258),(kid14_part259),(kid14_part260),(kid14_part261),(kid14_part262),(kid14_part263),(kid14_part264),(kid14_part265),(kid14_part266),(kid14_part267),(kid14_part268),(kid14_part269),(kid14_part270),(kid14_part271),(kid14_part272),(kid14_part273),(kid14_part274),(kid14_part275),(kid14_part276),(kid14_part277),(kid14_part278),(kid14_part279),(kid14_part280),(kid14_part281)])

theorem kid14_part257_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part257) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid14_part258),(kid14_part259),(kid14_part260),(kid14_part261),(kid14_part262),(kid14_part263),(kid14_part264),(kid14_part265),(kid14_part266),(kid14_part267),(kid14_part268),(kid14_part269),(kid14_part270),(kid14_part271),(kid14_part272),(kid14_part273),(kid14_part274),(kid14_part275),(kid14_part276),(kid14_part277),(kid14_part278),(kid14_part279),(kid14_part280),(kid14_part281)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part258_checked

  · exact kid14_part264_checked

  · exact kid14_part270_checked

  · exact kid14_part276_checked

  · exact kid14_part259_checked

  · exact kid14_part265_checked

  · exact kid14_part271_checked

  · exact kid14_part277_checked

  · exact kid14_part260_checked

  · exact kid14_part266_checked

  · exact kid14_part272_checked

  · exact kid14_part278_checked

  · exact kid14_part261_checked

  · exact kid14_part267_checked

  · exact kid14_part273_checked

  · exact kid14_part279_checked

  · exact kid14_part262_checked

  · exact kid14_part268_checked

  · exact kid14_part274_checked

  · exact kid14_part280_checked

  · exact kid14_part263_checked

  · exact kid14_part269_checked

  · exact kid14_part275_checked

  · exact kid14_part281_checked

def kid14_part282 : Audit := .cycle 0 10 true (0)
theorem kid14_part282_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part282) = true := by rfl

def kid14_part283 : Audit := .cycle 1 9 true (1)
theorem kid14_part283_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part283) = true := by rfl

def kid14_part284 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (0),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 24 2 false (6),
.cycle 25 1 false (5),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 24 2 true (5),
.cycle 25 1 true (5),
.cycle 31 1 false (7),
.cycle 1 33 true (0),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 24 2 false (6),
.cycle 25 1 false (5),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (9),
.cycle 1 28 true (0),
.last 27 (5,true),
.cycle 25 1 true (5)
]),
.cycle 0 25 true (0),
.cycle 35 1 false (11),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 24 2 true (6),
.cycle 25 1 false (7),
.cycle 0 26 true (0),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.cycle 26 1 false (8),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 31 1 false (9),
.cycle 23 4 true (5),
.cycle 0 28 true (0),
.cycle 26 1 false (6),
.last 27 (5,true),
.cycle 25 1 false (7),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (11),
.cycle 1 28 true (0),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
]),
.cycle 30 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.split 25 (5,false) (byMove [
.cycle 27 5 true (5),
.cycle 0 29 true (0),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 24 2 false (6),
.cycle 25 1 false (5),
.cycle 1 26 true (0),
.cycle 0 29 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 28 1 false (8),
.last 26 (5,true),
.cycle 21 7 true (3),
.cycle 42 1 false (10),
.cycle 1 28 true (0),
.cycle 26 1 false (4),
.cycle 24 2 false (6),
.cycle 25 1 false (5),
.cycle 1 26 true (0),
.cycle 30 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 21 13 true (3),
.last 26 (5,true)
]),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 34 1 false (10),
.cycle 1 27 true (0),
.cycle 24 1 true (6),
.split 25 (5,false) (byMove [
.cycle 1 26 true (0),
.cycle 0 29 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 28 1 false (8),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 52 1 false (14),
.cycle 21 12 true (3),
.cycle 34 1 false (10),
.cycle 24 2 true (6),
.cycle 25 1 true (7),
.cycle 31 1 false (9),
.cycle 1 29 true (0),
.cycle 29 1 false (9),
.cycle 1 27 true (0),
.cycle 22 4 true (4),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 1 28 true (0),
.cycle 24 2 true (6),
.cycle 25 1 true (7)
])
])
theorem kid14_part284_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part284) = true := by rfl

def kid14_part285 : Audit := .cycle 1 20 true (0)
theorem kid14_part285_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part285) = true := by rfl

def kid14_part286 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.cycle 15 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 15 2 false (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 10 2 true (3),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 1 19 true (1),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 16 2 false (2),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 11 1 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 10 2 true (4),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.last 13 (5,true),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
]),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.cycle 19 1 false (5),
.split 11 (5,false) (byMove [
.cycle 13 5 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 15 2 false (1),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 9 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 23 1 false (3),
.cycle 19 2 false (5),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
])
theorem kid14_part286_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part286) = true := by rfl

def kid14_part288 : Audit := .cycle 0 11 true (0)
theorem kid14_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part288) = true := by rfl

def kid14_part289 : Audit := .cycle 1 10 true (1)
theorem kid14_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part289) = true := by rfl

def kid14_part290 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 1 22 true (0),
.cycle 0 25 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.cycle 25 1 false (5),
.cycle 33 1 false (5),
.last 38 (4,false),
.cycle 1 24 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 1 22 true (0),
.cycle 27 1 false (5),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 34 1 false (6),
.last 25 (4,false)
])
theorem kid14_part290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part290) = true := by rfl

def kid14_part291 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 21 1 false (3),
.cycle 25 1 false (3),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 1 22 true (0),
.last 20 (4,false),
.cycle 0 22 true (0)
])
theorem kid14_part291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part291) = true := by rfl

def kid14_part292 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 11 1 true (3),
.cycle 10 2 true (3),
.cycle 7 6 true (2),
.cycle 11 3 true (2),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (3)
])
theorem kid14_part292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part292) = true := by rfl

def kid14_part293 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 19 1 false (1),
.last 17 (4,false),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 1 17 true (0),
.last 15 (4,false),
.cycle 13 2 true (0)
])
theorem kid14_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part293) = true := by rfl

def kid14_part294 : Audit := .cycle 0 11 true (0)
theorem kid14_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part294) = true := by rfl

def kid14_part295 : Audit := .cycle 1 10 true (1)
theorem kid14_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part295) = true := by rfl

def kid14_part296 : Audit := .split 23 (5,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 91 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.last 24 (4,false),
.cycle 33 1 false (9),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.cycle 29 1 false (9),
.cycle 45 1 false (9),
.last 50 (4,false),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.last 24 (4,false),
.cycle 33 1 false (9),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.cycle 51 15 true (7),
.cycle 5 19 true (0),
.cycle 24 13 true (4),
.cycle 26 11 true (6)
])
theorem kid14_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part296) = true := by rfl

def kid14_part297 : Audit := .split 21 (5,true) (byMove [
.last 40 (4,false),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 23 1 false (3),
.cycle 27 1 false (7),
.cycle 1 25 true (0),
.cycle 25 1 false (7),
.cycle 1 23 true (0),
.last 24 (4,false),
.cycle 25 1 false (7),
.cycle 37 1 false (7),
.last 28 (4,false),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 29 1 false (7),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.last 36 (4,false),
.cycle 1 23 true (0),
.last 24 (4,false),
.cycle 3 22 true (0)
])
theorem kid14_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part297) = true := by rfl

def kid14_part298 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 18 1 false (2),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 17 (5,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part298) = true := by rfl

def kid14_part299 : Audit := .cycle 10 1 true (4)
theorem kid14_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part299) = true := by rfl

def kid14_part300 : Audit := .cycle 7 5 true (2)
theorem kid14_part300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part300) = true := by rfl

def kid14_part301 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 6 true (3),
.cycle 1 18 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (5,true),
.last 22 (5,true),
.cycle 13 1 true (5),
.cycle 10 4 true (3),
.cycle 7 8 true (2),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (5,true),
.cycle 5 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 1 18 true (1)
])
theorem kid14_part301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part301) = true := by rfl

def kid14_part302 : Audit := .cycle 0 13 true (0)
theorem kid14_part302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part302) = true := by rfl

def kid14_part303 : Audit := .split 19 (5,true) (byMove [
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (1),
.cycle 1 20 true (0),
.cycle 0 23 true (0),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 22 1 false (4),
.cycle 30 1 false (4),
.last 34 (4,false),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (1),
.cycle 1 20 true (0),
.cycle 24 1 false (4),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 29 1 false (5),
.cycle 1 23 true (0)
])
theorem kid14_part303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part303) = true := by rfl

def kid14_part304 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 21 (5,true),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 27 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.last 16 (5,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 19 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
])
theorem kid14_part304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part304) = true := by rfl

def kid14_part305 : Audit := .split 14 (5,true) (byMove [
.last 23 (4,false),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 1 20 true (0),
.cycle 32 1 false (8),
.last 19 (4,false),
.cycle 21 1 false (5),
.last 19 (4,false),
.cycle 19 1 false (5),
.cycle 39 1 false (5),
.last 25 (4,false),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 1 20 true (0),
.cycle 1 22 true (0),
.last 19 (4,false),
.cycle 1 23 true (0),
.last 19 (4,false),
.cycle 17 3 true (3)
])
theorem kid14_part305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part305) = true := by rfl

def kid14_part306 : Audit := .cycle 0 11 true (0)
theorem kid14_part306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part306) = true := by rfl

def kid14_part307 : Audit := .cycle 1 10 true (1)
theorem kid14_part307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part307) = true := by rfl

def kid14_part308 : Audit := .cycle 2 9 true (1)
theorem kid14_part308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part308) = true := by rfl

def kid14_part309 : Audit := .cycle 1 13 true (1)
theorem kid14_part309_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part309) = true := by rfl

def kid14_part310 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 25 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part310_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part310) = true := by rfl

def kid14_part311 : Audit := .cycle 10 1 true (4)
theorem kid14_part311_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part311) = true := by rfl

def kid14_part287 : Audit := .split 10 (5,false) (byMove [(kid14_part288),(kid14_part289),(kid14_part290),(kid14_part291),(kid14_part292),(kid14_part293),(kid14_part294),(kid14_part295),(kid14_part296),(kid14_part297),(kid14_part298),(kid14_part299),(kid14_part300),(kid14_part301),(kid14_part302),(kid14_part303),(kid14_part304),(kid14_part305),(kid14_part306),(kid14_part307),(kid14_part308),(kid14_part309),(kid14_part310),(kid14_part311)])

theorem kid14_part287_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part287) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part288),(kid14_part289),(kid14_part290),(kid14_part291),(kid14_part292),(kid14_part293),(kid14_part294),(kid14_part295),(kid14_part296),(kid14_part297),(kid14_part298),(kid14_part299),(kid14_part300),(kid14_part301),(kid14_part302),(kid14_part303),(kid14_part304),(kid14_part305),(kid14_part306),(kid14_part307),(kid14_part308),(kid14_part309),(kid14_part310),(kid14_part311)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part288_checked

  · exact kid14_part294_checked

  · exact kid14_part300_checked

  · exact kid14_part306_checked

  · exact kid14_part289_checked

  · exact kid14_part295_checked

  · exact kid14_part301_checked

  · exact kid14_part307_checked

  · exact kid14_part290_checked

  · exact kid14_part296_checked

  · exact kid14_part302_checked

  · exact kid14_part308_checked

  · exact kid14_part291_checked

  · exact kid14_part297_checked

  · exact kid14_part303_checked

  · exact kid14_part309_checked

  · exact kid14_part292_checked

  · exact kid14_part298_checked

  · exact kid14_part304_checked

  · exact kid14_part310_checked

  · exact kid14_part293_checked

  · exact kid14_part299_checked

  · exact kid14_part305_checked

  · exact kid14_part311_checked

def kid14_part312 : Audit := .cycle 7 4 true (2)
theorem kid14_part312_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part312) = true := by rfl

def kid14_part313 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 1 23 true (-1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.cycle 1 23 true (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.cycle 12 2 true (3),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.cycle 14 14 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 13 1 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 19 true (2),
.cycle 8 14 true (2),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.cycle 12 2 true (4),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 24 true (2),
.cycle 8 19 true (2),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 8 14 true (2),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
]),
.cycle 7 7 true (2),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 14 17 true (1),
.split 13 (5,false) (byMove [
.cycle 10 5 true (2),
.cycle 7 11 true (1),
.cycle 45 1 false (1),
.cycle 7 9 true (2),
.cycle 14 23 true (-1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 9 5 true (2),
.last 14 (5,true),
.cycle 8 11 true (2),
.cycle 5 11 true (1),
.cycle 8 9 true (2),
.cycle 5 9 true (1),
.cycle 14 17 true (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 8 11 true (2),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 9 5 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.cycle 12 2 true (4),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (4),
.cycle 13 1 true (5)
])
])
theorem kid14_part313_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part313) = true := by rfl

def kid14_part314 : Audit := .cycle 0 12 true (0)
theorem kid14_part314_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part314) = true := by rfl

def kid14_part315 : Audit := .cycle 17 1 false (1)
theorem kid14_part315_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part315) = true := by rfl

def kid14_part316 : Audit := .split 10 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 1 19 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 20 11 false (2),
.cycle 16 1 false (0),
.cycle 0 19 true (0),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (1),
.last 13 (5,true),
.cycle 13 6 false (1),
.last 37 (5,true),
.cycle 12 8 true (-2),
.cycle 1 19 true (0),
.cycle 13 2 false (-1),
.last 12 (5,true),
.last 17 (5,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.last 13 (5,true)
]),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 41 1 false (9),
.cycle 0 12 true (0),
.cycle 9 2 true (2),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 31 (5,false),
.cycle 1 24 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
]),
.cycle 17 5 false (1),
.cycle 15 12 true (-2),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 17 (5,true),
.cycle 1 33 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 2 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 13 6 false (1),
.last 25 (5,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 2 false (-1),
.last 12 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 13 true (1),
.cycle 13 4 false (1),
.last 12 (5,true)
]),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 15 3 false (1),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (5,false),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 16 3 false (0),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
])
theorem kid14_part316_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part316) = true := by rfl

def kid14_part318 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 17 (5,true),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 25 true (2),
.cycle 12 18 true (2),
.cycle 14 1 true (4),
.cycle 0 16 true (0),
.cycle 12 9 true (2),
.cycle 12 3 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 17 (5,true),
.cycle 12 5 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (4),
.cycle 1 16 true (1)
])
theorem kid14_part318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part318) = true := by rfl

def kid14_part319 : Audit := .cycle 0 14 true (0)
theorem kid14_part319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part319) = true := by rfl

def kid14_part320 : Audit := .cycle 21 1 false (1)
theorem kid14_part320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part320) = true := by rfl

def kid14_part321 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 0 58 true (0),
.cycle 7 43 true (0),
.cycle 7 28 true (0),
.cycle 16 1 true (4),
.cycle 3 15 true (0),
.cycle 7 17 true (0),
.cycle 14 3 true (2),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.last 19 (5,true),
.cycle 7 13 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 256, 256, 128, 256, 8, 128, 256, 128, 4096],[128, 1, 16, 1, 16, 4096, 128, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 19 true (0),
.cycle 16 1 true (4),
.cycle 0 19 true (0)
])
theorem kid14_part321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part321) = true := by rfl

def kid14_part322 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 30 11 false (2),
.cycle 15 1 false (1),
.cycle 1 19 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 4 true (1),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 16 3 true (2),
.cycle 12 8 true (-2),
.cycle 4 13 true (0),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 18 (5,true),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.last 14 (5,true)
])
theorem kid14_part322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part322) = true := by rfl

def kid14_part323 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 15 (4,false),
.last 18 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 18 (4,false),
.last 13 (4,false),
.cycle 11 2 true (0)
])
theorem kid14_part323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part323) = true := by rfl

def kid14_part324 : Audit := .cycle 1 11 true (1)
theorem kid14_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part324) = true := by rfl

def kid14_part325 : Audit := .cycle 0 14 true (0)
theorem kid14_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part325) = true := by rfl

def kid14_part326 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (5),
.cycle 27 1 false (3),
.cycle 19 1 false (1),
.cycle 39 1 false (7),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 12 1 true (4),
.cycle 47 1 false (11),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 30 1 false (4),
.cycle 31 1 false (5),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 8 16 true (2)
])
theorem kid14_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part326) = true := by rfl

def kid14_part327 : Audit := .cycle 0 12 true (0)
theorem kid14_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part327) = true := by rfl

def kid14_part328 : Audit := .cycle 9 2 true (2)
theorem kid14_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part328) = true := by rfl

def kid14_part329 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 30 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part329) = true := by rfl

def kid14_part330 : Audit := .cycle 17 5 false (1)
theorem kid14_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part330) = true := by rfl

def kid14_part331 : Audit := .cycle 15 12 true (-2)
theorem kid14_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part331) = true := by rfl

def kid14_part332 : Audit := .cycle 1 13 true (1)
theorem kid14_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part332) = true := by rfl

def kid14_part333 : Audit := .cycle 18 1 false (0)
theorem kid14_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part333) = true := by rfl

def kid14_part334 : Audit := .split 11 (4,false) (byMove [
.last 18 (5,true),
.cycle 1 33 true (-1),
.cycle 15 1 false (1),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 14 3 false (0),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 18 7 false (2),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.last 12 (5,true),
.last 18 (5,true),
.cycle 16 5 false (0),
.last 16 (5,true),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid14_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part334) = true := by rfl

def kid14_part335 : Audit := .split 12 (5,true) (byMove [
.cycle 14 6 true (-1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.cycle 14 1 false (0),
.cycle 16 1 false (4),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.cycle 11 4 true (0),
.cycle 5 8 true (0),
.cycle 12 2 true (0),
.cycle 14 3 true (2)
])
theorem kid14_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part335) = true := by rfl

def kid14_part336 : Audit := .cycle 1 11 true (1)
theorem kid14_part336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part336) = true := by rfl

def kid14_part337 : Audit := .cycle 7 4 true (2)
theorem kid14_part337_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part337) = true := by rfl

def kid14_part338 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 20 (5,true),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 19 true (2),
.cycle 8 14 true (2),
.cycle 12 1 true (4),
.cycle 2 12 true (1),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 26 (5,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 2 12 true (1)
])
theorem kid14_part338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part338) = true := by rfl

def kid14_part339 : Audit := .cycle 0 12 true (0)
theorem kid14_part339_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part339) = true := by rfl

def kid14_part340 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 15 (4,false),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 15 (4,false)
])
theorem kid14_part340_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part340) = true := by rfl

def kid14_part341 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 17 (4,false),
.cycle 13 1 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 17 (4,false),
.cycle 15 3 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part341_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part341) = true := by rfl

def kid14_part317 : Audit := .split 10 (5,false) (byMove [(kid14_part318),(kid14_part319),(kid14_part320),(kid14_part321),(kid14_part322),(kid14_part323),(kid14_part324),(kid14_part325),(kid14_part326),(kid14_part327),(kid14_part328),(kid14_part329),(kid14_part330),(kid14_part331),(kid14_part332),(kid14_part333),(kid14_part334),(kid14_part335),(kid14_part336),(kid14_part337),(kid14_part338),(kid14_part339),(kid14_part340),(kid14_part341)])

theorem kid14_part317_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part317) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid14_part318),(kid14_part319),(kid14_part320),(kid14_part321),(kid14_part322),(kid14_part323),(kid14_part324),(kid14_part325),(kid14_part326),(kid14_part327),(kid14_part328),(kid14_part329),(kid14_part330),(kid14_part331),(kid14_part332),(kid14_part333),(kid14_part334),(kid14_part335),(kid14_part336),(kid14_part337),(kid14_part338),(kid14_part339),(kid14_part340),(kid14_part341)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part318_checked

  · exact kid14_part324_checked

  · exact kid14_part330_checked

  · exact kid14_part336_checked

  · exact kid14_part319_checked

  · exact kid14_part325_checked

  · exact kid14_part331_checked

  · exact kid14_part337_checked

  · exact kid14_part320_checked

  · exact kid14_part326_checked

  · exact kid14_part332_checked

  · exact kid14_part338_checked

  · exact kid14_part321_checked

  · exact kid14_part327_checked

  · exact kid14_part333_checked

  · exact kid14_part339_checked

  · exact kid14_part322_checked

  · exact kid14_part328_checked

  · exact kid14_part334_checked

  · exact kid14_part340_checked

  · exact kid14_part323_checked

  · exact kid14_part329_checked

  · exact kid14_part335_checked

  · exact kid14_part341_checked

def kid14_part342 : Audit := .cycle 0 10 true (0)
theorem kid14_part342_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part342) = true := by rfl

def kid14_part343 : Audit := .cycle 1 9 true (1)
theorem kid14_part343_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part343) = true := by rfl

def kid14_part344 : Audit := .cycle 2 8 true (1)
theorem kid14_part344_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part344) = true := by rfl

def kid14_part345 : Audit := .cycle 1 12 true (1)
theorem kid14_part345_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part345) = true := by rfl

def kid14_part346 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 2 26 true (0),
.cycle 0 12 true (0),
.cycle 9 2 true (3),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,false),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 12 true (4),
.cycle 3 22 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 23 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 11 true (3),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 14 true (3),
.cycle 9 11 true (3),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
]),
.cycle 6 5 true (2),
.cycle 1 14 true (1),
.cycle 8 3 true (2),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.split 11 (5,true) (byMove [
.last 16 (5,false),
.cycle 0 15 true (0),
.last 27 (5,false),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 13 (5,false),
.cycle 13 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 5 18 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 9 6 true (3),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
])
theorem kid14_part346_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part346) = true := by rfl

def kid14_part348 : Audit := .cycle 1 11 true (1)
theorem kid14_part348_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part348) = true := by rfl

def kid14_part349 : Audit := .cycle 0 14 true (0)
theorem kid14_part349_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part349) = true := by rfl

def kid14_part350 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 19 1 false (1),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 12 1 true (4),
.last 25 (5,true),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 21 (5,true),
.last 17 (5,true),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
])
theorem kid14_part350_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part350) = true := by rfl

def kid14_part351 : Audit := .cycle 0 12 true (0)
theorem kid14_part351_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part351) = true := by rfl

def kid14_part352 : Audit := .cycle 9 2 true (3)
theorem kid14_part352_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part352) = true := by rfl

def kid14_part353 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (0),
.cycle 0 23 true (0),
.last 12 (4,false),
.cycle 17 1 false (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 1 21 true (0),
.last 12 (4,false),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 10 2 true (3)
])
theorem kid14_part353_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part353) = true := by rfl

def kid14_part354 : Audit := .cycle 0 11 true (0)
theorem kid14_part354_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part354) = true := by rfl

def kid14_part355 : Audit := .cycle 1 10 true (1)
theorem kid14_part355_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part355) = true := by rfl

def kid14_part356 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 9 12 true (3),
.cycle 39 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.last 21 (4,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 4, 64],[2, 33, 16, 1, 32, 32, 64],80⟩,
.cycle 6 15 true (2),
.cycle 1 24 true (1),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.cycle 19 2 true (5),
.cycle 8 15 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 10 11 true (3)
])
theorem kid14_part356_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part356) = true := by rfl

def kid14_part357 : Audit := .cycle 3 8 true (1)
theorem kid14_part357_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part357) = true := by rfl

def kid14_part358 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part358_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part358) = true := by rfl

def kid14_part359 : Audit := .cycle 10 1 true (4)
theorem kid14_part359_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part359) = true := by rfl

def kid14_part360 : Audit := .cycle 6 5 true (2)
theorem kid14_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part360) = true := by rfl

def kid14_part361 : Audit := .cycle 1 14 true (1)
theorem kid14_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part361) = true := by rfl

def kid14_part362 : Audit := .cycle 8 3 true (2)
theorem kid14_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part362) = true := by rfl

def kid14_part363 : Audit := .cycle 1 12 true (1)
theorem kid14_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part363) = true := by rfl

def kid14_part364 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 10 3 true (3)
])
theorem kid14_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part364) = true := by rfl

def kid14_part365 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,false),
.cycle 0 15 true (0),
.last 23 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 24 1 false (6),
.cycle 6 11 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.last 12 (4,false),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 10 3 true (3)
])
theorem kid14_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part365) = true := by rfl

def kid14_part366 : Audit := .cycle 0 11 true (0)
theorem kid14_part366_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part366) = true := by rfl

def kid14_part367 : Audit := .cycle 1 10 true (1)
theorem kid14_part367_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part367) = true := by rfl

def kid14_part368 : Audit := .cycle 2 9 true (1)
theorem kid14_part368_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part368) = true := by rfl

def kid14_part369 : Audit := .cycle 1 13 true (1)
theorem kid14_part369_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part369) = true := by rfl

def kid14_part370 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.last 15 (5,true),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part370_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part370) = true := by rfl

def kid14_part371 : Audit := .cycle 10 1 true (4)
theorem kid14_part371_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part371) = true := by rfl

def kid14_part347 : Audit := .split 10 (5,false) (byMove [(kid14_part348),(kid14_part349),(kid14_part350),(kid14_part351),(kid14_part352),(kid14_part353),(kid14_part354),(kid14_part355),(kid14_part356),(kid14_part357),(kid14_part358),(kid14_part359),(kid14_part360),(kid14_part361),(kid14_part362),(kid14_part363),(kid14_part364),(kid14_part365),(kid14_part366),(kid14_part367),(kid14_part368),(kid14_part369),(kid14_part370),(kid14_part371)])

theorem kid14_part347_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part347) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part348),(kid14_part349),(kid14_part350),(kid14_part351),(kid14_part352),(kid14_part353),(kid14_part354),(kid14_part355),(kid14_part356),(kid14_part357),(kid14_part358),(kid14_part359),(kid14_part360),(kid14_part361),(kid14_part362),(kid14_part363),(kid14_part364),(kid14_part365),(kid14_part366),(kid14_part367),(kid14_part368),(kid14_part369),(kid14_part370),(kid14_part371)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part348_checked

  · exact kid14_part354_checked

  · exact kid14_part360_checked

  · exact kid14_part366_checked

  · exact kid14_part349_checked

  · exact kid14_part355_checked

  · exact kid14_part361_checked

  · exact kid14_part367_checked

  · exact kid14_part350_checked

  · exact kid14_part356_checked

  · exact kid14_part362_checked

  · exact kid14_part368_checked

  · exact kid14_part351_checked

  · exact kid14_part357_checked

  · exact kid14_part363_checked

  · exact kid14_part369_checked

  · exact kid14_part352_checked

  · exact kid14_part358_checked

  · exact kid14_part364_checked

  · exact kid14_part370_checked

  · exact kid14_part353_checked

  · exact kid14_part359_checked

  · exact kid14_part365_checked

  · exact kid14_part371_checked

def kid14_part251 : Audit := .split 9 (4,true) (byMove [(kid14_part252),(kid14_part253),(kid14_part254),(kid14_part255),(kid14_part256),(kid14_part257),(kid14_part282),(kid14_part283),(kid14_part284),(kid14_part285),(kid14_part286),(kid14_part287),(kid14_part312),(kid14_part313),(kid14_part314),(kid14_part315),(kid14_part316),(kid14_part317),(kid14_part342),(kid14_part343),(kid14_part344),(kid14_part345),(kid14_part346),(kid14_part347)])

theorem kid14_part251_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (kid14_part251) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid14_part252),(kid14_part253),(kid14_part254),(kid14_part255),(kid14_part256),(kid14_part257),(kid14_part282),(kid14_part283),(kid14_part284),(kid14_part285),(kid14_part286),(kid14_part287),(kid14_part312),(kid14_part313),(kid14_part314),(kid14_part315),(kid14_part316),(kid14_part317),(kid14_part342),(kid14_part343),(kid14_part344),(kid14_part345),(kid14_part346),(kid14_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part252_checked

  · exact kid14_part282_checked

  · exact kid14_part312_checked

  · exact kid14_part342_checked

  · exact kid14_part253_checked

  · exact kid14_part283_checked

  · exact kid14_part313_checked

  · exact kid14_part343_checked

  · exact kid14_part254_checked

  · exact kid14_part284_checked

  · exact kid14_part314_checked

  · exact kid14_part344_checked

  · exact kid14_part255_checked

  · exact kid14_part285_checked

  · exact kid14_part315_checked

  · exact kid14_part345_checked

  · exact kid14_part256_checked

  · exact kid14_part286_checked

  · exact kid14_part316_checked

  · exact kid14_part346_checked

  · exact kid14_part257_checked

  · exact kid14_part287_checked

  · exact kid14_part317_checked

  · exact kid14_part347_checked

def kid14_part373 : Audit := .cycle 0 10 true (0)
theorem kid14_part373_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part373) = true := by rfl

def kid14_part374 : Audit := .cycle 1 9 true (1)
theorem kid14_part374_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part374) = true := by rfl

def kid14_part375 : Audit := .cycle 20 1 false (2)
theorem kid14_part375_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part375) = true := by rfl

def kid14_part376 : Audit := .cycle 17 1 false (1)
theorem kid14_part376_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part376) = true := by rfl

def kid14_part378 : Audit := .cycle 0 11 true (0)
theorem kid14_part378_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part378) = true := by rfl

def kid14_part379 : Audit := .cycle 1 10 true (1)
theorem kid14_part379_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part379) = true := by rfl

def kid14_part380 : Audit := .cycle 21 1 false (1)
theorem kid14_part380_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part380) = true := by rfl

def kid14_part381 : Audit := .cycle 1 13 true (0)
theorem kid14_part381_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part381) = true := by rfl

def kid14_part382 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 17 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid14_part382_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part382) = true := by rfl

def kid14_part383 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 10 2 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 11 1 true (1)
])
theorem kid14_part383_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part383) = true := by rfl

def kid14_part384 : Audit := .cycle 0 11 true (0)
theorem kid14_part384_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part384) = true := by rfl

def kid14_part385 : Audit := .cycle 1 10 true (1)
theorem kid14_part385_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part385) = true := by rfl

def kid14_part386 : Audit := .cycle 1 24 true (0)
theorem kid14_part386_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part386) = true := by rfl

def kid14_part387 : Audit := .cycle 20 1 false (2)
theorem kid14_part387_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part387) = true := by rfl

def kid14_part388 : Audit := .cycle 10 1 true (2)
theorem kid14_part388_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part388) = true := by rfl

def kid14_part389 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 32 1 false (8),
.cycle 1 24 true (0),
.cycle 10 2 true (2),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 11 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 4 true (2),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3)
])
theorem kid14_part389_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part389) = true := by rfl

def kid14_part390 : Audit := .cycle 17 5 false (1)
theorem kid14_part390_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part390) = true := by rfl

def kid14_part391 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 16 true (-2),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 20 true (1),
.cycle 0 27 true (0),
.cycle 10 4 true (1),
.cycle 13 1 true (3),
.cycle 11 24 true (-2),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 15 12 true (-2),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 18 true (1),
.cycle 13 1 true (3)
])
theorem kid14_part391_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part391) = true := by rfl

def kid14_part392 : Audit := .cycle 0 13 true (0)
theorem kid14_part392_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part392) = true := by rfl

def kid14_part393 : Audit := .cycle 18 1 false (0)
theorem kid14_part393_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part393) = true := by rfl

def kid14_part394 : Audit := .split 12 (4,true) (byMove [
.last 22 (5,false),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 17 1 false (1),
.cycle 1 16 true (0),
.cycle 15 1 false (1),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.last 18 (5,false),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.last 15 (5,false)
])
theorem kid14_part394_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part394) = true := by rfl

def kid14_part395 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 24 true (-1),
.cycle 15 1 false (1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 38 1 false (8),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 14 3 false (0),
.cycle 13 6 false (1),
.cycle 18 7 false (2),
.cycle 0 24 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid14_part395_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part395) = true := by rfl

def kid14_part396 : Audit := .cycle 0 11 true (0)
theorem kid14_part396_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part396) = true := by rfl

def kid14_part397 : Audit := .cycle 1 10 true (1)
theorem kid14_part397_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part397) = true := by rfl

def kid14_part398 : Audit := .cycle 2 9 true (1)
theorem kid14_part398_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part398) = true := by rfl

def kid14_part399 : Audit := .cycle 1 13 true (1)
theorem kid14_part399_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part399) = true := by rfl

def kid14_part400 : Audit := .cycle 10 1 true (2)
theorem kid14_part400_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part400) = true := by rfl

def kid14_part401 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 19 19 true (3),
.cycle 3 9 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (2),
.cycle 11 1 true (3)
])
theorem kid14_part401_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part401) = true := by rfl

def kid14_part377 : Audit := .split 10 (4,false) (byMove [(kid14_part378),(kid14_part379),(kid14_part380),(kid14_part381),(kid14_part382),(kid14_part383),(kid14_part384),(kid14_part385),(kid14_part386),(kid14_part387),(kid14_part388),(kid14_part389),(kid14_part390),(kid14_part391),(kid14_part392),(kid14_part393),(kid14_part394),(kid14_part395),(kid14_part396),(kid14_part397),(kid14_part398),(kid14_part399),(kid14_part400),(kid14_part401)])

theorem kid14_part377_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part377) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid14_part378),(kid14_part379),(kid14_part380),(kid14_part381),(kid14_part382),(kid14_part383),(kid14_part384),(kid14_part385),(kid14_part386),(kid14_part387),(kid14_part388),(kid14_part389),(kid14_part390),(kid14_part391),(kid14_part392),(kid14_part393),(kid14_part394),(kid14_part395),(kid14_part396),(kid14_part397),(kid14_part398),(kid14_part399),(kid14_part400),(kid14_part401)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part378_checked

  · exact kid14_part384_checked

  · exact kid14_part390_checked

  · exact kid14_part396_checked

  · exact kid14_part379_checked

  · exact kid14_part385_checked

  · exact kid14_part391_checked

  · exact kid14_part397_checked

  · exact kid14_part380_checked

  · exact kid14_part386_checked

  · exact kid14_part392_checked

  · exact kid14_part398_checked

  · exact kid14_part381_checked

  · exact kid14_part387_checked

  · exact kid14_part393_checked

  · exact kid14_part399_checked

  · exact kid14_part382_checked

  · exact kid14_part388_checked

  · exact kid14_part394_checked

  · exact kid14_part400_checked

  · exact kid14_part383_checked

  · exact kid14_part389_checked

  · exact kid14_part395_checked

  · exact kid14_part401_checked

def kid14_part402 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 13 (4,true)
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
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (9),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 10 2 true (2),
.cycle 7 6 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2)
]),
.cycle 10 1 true (2),
.cycle 17 5 false (1),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 10 5 true (0),
.cycle 0 24 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 13 6 false (1),
.last 25 (4,true),
.last 26 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 1 12 true (1),
.last 16 (4,true),
.cycle 10 3 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 14 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (2)
]),
.cycle 10 1 true (2)
])
theorem kid14_part402_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part402) = true := by rfl

def kid14_part403 : Audit := .cycle 0 10 true (0)
theorem kid14_part403_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part403) = true := by rfl

def kid14_part404 : Audit := .cycle 1 9 true (1)
theorem kid14_part404_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part404) = true := by rfl

def kid14_part405 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 25 1 false (5),
.cycle 24 2 false (6),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 25 1 true (5),
.cycle 24 2 true (5),
.cycle 31 1 false (7),
.cycle 1 33 true (0),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (5),
.cycle 24 2 false (6),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (9),
.cycle 1 28 true (0),
.cycle 25 1 true (5),
.last 27 (4,true)
]),
.cycle 24 1 false (6),
.cycle 0 25 true (0),
.cycle 35 1 false (11),
.cycle 26 1 false (8),
.cycle 25 1 false (7),
.split 25 (4,false) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 25 1 false (7),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.cycle 26 1 false (8),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 31 1 false (9),
.cycle 23 4 true (5),
.cycle 0 28 true (0),
.cycle 26 1 false (6),
.cycle 25 1 false (7),
.last 27 (4,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (11),
.cycle 1 28 true (0),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6),
.cycle 30 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.split 25 (4,false) (byMove [
.cycle 27 5 true (5),
.cycle 0 29 true (0),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 25 1 false (5),
.cycle 24 2 false (6),
.cycle 1 26 true (0),
.cycle 0 29 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 28 1 false (8),
.cycle 21 7 true (3),
.cycle 42 1 false (10),
.cycle 1 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (5),
.cycle 24 2 false (6),
.cycle 1 26 true (0),
.cycle 30 1 false (8),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 21 13 true (3)
]),
.cycle 24 1 false (6),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 34 1 false (10),
.cycle 1 27 true (0),
.split 25 (4,false) (byMove [
.cycle 1 26 true (0),
.cycle 0 29 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 28 1 false (8),
.cycle 0 26 true (0),
.cycle 52 1 false (14),
.cycle 21 12 true (3),
.cycle 34 1 false (10),
.cycle 25 1 true (7),
.cycle 24 2 true (6),
.cycle 31 1 false (9),
.cycle 1 29 true (0),
.cycle 29 1 false (9),
.cycle 1 27 true (0),
.last 26 (4,true),
.cycle 22 4 true (4),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 1 28 true (0),
.cycle 25 1 true (7),
.cycle 24 2 true (6)
]),
.cycle 24 1 true (6)
])
theorem kid14_part405_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part405) = true := by rfl

def kid14_part406 : Audit := .cycle 1 20 true (0)
theorem kid14_part406_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part406) = true := by rfl

def kid14_part408 : Audit := .cycle 0 11 true (0)
theorem kid14_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part408) = true := by rfl

def kid14_part409 : Audit := .cycle 1 10 true (1)
theorem kid14_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part409) = true := by rfl

def kid14_part410 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.last 22 (5,false),
.cycle 1 22 true (0),
.cycle 0 25 true (0),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.cycle 25 1 false (5),
.cycle 33 1 false (5),
.last 38 (5,false),
.cycle 1 24 true (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.last 22 (5,false),
.cycle 1 22 true (0),
.cycle 27 1 false (5),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 25 (5,false),
.cycle 34 1 false (6)
])
theorem kid14_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part410) = true := by rfl

def kid14_part411 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.last 20 (5,false),
.cycle 25 1 false (3),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.last 20 (5,false)
])
theorem kid14_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part411) = true := by rfl

def kid14_part412 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 24 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 19 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (3),
.cycle 1 17 true (0),
.cycle 13 2 true (0),
.last 15 (5,false)
])
theorem kid14_part412_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part412) = true := by rfl

def kid14_part413 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 10 2 true (3),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 11 3 true (2),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 11 1 true (3)
])
theorem kid14_part413_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part413) = true := by rfl

def kid14_part414 : Audit := .cycle 0 11 true (0)
theorem kid14_part414_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part414) = true := by rfl

def kid14_part415 : Audit := .cycle 1 10 true (1)
theorem kid14_part415_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part415) = true := by rfl

def kid14_part416 : Audit := .split 23 (4,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 91 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.last 24 (5,false),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.cycle 28 1 false (8),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.cycle 29 1 false (9),
.cycle 45 1 false (9),
.last 50 (5,false),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.last 24 (5,false),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.cycle 51 15 true (7),
.cycle 5 19 true (0),
.cycle 26 11 true (6),
.cycle 24 13 true (4)
])
theorem kid14_part416_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part416) = true := by rfl

def kid14_part417 : Audit := .split 21 (4,true) (byMove [
.last 40 (5,false),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.last 22 (5,false),
.cycle 27 1 false (7),
.cycle 1 25 true (0),
.cycle 25 1 false (7),
.cycle 1 23 true (0),
.cycle 25 1 false (7),
.last 24 (5,false),
.cycle 37 1 false (7),
.last 28 (5,false),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 29 1 false (7),
.last 22 (5,false),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.last 36 (5,false),
.cycle 1 23 true (0),
.cycle 3 22 true (0),
.last 24 (5,false)
])
theorem kid14_part417_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part417) = true := by rfl

def kid14_part418 : Audit := .cycle 10 1 true (4)
theorem kid14_part418_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part418) = true := by rfl

def kid14_part419 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 10 2 true (4),
.cycle 18 1 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.last 21 (4,true),
.cycle 9 4 true (3),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part419_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part419) = true := by rfl

def kid14_part420 : Audit := .cycle 7 5 true (2)
theorem kid14_part420_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part420) = true := by rfl

def kid14_part421 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 18 true (1),
.cycle 9 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 10 4 true (3),
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.cycle 11 3 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 5 12 true (1),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 18 true (1),
.cycle 13 1 true (5)
])
theorem kid14_part421_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part421) = true := by rfl

def kid14_part422 : Audit := .cycle 0 13 true (0)
theorem kid14_part422_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part422) = true := by rfl

def kid14_part423 : Audit := .split 19 (4,true) (byMove [
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.last 20 (5,false),
.cycle 1 20 true (0),
.cycle 0 23 true (0),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 22 1 false (4),
.cycle 30 1 false (4),
.last 34 (5,false),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.last 20 (5,false),
.cycle 1 20 true (0),
.cycle 24 1 false (4),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 23 true (0),
.cycle 29 1 false (5)
])
theorem kid14_part423_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part423) = true := by rfl

def kid14_part424 : Audit := .split 14 (4,true) (byMove [
.last 23 (5,false),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 20 true (0),
.cycle 32 1 false (8),
.last 19 (5,false),
.cycle 21 1 false (5),
.cycle 19 1 false (5),
.last 19 (5,false),
.cycle 39 1 false (5),
.last 25 (5,false),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 20 true (0),
.cycle 1 22 true (0),
.last 19 (5,false),
.cycle 1 23 true (0),
.cycle 17 3 true (3),
.last 19 (5,false)
])
theorem kid14_part424_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part424) = true := by rfl

def kid14_part425 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 27 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.last 16 (4,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 19 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3)
])
theorem kid14_part425_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part425) = true := by rfl

def kid14_part426 : Audit := .cycle 0 11 true (0)
theorem kid14_part426_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part426) = true := by rfl

def kid14_part427 : Audit := .cycle 1 10 true (1)
theorem kid14_part427_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part427) = true := by rfl

def kid14_part428 : Audit := .cycle 2 9 true (1)
theorem kid14_part428_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part428) = true := by rfl

def kid14_part429 : Audit := .cycle 1 13 true (1)
theorem kid14_part429_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part429) = true := by rfl

def kid14_part430 : Audit := .cycle 10 1 true (4)
theorem kid14_part430_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part430) = true := by rfl

def kid14_part431 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 25 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part431_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part431) = true := by rfl

def kid14_part407 : Audit := .split 10 (4,false) (byMove [(kid14_part408),(kid14_part409),(kid14_part410),(kid14_part411),(kid14_part412),(kid14_part413),(kid14_part414),(kid14_part415),(kid14_part416),(kid14_part417),(kid14_part418),(kid14_part419),(kid14_part420),(kid14_part421),(kid14_part422),(kid14_part423),(kid14_part424),(kid14_part425),(kid14_part426),(kid14_part427),(kid14_part428),(kid14_part429),(kid14_part430),(kid14_part431)])

theorem kid14_part407_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part407) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part408),(kid14_part409),(kid14_part410),(kid14_part411),(kid14_part412),(kid14_part413),(kid14_part414),(kid14_part415),(kid14_part416),(kid14_part417),(kid14_part418),(kid14_part419),(kid14_part420),(kid14_part421),(kid14_part422),(kid14_part423),(kid14_part424),(kid14_part425),(kid14_part426),(kid14_part427),(kid14_part428),(kid14_part429),(kid14_part430),(kid14_part431)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part408_checked

  · exact kid14_part414_checked

  · exact kid14_part420_checked

  · exact kid14_part426_checked

  · exact kid14_part409_checked

  · exact kid14_part415_checked

  · exact kid14_part421_checked

  · exact kid14_part427_checked

  · exact kid14_part410_checked

  · exact kid14_part416_checked

  · exact kid14_part422_checked

  · exact kid14_part428_checked

  · exact kid14_part411_checked

  · exact kid14_part417_checked

  · exact kid14_part423_checked

  · exact kid14_part429_checked

  · exact kid14_part412_checked

  · exact kid14_part418_checked

  · exact kid14_part424_checked

  · exact kid14_part430_checked

  · exact kid14_part413_checked

  · exact kid14_part419_checked

  · exact kid14_part425_checked

  · exact kid14_part431_checked

def kid14_part432 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 15 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 11 1 true (3),
.cycle 10 2 true (3),
.cycle 7 6 true (2),
.cycle 1 19 true (1),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.last 14 (4,true),
.cycle 16 2 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 13 (4,true)
]),
.cycle 15 1 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.last 16 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.split 11 (4,false) (byMove [
.cycle 13 5 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 15 2 false (1),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 9 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 23 1 false (3),
.last 14 (4,true),
.cycle 19 2 false (5),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3)
]),
.cycle 19 1 false (5),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4)
])
theorem kid14_part432_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part432) = true := by rfl

def kid14_part433 : Audit := .cycle 7 4 true (2)
theorem kid14_part433_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part433) = true := by rfl

def kid14_part434 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 23 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.cycle 12 2 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 14 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.last 15 (4,true)
]),
.cycle 1 23 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 19 true (2),
.cycle 8 14 true (2),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 24 true (2),
.cycle 8 19 true (2),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 7 8 true (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 8 14 true (2),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.split 13 (4,false) (byMove [
.cycle 10 5 true (2),
.cycle 7 11 true (1),
.cycle 45 1 false (1),
.cycle 7 9 true (2),
.last 14 (4,true),
.cycle 14 23 true (-1),
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 9 5 true (2),
.cycle 8 11 true (2),
.cycle 5 11 true (1),
.cycle 8 9 true (2),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 14 17 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 11 true (2)
]),
.cycle 14 17 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 0 17 true (0),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 9 5 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 16 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 12 2 true (4),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 8 8 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 12 2 true (4)
]),
.cycle 12 1 true (4)
])
theorem kid14_part434_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part434) = true := by rfl

def kid14_part435 : Audit := .cycle 0 12 true (0)
theorem kid14_part435_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part435) = true := by rfl

def kid14_part436 : Audit := .cycle 17 1 false (1)
theorem kid14_part436_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part436) = true := by rfl

def kid14_part438 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 25 true (2),
.cycle 12 18 true (2),
.cycle 0 16 true (0),
.cycle 14 1 true (4),
.cycle 12 9 true (2),
.cycle 12 3 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 12 5 true (2),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.cycle 14 1 true (4)
])
theorem kid14_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part438) = true := by rfl

def kid14_part439 : Audit := .cycle 0 14 true (0)
theorem kid14_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part439) = true := by rfl

def kid14_part440 : Audit := .cycle 21 1 false (1)
theorem kid14_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part440) = true := by rfl

def kid14_part441 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.last 19 (4,true),
.cycle 0 17 true (0),
.cycle 0 58 true (0),
.cycle 7 43 true (0),
.cycle 7 28 true (0),
.cycle 3 15 true (0),
.cycle 16 1 true (4),
.cycle 7 17 true (0),
.cycle 14 3 true (2),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.cycle 7 13 true (0),
.last 19 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 256, 256, 128, 256, 8, 128, 128, 256, 4096],[128, 1, 32, 1, 4096, 32, 128, 32, 32, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 16 1 true (4)
])
theorem kid14_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part441) = true := by rfl

def kid14_part442 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 13 (5,false),
.cycle 17 1 false (-1),
.last 15 (5,false),
.last 18 (5,false),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 18 (5,false),
.cycle 11 2 true (0),
.last 13 (5,false)
])
theorem kid14_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part442) = true := by rfl

def kid14_part443 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 30 11 false (2),
.cycle 15 1 false (1),
.cycle 1 19 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (1),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 16 3 true (2),
.cycle 12 8 true (-2),
.cycle 4 13 true (0),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (4,true),
.last 14 (4,true)
])
theorem kid14_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part443) = true := by rfl

def kid14_part444 : Audit := .cycle 1 11 true (1)
theorem kid14_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part444) = true := by rfl

def kid14_part445 : Audit := .cycle 0 14 true (0)
theorem kid14_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part445) = true := by rfl

def kid14_part446 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (5),
.cycle 27 1 false (3),
.cycle 39 1 false (7),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 47 1 false (11),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 30 1 false (4),
.cycle 10 3 true (2),
.cycle 31 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 16 true (2),
.cycle 12 1 true (4)
])
theorem kid14_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part446) = true := by rfl

def kid14_part447 : Audit := .cycle 0 12 true (0)
theorem kid14_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part447) = true := by rfl

def kid14_part448 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 30 (5,false),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
])
theorem kid14_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part448) = true := by rfl

def kid14_part449 : Audit := .cycle 9 2 true (2)
theorem kid14_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part449) = true := by rfl

def kid14_part450 : Audit := .cycle 17 5 false (1)
theorem kid14_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part450) = true := by rfl

def kid14_part451 : Audit := .cycle 15 12 true (-2)
theorem kid14_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part451) = true := by rfl

def kid14_part452 : Audit := .cycle 1 13 true (1)
theorem kid14_part452_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part452) = true := by rfl

def kid14_part453 : Audit := .cycle 18 1 false (0)
theorem kid14_part453_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part453) = true := by rfl

def kid14_part454 : Audit := .split 12 (4,true) (byMove [
.cycle 14 6 true (-1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 13 (5,false),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.cycle 11 4 true (0),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.cycle 12 2 true (0)
])
theorem kid14_part454_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part454) = true := by rfl

def kid14_part455 : Audit := .split 11 (5,false) (byMove [
.last 18 (4,true),
.cycle 1 33 true (-1),
.cycle 15 1 false (1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 14 3 false (0),
.cycle 13 6 false (1),
.cycle 18 7 false (2),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 16 5 false (0),
.last 16 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid14_part455_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part455) = true := by rfl

def kid14_part456 : Audit := .cycle 1 11 true (1)
theorem kid14_part456_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part456) = true := by rfl

def kid14_part457 : Audit := .cycle 7 4 true (2)
theorem kid14_part457_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part457) = true := by rfl

def kid14_part458 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 19 true (2),
.cycle 8 14 true (2),
.cycle 2 12 true (1),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 3 true (2),
.last 26 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.cycle 12 1 true (4)
])
theorem kid14_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part458) = true := by rfl

def kid14_part459 : Audit := .cycle 0 12 true (0)
theorem kid14_part459_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part459) = true := by rfl

def kid14_part460 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.last 17 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,false),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 15 3 false (1),
.last 17 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
])
theorem kid14_part460_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part460) = true := by rfl

def kid14_part461 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (5,false),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 9 4 true (2),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 16 3 false (0),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 11 2 true (2)
])
theorem kid14_part461_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part461) = true := by rfl

def kid14_part437 : Audit := .split 10 (4,false) (byMove [(kid14_part438),(kid14_part439),(kid14_part440),(kid14_part441),(kid14_part442),(kid14_part443),(kid14_part444),(kid14_part445),(kid14_part446),(kid14_part447),(kid14_part448),(kid14_part449),(kid14_part450),(kid14_part451),(kid14_part452),(kid14_part453),(kid14_part454),(kid14_part455),(kid14_part456),(kid14_part457),(kid14_part458),(kid14_part459),(kid14_part460),(kid14_part461)])

theorem kid14_part437_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part437) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid14_part438),(kid14_part439),(kid14_part440),(kid14_part441),(kid14_part442),(kid14_part443),(kid14_part444),(kid14_part445),(kid14_part446),(kid14_part447),(kid14_part448),(kid14_part449),(kid14_part450),(kid14_part451),(kid14_part452),(kid14_part453),(kid14_part454),(kid14_part455),(kid14_part456),(kid14_part457),(kid14_part458),(kid14_part459),(kid14_part460),(kid14_part461)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part438_checked

  · exact kid14_part444_checked

  · exact kid14_part450_checked

  · exact kid14_part456_checked

  · exact kid14_part439_checked

  · exact kid14_part445_checked

  · exact kid14_part451_checked

  · exact kid14_part457_checked

  · exact kid14_part440_checked

  · exact kid14_part446_checked

  · exact kid14_part452_checked

  · exact kid14_part458_checked

  · exact kid14_part441_checked

  · exact kid14_part447_checked

  · exact kid14_part453_checked

  · exact kid14_part459_checked

  · exact kid14_part442_checked

  · exact kid14_part448_checked

  · exact kid14_part454_checked

  · exact kid14_part460_checked

  · exact kid14_part443_checked

  · exact kid14_part449_checked

  · exact kid14_part455_checked

  · exact kid14_part461_checked

def kid14_part462 : Audit := .split 10 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 1 19 true (0),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 20 11 false (2),
.cycle 16 1 false (0),
.cycle 0 19 true (0),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 7 6 true (1),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.last 37 (4,true),
.cycle 12 8 true (-2),
.cycle 1 19 true (0),
.last 12 (4,true),
.cycle 13 2 false (-1),
.last 17 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 13 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 41 1 false (9),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 31 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
]),
.cycle 9 2 true (2),
.cycle 17 5 false (1),
.cycle 15 12 true (-2),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 17 (4,true),
.cycle 1 33 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 2 false (-1),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 13 6 false (1),
.last 25 (4,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 2 false (-1),
.last 17 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 13 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
]),
.cycle 15 3 false (1)
])
theorem kid14_part462_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part462) = true := by rfl

def kid14_part463 : Audit := .cycle 0 10 true (0)
theorem kid14_part463_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part463) = true := by rfl

def kid14_part464 : Audit := .cycle 1 9 true (1)
theorem kid14_part464_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part464) = true := by rfl

def kid14_part465 : Audit := .cycle 2 8 true (1)
theorem kid14_part465_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part465) = true := by rfl

def kid14_part466 : Audit := .cycle 1 12 true (1)
theorem kid14_part466_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part466) = true := by rfl

def kid14_part468 : Audit := .cycle 1 11 true (1)
theorem kid14_part468_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part468) = true := by rfl

def kid14_part469 : Audit := .cycle 0 14 true (0)
theorem kid14_part469_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part469) = true := by rfl

def kid14_part470 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (4,true),
.last 21 (4,true),
.last 23 (4,true),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.last 25 (4,true),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 21 (4,true),
.last 23 (4,true),
.last 17 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
])
theorem kid14_part470_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part470) = true := by rfl

def kid14_part471 : Audit := .cycle 0 12 true (0)
theorem kid14_part471_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part471) = true := by rfl

def kid14_part472 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,false),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (0),
.cycle 0 23 true (0),
.cycle 17 1 false (1),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 21 true (0),
.cycle 15 1 false (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.last 12 (5,false)
])
theorem kid14_part472_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part472) = true := by rfl

def kid14_part473 : Audit := .cycle 9 2 true (3)
theorem kid14_part473_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part473) = true := by rfl

def kid14_part474 : Audit := .cycle 0 11 true (0)
theorem kid14_part474_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part474) = true := by rfl

def kid14_part475 : Audit := .cycle 1 10 true (1)
theorem kid14_part475_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part475) = true := by rfl

def kid14_part476 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 39 1 false (3),
.cycle 9 12 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 4, 64, 64],[2, 17, 32, 1, 16, 16, 64],96⟩,
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 1 24 true (1),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.cycle 8 15 true (2),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.last 21 (5,false)
])
theorem kid14_part476_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part476) = true := by rfl

def kid14_part477 : Audit := .cycle 3 8 true (1)
theorem kid14_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part477) = true := by rfl

def kid14_part478 : Audit := .cycle 10 1 true (4)
theorem kid14_part478_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part478) = true := by rfl

def kid14_part479 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 11 3 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part479_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part479) = true := by rfl

def kid14_part480 : Audit := .cycle 6 5 true (2)
theorem kid14_part480_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part480) = true := by rfl

def kid14_part481 : Audit := .cycle 1 14 true (1)
theorem kid14_part481_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part481) = true := by rfl

def kid14_part482 : Audit := .cycle 8 3 true (2)
theorem kid14_part482_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part482) = true := by rfl

def kid14_part483 : Audit := .cycle 1 12 true (1)
theorem kid14_part483_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part483) = true := by rfl

def kid14_part484 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,false),
.cycle 0 15 true (0),
.last 23 (5,false),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.cycle 9 3 true (3),
.cycle 6 11 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 15 1 false (-1),
.last 12 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 9 3 true (3)
])
theorem kid14_part484_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part484) = true := by rfl

def kid14_part485 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.last 13 (5,false)
])
theorem kid14_part485_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part485) = true := by rfl

def kid14_part486 : Audit := .cycle 0 11 true (0)
theorem kid14_part486_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part486) = true := by rfl

def kid14_part487 : Audit := .cycle 1 10 true (1)
theorem kid14_part487_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part487) = true := by rfl

def kid14_part488 : Audit := .cycle 2 9 true (1)
theorem kid14_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part488) = true := by rfl

def kid14_part489 : Audit := .cycle 1 13 true (1)
theorem kid14_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part489) = true := by rfl

def kid14_part490 : Audit := .cycle 10 1 true (4)
theorem kid14_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part490) = true := by rfl

def kid14_part491 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 15 (4,true),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part491) = true := by rfl

def kid14_part467 : Audit := .split 10 (4,false) (byMove [(kid14_part468),(kid14_part469),(kid14_part470),(kid14_part471),(kid14_part472),(kid14_part473),(kid14_part474),(kid14_part475),(kid14_part476),(kid14_part477),(kid14_part478),(kid14_part479),(kid14_part480),(kid14_part481),(kid14_part482),(kid14_part483),(kid14_part484),(kid14_part485),(kid14_part486),(kid14_part487),(kid14_part488),(kid14_part489),(kid14_part490),(kid14_part491)])

theorem kid14_part467_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part467) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part468),(kid14_part469),(kid14_part470),(kid14_part471),(kid14_part472),(kid14_part473),(kid14_part474),(kid14_part475),(kid14_part476),(kid14_part477),(kid14_part478),(kid14_part479),(kid14_part480),(kid14_part481),(kid14_part482),(kid14_part483),(kid14_part484),(kid14_part485),(kid14_part486),(kid14_part487),(kid14_part488),(kid14_part489),(kid14_part490),(kid14_part491)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part468_checked

  · exact kid14_part474_checked

  · exact kid14_part480_checked

  · exact kid14_part486_checked

  · exact kid14_part469_checked

  · exact kid14_part475_checked

  · exact kid14_part481_checked

  · exact kid14_part487_checked

  · exact kid14_part470_checked

  · exact kid14_part476_checked

  · exact kid14_part482_checked

  · exact kid14_part488_checked

  · exact kid14_part471_checked

  · exact kid14_part477_checked

  · exact kid14_part483_checked

  · exact kid14_part489_checked

  · exact kid14_part472_checked

  · exact kid14_part478_checked

  · exact kid14_part484_checked

  · exact kid14_part490_checked

  · exact kid14_part473_checked

  · exact kid14_part479_checked

  · exact kid14_part485_checked

  · exact kid14_part491_checked

def kid14_part492 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 2 26 true (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 12 true (4),
.cycle 3 22 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 1 23 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 10 2 true (3)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 11 true (3),
.cycle 3 8 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 14 true (3),
.cycle 9 11 true (3),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.cycle 1 14 true (1),
.cycle 8 3 true (2),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 16 (4,false),
.cycle 0 15 true (0),
.last 27 (4,false),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 9 3 true (3),
.cycle 13 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 5 18 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 9 3 true (3)
]),
.cycle 9 3 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 9 6 true (3),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4)
])
theorem kid14_part492_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part492) = true := by rfl

def kid14_part372 : Audit := .split 9 (5,true) (byMove [(kid14_part373),(kid14_part374),(kid14_part375),(kid14_part376),(kid14_part377),(kid14_part402),(kid14_part403),(kid14_part404),(kid14_part405),(kid14_part406),(kid14_part407),(kid14_part432),(kid14_part433),(kid14_part434),(kid14_part435),(kid14_part436),(kid14_part437),(kid14_part462),(kid14_part463),(kid14_part464),(kid14_part465),(kid14_part466),(kid14_part467),(kid14_part492)])

theorem kid14_part372_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (kid14_part372) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid14_part373),(kid14_part374),(kid14_part375),(kid14_part376),(kid14_part377),(kid14_part402),(kid14_part403),(kid14_part404),(kid14_part405),(kid14_part406),(kid14_part407),(kid14_part432),(kid14_part433),(kid14_part434),(kid14_part435),(kid14_part436),(kid14_part437),(kid14_part462),(kid14_part463),(kid14_part464),(kid14_part465),(kid14_part466),(kid14_part467),(kid14_part492)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part373_checked

  · exact kid14_part403_checked

  · exact kid14_part433_checked

  · exact kid14_part463_checked

  · exact kid14_part374_checked

  · exact kid14_part404_checked

  · exact kid14_part434_checked

  · exact kid14_part464_checked

  · exact kid14_part375_checked

  · exact kid14_part405_checked

  · exact kid14_part435_checked

  · exact kid14_part465_checked

  · exact kid14_part376_checked

  · exact kid14_part406_checked

  · exact kid14_part436_checked

  · exact kid14_part466_checked

  · exact kid14_part377_checked

  · exact kid14_part407_checked

  · exact kid14_part437_checked

  · exact kid14_part467_checked

  · exact kid14_part402_checked

  · exact kid14_part432_checked

  · exact kid14_part462_checked

  · exact kid14_part492_checked

def kid14_part493 : Audit := .cycle 13 3 false (1)
theorem kid14_part493_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,0⟩)) (kid14_part493) = true := by rfl

def kid14_part494 : Audit := .cycle 11 8 true (-2)
theorem kid14_part494_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,1⟩)) (kid14_part494) = true := by rfl

def kid14_part495 : Audit := .cycle 1 11 true (1)
theorem kid14_part495_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,2⟩)) (kid14_part495) = true := by rfl

def kid14_part496 : Audit := .cycle 14 1 false (0)
theorem kid14_part496_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,3⟩)) (kid14_part496) = true := by rfl

def kid14_part498 : Audit := .split 13 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 11 11 false (2),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 0 16 false (3),
.split 14 (5,true) (byMove [
.cycle 1 19 true (-1),
.cycle 11 14 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 16 false (3),
.last 15 (5,false),
.cycle 11 9 false (2),
.last 18 (5,false),
.cycle 1 17 true (0),
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
.cycle 1 17 true (0),
.cycle 11 11 false (2),
.cycle 9 6 true (0),
.last 15 (5,false)
]),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.cycle 0 17 true (0),
.split 14 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 11 13 false (2),
.cycle 1 24 true (0),
.cycle 0 20 true (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 11 36 true (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 11 14 false (2),
.cycle 11 4 true (1),
.cycle 1 17 true (0),
.cycle 11 11 false (2),
.cycle 9 6 true (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 7 8 true (0),
.cycle 11 16 true (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false)
]),
.cycle 11 8 false (2),
.cycle 11 11 false (2),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 11 6 false (2),
.split 14 (5,true) (byMove [
.cycle 11 5 false (2),
.cycle 11 24 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 21 16 false (3),
.last 15 (5,false),
.cycle 11 9 false (2),
.cycle 11 12 true (0),
.cycle 11 7 false (2),
.cycle 11 10 true (0),
.last 16 (5,false),
.last 18 (5,false),
.cycle 11 9 false (2),
.last 18 (5,false),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.cycle 11 6 false (2),
.last 15 (5,false),
.last 19 (5,false),
.cycle 11 8 false (2),
.last 17 (5,false),
.cycle 5 10 true (0),
.cycle 13 2 true (0),
.last 18 (5,false)
]),
.cycle 12 4 true (1),
.cycle 11 10 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.cycle 1 17 true (0),
.split 14 (5,true) (byMove [
.cycle 1 20 true (0),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 7 10 true (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 8 28 true (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 11 14 false (2),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 5 10 true (0),
.cycle 13 2 true (1),
.last 17 (5,false),
.cycle 1 15 true (0),
.cycle 12 4 true (1),
.cycle 2 16 true (0),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false)
])
])
theorem kid14_part498_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part498) = true := by rfl

def kid14_part499 : Audit := .cycle 1 27 true (-1)
theorem kid14_part499_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part499) = true := by rfl

def kid14_part500 : Audit := .cycle 13 1 false (-1)
theorem kid14_part500_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part500) = true := by rfl

def kid14_part501 : Audit := .cycle 15 1 false (-1)
theorem kid14_part501_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part501) = true := by rfl

def kid14_part502 : Audit := .split 10 (4,true) (byMove [
.cycle 1 15 true (-1),
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
.cycle 1 15 true (-1),
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
.cycle 1 15 true (-1),
.cycle 19 1 false (-1),
.last 18 (5,true),
.cycle 9 3 false (1),
.last 14 (5,true)
]),
.cycle 14 1 false (0),
.cycle 1 17 true (0),
.cycle 1 13 true (0),
.cycle 11 1 false (1),
.cycle 11 1 false (1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 15 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 1 13 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.last 16 (5,true),
.cycle 14 1 false (0),
.last 14 (5,true),
.cycle 1 13 true (0),
.last 13 (5,true),
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
.cycle 18 1 false (0),
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
.cycle 12 4 true (0),
.cycle 19 1 false (-1),
.cycle 1 13 true (0),
.cycle 16 1 false (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 13 (5,true),
.last 12 (5,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (5,true),
.last 12 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
])
theorem kid14_part502_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part502) = true := by rfl

def kid14_part504 : Audit := .cycle 1 15 true (-1)
theorem kid14_part504_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part504) = true := by rfl

def kid14_part505 : Audit := .split 20 (5,false) (byMove [
.cycle 22 43 true (-2),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.cycle 1 37 true (-2),
.cycle 21 1 false (-1),
.cycle 19 2 true (-2),
.cycle 0 36 true (-2),
.cycle 17 5 false (1),
.last 23 (4,true),
.cycle 17 7 false (1),
.cycle 21 1 false (-3),
.cycle 19 2 false (-1),
.cycle 20 1 false (-2),
.last 24 (4,true),
.last 23 (4,true),
.cycle 1 37 true (-2),
.cycle 14 7 false (1),
.cycle 9 12 false (1),
.cycle 17 6 false (1)
])
theorem kid14_part505_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part505) = true := by rfl

def kid14_part506 : Audit := .cycle 12 1 false (0)
theorem kid14_part506_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part506) = true := by rfl

def kid14_part507 : Audit := .cycle 11 1 false (-1)
theorem kid14_part507_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part507) = true := by rfl

def kid14_part508 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 1 17 true (-2),
.last 25 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 23 1 true (1),
.cycle 11 5 false (-1),
.last 15 (4,true),
.last 33 (4,true),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 1 17 true (-2),
.cycle 1 12 false (3),
.last 27 (4,true),
.cycle 1 19 true (-2),
.cycle 9 4 false (1),
.last 17 (4,true)
])
theorem kid14_part508_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part508) = true := by rfl

def kid14_part509 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 true (-1),
.cycle 18 1 true (2),
.cycle 11 5 false (-1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 1 15 true (-1),
.cycle 1 37 true (-2),
.last 17 (4,true),
.cycle 9 3 false (1),
.cycle 29 1 true (-3)
])
theorem kid14_part509_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part509) = true := by rfl

def kid14_part510 : Audit := .split 15 (5,false) (byMove [
.cycle 1 29 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.last 18 (4,true),
.cycle 1 25 true (-1),
.cycle 16 1 false (0),
.cycle 14 2 true (-1),
.cycle 1 25 true (-1),
.cycle 11 5 false (2),
.last 18 (4,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 1 25 true (-1),
.cycle 12 7 false (2),
.cycle 9 7 false (2),
.cycle 7 17 false (3)
])
theorem kid14_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part510) = true := by rfl

def kid14_part511 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (0),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.cycle 1 17 true (0),
.last 16 (5,false),
.cycle 1 15 true (0),
.last 17 (5,false),
.cycle 0 18 true (0),
.last 18 (5,false),
.cycle 11 3 false (2),
.last 20 (5,false),
.cycle 14 1 false (0),
.last 15 (5,false),
.last 14 (5,false),
.cycle 12 4 true (1),
.last 17 (5,false),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.last 27 (5,false),
.cycle 0 18 true (0)
])
theorem kid14_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part511) = true := by rfl

def kid14_part512 : Audit := .cycle 1 13 true (0)
theorem kid14_part512_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part512) = true := by rfl

def kid14_part513 : Audit := .cycle 11 1 false (1)
theorem kid14_part513_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part513) = true := by rfl

def kid14_part514 : Audit := .split 12 (5,false) (byMove [
.cycle 1 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.cycle 11 5 false (2),
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 11 2 true (0),
.last 15 (4,true),
.cycle 11 5 false (1),
.last 15 (4,true),
.cycle 11 7 false (2),
.cycle 13 1 false (-1),
.cycle 11 2 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 11 7 false (2),
.cycle 9 4 true (0),
.last 15 (4,true)
])
theorem kid14_part514_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part514) = true := by rfl

def kid14_part515 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.cycle 13 5 false (3),
.cycle 1 15 true (0),
.cycle 1 17 true (0),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (4),
.cycle 11 5 false (1),
.last 14 (4,true),
.cycle 15 7 false (3),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 1 false (1),
.last 15 (4,true),
.last 18 (4,true),
.last 13 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part515_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part515) = true := by rfl

def kid14_part516 : Audit := .split 15 (5,false) (byMove [
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
theorem kid14_part516_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part516) = true := by rfl

def kid14_part517 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 6 12 true (-1),
.last 21 (5,false),
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
.cycle 16 4 true (1),
.last 17 (5,false),
.cycle 12 2 true (-1),
.cycle 7 9 false (3),
.cycle 23 8 true (0),
.last 26 (5,false)
])
theorem kid14_part517_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part517) = true := by rfl

def kid14_part518 : Audit := .split 17 (5,false) (byMove [
.cycle 1 31 true (-2),
.cycle 14 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.last 20 (4,true),
.cycle 1 27 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 1 31 true (-1),
.cycle 13 5 false (2),
.last 20 (4,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.last 20 (4,true),
.cycle 1 27 true (-1),
.cycle 14 7 false (2),
.cycle 9 9 false (2),
.last 21 (4,true)
])
theorem kid14_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part518) = true := by rfl

def kid14_part519 : Audit := .cycle 11 1 false (-1)
theorem kid14_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part519) = true := by rfl

def kid14_part520 : Audit := .split 12 (5,false) (byMove [
.cycle 14 35 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.last 15 (4,true),
.cycle 1 29 true (-2),
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
.cycle 1 29 true (-2),
.cycle 11 7 false (0),
.cycle 9 4 false (1),
.last 15 (4,true)
])
theorem kid14_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part520) = true := by rfl

def kid14_part521 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.last 26 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 22 (4,true),
.cycle 1 31 true (-2),
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
theorem kid14_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part521) = true := by rfl

def kid14_part522 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.last 22 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 19 (5,false),
.cycle 1 21 true (0),
.last 19 (5,false),
.cycle 13 3 false (1),
.last 21 (5,false),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 12 4 true (0),
.last 18 (5,false),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 0 20 true (0),
.cycle 1 21 true (0)
])
theorem kid14_part522_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part522) = true := by rfl

def kid14_part523 : Audit := .split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.last 21 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.cycle 10 4 true (0),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.last 17 (5,false),
.cycle 7 8 true (0),
.last 18 (5,false),
.last 21 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.cycle 12 4 true (1),
.last 20 (5,false),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.cycle 1 17 true (0),
.cycle 12 4 true (1)
])
theorem kid14_part523_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part523) = true := by rfl

def kid14_part524 : Audit := .cycle 1 13 true (0)
theorem kid14_part524_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part524) = true := by rfl

def kid14_part525 : Audit := .split 17 (5,false) (byMove [
.cycle 1 31 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 1 27 true (-1),
.cycle 18 1 false (0),
.cycle 16 2 true (-1),
.cycle 1 21 true (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 14 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.last 20 (4,true),
.cycle 1 27 true (-1),
.cycle 11 7 false (2),
.cycle 9 9 false (2),
.cycle 1 21 true (-1)
])
theorem kid14_part525_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part525) = true := by rfl

def kid14_part526 : Audit := .cycle 9 2 true (0)
theorem kid14_part526_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part526) = true := by rfl

def kid14_part527 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 16 10 false (2),
.cycle 16 1 false (-2),
.cycle 18 1 false (-2),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (4),
.cycle 13 5 false (1),
.last 22 (4,true),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.last 12 (4,true),
.cycle 14 3 true (2),
.last 15 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 14 1 true (4)
])
theorem kid14_part527_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part527) = true := by rfl

def kid14_part503 : Audit := .split 10 (5,true) (byMove [(kid14_part504),(kid14_part505),(kid14_part506),(kid14_part507),(kid14_part508),(kid14_part509),(kid14_part510),(kid14_part511),(kid14_part512),(kid14_part513),(kid14_part514),(kid14_part515),(kid14_part516),(kid14_part517),(kid14_part518),(kid14_part519),(kid14_part520),(kid14_part521),(kid14_part522),(kid14_part523),(kid14_part524),(kid14_part525),(kid14_part526),(kid14_part527)])

theorem kid14_part503_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part503) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part504),(kid14_part505),(kid14_part506),(kid14_part507),(kid14_part508),(kid14_part509),(kid14_part510),(kid14_part511),(kid14_part512),(kid14_part513),(kid14_part514),(kid14_part515),(kid14_part516),(kid14_part517),(kid14_part518),(kid14_part519),(kid14_part520),(kid14_part521),(kid14_part522),(kid14_part523),(kid14_part524),(kid14_part525),(kid14_part526),(kid14_part527)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part504_checked

  · exact kid14_part510_checked

  · exact kid14_part516_checked

  · exact kid14_part522_checked

  · exact kid14_part505_checked

  · exact kid14_part511_checked

  · exact kid14_part517_checked

  · exact kid14_part523_checked

  · exact kid14_part506_checked

  · exact kid14_part512_checked

  · exact kid14_part518_checked

  · exact kid14_part524_checked

  · exact kid14_part507_checked

  · exact kid14_part513_checked

  · exact kid14_part519_checked

  · exact kid14_part525_checked

  · exact kid14_part508_checked

  · exact kid14_part514_checked

  · exact kid14_part520_checked

  · exact kid14_part526_checked

  · exact kid14_part509_checked

  · exact kid14_part515_checked

  · exact kid14_part521_checked

  · exact kid14_part527_checked

def kid14_part528 : Audit := .cycle 6 4 true (1)
theorem kid14_part528_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part528) = true := by rfl

def kid14_part529 : Audit := .cycle 1 13 true (1)
theorem kid14_part529_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part529) = true := by rfl

def kid14_part530 : Audit := .cycle 8 2 true (1)
theorem kid14_part530_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part530) = true := by rfl

def kid14_part531 : Audit := .cycle 1 11 true (1)
theorem kid14_part531_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part531) = true := by rfl

def kid14_part532 : Audit := .split 10 (4,true) (byMove [
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 14 1 true (2),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 17 (5,true),
.cycle 21 1 true (1),
.last 12 (5,true),
.cycle 7 6 true (1),
.cycle 10 4 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 15 1 true (3),
.last 13 (5,true),
.cycle 13 6 false (1),
.last 19 (5,true),
.cycle 12 8 true (-2),
.last 17 (5,true),
.cycle 12 3 false (0),
.last 12 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 1 true (3),
.last 13 (5,true)
]),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 39 1 false (7),
.cycle 0 12 true (0),
.cycle 12 1 true (4),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 32 (5,false),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 7 6 true (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
]),
.cycle 14 5 false (0),
.cycle 21 3 false (1),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 12 4 true (-2),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.cycle 19 4 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 12 (5,true),
.last 16 (5,true),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true)
]),
.cycle 1 11 true (1),
.cycle 7 4 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 12 1 true (4),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,false),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
])
])
theorem kid14_part532_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part532) = true := by rfl

def kid14_part534 : Audit := .split 14 (4,true) (byMove [
.cycle 12 4 true (1),
.cycle 15 12 true (-2),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.last 18 (5,false),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 20 9 false (0),
.cycle 15 12 true (-2),
.cycle 21 7 false (2),
.cycle 5 10 true (1),
.cycle 15 7 false (1),
.cycle 17 5 false (2),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 1 16 true (1)
])
theorem kid14_part534_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part534) = true := by rfl

def kid14_part535 : Audit := .cycle 0 14 true (0)
theorem kid14_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part535) = true := by rfl

def kid14_part536 : Audit := .cycle 21 1 false (1)
theorem kid14_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part536) = true := by rfl

def kid14_part537 : Audit := .split 16 (4,true) (byMove [
.cycle 13 4 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.last 19 (5,false),
.cycle 18 1 false (0),
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.cycle 1 22 true (0),
.cycle 0 18 true (0),
.last 19 (5,false),
.cycle 1 20 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 1 17 true (0),
.cycle 24 1 false (0),
.cycle 15 2 true (2),
.cycle 0 18 true (0),
.last 19 (5,false),
.cycle 0 19 true (0)
])
theorem kid14_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part537) = true := by rfl

def kid14_part538 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (4,true),
.cycle 11 2 true (1),
.cycle 16 1 false (0),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 true (3),
.last 16 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.cycle 16 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
])
theorem kid14_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part538) = true := by rfl

def kid14_part539 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.last 18 (4,true),
.cycle 17 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 2 true (2),
.cycle 14 1 true (2),
.cycle 13 6 false (1),
.last 18 (4,true),
.cycle 12 8 true (-2),
.last 16 (4,true),
.last 12 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 14 2 true (2),
.cycle 17 1 true (-1)
])
theorem kid14_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part539) = true := by rfl

def kid14_part540 : Audit := .cycle 1 11 true (1)
theorem kid14_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part540) = true := by rfl

def kid14_part541 : Audit := .cycle 0 14 true (0)
theorem kid14_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part541) = true := by rfl

def kid14_part542 : Audit := .cycle 39 1 false (7)
theorem kid14_part542_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part542) = true := by rfl

def kid14_part543 : Audit := .cycle 0 12 true (0)
theorem kid14_part543_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part543) = true := by rfl

def kid14_part544 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 33 (5,false),
.cycle 1 24 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 7 6 true (1),
.cycle 26 3 false (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 15 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid14_part544_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part544) = true := by rfl

def kid14_part545 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 12 2 true (3),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.cycle 7 7 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 11 3 true (3),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4)
])
theorem kid14_part545_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part545) = true := by rfl

def kid14_part546 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 7 17 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 16 5 false (2),
.cycle 19 5 false (3),
.cycle 15 5 false (1),
.cycle 17 5 false (3),
.last 19 (5,false),
.cycle 15 5 false (1),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 18 5 false (2),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 12 4 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.last 19 (5,false),
.cycle 17 5 false (1)
])
theorem kid14_part546_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part546) = true := by rfl

def kid14_part547 : Audit := .split 13 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 1 39 true (-1),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.last 16 (5,false),
.last 18 (5,false),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.last 17 (5,false),
.cycle 10 4 true (1),
.cycle 15 8 false (1),
.cycle 22 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.cycle 14 5 false (0),
.last 18 (5,false),
.cycle 12 4 true (1),
.cycle 15 7 false (1),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.last 17 (5,false),
.cycle 15 12 true (-2)
])
theorem kid14_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part547) = true := by rfl

def kid14_part548 : Audit := .cycle 1 13 true (1)
theorem kid14_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part548) = true := by rfl

def kid14_part549 : Audit := .cycle 18 1 false (0)
theorem kid14_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part549) = true := by rfl

def kid14_part550 : Audit := .cycle 9 2 true (1)
theorem kid14_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part550) = true := by rfl

def kid14_part551 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.last 23 (4,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 13 3 false (1)
])
theorem kid14_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part551) = true := by rfl

def kid14_part552 : Audit := .cycle 1 11 true (1)
theorem kid14_part552_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part552) = true := by rfl

def kid14_part553 : Audit := .cycle 7 4 true (1)
theorem kid14_part553_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part553) = true := by rfl

def kid14_part554 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 15 7 false (1),
.cycle 24 3 false (2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 12 true (1)
])
theorem kid14_part554_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part554) = true := by rfl

def kid14_part555 : Audit := .cycle 0 12 true (0)
theorem kid14_part555_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part555) = true := by rfl

def kid14_part556 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 16 (5,false),
.cycle 0 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (5,false),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 9 4 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid14_part556_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part556) = true := by rfl

def kid14_part557 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 22 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4)
])
theorem kid14_part557_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part557) = true := by rfl

def kid14_part533 : Audit := .split 10 (5,true) (byMove [(kid14_part534),(kid14_part535),(kid14_part536),(kid14_part537),(kid14_part538),(kid14_part539),(kid14_part540),(kid14_part541),(kid14_part542),(kid14_part543),(kid14_part544),(kid14_part545),(kid14_part546),(kid14_part547),(kid14_part548),(kid14_part549),(kid14_part550),(kid14_part551),(kid14_part552),(kid14_part553),(kid14_part554),(kid14_part555),(kid14_part556),(kid14_part557)])

theorem kid14_part533_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part533) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid14_part534),(kid14_part535),(kid14_part536),(kid14_part537),(kid14_part538),(kid14_part539),(kid14_part540),(kid14_part541),(kid14_part542),(kid14_part543),(kid14_part544),(kid14_part545),(kid14_part546),(kid14_part547),(kid14_part548),(kid14_part549),(kid14_part550),(kid14_part551),(kid14_part552),(kid14_part553),(kid14_part554),(kid14_part555),(kid14_part556),(kid14_part557)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part534_checked

  · exact kid14_part540_checked

  · exact kid14_part546_checked

  · exact kid14_part552_checked

  · exact kid14_part535_checked

  · exact kid14_part541_checked

  · exact kid14_part547_checked

  · exact kid14_part553_checked

  · exact kid14_part536_checked

  · exact kid14_part542_checked

  · exact kid14_part548_checked

  · exact kid14_part554_checked

  · exact kid14_part537_checked

  · exact kid14_part543_checked

  · exact kid14_part549_checked

  · exact kid14_part555_checked

  · exact kid14_part538_checked

  · exact kid14_part544_checked

  · exact kid14_part550_checked

  · exact kid14_part556_checked

  · exact kid14_part539_checked

  · exact kid14_part545_checked

  · exact kid14_part551_checked

  · exact kid14_part557_checked

def kid14_part558 : Audit := .cycle 11 4 false (1)
theorem kid14_part558_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part558) = true := by rfl

def kid14_part559 : Audit := .split 19 (4,true) (byMove [
.cycle 21 4 true (-2),
.cycle 14 20 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 16 4 false (0),
.split 20 (5,false) (byMove [
.last 32 (5,true),
.cycle 12 13 false (2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 14 8 false (2),
.cycle 17 4 true (-2),
.cycle 11 10 true (-2),
.cycle 21 1 false (-1),
.cycle 16 5 false (0),
.last 22 (5,true),
.cycle 14 8 false (2),
.cycle 17 4 false (0),
.cycle 14 10 false (2),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 18 5 false (0),
.last 24 (5,true),
.last 30 (5,true),
.cycle 12 10 false (2),
.cycle 9 12 false (2),
.last 22 (5,true)
]),
.cycle 13 7 false (2),
.cycle 10 10 true (-1),
.cycle 15 5 false (1),
.cycle 12 8 true (-1),
.cycle 22 5 true (2),
.split 20 (5,true) (byMove [
.cycle 17 34 true (-1),
.cycle 1 35 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 16 5 false (0),
.last 21 (5,false),
.cycle 13 8 true (-1),
.cycle 1 35 true (-1),
.cycle 15 6 true (-1),
.cycle 1 31 true (-1),
.last 24 (5,false),
.last 24 (5,false),
.cycle 14 8 false (2),
.cycle 17 4 true (-1),
.cycle 11 10 true (-1),
.cycle 21 1 false (-1),
.cycle 16 5 false (0),
.last 21 (5,false),
.cycle 18 37 true (-1),
.cycle 14 7 false (2),
.cycle 21 18 true (0),
.cycle 5 16 true (-1),
.last 24 (5,false),
.last 24 (5,false)
]),
.cycle 14 7 false (2),
.cycle 17 3 false (0),
.cycle 11 9 false (2),
.cycle 20 1 false (-2),
.cycle 16 4 false (0),
.split 20 (5,false) (byMove [
.last 25 (5,true),
.last 31 (5,true),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 13 8 false (2),
.cycle 10 11 false (2),
.cycle 15 6 false (1),
.cycle 12 9 false (2),
.cycle 19 2 true (-2),
.last 21 (5,true),
.cycle 14 8 false (2),
.cycle 17 4 false (0),
.cycle 11 10 false (2),
.cycle 21 1 false (-3),
.cycle 16 5 false (0),
.cycle 20 1 false (-2),
.cycle 18 5 false (0),
.cycle 14 7 false (2),
.cycle 18 3 false (0),
.cycle 5 16 false (3),
.last 22 (5,true),
.last 21 (5,true)
]),
.cycle 18 4 true (-1),
.cycle 14 6 false (2),
.cycle 18 2 true (-1),
.cycle 5 15 false (3),
.cycle 20 7 true (0),
.split 20 (5,true) (byMove [
.cycle 17 34 true (-1),
.cycle 14 11 false (2),
.cycle 15 6 false (1),
.cycle 14 9 false (2),
.last 22 (5,false),
.last 22 (5,false),
.cycle 6 15 false (3),
.cycle 1 35 true (-1),
.cycle 8 13 false (2),
.cycle 1 31 true (-1),
.last 24 (5,false),
.last 24 (5,false),
.cycle 13 8 false (2),
.cycle 10 11 false (2),
.cycle 15 6 false (1),
.cycle 12 9 false (2),
.cycle 19 2 true (-1),
.last 22 (5,false),
.cycle 18 29 true (-1),
.cycle 18 4 true (-1),
.cycle 18 24 true (-1),
.cycle 14 12 false (3),
.last 24 (5,false),
.last 24 (5,false)
])
])
theorem kid14_part559_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part559) = true := by rfl

def kid14_part560 : Audit := .cycle 10 6 true (-2)
theorem kid14_part560_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part560) = true := by rfl

def kid14_part561 : Audit := .cycle 15 1 false (-1)
theorem kid14_part561_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part561) = true := by rfl

def kid14_part562 : Audit := .split 10 (4,true) (byMove [
.cycle 12 4 true (-1),
.cycle 9 9 false (3),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 22 (5,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 17 1 false (1),
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
.cycle 9 9 false (3),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.last 13 (5,true)
]),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (4),
.split 11 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 15 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 1 13 true (0),
.cycle 14 1 false (4),
.last 14 (5,false),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 1 17 true (0),
.cycle 14 1 false (0),
.cycle 25 1 false (3),
.cycle 1 13 true (0),
.cycle 12 3 true (2),
.last 14 (5,false)
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
.cycle 18 1 false (0),
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
.cycle 10 4 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 5 6 true (0),
.cycle 12 3 true (2),
.split 11 (5,true) (byMove [
.cycle 1 22 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 19 (5,false),
.last 14 (5,false),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 1 17 true (0),
.cycle 10 4 true (0),
.cycle 2 16 true (0),
.cycle 1 13 true (0),
.cycle 12 3 true (2),
.last 14 (5,false)
])
])
theorem kid14_part562_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part562) = true := by rfl

def kid14_part564 : Audit := .split 14 (4,true) (byMove [
.cycle 12 4 true (-1),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.last 24 (5,false),
.cycle 6 9 false (3),
.last 22 (5,false),
.cycle 8 7 false (2),
.last 20 (5,false),
.last 19 (5,false),
.cycle 12 26 true (0),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.cycle 10 5 false (1),
.cycle 13 4 true (0),
.last 21 (5,false),
.cycle 13 2 true (0),
.cycle 12 10 true (-1),
.cycle 16 7 true (2),
.cycle 12 26 true (0)
])
theorem kid14_part564_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part564) = true := by rfl

def kid14_part565 : Audit := .split 18 (5,false) (byMove [
.last 22 (4,true),
.cycle 11 16 false (3),
.cycle 23 1 false (-3),
.cycle 25 1 false (-3),
.last 19 (4,true),
.cycle 29 1 false (-3),
.cycle 6 13 false (3),
.cycle 12 8 true (0),
.cycle 8 11 false (3),
.cycle 13 6 true (0),
.last 19 (4,true),
.cycle 1 23 true (-1),
.cycle 20 5 false (0),
.last 29 (4,true),
.cycle 19 7 false (-1),
.cycle 25 1 false (-3),
.last 19 (4,true),
.cycle 10 9 false (3),
.last 22 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.cycle 5 28 false (3),
.last 19 (4,true),
.cycle 20 9 false (0)
])
theorem kid14_part565_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part565) = true := by rfl

def kid14_part566 : Audit := .cycle 12 1 false (0)
theorem kid14_part566_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part566) = true := by rfl

def kid14_part567 : Audit := .cycle 11 1 false (-1)
theorem kid14_part567_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part567) = true := by rfl

def kid14_part568 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 17 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.last 16 (4,true),
.cycle 17 8 true (-2),
.cycle 11 3 false (-1),
.cycle 15 6 true (-2),
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
theorem kid14_part568_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part568) = true := by rfl

def kid14_part569 : Audit := .split 11 (5,false) (byMove [
.last 24 (4,true),
.cycle 18 16 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 13 5 false (1),
.last 14 (4,true),
.cycle 16 3 false (2),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 20 1 true (2),
.cycle 11 5 false (-1),
.last 14 (4,true),
.cycle 15 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 14 (4,true),
.last 20 (4,true),
.cycle 5 14 false (3),
.cycle 9 3 false (1),
.cycle 38 1 true (-4)
])
theorem kid14_part569_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part569) = true := by rfl

def kid14_part570 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.cycle 12 16 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.cycle 11 5 false (2),
.cycle 11 8 true (-1),
.cycle 13 3 false (1),
.cycle 11 6 true (-1),
.last 16 (4,true),
.cycle 10 6 true (-1),
.cycle 12 5 false (2),
.last 18 (4,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 14 2 false (0),
.cycle 15 1 false (-1),
.last 19 (4,true),
.cycle 12 4 false (2),
.last 17 (4,true),
.cycle 5 11 false (3),
.last 16 (4,true),
.cycle 6 11 false (3)
])
theorem kid14_part570_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part570) = true := by rfl

def kid14_part571 : Audit := .split 18 (5,false) (byMove [
.last 22 (4,true),
.cycle 15 16 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.cycle 14 5 false (3),
.cycle 11 8 true (0),
.cycle 16 3 false (2),
.cycle 13 6 true (0),
.last 19 (4,true),
.cycle 1 23 true (0),
.cycle 15 5 false (3),
.last 21 (4,true),
.cycle 12 7 false (3),
.cycle 19 1 false (-1),
.cycle 17 2 false (1),
.cycle 18 1 false (0),
.last 22 (4,true),
.cycle 15 4 false (3),
.last 20 (4,true),
.cycle 5 14 true (0),
.last 19 (4,true),
.cycle 1 23 true (0)
])
theorem kid14_part571_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part571) = true := by rfl

def kid14_part572 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 11 16 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
.cycle 11 3 false (1),
.cycle 11 6 true (-1),
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
theorem kid14_part572_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part572) = true := by rfl

def kid14_part573 : Audit := .split 16 (5,false) (byMove [
.last 20 (4,true),
.cycle 13 16 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 12 5 false (3),
.cycle 11 8 true (0),
.cycle 14 3 false (2),
.cycle 11 6 true (0),
.last 17 (4,true),
.cycle 1 19 true (0),
.cycle 13 5 false (3),
.last 19 (4,true),
.cycle 11 7 false (3),
.cycle 17 1 false (-1),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.last 20 (4,true),
.cycle 13 4 false (3),
.last 18 (4,true),
.cycle 5 12 true (0),
.last 17 (4,true),
.cycle 1 19 true (0)
])
theorem kid14_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part573) = true := by rfl

def kid14_part574 : Audit := .split 11 (4,true) (byMove [
.cycle 13 4 true (0),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.last 16 (5,false),
.cycle 1 15 true (0),
.last 14 (5,false),
.cycle 1 13 true (0),
.last 15 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.cycle 11 3 false (1),
.last 18 (5,false),
.cycle 12 1 false (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 11 4 true (1),
.last 15 (5,false),
.cycle 11 2 true (1),
.cycle 1 13 true (0),
.cycle 13 3 true (3),
.last 14 (5,false)
])
theorem kid14_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part574) = true := by rfl

def kid14_part575 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 21 16 false (5),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 2 false (4),
.cycle 14 1 false (4),
.cycle 0 15 true (0),
.cycle 19 8 true (4),
.cycle 16 1 false (6),
.cycle 15 1 false (5),
.last 17 (4,true),
.cycle 14 1 true (4),
.cycle 14 5 false (4),
.last 17 (4,true),
.cycle 0 17 true (0),
.cycle 15 1 false (3),
.cycle 14 2 false (4),
.cycle 14 1 false (4),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.last 25 (4,true),
.cycle 1 17 true (0),
.cycle 12 4 true (2),
.cycle 14 1 true (4)
])
theorem kid14_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part575) = true := by rfl

def kid14_part576 : Audit := .split 15 (5,false) (byMove [
.last 19 (4,true),
.cycle 11 16 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 14 2 false (-2),
.cycle 15 1 false (-3),
.cycle 12 5 false (0),
.cycle 12 8 true (-3),
.cycle 13 3 false (-1),
.cycle 12 6 true (-3),
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
.cycle 5 11 false (3),
.last 16 (4,true),
.cycle 12 6 false (0)
])
theorem kid14_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part576) = true := by rfl

def kid14_part577 : Audit := .split 13 (4,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.last 21 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 10 4 true (-1),
.last 18 (5,false),
.cycle 11 3 false (0),
.last 20 (5,false),
.cycle 14 1 false (-2),
.last 15 (5,false),
.last 14 (5,false),
.cycle 12 4 true (-1),
.last 17 (5,false),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.cycle 12 9 true (-1),
.last 22 (5,false)
])
theorem kid14_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part577) = true := by rfl

def kid14_part578 : Audit := .split 17 (5,false) (byMove [
.last 21 (4,true),
.cycle 14 16 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (2),
.cycle 11 8 true (-1),
.cycle 15 3 false (1),
.cycle 12 6 true (-1),
.last 18 (4,true),
.cycle 10 8 true (-1),
.cycle 14 5 false (2),
.last 20 (4,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.last 21 (4,true),
.cycle 14 4 false (2),
.last 19 (4,true),
.cycle 5 13 false (3),
.last 18 (4,true),
.cycle 15 4 false (1)
])
theorem kid14_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part578) = true := by rfl

def kid14_part579 : Audit := .cycle 11 1 false (-1)
theorem kid14_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part579) = true := by rfl

def kid14_part580 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,true),
.cycle 11 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 11 5 false (0),
.cycle 11 8 true (-2),
.cycle 11 3 false (-1),
.cycle 11 6 true (-2),
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
theorem kid14_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part580) = true := by rfl

def kid14_part581 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,true),
.cycle 11 16 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 1 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
.cycle 11 3 false (0),
.cycle 11 6 true (-1),
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
theorem kid14_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part581) = true := by rfl

def kid14_part582 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.last 22 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 19 (5,false),
.cycle 1 21 true (0),
.last 19 (5,false),
.cycle 13 3 false (1),
.last 21 (5,false),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 11 4 true (0),
.last 18 (5,false),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 1 20 true (0),
.cycle 1 21 true (0)
])
theorem kid14_part582_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part582) = true := by rfl

def kid14_part583 : Audit := .split 14 (5,false) (byMove [
.last 18 (4,true),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 11 5 false (1),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 11 6 true (-2),
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
.cycle 5 10 false (3),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid14_part583_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part583) = true := by rfl

def kid14_part584 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.last 20 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 15 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 28 (5,false),
.last 17 (5,false),
.cycle 11 3 false (1),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 11 4 true (0),
.last 16 (5,false),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 14 5 true (2),
.cycle 2 18 true (0)
])
theorem kid14_part584_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part584) = true := by rfl

def kid14_part585 : Audit := .cycle 5 6 true (0)
theorem kid14_part585_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part585) = true := by rfl

def kid14_part586 : Audit := .split 11 (4,true) (byMove [
.cycle 11 4 true (0),
.last 19 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 9 4 true (0),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 15 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 14 (5,false),
.cycle 10 2 true (0),
.cycle 11 4 true (1),
.last 18 (5,false),
.cycle 11 2 true (1),
.cycle 1 13 true (0),
.cycle 13 3 true (3),
.last 14 (5,false)
])
theorem kid14_part586_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part586) = true := by rfl

def kid14_part587 : Audit := .split 14 (5,false) (byMove [
.cycle 1 15 true (0),
.last 17 (4,true),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 13 2 true (3),
.cycle 0 15 true (0),
.cycle 19 8 true (4),
.cycle 10 15 true (0),
.cycle 3 12 true (0),
.last 17 (4,true),
.cycle 14 1 true (4),
.last 18 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.cycle 1 16 true (0),
.last 15 (4,true),
.cycle 12 3 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 12 4 true (2),
.cycle 14 1 true (4)
])
theorem kid14_part587_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part587) = true := by rfl

def kid14_part563 : Audit := .split 10 (5,true) (byMove [(kid14_part564),(kid14_part565),(kid14_part566),(kid14_part567),(kid14_part568),(kid14_part569),(kid14_part570),(kid14_part571),(kid14_part572),(kid14_part573),(kid14_part574),(kid14_part575),(kid14_part576),(kid14_part577),(kid14_part578),(kid14_part579),(kid14_part580),(kid14_part581),(kid14_part582),(kid14_part583),(kid14_part584),(kid14_part585),(kid14_part586),(kid14_part587)])

theorem kid14_part563_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part563) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part564),(kid14_part565),(kid14_part566),(kid14_part567),(kid14_part568),(kid14_part569),(kid14_part570),(kid14_part571),(kid14_part572),(kid14_part573),(kid14_part574),(kid14_part575),(kid14_part576),(kid14_part577),(kid14_part578),(kid14_part579),(kid14_part580),(kid14_part581),(kid14_part582),(kid14_part583),(kid14_part584),(kid14_part585),(kid14_part586),(kid14_part587)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part564_checked

  · exact kid14_part570_checked

  · exact kid14_part576_checked

  · exact kid14_part582_checked

  · exact kid14_part565_checked

  · exact kid14_part571_checked

  · exact kid14_part577_checked

  · exact kid14_part583_checked

  · exact kid14_part566_checked

  · exact kid14_part572_checked

  · exact kid14_part578_checked

  · exact kid14_part584_checked

  · exact kid14_part567_checked

  · exact kid14_part573_checked

  · exact kid14_part579_checked

  · exact kid14_part585_checked

  · exact kid14_part568_checked

  · exact kid14_part574_checked

  · exact kid14_part580_checked

  · exact kid14_part586_checked

  · exact kid14_part569_checked

  · exact kid14_part575_checked

  · exact kid14_part581_checked

  · exact kid14_part587_checked

def kid14_part588 : Audit := .split 13 (4,true) (byMove [
.cycle 12 4 true (0),
.cycle 1 39 true (-1),
.cycle 23 1 false (-1),
.cycle 23 1 false (-1),
.cycle 1 27 true (-2),
.split 14 (5,true) (byMove [
.cycle 1 19 true (-1),
.last 28 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 22 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.last 20 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.last 25 (5,false),
.cycle 15 1 false (-1),
.last 22 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 12 4 true (0),
.cycle 1 17 true (0),
.last 25 (5,false),
.cycle 9 6 true (0),
.last 15 (5,false)
]),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.cycle 0 17 true (0),
.split 14 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 1 24 true (0),
.cycle 11 6 true (1),
.last 15 (5,false),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 16 9 false (2),
.cycle 12 4 true (1),
.cycle 1 17 true (1),
.cycle 26 1 false (0),
.cycle 9 6 true (1),
.last 15 (5,false),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false)
]),
.cycle 15 8 false (1),
.cycle 23 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.cycle 14 5 false (1),
.split 14 (5,true) (byMove [
.cycle 12 5 false (2),
.last 26 (5,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 20 (5,false),
.last 15 (5,false),
.last 23 (5,false),
.last 26 (5,false),
.last 21 (5,false),
.last 24 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.last 23 (5,false),
.last 18 (5,false),
.last 25 (5,false),
.cycle 15 1 false (-1),
.last 20 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.cycle 5 10 true (0),
.cycle 13 2 true (0),
.last 18 (5,false)
]),
.cycle 10 4 true (1),
.cycle 14 7 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.cycle 0 17 true (0),
.split 14 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 15 12 true (-2),
.cycle 0 24 true (-1),
.cycle 7 10 true (1),
.last 16 (5,false),
.last 17 (5,false),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 15 9 false (2),
.cycle 15 12 true (-2),
.cycle 15 7 false (1),
.cycle 5 10 true (1),
.cycle 13 2 true (1),
.last 17 (5,false),
.cycle 1 15 true (1),
.cycle 11 4 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.last 16 (5,false)
])
])
theorem kid14_part588_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part588) = true := by rfl

def kid14_part589 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 7 13 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 15 false (3),
.split 13 (5,false) (byMove [
.last 28 (5,true),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 28 (5,true),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 11 4 true (-1),
.cycle 17 3 false (3),
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
.cycle 7 13 false (3),
.cycle 17 3 false (1),
.cycle 9 5 false (2),
.last 15 (5,true)
]),
.cycle 14 3 false (2),
.cycle 17 3 false (3),
.cycle 13 3 false (1),
.cycle 15 3 false (3),
.cycle 1 16 true (0),
.split 13 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 1 24 true (0),
.last 14 (5,false),
.cycle 15 3 false (3),
.cycle 1 17 true (0),
.cycle 14 3 false (2),
.cycle 1 15 true (0),
.cycle 1 16 true (0),
.last 16 (5,false),
.cycle 15 3 false (1),
.cycle 11 4 true (0),
.cycle 17 3 false (3),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.last 14 (5,false),
.cycle 1 19 true (0),
.cycle 14 3 false (2),
.cycle 25 3 false (5),
.cycle 1 15 true (0),
.cycle 1 16 true (0),
.last 16 (5,false)
]),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 16 3 false (2),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.split 13 (5,false) (byMove [
.last 18 (5,true),
.cycle 7 14 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 18 (5,true),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
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
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 10 4 true (0),
.cycle 13 3 false (1),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 1 16 true (0),
.split 13 (5,true) (byMove [
.cycle 1 24 true (0),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.cycle 1 16 true (0),
.last 16 (5,false),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
.cycle 12 2 true (0),
.last 15 (5,false),
.cycle 1 19 true (0),
.cycle 10 4 true (0),
.cycle 2 18 true (0),
.cycle 1 15 true (0),
.cycle 1 16 true (0),
.last 16 (5,false)
])
])
theorem kid14_part589_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part589) = true := by rfl

def kid14_part590 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 1 45 true (-2),
.split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 24 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.cycle 1 15 true (0),
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
.cycle 1 15 true (0),
.last 21 (5,false),
.cycle 9 4 true (0),
.last 13 (5,false)
]),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 2 13 true (1),
.split 12 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 1 22 true (0),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 15 7 false (1),
.cycle 10 4 true (1),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false)
]),
.cycle 13 6 false (1),
.cycle 19 3 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 22 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 16 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.cycle 5 8 true (0),
.cycle 11 2 true (0),
.last 16 (5,false)
]),
.cycle 10 4 true (1),
.cycle 13 5 false (1),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.cycle 2 13 true (1),
.split 12 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 13 10 true (-2),
.cycle 13 5 false (1),
.cycle 7 8 true (1),
.last 14 (5,false),
.last 15 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 8 22 true (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 15 7 false (1),
.cycle 13 10 true (-2),
.cycle 13 5 false (1),
.cycle 5 8 true (1),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 1 13 true (1),
.cycle 10 4 true (1),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false)
])
])
theorem kid14_part590_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part590) = true := by rfl

def kid14_part591 : Audit := .cycle 1 11 true (1)
theorem kid14_part591_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part591) = true := by rfl

def kid14_part592 : Audit := .split 10 (4,true) (byMove [
.cycle 10 4 true (1),
.cycle 11 8 true (-2),
.cycle 14 1 false (0),
.cycle 7 6 true (1),
.cycle 22 1 true (-2),
.split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 18 11 false (2),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.last 13 (5,false),
.last 13 (5,false),
.cycle 7 6 true (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 15 1 true (3),
.last 12 (5,false),
.cycle 13 6 false (1),
.last 23 (5,false),
.cycle 12 8 true (-2),
.cycle 18 1 false (0),
.last 13 (5,false),
.last 13 (5,false),
.last 21 (5,false),
.cycle 10 4 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 1 true (3),
.last 12 (5,false)
]),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 8 16 true (1),
.cycle 0 12 true (0),
.cycle 12 1 true (4),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 15 11 false (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
]),
.cycle 16 5 false (0),
.cycle 11 8 true (-2),
.cycle 17 3 false (1),
.cycle 5 6 true (1),
.cycle 11 3 false (1),
.split 11 (5,true) (byMove [
.cycle 13 5 false (2),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 13 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 13 6 false (1),
.last 24 (5,false),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 13 (5,false),
.last 21 (5,false),
.last 15 (5,false),
.last 17 (5,false),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 14 (5,false)
]),
.cycle 1 11 true (1),
.cycle 13 7 false (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 12 1 true (4),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 5 false (2),
.last 21 (5,false),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 15 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,false),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.last 12 (5,false),
.cycle 15 11 false (2),
.cycle 20 5 false (2),
.cycle 13 7 false (2),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 15 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 12 (5,false)
])
])
theorem kid14_part592_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part592) = true := by rfl

def kid14_part594 : Audit := .split 14 (4,true) (byMove [
.cycle 11 4 true (1),
.cycle 15 12 true (-2),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.last 18 (5,false),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 20 9 false (0),
.cycle 15 12 true (-2),
.cycle 21 7 false (2),
.cycle 5 10 true (1),
.cycle 15 7 false (1),
.cycle 17 5 false (2),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.last 17 (5,false),
.cycle 1 16 true (1)
])
theorem kid14_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part594) = true := by rfl

def kid14_part595 : Audit := .cycle 11 8 true (-2)
theorem kid14_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part595) = true := by rfl

def kid14_part596 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 32, 64, 64],[2, 15, 15, 1, 15, 15, 64],112⟩,
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 17 true (0),
.cycle 18 3 false (2),
.cycle 13 3 false (1),
.cycle 16 3 false (2),
.cycle 14 3 false (3),
.cycle 15 1 false (1),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 19 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 1 17 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 7 8 true (0),
.last 20 (5,false),
.cycle 13 3 false (1)
])
theorem kid14_part596_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part596) = true := by rfl

def kid14_part597 : Audit := .cycle 7 6 true (1)
theorem kid14_part597_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part597) = true := by rfl

def kid14_part598 : Audit := .split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 23 11 false (3),
.cycle 17 1 false (-1),
.cycle 24 1 false (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 7 6 true (1),
.cycle 0 18 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 16 (5,false),
.last 12 (5,false),
.cycle 13 6 false (1),
.cycle 27 3 false (1),
.cycle 12 8 true (-2),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.last 14 (5,false),
.cycle 13 4 true (1),
.cycle 16 11 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 16 (5,false),
.last 12 (5,false)
])
theorem kid14_part598_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part598) = true := by rfl

def kid14_part599 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.cycle 1 29 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 19 2 true (1),
.cycle 18 1 true (2),
.cycle 11 7 false (1),
.last 16 (4,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 11 4 false (1),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 0 20 true (-1),
.cycle 22 2 true (-2),
.cycle 22 1 true (-2)
])
theorem kid14_part599_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part599) = true := by rfl

def kid14_part600 : Audit := .cycle 1 11 true (1)
theorem kid14_part600_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part600) = true := by rfl

def kid14_part601 : Audit := .cycle 0 14 true (0)
theorem kid14_part601_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part601) = true := by rfl

def kid14_part602 : Audit := .cycle 8 16 true (1)
theorem kid14_part602_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part602) = true := by rfl

def kid14_part603 : Audit := .cycle 0 12 true (0)
theorem kid14_part603_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part603) = true := by rfl

def kid14_part604 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.last 13 (5,false),
.last 12 (5,false),
.cycle 17 10 false (1),
.cycle 15 12 true (-2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 15 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid14_part604_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part604) = true := by rfl

def kid14_part605 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 32, 2048, 32, 8192, 16384, 8, 128, 131072, 32, 8192, 16384, 8, 128, 131072, 262144, 262144],[128, 1, 32, 1, 262144, 32, 8192, 32, 262144, 1, 262144, 32, 8192, 262144, 262144, 1, 262144, 32, 262144],459776⟩,
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 32, 2048, 4, 8192, 16384, 8, 128, 131072, 4, 8192, 16384, 8, 128, 131072, 4, 262144],[128, 1, 32, 1, 262144, 32, 8192, 32, 262144, 1, 262144, 32, 8192, 262144, 262144, 1, 262144, 32, 262144],262144⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 32, 2048, 8, 8192, 16384, 8, 128, 131072, 8, 8192, 16384, 8, 128, 131072, 8, 262144],[128, 1, 32, 1, 262144, 32, 8192, 32, 262144, 1, 262144, 32, 8192, 262144, 262144, 1, 262144, 32, 262144],262144⟩,
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.cycle 7 7 true (1),
.last 15 (4,true),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 32, 2048, 32, 8192, 16384, 8, 128, 131072, 128, 8192, 16384, 8, 128, 131072, 128, 262144],[128, 1, 32, 1, 262144, 32, 8192, 32, 262144, 1, 262144, 32, 8192, 262144, 262144, 1, 262144, 32, 262144],262144⟩,
.cycle 11 3 true (3),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4)
])
theorem kid14_part605_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part605) = true := by rfl

def kid14_part606 : Audit := .split 14 (4,true) (byMove [
.cycle 16 4 true (-1),
.cycle 6 17 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,false),
.last 15 (5,false),
.cycle 15 5 false (2),
.cycle 18 5 false (3),
.cycle 15 5 false (1),
.cycle 16 5 false (3),
.last 19 (5,false),
.cycle 17 5 false (1),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 17 5 false (2),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 11 4 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.last 19 (5,false),
.cycle 15 5 false (1)
])
theorem kid14_part606_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part606) = true := by rfl

def kid14_part607 : Audit := .cycle 11 8 true (-2)
theorem kid14_part607_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part607) = true := by rfl

def kid14_part608 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (-1),
.cycle 8 13 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 13 3 false (1),
.cycle 16 3 false (2),
.last 17 (5,false),
.cycle 18 3 false (2),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 11 4 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.last 17 (5,false),
.cycle 13 3 false (1)
])
theorem kid14_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part608) = true := by rfl

def kid14_part609 : Audit := .cycle 5 6 true (1)
theorem kid14_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part609) = true := by rfl

def kid14_part610 : Audit := .split 11 (4,true) (byMove [
.cycle 11 4 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 14 (5,false),
.last 16 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 15 (5,false),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.cycle 20 3 false (0),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 11 4 true (1),
.cycle 14 5 false (1),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.last 15 (5,false),
.cycle 10 2 true (1)
])
theorem kid14_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part610) = true := by rfl

def kid14_part611 : Audit := .split 13 (5,false) (byMove [
.last 17 (4,true),
.cycle 11 20 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (4,true),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 11 10 true (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
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
theorem kid14_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part611) = true := by rfl

def kid14_part612 : Audit := .cycle 1 11 true (1)
theorem kid14_part612_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part612) = true := by rfl

def kid14_part613 : Audit := .split 13 (4,true) (byMove [
.cycle 12 4 true (0),
.cycle 1 39 true (-1),
.cycle 23 1 false (-1),
.cycle 23 1 false (-1),
.last 16 (5,false),
.cycle 12 4 true (0),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.last 17 (5,false),
.cycle 7 8 true (1),
.cycle 15 8 false (1),
.cycle 23 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.cycle 14 5 false (1),
.last 22 (5,false),
.cycle 11 4 true (1),
.cycle 14 7 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.last 17 (5,false),
.cycle 10 4 true (1)
])
theorem kid14_part613_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part613) = true := by rfl

def kid14_part614 : Audit := .split 12 (4,true) (byMove [
.cycle 11 4 true (1),
.cycle 13 10 true (-2),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 18 7 false (0),
.cycle 13 10 true (-2),
.cycle 19 5 false (2),
.cycle 5 8 true (1),
.cycle 13 5 false (1),
.last 19 (5,false),
.cycle 1 13 true (1),
.cycle 14 9 false (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 12 true (1)
])
theorem kid14_part614_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part614) = true := by rfl

def kid14_part615 : Audit := .cycle 0 12 true (0)
theorem kid14_part615_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part615) = true := by rfl

def kid14_part616 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 18 true (-1),
.last 20 (5,false),
.cycle 0 13 true (0),
.last 16 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (5,false),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.cycle 12 5 false (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,false),
.last 12 (5,false)
])
theorem kid14_part616_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part616) = true := by rfl

def kid14_part617 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 12 1 true (4)
])
theorem kid14_part617_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part617) = true := by rfl

def kid14_part593 : Audit := .split 10 (5,true) (byMove [(kid14_part594),(kid14_part595),(kid14_part596),(kid14_part597),(kid14_part598),(kid14_part599),(kid14_part600),(kid14_part601),(kid14_part602),(kid14_part603),(kid14_part604),(kid14_part605),(kid14_part606),(kid14_part607),(kid14_part608),(kid14_part609),(kid14_part610),(kid14_part611),(kid14_part612),(kid14_part613),(kid14_part614),(kid14_part615),(kid14_part616),(kid14_part617)])

theorem kid14_part593_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part593) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid14_part594),(kid14_part595),(kid14_part596),(kid14_part597),(kid14_part598),(kid14_part599),(kid14_part600),(kid14_part601),(kid14_part602),(kid14_part603),(kid14_part604),(kid14_part605),(kid14_part606),(kid14_part607),(kid14_part608),(kid14_part609),(kid14_part610),(kid14_part611),(kid14_part612),(kid14_part613),(kid14_part614),(kid14_part615),(kid14_part616),(kid14_part617)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part594_checked

  · exact kid14_part600_checked

  · exact kid14_part606_checked

  · exact kid14_part612_checked

  · exact kid14_part595_checked

  · exact kid14_part601_checked

  · exact kid14_part607_checked

  · exact kid14_part613_checked

  · exact kid14_part596_checked

  · exact kid14_part602_checked

  · exact kid14_part608_checked

  · exact kid14_part614_checked

  · exact kid14_part597_checked

  · exact kid14_part603_checked

  · exact kid14_part609_checked

  · exact kid14_part615_checked

  · exact kid14_part598_checked

  · exact kid14_part604_checked

  · exact kid14_part610_checked

  · exact kid14_part616_checked

  · exact kid14_part599_checked

  · exact kid14_part605_checked

  · exact kid14_part611_checked

  · exact kid14_part617_checked

def kid14_part497 : Audit := .split 9 (4,false) (byMove [(kid14_part498),(kid14_part499),(kid14_part500),(kid14_part501),(kid14_part502),(kid14_part503),(kid14_part528),(kid14_part529),(kid14_part530),(kid14_part531),(kid14_part532),(kid14_part533),(kid14_part558),(kid14_part559),(kid14_part560),(kid14_part561),(kid14_part562),(kid14_part563),(kid14_part588),(kid14_part589),(kid14_part590),(kid14_part591),(kid14_part592),(kid14_part593)])

theorem kid14_part497_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (kid14_part497) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid14_part498),(kid14_part499),(kid14_part500),(kid14_part501),(kid14_part502),(kid14_part503),(kid14_part528),(kid14_part529),(kid14_part530),(kid14_part531),(kid14_part532),(kid14_part533),(kid14_part558),(kid14_part559),(kid14_part560),(kid14_part561),(kid14_part562),(kid14_part563),(kid14_part588),(kid14_part589),(kid14_part590),(kid14_part591),(kid14_part592),(kid14_part593)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part498_checked

  · exact kid14_part528_checked

  · exact kid14_part558_checked

  · exact kid14_part588_checked

  · exact kid14_part499_checked

  · exact kid14_part529_checked

  · exact kid14_part559_checked

  · exact kid14_part589_checked

  · exact kid14_part500_checked

  · exact kid14_part530_checked

  · exact kid14_part560_checked

  · exact kid14_part590_checked

  · exact kid14_part501_checked

  · exact kid14_part531_checked

  · exact kid14_part561_checked

  · exact kid14_part591_checked

  · exact kid14_part502_checked

  · exact kid14_part532_checked

  · exact kid14_part562_checked

  · exact kid14_part592_checked

  · exact kid14_part503_checked

  · exact kid14_part533_checked

  · exact kid14_part563_checked

  · exact kid14_part593_checked

def kid14_part619 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (0),
.cycle 11 11 false (2),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.split 14 (4,true) (byMove [
.cycle 1 19 true (-1),
.cycle 11 14 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 0 16 false (3),
.cycle 11 9 false (2),
.last 18 (4,false),
.cycle 1 17 true (0),
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
.cycle 1 17 true (0),
.cycle 11 11 false (2),
.last 15 (4,false),
.cycle 9 6 true (0)
]),
.cycle 0 16 false (3),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.split 14 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 11 13 false (2),
.cycle 1 24 true (0),
.last 15 (4,false),
.cycle 0 20 true (0),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 11 36 true (0),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false),
.cycle 11 14 false (2),
.cycle 11 4 true (1),
.cycle 1 17 true (0),
.cycle 11 11 false (2),
.last 15 (4,false),
.cycle 9 6 true (0),
.cycle 1 15 true (0),
.cycle 7 8 true (0),
.cycle 11 16 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 0 17 true (0),
.cycle 11 8 false (2),
.cycle 11 11 false (2),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 11 24 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 21 16 false (3),
.cycle 11 9 false (2),
.cycle 11 12 true (0),
.cycle 11 7 false (2),
.cycle 11 10 true (0),
.last 18 (4,false),
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
.cycle 5 10 true (0),
.last 18 (4,false),
.cycle 13 2 true (0)
]),
.cycle 11 6 false (2),
.cycle 12 4 true (1),
.cycle 11 10 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.split 14 (4,true) (byMove [
.cycle 1 20 true (0),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 7 10 true (0),
.last 17 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.cycle 8 28 true (0),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false),
.cycle 11 14 false (2),
.cycle 11 8 false (2),
.cycle 11 10 false (2),
.cycle 5 10 true (0),
.last 17 (4,false),
.cycle 13 2 true (1),
.cycle 1 15 true (0),
.cycle 12 4 true (1),
.cycle 2 16 true (0),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 1 17 true (0)
])
theorem kid14_part619_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part619) = true := by rfl

def kid14_part620 : Audit := .cycle 1 27 true (-1)
theorem kid14_part620_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part620) = true := by rfl

def kid14_part621 : Audit := .cycle 13 1 false (-1)
theorem kid14_part621_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part621) = true := by rfl

def kid14_part622 : Audit := .cycle 15 1 false (-1)
theorem kid14_part622_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part622) = true := by rfl

def kid14_part624 : Audit := .cycle 1 15 true (-1)
theorem kid14_part624_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part624) = true := by rfl

def kid14_part625 : Audit := .split 20 (4,false) (byMove [
.cycle 22 43 true (-2),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 17 5 false (1),
.last 23 (5,true),
.cycle 1 37 true (-2),
.cycle 21 1 false (-1),
.cycle 0 36 true (-2),
.cycle 19 2 true (-2),
.cycle 17 5 false (1),
.last 23 (5,true),
.cycle 17 7 false (1),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 24 (5,true),
.last 23 (5,true),
.cycle 1 37 true (-2),
.cycle 14 7 false (1),
.cycle 17 6 false (1),
.cycle 9 12 false (1)
])
theorem kid14_part625_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part625) = true := by rfl

def kid14_part626 : Audit := .cycle 12 1 false (0)
theorem kid14_part626_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part626) = true := by rfl

def kid14_part627 : Audit := .cycle 11 1 false (-1)
theorem kid14_part627_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part627) = true := by rfl

def kid14_part628 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 18 1 true (2),
.cycle 11 2 true (-1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 17 (5,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.cycle 1 15 true (-1),
.cycle 1 37 true (-2),
.last 17 (5,true),
.cycle 29 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid14_part628_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part628) = true := by rfl

def kid14_part629 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 1 17 true (-2),
.last 25 (5,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 23 1 true (1),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 33 (5,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 1 17 true (-2),
.cycle 1 12 false (3),
.last 27 (5,true),
.cycle 1 19 true (-2),
.last 17 (5,true),
.cycle 9 4 false (1)
])
theorem kid14_part629_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part629) = true := by rfl

def kid14_part630 : Audit := .split 15 (4,false) (byMove [
.cycle 1 29 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.last 18 (5,true),
.cycle 1 25 true (-1),
.cycle 16 1 false (0),
.cycle 1 25 true (-1),
.cycle 14 2 true (-1),
.cycle 11 5 false (2),
.last 18 (5,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 1 25 true (-1),
.cycle 12 7 false (2),
.cycle 7 17 false (3),
.cycle 9 7 false (2)
])
theorem kid14_part630_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part630) = true := by rfl

def kid14_part631 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (0),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 1 17 true (0),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 17 (4,false),
.last 18 (4,false),
.cycle 11 3 false (2),
.last 20 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 4 true (1),
.last 17 (4,false),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.cycle 0 18 true (0),
.last 27 (4,false)
])
theorem kid14_part631_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part631) = true := by rfl

def kid14_part632 : Audit := .cycle 1 13 true (0)
theorem kid14_part632_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part632) = true := by rfl

def kid14_part633 : Audit := .cycle 11 1 false (1)
theorem kid14_part633_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part633) = true := by rfl

def kid14_part634 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 13 5 false (3),
.cycle 1 15 true (0),
.cycle 1 17 true (0),
.cycle 1 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true),
.cycle 11 5 false (1),
.last 14 (5,true),
.cycle 15 7 false (3),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.last 15 (5,true),
.last 18 (5,true),
.last 13 (5,true),
.cycle 1 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true)
])
theorem kid14_part634_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part634) = true := by rfl

def kid14_part635 : Audit := .split 12 (4,false) (byMove [
.cycle 1 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 5 false (2),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 15 (5,true),
.cycle 11 2 true (0),
.cycle 11 5 false (1),
.last 15 (5,true),
.cycle 11 7 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (0),
.cycle 11 7 false (2),
.last 15 (5,true),
.cycle 9 4 true (0)
])
theorem kid14_part635_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part635) = true := by rfl

def kid14_part636 : Audit := .split 15 (4,false) (byMove [
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
theorem kid14_part636_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part636) = true := by rfl

def kid14_part637 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 6 12 true (-1),
.last 21 (4,false),
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
.cycle 16 4 true (1),
.last 17 (4,false),
.cycle 12 2 true (-1),
.cycle 7 9 false (3),
.last 26 (4,false),
.cycle 23 8 true (0)
])
theorem kid14_part637_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part637) = true := by rfl

def kid14_part638 : Audit := .split 17 (4,false) (byMove [
.cycle 1 31 true (-2),
.cycle 14 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.last 20 (5,true),
.cycle 1 27 true (-1),
.cycle 18 1 false (0),
.cycle 1 31 true (-1),
.cycle 16 2 true (-1),
.cycle 13 5 false (2),
.last 20 (5,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 1 27 true (-1),
.cycle 14 7 false (2),
.last 21 (5,true),
.cycle 9 9 false (2)
])
theorem kid14_part638_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part638) = true := by rfl

def kid14_part639 : Audit := .cycle 11 1 false (-1)
theorem kid14_part639_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part639) = true := by rfl

def kid14_part640 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.last 26 (5,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 22 (5,true),
.cycle 1 31 true (-2),
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
theorem kid14_part640_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part640) = true := by rfl

def kid14_part641 : Audit := .split 12 (4,false) (byMove [
.cycle 14 35 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.last 15 (5,true),
.cycle 1 29 true (-2),
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
.cycle 1 29 true (-2),
.cycle 11 7 false (0),
.last 15 (5,true),
.cycle 9 4 false (1)
])
theorem kid14_part641_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part641) = true := by rfl

def kid14_part642 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.cycle 1 21 true (0),
.last 19 (4,false),
.last 19 (4,false),
.cycle 13 3 false (1),
.last 21 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 12 4 true (0),
.last 18 (4,false),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 1 21 true (0),
.cycle 0 20 true (0)
])
theorem kid14_part642_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part642) = true := by rfl

def kid14_part643 : Audit := .split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.last 21 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 10 4 true (0),
.last 16 (4,false),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.cycle 7 8 true (0),
.last 17 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.cycle 12 4 true (1),
.last 20 (4,false),
.cycle 12 2 true (1),
.cycle 1 15 true (0),
.cycle 12 4 true (1),
.cycle 1 17 true (0)
])
theorem kid14_part643_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part643) = true := by rfl

def kid14_part644 : Audit := .cycle 1 13 true (0)
theorem kid14_part644_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part644) = true := by rfl

def kid14_part645 : Audit := .split 17 (4,false) (byMove [
.cycle 1 31 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 14 5 false (2),
.last 20 (5,true),
.cycle 1 27 true (-1),
.cycle 18 1 false (0),
.cycle 1 21 true (-1),
.cycle 16 2 true (-1),
.cycle 14 5 false (2),
.last 20 (5,true),
.cycle 14 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 1 27 true (-1),
.cycle 11 7 false (2),
.cycle 1 21 true (-1),
.cycle 9 9 false (2)
])
theorem kid14_part645_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part645) = true := by rfl

def kid14_part646 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 16 10 false (2),
.cycle 16 1 false (-2),
.cycle 18 1 false (-2),
.cycle 10 2 true (0),
.last 12 (5,true),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true),
.cycle 13 5 false (1),
.last 22 (5,true),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.cycle 14 3 true (2),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (0),
.cycle 14 1 true (4),
.last 12 (5,true)
])
theorem kid14_part646_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part646) = true := by rfl

def kid14_part647 : Audit := .cycle 9 2 true (0)
theorem kid14_part647_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part647) = true := by rfl

def kid14_part623 : Audit := .split 10 (4,true) (byMove [(kid14_part624),(kid14_part625),(kid14_part626),(kid14_part627),(kid14_part628),(kid14_part629),(kid14_part630),(kid14_part631),(kid14_part632),(kid14_part633),(kid14_part634),(kid14_part635),(kid14_part636),(kid14_part637),(kid14_part638),(kid14_part639),(kid14_part640),(kid14_part641),(kid14_part642),(kid14_part643),(kid14_part644),(kid14_part645),(kid14_part646),(kid14_part647)])

theorem kid14_part623_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part623) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part624),(kid14_part625),(kid14_part626),(kid14_part627),(kid14_part628),(kid14_part629),(kid14_part630),(kid14_part631),(kid14_part632),(kid14_part633),(kid14_part634),(kid14_part635),(kid14_part636),(kid14_part637),(kid14_part638),(kid14_part639),(kid14_part640),(kid14_part641),(kid14_part642),(kid14_part643),(kid14_part644),(kid14_part645),(kid14_part646),(kid14_part647)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part624_checked

  · exact kid14_part630_checked

  · exact kid14_part636_checked

  · exact kid14_part642_checked

  · exact kid14_part625_checked

  · exact kid14_part631_checked

  · exact kid14_part637_checked

  · exact kid14_part643_checked

  · exact kid14_part626_checked

  · exact kid14_part632_checked

  · exact kid14_part638_checked

  · exact kid14_part644_checked

  · exact kid14_part627_checked

  · exact kid14_part633_checked

  · exact kid14_part639_checked

  · exact kid14_part645_checked

  · exact kid14_part628_checked

  · exact kid14_part634_checked

  · exact kid14_part640_checked

  · exact kid14_part646_checked

  · exact kid14_part629_checked

  · exact kid14_part635_checked

  · exact kid14_part641_checked

  · exact kid14_part647_checked

def kid14_part648 : Audit := .split 10 (5,true) (byMove [
.cycle 1 15 true (-1),
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
.cycle 1 15 true (-1),
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
.cycle 1 15 true (-1),
.cycle 19 1 false (-1),
.last 18 (4,true),
.last 14 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.cycle 1 17 true (0),
.cycle 1 13 true (0),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 15 1 false (-1),
.last 15 (4,true),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.last 16 (4,true),
.cycle 14 1 false (0),
.last 14 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
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
.cycle 18 1 false (0),
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
.cycle 12 4 true (0),
.cycle 19 1 false (-1),
.cycle 1 13 true (0),
.cycle 16 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.cycle 10 2 true (0),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 12 (4,true),
.last 13 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 9 2 true (0)
])
theorem kid14_part648_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part648) = true := by rfl

def kid14_part649 : Audit := .cycle 6 4 true (1)
theorem kid14_part649_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part649) = true := by rfl

def kid14_part650 : Audit := .cycle 1 13 true (1)
theorem kid14_part650_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part650) = true := by rfl

def kid14_part651 : Audit := .cycle 8 2 true (1)
theorem kid14_part651_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part651) = true := by rfl

def kid14_part652 : Audit := .cycle 1 11 true (1)
theorem kid14_part652_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part652) = true := by rfl

def kid14_part654 : Audit := .split 14 (5,true) (byMove [
.cycle 12 4 true (1),
.cycle 15 12 true (-2),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.cycle 0 20 true (0),
.last 18 (4,false),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 20 9 false (0),
.cycle 15 12 true (-2),
.cycle 21 7 false (2),
.cycle 5 10 true (1),
.cycle 17 5 false (2),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 17 (4,false)
])
theorem kid14_part654_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part654) = true := by rfl

def kid14_part655 : Audit := .cycle 0 14 true (0)
theorem kid14_part655_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part655) = true := by rfl

def kid14_part656 : Audit := .cycle 21 1 false (1)
theorem kid14_part656_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part656) = true := by rfl

def kid14_part657 : Audit := .split 16 (5,true) (byMove [
.cycle 13 4 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 1 17 true (0),
.cycle 0 20 true (0),
.cycle 1 22 true (0),
.cycle 0 18 true (0),
.cycle 1 20 true (0),
.last 19 (4,false),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.cycle 20 1 false (0),
.cycle 1 17 true (0),
.cycle 24 1 false (0),
.cycle 15 2 true (2),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.last 19 (4,false)
])
theorem kid14_part657_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part657) = true := by rfl

def kid14_part658 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 18 (5,true),
.cycle 17 1 false (-1),
.last 16 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.cycle 14 2 true (2),
.cycle 13 6 false (1),
.last 18 (5,true),
.cycle 12 8 true (-2),
.last 16 (5,true),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 14 2 true (2)
])
theorem kid14_part658_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part658) = true := by rfl

def kid14_part659 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (5,true),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.cycle 15 1 true (3),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid14_part659_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part659) = true := by rfl

def kid14_part660 : Audit := .cycle 1 11 true (1)
theorem kid14_part660_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part660) = true := by rfl

def kid14_part661 : Audit := .cycle 0 14 true (0)
theorem kid14_part661_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part661) = true := by rfl

def kid14_part662 : Audit := .cycle 39 1 false (7)
theorem kid14_part662_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part662) = true := by rfl

def kid14_part663 : Audit := .cycle 0 12 true (0)
theorem kid14_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part663) = true := by rfl

def kid14_part664 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 17 1 false (1),
.cycle 12 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 7 7 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part664) = true := by rfl

def kid14_part665 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 33 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (1),
.cycle 26 3 false (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid14_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part665) = true := by rfl

def kid14_part666 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 7 17 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 16 5 false (2),
.cycle 19 5 false (3),
.cycle 15 5 false (1),
.cycle 17 5 false (3),
.cycle 15 5 false (1),
.last 19 (4,false),
.cycle 15 5 false (0),
.cycle 13 3 false (1),
.cycle 18 5 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 12 4 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 17 5 false (1),
.last 19 (4,false)
])
theorem kid14_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part666) = true := by rfl

def kid14_part667 : Audit := .split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 1 39 true (-1),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.last 18 (4,false),
.last 16 (4,false),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (1),
.last 17 (4,false),
.cycle 15 8 false (1),
.cycle 22 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.last 18 (4,false),
.cycle 14 5 false (0),
.cycle 12 4 true (1),
.cycle 15 7 false (1),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.cycle 15 12 true (-2),
.last 17 (4,false)
])
theorem kid14_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part667) = true := by rfl

def kid14_part668 : Audit := .cycle 1 13 true (1)
theorem kid14_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part668) = true := by rfl

def kid14_part669 : Audit := .cycle 18 1 false (0)
theorem kid14_part669_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part669) = true := by rfl

def kid14_part670 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (5,true),
.cycle 13 6 false (1),
.last 23 (5,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 12 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.last 12 (5,true)
])
theorem kid14_part670_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part670) = true := by rfl

def kid14_part671 : Audit := .cycle 9 2 true (1)
theorem kid14_part671_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part671) = true := by rfl

def kid14_part672 : Audit := .cycle 1 11 true (1)
theorem kid14_part672_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part672) = true := by rfl

def kid14_part673 : Audit := .cycle 7 4 true (1)
theorem kid14_part673_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part673) = true := by rfl

def kid14_part674 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 15 (4,false),
.cycle 15 7 false (1),
.cycle 24 3 false (2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 15 (4,false)
])
theorem kid14_part674_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part674) = true := by rfl

def kid14_part675 : Audit := .cycle 0 12 true (0)
theorem kid14_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part675) = true := by rfl

def kid14_part676 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.last 16 (5,true),
.last 22 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part676) = true := by rfl

def kid14_part677 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 16 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 9 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid14_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part677) = true := by rfl

def kid14_part653 : Audit := .split 10 (4,true) (byMove [(kid14_part654),(kid14_part655),(kid14_part656),(kid14_part657),(kid14_part658),(kid14_part659),(kid14_part660),(kid14_part661),(kid14_part662),(kid14_part663),(kid14_part664),(kid14_part665),(kid14_part666),(kid14_part667),(kid14_part668),(kid14_part669),(kid14_part670),(kid14_part671),(kid14_part672),(kid14_part673),(kid14_part674),(kid14_part675),(kid14_part676),(kid14_part677)])

theorem kid14_part653_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part653) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid14_part654),(kid14_part655),(kid14_part656),(kid14_part657),(kid14_part658),(kid14_part659),(kid14_part660),(kid14_part661),(kid14_part662),(kid14_part663),(kid14_part664),(kid14_part665),(kid14_part666),(kid14_part667),(kid14_part668),(kid14_part669),(kid14_part670),(kid14_part671),(kid14_part672),(kid14_part673),(kid14_part674),(kid14_part675),(kid14_part676),(kid14_part677)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part654_checked

  · exact kid14_part660_checked

  · exact kid14_part666_checked

  · exact kid14_part672_checked

  · exact kid14_part655_checked

  · exact kid14_part661_checked

  · exact kid14_part667_checked

  · exact kid14_part673_checked

  · exact kid14_part656_checked

  · exact kid14_part662_checked

  · exact kid14_part668_checked

  · exact kid14_part674_checked

  · exact kid14_part657_checked

  · exact kid14_part663_checked

  · exact kid14_part669_checked

  · exact kid14_part675_checked

  · exact kid14_part658_checked

  · exact kid14_part664_checked

  · exact kid14_part670_checked

  · exact kid14_part676_checked

  · exact kid14_part659_checked

  · exact kid14_part665_checked

  · exact kid14_part671_checked

  · exact kid14_part677_checked

def kid14_part678 : Audit := .split 10 (5,true) (byMove [
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 12 (4,true),
.cycle 21 1 true (1),
.cycle 7 6 true (1),
.cycle 10 4 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.cycle 15 1 true (3),
.cycle 13 6 false (1),
.last 19 (4,true),
.cycle 12 8 true (-2),
.last 17 (4,true),
.last 12 (4,true),
.cycle 12 3 false (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 15 1 true (3)
]),
.cycle 14 1 true (2),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 39 1 false (7),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 32 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 7 6 true (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
]),
.cycle 12 1 true (4),
.cycle 14 5 false (0),
.cycle 21 3 false (1),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 4 true (-2),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 19 4 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 3 false (0),
.last 16 (4,true),
.cycle 14 5 false (0),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 9 2 true (1),
.cycle 1 11 true (1),
.cycle 7 4 true (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
]),
.cycle 12 1 true (4)
])
theorem kid14_part678_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part678) = true := by rfl

def kid14_part679 : Audit := .cycle 11 4 false (1)
theorem kid14_part679_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part679) = true := by rfl

def kid14_part680 : Audit := .split 19 (5,true) (byMove [
.cycle 21 4 true (-2),
.cycle 14 20 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.last 32 (4,true),
.cycle 12 13 false (2),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 16 5 false (0),
.cycle 14 8 false (2),
.cycle 17 4 true (-2),
.cycle 11 10 true (-2),
.cycle 21 1 false (-1),
.last 22 (4,true),
.cycle 16 5 false (0),
.cycle 14 8 false (2),
.cycle 17 4 false (0),
.cycle 14 10 false (2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 16 5 false (0),
.cycle 18 5 false (0),
.last 24 (4,true),
.last 30 (4,true),
.cycle 12 10 false (2),
.last 22 (4,true),
.cycle 9 12 false (2)
]),
.cycle 16 4 false (0),
.cycle 13 7 false (2),
.cycle 10 10 true (-1),
.cycle 15 5 false (1),
.cycle 12 8 true (-1),
.split 20 (4,true) (byMove [
.cycle 17 34 true (-1),
.cycle 1 35 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 16 5 false (0),
.cycle 13 8 true (-1),
.cycle 1 35 true (-1),
.cycle 15 6 true (-1),
.cycle 1 31 true (-1),
.last 24 (4,false),
.last 24 (4,false),
.cycle 14 8 false (2),
.cycle 17 4 true (-1),
.cycle 11 10 true (-1),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 16 5 false (0),
.cycle 18 37 true (-1),
.cycle 14 7 false (2),
.cycle 21 18 true (0),
.cycle 5 16 true (-1),
.last 24 (4,false),
.last 24 (4,false)
]),
.cycle 22 5 true (2),
.cycle 14 7 false (2),
.cycle 17 3 false (0),
.cycle 11 9 false (2),
.cycle 20 1 false (-2),
.split 20 (4,false) (byMove [
.last 25 (4,true),
.last 31 (4,true),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 16 5 false (0),
.cycle 13 8 false (2),
.cycle 10 11 false (2),
.cycle 15 6 false (1),
.cycle 12 9 false (2),
.last 21 (4,true),
.cycle 19 2 true (-2),
.cycle 14 8 false (2),
.cycle 17 4 false (0),
.cycle 11 10 false (2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 16 5 false (0),
.cycle 18 5 false (0),
.cycle 14 7 false (2),
.cycle 18 3 false (0),
.cycle 5 16 false (3),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 16 4 false (0),
.cycle 18 4 true (-1),
.cycle 14 6 false (2),
.cycle 18 2 true (-1),
.cycle 5 15 false (3),
.split 20 (4,true) (byMove [
.cycle 17 34 true (-1),
.cycle 14 11 false (2),
.cycle 15 6 false (1),
.cycle 14 9 false (2),
.last 22 (4,false),
.last 22 (4,false),
.cycle 6 15 false (3),
.cycle 1 35 true (-1),
.cycle 8 13 false (2),
.cycle 1 31 true (-1),
.last 24 (4,false),
.last 24 (4,false),
.cycle 13 8 false (2),
.cycle 10 11 false (2),
.cycle 15 6 false (1),
.cycle 12 9 false (2),
.last 22 (4,false),
.cycle 19 2 true (-1),
.cycle 18 29 true (-1),
.cycle 18 4 true (-1),
.cycle 18 24 true (-1),
.cycle 14 12 false (3),
.last 24 (4,false),
.last 24 (4,false)
]),
.cycle 20 7 true (0)
])
theorem kid14_part680_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part680) = true := by rfl

def kid14_part681 : Audit := .cycle 10 6 true (-2)
theorem kid14_part681_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part681) = true := by rfl

def kid14_part682 : Audit := .cycle 15 1 false (-1)
theorem kid14_part682_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part682) = true := by rfl

def kid14_part684 : Audit := .split 14 (5,true) (byMove [
.cycle 12 4 true (-1),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.last 24 (4,false),
.last 17 (4,false),
.cycle 6 9 false (3),
.last 22 (4,false),
.cycle 8 7 false (2),
.last 20 (4,false),
.cycle 12 26 true (0),
.last 19 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.cycle 10 5 false (1),
.last 17 (4,false),
.cycle 13 4 true (0),
.last 21 (4,false),
.cycle 13 2 true (0),
.cycle 12 10 true (-1),
.cycle 12 26 true (0),
.cycle 16 7 true (2)
])
theorem kid14_part684_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part684) = true := by rfl

def kid14_part685 : Audit := .split 18 (4,false) (byMove [
.last 22 (5,true),
.cycle 11 16 false (3),
.cycle 23 1 false (-3),
.cycle 25 1 false (-3),
.cycle 29 1 false (-3),
.last 19 (5,true),
.cycle 6 13 false (3),
.cycle 12 8 true (0),
.cycle 8 11 false (3),
.cycle 13 6 true (0),
.cycle 1 23 true (-1),
.last 19 (5,true),
.cycle 20 5 false (0),
.last 29 (5,true),
.cycle 19 7 false (-1),
.cycle 25 1 false (-3),
.cycle 10 9 false (3),
.last 19 (5,true),
.last 22 (5,true),
.last 21 (5,true),
.last 20 (5,true),
.cycle 5 28 false (3),
.cycle 20 9 false (0),
.last 19 (5,true)
])
theorem kid14_part685_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part685) = true := by rfl

def kid14_part686 : Audit := .cycle 12 1 false (0)
theorem kid14_part686_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part686) = true := by rfl

def kid14_part687 : Audit := .cycle 11 1 false (-1)
theorem kid14_part687_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part687) = true := by rfl

def kid14_part688 : Audit := .split 11 (4,false) (byMove [
.last 24 (5,true),
.cycle 18 16 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 13 5 false (1),
.last 14 (5,true),
.cycle 16 3 false (2),
.cycle 12 1 false (0),
.cycle 20 1 true (2),
.last 14 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 15 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 15 (5,true),
.last 14 (5,true),
.last 20 (5,true),
.cycle 5 14 false (3),
.cycle 38 1 true (-4),
.cycle 9 3 false (1)
])
theorem kid14_part688_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part688) = true := by rfl

def kid14_part689 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 17 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 16 (5,true),
.cycle 17 8 true (-2),
.cycle 11 3 false (-1),
.cycle 15 6 true (-2),
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
theorem kid14_part689_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part689) = true := by rfl

def kid14_part690 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.cycle 12 16 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.cycle 11 8 true (-1),
.cycle 13 3 false (1),
.cycle 11 6 true (-1),
.cycle 10 6 true (-1),
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
.cycle 5 11 false (3),
.cycle 6 11 false (3),
.last 16 (5,true)
])
theorem kid14_part690_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part690) = true := by rfl

def kid14_part691 : Audit := .split 18 (4,false) (byMove [
.last 22 (5,true),
.cycle 15 16 false (3),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 2 false (1),
.cycle 14 5 false (3),
.cycle 11 8 true (0),
.cycle 16 3 false (2),
.cycle 13 6 true (0),
.cycle 1 23 true (0),
.last 19 (5,true),
.cycle 15 5 false (3),
.last 21 (5,true),
.cycle 12 7 false (3),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 17 2 false (1),
.last 22 (5,true),
.cycle 15 4 false (3),
.last 20 (5,true),
.cycle 5 14 true (0),
.cycle 1 23 true (0),
.last 19 (5,true)
])
theorem kid14_part691_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part691) = true := by rfl

def kid14_part692 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.cycle 11 16 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
.cycle 11 3 false (1),
.cycle 11 6 true (-1),
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
theorem kid14_part692_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part692) = true := by rfl

def kid14_part693 : Audit := .split 16 (4,false) (byMove [
.last 20 (5,true),
.cycle 13 16 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.cycle 12 5 false (3),
.cycle 11 8 true (0),
.cycle 14 3 false (2),
.cycle 11 6 true (0),
.cycle 1 19 true (0),
.last 17 (5,true),
.cycle 13 5 false (3),
.last 19 (5,true),
.cycle 11 7 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 2 false (1),
.last 20 (5,true),
.cycle 13 4 false (3),
.last 18 (5,true),
.cycle 5 12 true (0),
.cycle 1 19 true (0),
.last 17 (5,true)
])
theorem kid14_part693_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part693) = true := by rfl

def kid14_part694 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 21 16 false (5),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (4),
.cycle 14 2 false (4),
.cycle 0 15 true (0),
.cycle 19 8 true (4),
.cycle 16 1 false (6),
.cycle 15 1 false (5),
.cycle 14 1 true (4),
.last 17 (5,true),
.cycle 14 5 false (4),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (4),
.cycle 14 2 false (4),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.last 25 (5,true),
.cycle 1 17 true (0),
.cycle 14 1 true (4),
.cycle 12 4 true (2)
])
theorem kid14_part694_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part694) = true := by rfl

def kid14_part695 : Audit := .split 11 (5,true) (byMove [
.cycle 13 4 true (0),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
.last 14 (4,false),
.cycle 1 13 true (0),
.last 14 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.cycle 11 3 false (1),
.last 18 (4,false),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 11 4 true (1),
.last 15 (4,false),
.cycle 11 2 true (1),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 13 3 true (3)
])
theorem kid14_part695_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part695) = true := by rfl

def kid14_part696 : Audit := .split 15 (4,false) (byMove [
.last 19 (5,true),
.cycle 11 16 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 5 false (0),
.cycle 12 8 true (-3),
.cycle 13 3 false (-1),
.cycle 12 6 true (-3),
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
.cycle 5 11 false (3),
.cycle 12 6 false (0),
.last 16 (5,true)
])
theorem kid14_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part696) = true := by rfl

def kid14_part697 : Audit := .split 13 (5,true) (byMove [
.cycle 15 4 true (-2),
.last 21 (4,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.cycle 10 4 true (-1),
.last 19 (4,false),
.last 18 (4,false),
.cycle 11 3 false (0),
.last 20 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 4 true (-1),
.last 17 (4,false),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.last 22 (4,false),
.cycle 12 9 true (-1)
])
theorem kid14_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part697) = true := by rfl

def kid14_part698 : Audit := .split 17 (4,false) (byMove [
.last 21 (5,true),
.cycle 14 16 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.cycle 11 8 true (-1),
.cycle 15 3 false (1),
.cycle 12 6 true (-1),
.cycle 10 8 true (-1),
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
.cycle 5 13 false (3),
.cycle 15 4 false (1),
.last 18 (5,true)
])
theorem kid14_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part698) = true := by rfl

def kid14_part699 : Audit := .cycle 11 1 false (-1)
theorem kid14_part699_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part699) = true := by rfl

def kid14_part700 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,true),
.cycle 11 16 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
.cycle 11 3 false (0),
.cycle 11 6 true (-1),
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
theorem kid14_part700_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part700) = true := by rfl

def kid14_part701 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,true),
.cycle 11 16 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.cycle 11 8 true (-2),
.cycle 11 3 false (-1),
.cycle 11 6 true (-2),
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
theorem kid14_part701_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part701) = true := by rfl

def kid14_part702 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.last 22 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.cycle 1 21 true (0),
.last 19 (4,false),
.last 19 (4,false),
.cycle 13 3 false (1),
.last 21 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 11 4 true (0),
.last 18 (4,false),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 1 21 true (0),
.cycle 1 20 true (0)
])
theorem kid14_part702_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part702) = true := by rfl

def kid14_part703 : Audit := .split 14 (4,false) (byMove [
.last 18 (5,true),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 11 6 true (-2),
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
.cycle 5 10 false (3),
.last 18 (5,true),
.last 15 (5,true)
])
theorem kid14_part703_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part703) = true := by rfl

def kid14_part704 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.last 20 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.last 28 (4,false),
.last 17 (4,false),
.last 17 (4,false),
.cycle 11 3 false (1),
.last 19 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 11 4 true (0),
.last 16 (4,false),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 2 18 true (0),
.cycle 14 5 true (2)
])
theorem kid14_part704_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part704) = true := by rfl

def kid14_part705 : Audit := .cycle 5 6 true (0)
theorem kid14_part705_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part705) = true := by rfl

def kid14_part706 : Audit := .split 14 (4,false) (byMove [
.cycle 1 15 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 13 2 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 19 8 true (4),
.cycle 10 15 true (0),
.cycle 3 12 true (0),
.cycle 14 1 true (4),
.last 17 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.cycle 12 3 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.cycle 14 1 true (4),
.cycle 12 4 true (2)
])
theorem kid14_part706_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part706) = true := by rfl

def kid14_part707 : Audit := .split 11 (5,true) (byMove [
.cycle 11 4 true (0),
.last 19 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 9 4 true (0),
.last 14 (4,false),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 14 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 11 4 true (1),
.last 18 (4,false),
.cycle 11 2 true (1),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 13 3 true (3)
])
theorem kid14_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part707) = true := by rfl

def kid14_part683 : Audit := .split 10 (4,true) (byMove [(kid14_part684),(kid14_part685),(kid14_part686),(kid14_part687),(kid14_part688),(kid14_part689),(kid14_part690),(kid14_part691),(kid14_part692),(kid14_part693),(kid14_part694),(kid14_part695),(kid14_part696),(kid14_part697),(kid14_part698),(kid14_part699),(kid14_part700),(kid14_part701),(kid14_part702),(kid14_part703),(kid14_part704),(kid14_part705),(kid14_part706),(kid14_part707)])

theorem kid14_part683_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part683) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part684),(kid14_part685),(kid14_part686),(kid14_part687),(kid14_part688),(kid14_part689),(kid14_part690),(kid14_part691),(kid14_part692),(kid14_part693),(kid14_part694),(kid14_part695),(kid14_part696),(kid14_part697),(kid14_part698),(kid14_part699),(kid14_part700),(kid14_part701),(kid14_part702),(kid14_part703),(kid14_part704),(kid14_part705),(kid14_part706),(kid14_part707)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part684_checked

  · exact kid14_part690_checked

  · exact kid14_part696_checked

  · exact kid14_part702_checked

  · exact kid14_part685_checked

  · exact kid14_part691_checked

  · exact kid14_part697_checked

  · exact kid14_part703_checked

  · exact kid14_part686_checked

  · exact kid14_part692_checked

  · exact kid14_part698_checked

  · exact kid14_part704_checked

  · exact kid14_part687_checked

  · exact kid14_part693_checked

  · exact kid14_part699_checked

  · exact kid14_part705_checked

  · exact kid14_part688_checked

  · exact kid14_part694_checked

  · exact kid14_part700_checked

  · exact kid14_part706_checked

  · exact kid14_part689_checked

  · exact kid14_part695_checked

  · exact kid14_part701_checked

  · exact kid14_part707_checked

def kid14_part708 : Audit := .split 10 (5,true) (byMove [
.cycle 12 4 true (-1),
.cycle 9 9 false (3),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 22 (4,true),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 17 1 false (1),
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
.cycle 9 9 false (3),
.cycle 17 1 false (-1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.split 11 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 14 1 false (4),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 17 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 1 false (0),
.cycle 1 17 true (0),
.cycle 14 1 false (0),
.cycle 25 1 false (3),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 12 3 true (2)
]),
.cycle 14 1 false (4),
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
.cycle 18 1 false (0),
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
.cycle 10 4 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 5 6 true (0),
.split 11 (4,true) (byMove [
.cycle 1 22 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 6 6 true (0),
.cycle 1 15 true (0),
.cycle 8 4 true (0),
.cycle 1 13 true (0),
.last 14 (4,false),
.last 19 (4,false),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 13 (4,false),
.cycle 10 2 true (0),
.cycle 1 17 true (0),
.cycle 10 4 true (0),
.cycle 2 16 true (0),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 12 3 true (2)
]),
.cycle 12 3 true (2)
])
theorem kid14_part708_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part708) = true := by rfl

def kid14_part709 : Audit := .split 13 (5,true) (byMove [
.cycle 12 4 true (0),
.cycle 1 39 true (-1),
.cycle 23 1 false (-1),
.cycle 23 1 false (-1),
.split 14 (4,true) (byMove [
.cycle 1 19 true (-1),
.last 28 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 22 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.last 15 (4,false),
.last 20 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.last 25 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 22 (4,false),
.last 19 (4,false),
.cycle 12 4 true (0),
.cycle 1 17 true (0),
.last 25 (4,false),
.last 15 (4,false),
.cycle 9 6 true (0)
]),
.cycle 1 27 true (-2),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.split 14 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 1 24 true (0),
.last 15 (4,false),
.cycle 11 6 true (1),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false),
.cycle 16 9 false (2),
.cycle 12 4 true (1),
.cycle 1 17 true (1),
.cycle 26 1 false (0),
.last 15 (4,false),
.cycle 9 6 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 0 17 true (0),
.cycle 15 8 false (1),
.cycle 23 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.last 26 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 20 (4,false),
.last 23 (4,false),
.last 26 (4,false),
.last 21 (4,false),
.last 24 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.last 18 (4,false),
.last 25 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 20 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.cycle 5 10 true (0),
.last 18 (4,false),
.cycle 13 2 true (0)
]),
.cycle 14 5 false (1),
.cycle 10 4 true (1),
.cycle 14 7 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.split 14 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 15 12 true (-2),
.cycle 0 24 true (-1),
.cycle 7 10 true (1),
.last 17 (4,false),
.last 16 (4,false),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false),
.cycle 15 9 false (2),
.cycle 15 12 true (-2),
.cycle 15 7 false (1),
.cycle 5 10 true (1),
.last 17 (4,false),
.cycle 13 2 true (1),
.cycle 1 15 true (1),
.cycle 11 4 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 0 17 true (0)
])
theorem kid14_part709_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part709) = true := by rfl

def kid14_part710 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 7 13 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 28 (4,true),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 28 (4,true),
.cycle 15 3 false (1),
.cycle 11 4 true (-1),
.cycle 17 3 false (3),
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
.cycle 7 13 false (3),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 9 5 false (2)
]),
.cycle 15 15 false (3),
.cycle 14 3 false (2),
.cycle 17 3 false (3),
.cycle 13 3 false (1),
.cycle 15 3 false (3),
.split 13 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 1 24 true (0),
.cycle 15 3 false (3),
.cycle 1 17 true (0),
.cycle 14 3 false (2),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 1 16 true (0),
.cycle 15 3 false (1),
.cycle 11 4 true (0),
.cycle 17 3 false (3),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 3 false (1),
.cycle 1 19 true (0),
.cycle 14 3 false (2),
.cycle 25 3 false (5),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 1 16 true (0)
]),
.cycle 1 16 true (0),
.cycle 14 3 false (0),
.cycle 11 3 false (1),
.cycle 16 3 false (2),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 18 (4,true),
.cycle 7 14 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
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
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 13 3 false (0),
.cycle 10 4 true (0),
.cycle 13 3 false (1),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.split 13 (4,true) (byMove [
.cycle 1 24 true (0),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
.last 15 (4,false),
.last 15 (4,false),
.cycle 6 8 true (0),
.cycle 1 17 true (0),
.cycle 8 6 true (0),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 1 16 true (0),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 14 3 false (0),
.cycle 16 3 false (2),
.last 15 (4,false),
.cycle 12 2 true (0),
.cycle 1 19 true (0),
.cycle 10 4 true (0),
.cycle 2 18 true (0),
.cycle 1 15 true (0),
.last 16 (4,false),
.cycle 1 16 true (0)
]),
.cycle 1 16 true (0)
])
theorem kid14_part710_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part710) = true := by rfl

def kid14_part711 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 1 17 true (-1),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 24 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.cycle 1 15 true (0),
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
.cycle 1 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 9 4 true (0)
]),
.cycle 1 45 true (-2),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 1 22 true (0),
.last 13 (4,false),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 53 1 false (7),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 15 7 false (1),
.cycle 10 4 true (1),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false)
]),
.cycle 2 13 true (1),
.cycle 13 6 false (1),
.cycle 19 3 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 10 5 false (2),
.last 22 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 22 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.last 16 (4,false),
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
.cycle 5 8 true (0),
.last 16 (4,false),
.cycle 11 2 true (0)
]),
.cycle 12 3 false (0),
.cycle 10 4 true (1),
.cycle 13 5 false (1),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 1 18 true (1),
.cycle 13 10 true (-2),
.cycle 13 5 false (1),
.cycle 7 8 true (1),
.last 15 (4,false),
.last 14 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 8 22 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 15 7 false (1),
.cycle 13 10 true (-2),
.cycle 13 5 false (1),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 10 4 true (1),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false)
]),
.cycle 2 13 true (1)
])
theorem kid14_part711_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part711) = true := by rfl

def kid14_part712 : Audit := .cycle 1 11 true (1)
theorem kid14_part712_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part712) = true := by rfl

def kid14_part714 : Audit := .split 14 (5,true) (byMove [
.cycle 11 4 true (1),
.cycle 15 12 true (-2),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.cycle 0 20 true (0),
.last 18 (4,false),
.cycle 1 15 true (1),
.cycle 0 18 true (0),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 20 9 false (0),
.cycle 15 12 true (-2),
.cycle 21 7 false (2),
.cycle 5 10 true (1),
.cycle 17 5 false (2),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 16 11 false (2),
.cycle 13 2 true (2),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 17 (4,false)
])
theorem kid14_part714_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part714) = true := by rfl

def kid14_part715 : Audit := .cycle 11 8 true (-2)
theorem kid14_part715_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part715) = true := by rfl

def kid14_part716 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 16, 64],[2, 15, 15, 1, 15, 15, 64],112⟩,
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 17 true (0),
.cycle 18 3 false (2),
.cycle 13 3 false (1),
.cycle 16 3 false (2),
.cycle 15 1 false (1),
.cycle 14 3 false (3),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 19 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 1 17 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 7 8 true (0),
.cycle 13 3 false (1),
.last 20 (4,false)
])
theorem kid14_part716_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part716) = true := by rfl

def kid14_part717 : Audit := .cycle 7 6 true (1)
theorem kid14_part717_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part717) = true := by rfl

def kid14_part718 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 0 18 true (-1),
.cycle 1 29 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 18 1 true (2),
.cycle 19 2 true (1),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.cycle 0 18 true (-1),
.cycle 1 13 false (3),
.cycle 11 11 false (1),
.cycle 0 20 true (-1),
.cycle 22 1 true (-2),
.cycle 22 2 true (-2)
])
theorem kid14_part718_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part718) = true := by rfl

def kid14_part719 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 23 11 false (3),
.cycle 17 1 false (-1),
.cycle 24 1 false (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 7 6 true (1),
.cycle 0 18 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 16 (4,false),
.cycle 13 6 false (1),
.cycle 27 3 false (1),
.cycle 12 8 true (-2),
.cycle 24 1 false (0),
.last 14 (4,false),
.cycle 12 3 false (0),
.cycle 13 4 true (1),
.cycle 16 11 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.last 16 (4,false)
])
theorem kid14_part719_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part719) = true := by rfl

def kid14_part720 : Audit := .cycle 1 11 true (1)
theorem kid14_part720_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part720) = true := by rfl

def kid14_part721 : Audit := .cycle 0 14 true (0)
theorem kid14_part721_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part721) = true := by rfl

def kid14_part722 : Audit := .cycle 8 16 true (1)
theorem kid14_part722_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part722) = true := by rfl

def kid14_part723 : Audit := .cycle 0 12 true (0)
theorem kid14_part723_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part723) = true := by rfl

def kid14_part724 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 16, 1024, 8192, 16384, 8, 128, 16, 65536, 8192, 16384, 8, 128, 262144, 65536, 262144],[128, 1, 16, 1, 16, 262144, 8192, 16, 262144, 1, 16, 262144, 8192, 262144, 262144, 1, 16, 262144, 262144],460800⟩,
.cycle 3 10 true (1),
.cycle 19 1 false (1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 4, 1024, 8192, 16384, 8, 128, 4, 65536, 8192, 16384, 8, 128, 4, 65536, 262144],[128, 1, 16, 1, 16, 262144, 8192, 16, 262144, 1, 16, 262144, 8192, 262144, 262144, 1, 16, 262144, 262144],262144⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 8, 1024, 8192, 16384, 8, 128, 8, 65536, 8192, 16384, 8, 128, 8, 65536, 262144],[128, 1, 16, 1, 16, 262144, 8192, 16, 262144, 1, 16, 262144, 8192, 262144, 262144, 1, 16, 262144, 262144],262144⟩,
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.cycle 7 7 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 16, 1024, 8192, 16384, 8, 128, 128, 65536, 8192, 16384, 8, 128, 128, 65536, 262144],[128, 1, 16, 1, 16, 262144, 8192, 16, 262144, 1, 16, 262144, 8192, 262144, 262144, 1, 16, 262144, 262144],262144⟩,
.cycle 30 1 false (6),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part724_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part724) = true := by rfl

def kid14_part725 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 17 10 false (1),
.cycle 15 12 true (-2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid14_part725_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part725) = true := by rfl

def kid14_part726 : Audit := .split 14 (5,true) (byMove [
.cycle 16 4 true (-1),
.cycle 6 17 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 15 5 false (2),
.cycle 18 5 false (3),
.cycle 15 5 false (1),
.cycle 16 5 false (3),
.cycle 17 5 false (1),
.last 19 (4,false),
.cycle 16 5 false (0),
.cycle 13 3 false (1),
.cycle 17 5 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (0),
.cycle 11 4 true (0),
.cycle 15 5 false (1),
.cycle 13 2 true (0),
.cycle 5 10 true (0),
.cycle 15 5 false (1),
.last 19 (4,false)
])
theorem kid14_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part726) = true := by rfl

def kid14_part727 : Audit := .cycle 11 8 true (-2)
theorem kid14_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part727) = true := by rfl

def kid14_part728 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (-1),
.cycle 8 13 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 15 3 false (1),
.cycle 18 3 false (2),
.cycle 13 3 false (1),
.cycle 16 3 false (2),
.cycle 18 3 false (2),
.last 17 (4,false),
.cycle 15 3 false (-1),
.cycle 11 3 false (1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 11 4 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 13 3 false (1),
.last 17 (4,false)
])
theorem kid14_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part728) = true := by rfl

def kid14_part729 : Audit := .cycle 5 6 true (1)
theorem kid14_part729_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part729) = true := by rfl

def kid14_part730 : Audit := .split 13 (4,false) (byMove [
.last 17 (5,true),
.cycle 11 20 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 16 (5,true),
.cycle 11 7 false (1),
.cycle 11 10 true (-1),
.cycle 11 5 false (1),
.cycle 11 8 true (-1),
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
theorem kid14_part730_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part730) = true := by rfl

def kid14_part731 : Audit := .split 11 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 16 (4,false),
.last 14 (4,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 9 4 true (1),
.last 15 (4,false),
.cycle 13 6 false (1),
.cycle 20 3 false (0),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 11 4 true (1),
.cycle 14 5 false (1),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 15 (4,false)
])
theorem kid14_part731_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part731) = true := by rfl

def kid14_part732 : Audit := .cycle 1 11 true (1)
theorem kid14_part732_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part732) = true := by rfl

def kid14_part733 : Audit := .split 13 (5,true) (byMove [
.cycle 12 4 true (0),
.cycle 1 39 true (-1),
.cycle 23 1 false (-1),
.cycle 23 1 false (-1),
.cycle 12 4 true (0),
.last 16 (4,false),
.cycle 6 8 true (1),
.cycle 1 17 true (1),
.cycle 8 6 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.last 17 (4,false),
.cycle 15 8 false (1),
.cycle 23 3 false (1),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.last 22 (4,false),
.cycle 14 5 false (1),
.cycle 11 4 true (1),
.cycle 14 7 false (2),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (1),
.last 17 (4,false)
])
theorem kid14_part733_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part733) = true := by rfl

def kid14_part734 : Audit := .split 12 (5,true) (byMove [
.cycle 11 4 true (1),
.cycle 13 10 true (-2),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.last 16 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 15 (4,false),
.cycle 18 7 false (0),
.cycle 13 10 true (-2),
.cycle 19 5 false (2),
.cycle 5 8 true (1),
.last 19 (4,false),
.cycle 13 5 false (1),
.cycle 1 13 true (1),
.cycle 14 9 false (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 15 (4,false)
])
theorem kid14_part734_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part734) = true := by rfl

def kid14_part735 : Audit := .cycle 0 12 true (0)
theorem kid14_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part735) = true := by rfl

def kid14_part736 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4),
.last 16 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 12 2 true (4)
])
theorem kid14_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part736) = true := by rfl

def kid14_part737 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 18 true (-1),
.last 20 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 16 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 17 10 false (1),
.cycle 13 3 false (1),
.cycle 14 10 true (-2),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 12 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid14_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part737) = true := by rfl

def kid14_part713 : Audit := .split 10 (4,true) (byMove [(kid14_part714),(kid14_part715),(kid14_part716),(kid14_part717),(kid14_part718),(kid14_part719),(kid14_part720),(kid14_part721),(kid14_part722),(kid14_part723),(kid14_part724),(kid14_part725),(kid14_part726),(kid14_part727),(kid14_part728),(kid14_part729),(kid14_part730),(kid14_part731),(kid14_part732),(kid14_part733),(kid14_part734),(kid14_part735),(kid14_part736),(kid14_part737)])

theorem kid14_part713_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part713) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid14_part714),(kid14_part715),(kid14_part716),(kid14_part717),(kid14_part718),(kid14_part719),(kid14_part720),(kid14_part721),(kid14_part722),(kid14_part723),(kid14_part724),(kid14_part725),(kid14_part726),(kid14_part727),(kid14_part728),(kid14_part729),(kid14_part730),(kid14_part731),(kid14_part732),(kid14_part733),(kid14_part734),(kid14_part735),(kid14_part736),(kid14_part737)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part714_checked

  · exact kid14_part720_checked

  · exact kid14_part726_checked

  · exact kid14_part732_checked

  · exact kid14_part715_checked

  · exact kid14_part721_checked

  · exact kid14_part727_checked

  · exact kid14_part733_checked

  · exact kid14_part716_checked

  · exact kid14_part722_checked

  · exact kid14_part728_checked

  · exact kid14_part734_checked

  · exact kid14_part717_checked

  · exact kid14_part723_checked

  · exact kid14_part729_checked

  · exact kid14_part735_checked

  · exact kid14_part718_checked

  · exact kid14_part724_checked

  · exact kid14_part730_checked

  · exact kid14_part736_checked

  · exact kid14_part719_checked

  · exact kid14_part725_checked

  · exact kid14_part731_checked

  · exact kid14_part737_checked

def kid14_part738 : Audit := .split 10 (5,true) (byMove [
.cycle 10 4 true (1),
.cycle 11 8 true (-2),
.cycle 14 1 false (0),
.cycle 7 6 true (1),
.split 11 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 18 11 false (2),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.last 13 (4,false),
.last 13 (4,false),
.cycle 7 6 true (1),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 15 1 true (3),
.cycle 13 6 false (1),
.last 23 (4,false),
.cycle 12 8 true (-2),
.cycle 18 1 false (0),
.last 13 (4,false),
.last 13 (4,false),
.last 21 (4,false),
.cycle 10 4 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.cycle 15 1 true (3)
]),
.cycle 22 1 true (-2),
.cycle 1 11 true (1),
.cycle 0 14 true (0),
.cycle 8 16 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (1),
.cycle 0 23 true (0),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 15 11 false (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
]),
.cycle 12 1 true (4),
.cycle 16 5 false (0),
.cycle 11 8 true (-2),
.cycle 17 3 false (1),
.cycle 5 6 true (1),
.split 11 (4,true) (byMove [
.cycle 13 5 false (2),
.cycle 1 33 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 13 (4,false),
.last 13 (4,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 14 (4,false),
.last 13 (4,false),
.cycle 13 6 false (1),
.last 24 (4,false),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 13 (4,false),
.last 13 (4,false),
.last 21 (4,false),
.last 15 (4,false),
.last 17 (4,false),
.cycle 1 13 true (1),
.last 14 (4,false),
.cycle 10 2 true (1)
]),
.cycle 11 3 false (1),
.cycle 1 11 true (1),
.cycle 13 7 false (2),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 5 false (2),
.last 21 (4,false),
.cycle 0 13 true (0),
.last 15 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 12 1 true (4),
.cycle 15 11 false (2),
.cycle 20 5 false (2),
.cycle 13 7 false (2),
.cycle 1 13 true (1),
.last 15 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 12 1 true (4)
]),
.cycle 12 1 true (4)
])
theorem kid14_part738_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part738) = true := by rfl

def kid14_part618 : Audit := .split 9 (5,false) (byMove [(kid14_part619),(kid14_part620),(kid14_part621),(kid14_part622),(kid14_part623),(kid14_part648),(kid14_part649),(kid14_part650),(kid14_part651),(kid14_part652),(kid14_part653),(kid14_part678),(kid14_part679),(kid14_part680),(kid14_part681),(kid14_part682),(kid14_part683),(kid14_part708),(kid14_part709),(kid14_part710),(kid14_part711),(kid14_part712),(kid14_part713),(kid14_part738)])

theorem kid14_part618_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (kid14_part618) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid14_part619),(kid14_part620),(kid14_part621),(kid14_part622),(kid14_part623),(kid14_part648),(kid14_part649),(kid14_part650),(kid14_part651),(kid14_part652),(kid14_part653),(kid14_part678),(kid14_part679),(kid14_part680),(kid14_part681),(kid14_part682),(kid14_part683),(kid14_part708),(kid14_part709),(kid14_part710),(kid14_part711),(kid14_part712),(kid14_part713),(kid14_part738)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part619_checked

  · exact kid14_part649_checked

  · exact kid14_part679_checked

  · exact kid14_part709_checked

  · exact kid14_part620_checked

  · exact kid14_part650_checked

  · exact kid14_part680_checked

  · exact kid14_part710_checked

  · exact kid14_part621_checked

  · exact kid14_part651_checked

  · exact kid14_part681_checked

  · exact kid14_part711_checked

  · exact kid14_part622_checked

  · exact kid14_part652_checked

  · exact kid14_part682_checked

  · exact kid14_part712_checked

  · exact kid14_part623_checked

  · exact kid14_part653_checked

  · exact kid14_part683_checked

  · exact kid14_part713_checked

  · exact kid14_part648_checked

  · exact kid14_part678_checked

  · exact kid14_part708_checked

  · exact kid14_part738_checked

def kid14_part739 : Audit := .cycle 1 9 true (1)
theorem kid14_part739_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,0⟩)) (kid14_part739) = true := by rfl

def kid14_part740 : Audit := .cycle 7 2 true (2)
theorem kid14_part740_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,1⟩)) (kid14_part740) = true := by rfl

def kid14_part741 : Audit := .cycle 2 8 true (1)
theorem kid14_part741_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,2⟩)) (kid14_part741) = true := by rfl

def kid14_part742 : Audit := .cycle 0 10 true (0)
theorem kid14_part742_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,3⟩)) (kid14_part742) = true := by rfl

def kid14_part744 : Audit := .cycle 1 10 true (1)
theorem kid14_part744_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part744) = true := by rfl

def kid14_part745 : Audit := .cycle 0 13 true (0)
theorem kid14_part745_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part745) = true := by rfl

def kid14_part746 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 21 7 false (1),
.cycle 13 18 true (-2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 25 1 false (1),
.split 12 (5,true) (byMove [
.cycle 14 5 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 7 15 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 28 1 false (2),
.last 14 (5,false),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (5,true),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 18 (5,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid14_part746_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part746) = true := by rfl

def kid14_part747 : Audit := .cycle 0 11 true (0)
theorem kid14_part747_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part747) = true := by rfl

def kid14_part748 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 11 2 true (0),
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
.last 19 (5,false),
.cycle 1 20 true (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,false),
.cycle 1 15 true (0),
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
.cycle 1 15 true (0),
.cycle 11 2 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.cycle 17 7 false (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
]),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 14 5 true (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 11 3 true (0),
.cycle 0 14 true (0),
.last 15 (5,false),
.last 14 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (0),
.last 18 (5,false),
.cycle 11 3 true (0),
.cycle 0 14 true (0),
.last 16 (5,false),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2),
.cycle 17 7 false (1),
.last 64 (5,true),
.cycle 15 5 false (1),
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (1),
.cycle 12 1 true (2)
])
])
theorem kid14_part748_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part748) = true := by rfl

def kid14_part750 : Audit := .cycle 0 11 true (0)
theorem kid14_part750_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part750) = true := by rfl

def kid14_part751 : Audit := .cycle 1 10 true (1)
theorem kid14_part751_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part751) = true := by rfl

def kid14_part752 : Audit := .cycle 21 1 false (1)
theorem kid14_part752_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part752) = true := by rfl

def kid14_part753 : Audit := .cycle 1 13 true (0)
theorem kid14_part753_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part753) = true := by rfl

def kid14_part754 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 11 2 true (0),
.cycle 0 13 true (0),
.last 13 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.last 12 (5,false),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.last 13 (5,false),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 12 (5,false)
])
theorem kid14_part754_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part754) = true := by rfl

def kid14_part755 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (1)
])
theorem kid14_part755_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part755) = true := by rfl

def kid14_part756 : Audit := .cycle 0 11 true (0)
theorem kid14_part756_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part756) = true := by rfl

def kid14_part757 : Audit := .cycle 1 10 true (1)
theorem kid14_part757_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part757) = true := by rfl

def kid14_part758 : Audit := .cycle 1 24 true (0)
theorem kid14_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part758) = true := by rfl

def kid14_part759 : Audit := .cycle 20 1 false (2)
theorem kid14_part759_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part759) = true := by rfl

def kid14_part760 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 15 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 13 true (3),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.last 12 (5,false),
.cycle 7 6 true (2),
.cycle 8 13 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 15 (5,false),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 12 (5,false)
])
theorem kid14_part760_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part760) = true := by rfl

def kid14_part761 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 15 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 30 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 18 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (3)
])
theorem kid14_part761_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part761) = true := by rfl

def kid14_part762 : Audit := .cycle 17 5 false (1)
theorem kid14_part762_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part762) = true := by rfl

def kid14_part763 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 1 21 true (-1),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.cycle 1 19 true (-1),
.cycle 11 16 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 15 true (2),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.last 14 (5,false),
.cycle 11 24 true (-2),
.cycle 11 11 true (-1),
.cycle 11 20 true (-2),
.cycle 1 15 true (1),
.cycle 11 9 true (-1),
.cycle 15 12 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid14_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part763) = true := by rfl

def kid14_part764 : Audit := .cycle 0 13 true (0)
theorem kid14_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part764) = true := by rfl

def kid14_part765 : Audit := .cycle 18 1 false (0)
theorem kid14_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part765) = true := by rfl

def kid14_part766 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 0 24 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 15 true (1),
.cycle 0 13 true (0),
.last 13 (5,false),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.last 26 (5,false),
.cycle 13 12 true (-2),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 1 12 true (1),
.last 17 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 15 (5,false),
.last 18 (5,false)
])
theorem kid14_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part766) = true := by rfl

def kid14_part767 : Audit := .split 11 (5,false) (byMove [
.last 15 (4,false),
.cycle 0 24 true (-1),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 14 (4,false),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 19 6 false (1),
.last 21 (4,false),
.cycle 19 1 false (-1),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 14 3 false (0),
.cycle 13 3 false (1)
])
theorem kid14_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part767) = true := by rfl

def kid14_part768 : Audit := .cycle 0 11 true (0)
theorem kid14_part768_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part768) = true := by rfl

def kid14_part769 : Audit := .cycle 1 10 true (1)
theorem kid14_part769_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part769) = true := by rfl

def kid14_part770 : Audit := .cycle 2 9 true (1)
theorem kid14_part770_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part770) = true := by rfl

def kid14_part771 : Audit := .cycle 1 13 true (1)
theorem kid14_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part771) = true := by rfl

def kid14_part772 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (2),
.cycle 0 13 true (0),
.last 13 (5,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 12 (5,false)
])
theorem kid14_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part772) = true := by rfl

def kid14_part773 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 16 (4,false),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 16 (4,false),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (3)
])
theorem kid14_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part773) = true := by rfl

def kid14_part749 : Audit := .split 10 (5,true) (byMove [(kid14_part750),(kid14_part751),(kid14_part752),(kid14_part753),(kid14_part754),(kid14_part755),(kid14_part756),(kid14_part757),(kid14_part758),(kid14_part759),(kid14_part760),(kid14_part761),(kid14_part762),(kid14_part763),(kid14_part764),(kid14_part765),(kid14_part766),(kid14_part767),(kid14_part768),(kid14_part769),(kid14_part770),(kid14_part771),(kid14_part772),(kid14_part773)])

theorem kid14_part749_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part749) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part750),(kid14_part751),(kid14_part752),(kid14_part753),(kid14_part754),(kid14_part755),(kid14_part756),(kid14_part757),(kid14_part758),(kid14_part759),(kid14_part760),(kid14_part761),(kid14_part762),(kid14_part763),(kid14_part764),(kid14_part765),(kid14_part766),(kid14_part767),(kid14_part768),(kid14_part769),(kid14_part770),(kid14_part771),(kid14_part772),(kid14_part773)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part750_checked

  · exact kid14_part756_checked

  · exact kid14_part762_checked

  · exact kid14_part768_checked

  · exact kid14_part751_checked

  · exact kid14_part757_checked

  · exact kid14_part763_checked

  · exact kid14_part769_checked

  · exact kid14_part752_checked

  · exact kid14_part758_checked

  · exact kid14_part764_checked

  · exact kid14_part770_checked

  · exact kid14_part753_checked

  · exact kid14_part759_checked

  · exact kid14_part765_checked

  · exact kid14_part771_checked

  · exact kid14_part754_checked

  · exact kid14_part760_checked

  · exact kid14_part766_checked

  · exact kid14_part772_checked

  · exact kid14_part755_checked

  · exact kid14_part761_checked

  · exact kid14_part767_checked

  · exact kid14_part773_checked

def kid14_part774 : Audit := .cycle 0 10 true (0)
theorem kid14_part774_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part774) = true := by rfl

def kid14_part775 : Audit := .cycle 1 9 true (1)
theorem kid14_part775_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part775) = true := by rfl

def kid14_part776 : Audit := .split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.cycle 8 24 true (2),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 25 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 8 24 true (2),
.cycle 11 11 true (2),
.last 23 (5,false),
.last 22 (5,false),
.cycle 7 16 true (2),
.cycle 16 10 true (3),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 25 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 20 2 true (5),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 20 2 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 8 24 true (2),
.cycle 11 11 true (2),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 7 16 true (2),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
]),
.cycle 6 15 true (2),
.cycle 1 24 true (1),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.cycle 18 3 true (4),
.split 21 (5,true) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 12 11 true (2),
.cycle 7 24 true (2),
.last 25 (5,false),
.last 22 (5,false),
.cycle 1 22 true (1),
.cycle 0 25 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 17 17 true (3),
.last 23 (5,false),
.cycle 16 7 true (3),
.cycle 8 15 true (2),
.cycle 1 24 true (1),
.cycle 13 9 true (2),
.last 25 (5,false),
.last 22 (5,false),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 9 13 true (2),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6),
.split 21 (5,false) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 9 13 true (2),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (2),
.cycle 3 19 true (1),
.cycle 20 2 true (6),
.cycle 21 1 true (7),
.cycle 6 16 true (2),
.cycle 16 6 true (3),
.cycle 8 14 true (2),
.cycle 1 23 true (1),
.cycle 18 4 true (4),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 20 2 true (6),
.cycle 21 1 true (7)
])
])
theorem kid14_part776_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part776) = true := by rfl

def kid14_part777 : Audit := .cycle 3 7 true (1)
theorem kid14_part777_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part777) = true := by rfl

def kid14_part778 : Audit := .split 10 (4,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 17 1 false (1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 16 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 1, 1024, 1, 16, 4096, 128, 16, 1024, 1, 16, 4096, 4096],5120⟩,
.cycle 3 9 true (1),
.cycle 10 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 20 2 false (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 11 1 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 4, 64, 64],[2, 17, 16, 1, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 8, 64, 64],[2, 17, 16, 1, 16, 64, 64],96⟩,
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 32, 51, 64],[2, 17, 16, 1, 16, 64, 64],64⟩,
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 32, 4, 64],[2, 17, 16, 1, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 32, 8, 64],[2, 17, 16, 1, 16, 64, 64],64⟩,
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 32, 19, 64],[2, 17, 16, 1, 16, 64, 64],64⟩,
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
]),
.cycle 7 5 true (2),
.cycle 9 8 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 26 1 false (6),
.split 11 (5,false) (byMove [
.last 16 (5,true),
.cycle 7 9 true (1),
.last 14 (5,true),
.cycle 7 7 true (2),
.last 16 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 13 7 true (2),
.cycle 5 9 true (1),
.cycle 1 19 true (1),
.cycle 5 7 true (1),
.last 20 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
])
theorem kid14_part778_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part778) = true := by rfl

def kid14_part780 : Audit := .cycle 0 11 true (0)
theorem kid14_part780_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part780) = true := by rfl

def kid14_part781 : Audit := .cycle 1 10 true (1)
theorem kid14_part781_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part781) = true := by rfl

def kid14_part782 : Audit := .cycle 2 9 true (1)
theorem kid14_part782_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part782) = true := by rfl

def kid14_part783 : Audit := .cycle 1 13 true (1)
theorem kid14_part783_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part783) = true := by rfl

def kid14_part784 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (2),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (3)
])
theorem kid14_part784_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part784) = true := by rfl

def kid14_part785 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,false),
.cycle 12 9 true (0),
.last 13 (4,false),
.cycle 17 1 false (1),
.cycle 21 7 false (2),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 11 2 true (2)
])
theorem kid14_part785_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part785) = true := by rfl

def kid14_part786 : Audit := .cycle 0 11 true (0)
theorem kid14_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part786) = true := by rfl

def kid14_part787 : Audit := .cycle 1 10 true (1)
theorem kid14_part787_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part787) = true := by rfl

def kid14_part788 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.last 27 (4,false),
.last 22 (4,false),
.cycle 0 25 true (0),
.cycle 1 22 true (1),
.cycle 0 25 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 1073741824, 4, 128, 256, 32768, 128, 1073741824, 16384, 128, 256, 2097152, 131072, 1073741824, 1048576, 128, 256, 134217728, 4194304, 1073741824, 67108864, 128, 256, 2097152, 536870912, 1073741824, 1048576, 1073741824],[128, 1, 1024, 1, 32, 16, 128, 131072, 1024, 4096, 131072, 65536, 128, 262144, 1024, 262144, 8388608, 4194304, 128, 16777216, 1024, 16777216, 536870912, 268435456, 128, 262144, 1024, 262144, 8388608, 4194304, 1073741824],1424051216⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 4, 64],[2, 33, 16, 1, 32, 32, 64],80⟩,
.cycle 7 21 true (2),
.cycle 8 15 true (2),
.cycle 1 24 true (1),
.cycle 4 25 true (1),
.last 22 (4,false),
.cycle 8 15 true (2),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 9 13 true (2),
.cycle 22 11 true (6)
])
theorem kid14_part788_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part788) = true := by rfl

def kid14_part789 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 3 18 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (4,false),
.cycle 11 9 true (2),
.last 20 (4,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 8, 64],[2, 33, 16, 1, 32, 32, 64],80⟩,
.cycle 7 14 true (2),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 20 (4,false),
.cycle 3 18 true (1)
])
theorem kid14_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part789) = true := by rfl

def kid14_part790 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 22 1 false (2),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.last 18 (5,true),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 15 (5,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part790) = true := by rfl

def kid14_part791 : Audit := .cycle 10 1 true (4)
theorem kid14_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part791) = true := by rfl

def kid14_part792 : Audit := .cycle 7 5 true (2)
theorem kid14_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part792) = true := by rfl

def kid14_part793 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.cycle 9 5 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 10 4 true (3),
.cycle 6 8 true (2),
.last 17 (5,true),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 18 (5,true)
])
theorem kid14_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part793) = true := by rfl

def kid14_part794 : Audit := .cycle 0 13 true (0)
theorem kid14_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part794) = true := by rfl

def kid14_part795 : Audit := .cycle 4 7 true (1)
theorem kid14_part795_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part795) = true := by rfl

def kid14_part796 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (1),
.cycle 11 2 true (2),
.cycle 7 7 true (2),
.cycle 18 1 false (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.last 16 (5,true),
.cycle 5 9 true (1),
.last 14 (5,true),
.cycle 5 7 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true)
])
theorem kid14_part796_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part796) = true := by rfl

def kid14_part797 : Audit := .split 12 (5,true) (byMove [
.cycle 14 7 true (2),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.cycle 1 30 true (0),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 26 1 false (6),
.cycle 14 17 true (1),
.last 19 (4,false),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.last 13 (4,false),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 15 (4,false),
.cycle 13 3 true (3)
])
theorem kid14_part797_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part797) = true := by rfl

def kid14_part798 : Audit := .cycle 0 11 true (0)
theorem kid14_part798_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part798) = true := by rfl

def kid14_part799 : Audit := .cycle 1 10 true (1)
theorem kid14_part799_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part799) = true := by rfl

def kid14_part800 : Audit := .cycle 2 9 true (1)
theorem kid14_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part800) = true := by rfl

def kid14_part801 : Audit := .cycle 1 13 true (1)
theorem kid14_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part801) = true := by rfl

def kid14_part802 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part802) = true := by rfl

def kid14_part803 : Audit := .cycle 10 1 true (4)
theorem kid14_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part803) = true := by rfl

def kid14_part779 : Audit := .split 10 (5,false) (byMove [(kid14_part780),(kid14_part781),(kid14_part782),(kid14_part783),(kid14_part784),(kid14_part785),(kid14_part786),(kid14_part787),(kid14_part788),(kid14_part789),(kid14_part790),(kid14_part791),(kid14_part792),(kid14_part793),(kid14_part794),(kid14_part795),(kid14_part796),(kid14_part797),(kid14_part798),(kid14_part799),(kid14_part800),(kid14_part801),(kid14_part802),(kid14_part803)])

theorem kid14_part779_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part779) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part780),(kid14_part781),(kid14_part782),(kid14_part783),(kid14_part784),(kid14_part785),(kid14_part786),(kid14_part787),(kid14_part788),(kid14_part789),(kid14_part790),(kid14_part791),(kid14_part792),(kid14_part793),(kid14_part794),(kid14_part795),(kid14_part796),(kid14_part797),(kid14_part798),(kid14_part799),(kid14_part800),(kid14_part801),(kid14_part802),(kid14_part803)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part780_checked

  · exact kid14_part786_checked

  · exact kid14_part792_checked

  · exact kid14_part798_checked

  · exact kid14_part781_checked

  · exact kid14_part787_checked

  · exact kid14_part793_checked

  · exact kid14_part799_checked

  · exact kid14_part782_checked

  · exact kid14_part788_checked

  · exact kid14_part794_checked

  · exact kid14_part800_checked

  · exact kid14_part783_checked

  · exact kid14_part789_checked

  · exact kid14_part795_checked

  · exact kid14_part801_checked

  · exact kid14_part784_checked

  · exact kid14_part790_checked

  · exact kid14_part796_checked

  · exact kid14_part802_checked

  · exact kid14_part785_checked

  · exact kid14_part791_checked

  · exact kid14_part797_checked

  · exact kid14_part803_checked

def kid14_part804 : Audit := .cycle 6 4 true (2)
theorem kid14_part804_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part804) = true := by rfl

def kid14_part805 : Audit := .cycle 1 13 true (1)
theorem kid14_part805_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part805) = true := by rfl

def kid14_part806 : Audit := .cycle 8 2 true (2)
theorem kid14_part806_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part806) = true := by rfl

def kid14_part807 : Audit := .cycle 1 11 true (1)
theorem kid14_part807_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part807) = true := by rfl

def kid14_part808 : Audit := .split 11 (4,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 28 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 20 (5,false),
.cycle 1 15 true (0),
.last 21 (5,false),
.cycle 11 2 true (0),
.last 13 (5,false)
]),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.split 12 (5,true) (byMove [
.last 17 (5,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 19 (5,false),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 17 (5,false),
.last 14 (5,false),
.cycle 17 7 false (1),
.cycle 16 7 false (2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 11 2 true (1),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 9 4 true (1),
.last 14 (5,false)
]),
.cycle 13 6 false (1),
.cycle 18 6 false (2),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.split 12 (5,true) (byMove [
.last 21 (5,false),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 22 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.cycle 5 8 true (0),
.last 16 (5,false),
.last 16 (5,false)
]),
.cycle 16 7 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.split 12 (5,true) (byMove [
.last 17 (5,false),
.cycle 13 10 true (-2),
.last 18 (5,false),
.cycle 7 8 true (1),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 15 (5,false),
.cycle 0 14 true (0),
.last 17 (5,false),
.last 14 (5,false),
.cycle 17 7 false (1),
.cycle 13 10 true (-2),
.cycle 15 5 false (1),
.cycle 5 8 true (1),
.cycle 14 3 false (0),
.last 15 (5,false),
.cycle 1 13 true (1),
.cycle 16 7 false (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 14 5 false (2),
.last 14 (5,false)
])
])
theorem kid14_part808_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part808) = true := by rfl

def kid14_part810 : Audit := .split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 12 8 true (1),
.cycle 13 2 true (3),
.cycle 0 16 true (0),
.cycle 12 6 true (1),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 19 true (2),
.cycle 3 12 true (1),
.cycle 14 1 true (4),
.last 15 (5,false),
.cycle 12 9 true (2),
.cycle 12 13 true (1),
.cycle 12 7 true (2),
.cycle 1 16 true (1),
.cycle 12 11 true (1),
.cycle 12 5 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (4),
.last 15 (5,false)
])
theorem kid14_part810_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part810) = true := by rfl

def kid14_part811 : Audit := .cycle 0 14 true (0)
theorem kid14_part811_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part811) = true := by rfl

def kid14_part812 : Audit := .cycle 21 1 false (1)
theorem kid14_part812_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part812) = true := by rfl

def kid14_part813 : Audit := .split 16 (4,false) (byMove [
.cycle 1 17 true (0),
.cycle 27 1 false (1),
.cycle 15 2 true (3),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 0 44 true (0),
.cycle 7 29 true (0),
.cycle 3 14 true (0),
.cycle 16 1 true (4),
.last 17 (5,false),
.cycle 7 17 true (0),
.cycle 27 1 false (1),
.cycle 7 15 true (0),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.cycle 7 13 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 16 1 true (4),
.last 17 (5,false)
])
theorem kid14_part813_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part813) = true := by rfl

def kid14_part814 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 24 (5,false),
.cycle 11 2 true (0),
.cycle 0 18 true (0),
.last 13 (5,false),
.last 14 (5,false),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (5,false),
.last 12 (5,false),
.cycle 13 6 false (1),
.last 24 (5,false),
.cycle 12 8 true (-2),
.cycle 1 18 true (0),
.last 13 (5,false),
.last 14 (5,false),
.last 26 (5,false),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 22 (5,false),
.last 12 (5,false)
])
theorem kid14_part814_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part814) = true := by rfl

def kid14_part815 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.last 18 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 7 6 true (1),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 14 1 true (2),
.cycle 13 6 false (1),
.last 18 (4,false),
.cycle 12 8 true (-2),
.last 16 (4,false),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 24 true (-1),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.cycle 17 1 true (-1)
])
theorem kid14_part815_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part815) = true := by rfl

def kid14_part816 : Audit := .cycle 1 11 true (1)
theorem kid14_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part816) = true := by rfl

def kid14_part817 : Audit := .cycle 0 14 true (0)
theorem kid14_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part817) = true := by rfl

def kid14_part818 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 39 1 false (7),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid14_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part818) = true := by rfl

def kid14_part819 : Audit := .cycle 0 12 true (0)
theorem kid14_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part819) = true := by rfl

def kid14_part820 : Audit := .split 12 (5,false) (byMove [
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (4,false),
.last 13 (4,false),
.last 15 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (4,false),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 1 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 14 (4,false)
])
theorem kid14_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part820) = true := by rfl

def kid14_part821 : Audit := .split 12 (5,false) (byMove [
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
.cycle 7 7 true (2),
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 13 (4,false),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part821) = true := by rfl

def kid14_part822 : Audit := .cycle 17 5 false (1)
theorem kid14_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part822) = true := by rfl

def kid14_part823 : Audit := .cycle 15 12 true (-2)
theorem kid14_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part823) = true := by rfl

def kid14_part824 : Audit := .cycle 1 13 true (1)
theorem kid14_part824_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part824) = true := by rfl

def kid14_part825 : Audit := .cycle 18 1 false (0)
theorem kid14_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part825) = true := by rfl

def kid14_part826 : Audit := .split 11 (4,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.last 26 (5,false),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 13 (5,false),
.last 14 (5,false),
.last 26 (5,false),
.last 17 (5,false),
.last 22 (5,false),
.cycle 1 13 true (1),
.last 15 (5,false),
.last 18 (5,false)
])
theorem kid14_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part826) = true := by rfl

def kid14_part827 : Audit := .split 11 (5,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 11 2 true (1),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 19 6 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 14 3 false (0),
.cycle 13 3 false (1)
])
theorem kid14_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part827) = true := by rfl

def kid14_part828 : Audit := .cycle 1 11 true (1)
theorem kid14_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part828) = true := by rfl

def kid14_part829 : Audit := .cycle 7 4 true (2)
theorem kid14_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part829) = true := by rfl

def kid14_part830 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 8 9 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 8 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid14_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part830) = true := by rfl

def kid14_part831 : Audit := .cycle 0 12 true (0)
theorem kid14_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part831) = true := by rfl

def kid14_part832 : Audit := .cycle 9 2 true (2)
theorem kid14_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part832) = true := by rfl

def kid14_part833 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 10 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 10 5 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part833_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part833) = true := by rfl

def kid14_part809 : Audit := .split 10 (5,true) (byMove [(kid14_part810),(kid14_part811),(kid14_part812),(kid14_part813),(kid14_part814),(kid14_part815),(kid14_part816),(kid14_part817),(kid14_part818),(kid14_part819),(kid14_part820),(kid14_part821),(kid14_part822),(kid14_part823),(kid14_part824),(kid14_part825),(kid14_part826),(kid14_part827),(kid14_part828),(kid14_part829),(kid14_part830),(kid14_part831),(kid14_part832),(kid14_part833)])

theorem kid14_part809_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part809) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid14_part810),(kid14_part811),(kid14_part812),(kid14_part813),(kid14_part814),(kid14_part815),(kid14_part816),(kid14_part817),(kid14_part818),(kid14_part819),(kid14_part820),(kid14_part821),(kid14_part822),(kid14_part823),(kid14_part824),(kid14_part825),(kid14_part826),(kid14_part827),(kid14_part828),(kid14_part829),(kid14_part830),(kid14_part831),(kid14_part832),(kid14_part833)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part810_checked

  · exact kid14_part816_checked

  · exact kid14_part822_checked

  · exact kid14_part828_checked

  · exact kid14_part811_checked

  · exact kid14_part817_checked

  · exact kid14_part823_checked

  · exact kid14_part829_checked

  · exact kid14_part812_checked

  · exact kid14_part818_checked

  · exact kid14_part824_checked

  · exact kid14_part830_checked

  · exact kid14_part813_checked

  · exact kid14_part819_checked

  · exact kid14_part825_checked

  · exact kid14_part831_checked

  · exact kid14_part814_checked

  · exact kid14_part820_checked

  · exact kid14_part826_checked

  · exact kid14_part832_checked

  · exact kid14_part815_checked

  · exact kid14_part821_checked

  · exact kid14_part827_checked

  · exact kid14_part833_checked

def kid14_part834 : Audit := .cycle 0 10 true (0)
theorem kid14_part834_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part834) = true := by rfl

def kid14_part835 : Audit := .cycle 1 9 true (1)
theorem kid14_part835_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part835) = true := by rfl

def kid14_part836 : Audit := .cycle 2 8 true (1)
theorem kid14_part836_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part836) = true := by rfl

def kid14_part837 : Audit := .cycle 1 12 true (1)
theorem kid14_part837_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part837) = true := by rfl

def kid14_part838 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 10 2 true (3),
.cycle 0 12 true (0),
.cycle 9 2 true (3),
.split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (2),
.cycle 3 9 true (1),
.last 13 (5,false),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.last 12 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 11 true (3),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 14 true (3),
.cycle 9 11 true (3),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (5,true),
.last 13 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
]),
.cycle 6 5 true (2),
.cycle 9 5 true (2),
.cycle 8 3 true (2),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.split 11 (5,true) (byMove [
.cycle 10 5 true (2),
.cycle 7 9 true (1),
.cycle 37 1 false (1),
.cycle 7 7 true (2),
.last 18 (5,false),
.last 13 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 13 (5,false),
.cycle 9 7 true (2),
.cycle 5 9 true (1),
.cycle 9 5 true (2),
.cycle 5 7 true (1),
.cycle 9 5 true (2),
.last 13 (5,false),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 13 (5,false)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 9 6 true (3),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
])
theorem kid14_part838_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part838) = true := by rfl

def kid14_part840 : Audit := .cycle 1 11 true (1)
theorem kid14_part840_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid14_part840) = true := by rfl

def kid14_part841 : Audit := .cycle 7 4 true (2)
theorem kid14_part841_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid14_part841) = true := by rfl

def kid14_part842 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 16 (5,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (3)
])
theorem kid14_part842_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid14_part842) = true := by rfl

def kid14_part843 : Audit := .cycle 0 12 true (0)
theorem kid14_part843_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid14_part843) = true := by rfl

def kid14_part844 : Audit := .cycle 9 2 true (3)
theorem kid14_part844_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid14_part844) = true := by rfl

def kid14_part845 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 19 1 false (1),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 11 2 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 10 2 true (3)
])
theorem kid14_part845_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid14_part845) = true := by rfl

def kid14_part846 : Audit := .cycle 0 11 true (0)
theorem kid14_part846_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid14_part846) = true := by rfl

def kid14_part847 : Audit := .cycle 1 10 true (1)
theorem kid14_part847_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid14_part847) = true := by rfl

def kid14_part848 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 9 12 true (3),
.cycle 52 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.last 21 (4,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 4, 64],[2, 33, 16, 1, 32, 32, 64],80⟩,
.cycle 6 15 true (2),
.cycle 17 4 true (4),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.cycle 19 2 true (5),
.cycle 18 6 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 21 (4,false),
.cycle 10 11 true (3)
])
theorem kid14_part848_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid14_part848) = true := by rfl

def kid14_part849 : Audit := .cycle 3 8 true (1)
theorem kid14_part849_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid14_part849) = true := by rfl

def kid14_part850 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (5,true),
.last 20 (5,true),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.last 18 (5,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part850_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid14_part850) = true := by rfl

def kid14_part851 : Audit := .cycle 10 1 true (4)
theorem kid14_part851_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid14_part851) = true := by rfl

def kid14_part852 : Audit := .cycle 6 5 true (2)
theorem kid14_part852_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid14_part852) = true := by rfl

def kid14_part853 : Audit := .split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 9 6 true (2),
.cycle 1 21 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.last 15 (4,false),
.last 18 (4,false),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.cycle 8 7 true (2),
.cycle 1 16 true (1),
.cycle 13 2 true (3),
.cycle 25 8 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 10 5 true (2)
])
theorem kid14_part853_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid14_part853) = true := by rfl

def kid14_part854 : Audit := .cycle 8 3 true (2)
theorem kid14_part854_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid14_part854) = true := by rfl

def kid14_part855 : Audit := .cycle 1 12 true (1)
theorem kid14_part855_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid14_part855) = true := by rfl

def kid14_part856 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 9 4 true (3),
.last 20 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 6 7 true (2),
.cycle 11 4 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 20 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 10 3 true (3)
])
theorem kid14_part856_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid14_part856) = true := by rfl

def kid14_part857 : Audit := .split 11 (5,true) (byMove [
.last 15 (4,false),
.cycle 7 9 true (1),
.last 13 (4,false),
.cycle 7 7 true (2),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 33 1 false (7),
.cycle 6 11 true (2),
.cycle 5 9 true (1),
.cycle 8 7 true (2),
.cycle 5 7 true (1),
.cycle 11 2 true (2),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (4,false),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.cycle 10 3 true (3)
])
theorem kid14_part857_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid14_part857) = true := by rfl

def kid14_part858 : Audit := .cycle 0 11 true (0)
theorem kid14_part858_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid14_part858) = true := by rfl

def kid14_part859 : Audit := .cycle 1 10 true (1)
theorem kid14_part859_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid14_part859) = true := by rfl

def kid14_part860 : Audit := .cycle 2 9 true (1)
theorem kid14_part860_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid14_part860) = true := by rfl

def kid14_part861 : Audit := .cycle 1 13 true (1)
theorem kid14_part861_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid14_part861) = true := by rfl

def kid14_part862 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.cycle 9 3 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.last 15 (5,true),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
])
theorem kid14_part862_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid14_part862) = true := by rfl

def kid14_part863 : Audit := .cycle 10 1 true (4)
theorem kid14_part863_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid14_part863) = true := by rfl

def kid14_part839 : Audit := .split 10 (5,false) (byMove [(kid14_part840),(kid14_part841),(kid14_part842),(kid14_part843),(kid14_part844),(kid14_part845),(kid14_part846),(kid14_part847),(kid14_part848),(kid14_part849),(kid14_part850),(kid14_part851),(kid14_part852),(kid14_part853),(kid14_part854),(kid14_part855),(kid14_part856),(kid14_part857),(kid14_part858),(kid14_part859),(kid14_part860),(kid14_part861),(kid14_part862),(kid14_part863)])

theorem kid14_part839_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part839) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid14_part840),(kid14_part841),(kid14_part842),(kid14_part843),(kid14_part844),(kid14_part845),(kid14_part846),(kid14_part847),(kid14_part848),(kid14_part849),(kid14_part850),(kid14_part851),(kid14_part852),(kid14_part853),(kid14_part854),(kid14_part855),(kid14_part856),(kid14_part857),(kid14_part858),(kid14_part859),(kid14_part860),(kid14_part861),(kid14_part862),(kid14_part863)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part840_checked

  · exact kid14_part846_checked

  · exact kid14_part852_checked

  · exact kid14_part858_checked

  · exact kid14_part841_checked

  · exact kid14_part847_checked

  · exact kid14_part853_checked

  · exact kid14_part859_checked

  · exact kid14_part842_checked

  · exact kid14_part848_checked

  · exact kid14_part854_checked

  · exact kid14_part860_checked

  · exact kid14_part843_checked

  · exact kid14_part849_checked

  · exact kid14_part855_checked

  · exact kid14_part861_checked

  · exact kid14_part844_checked

  · exact kid14_part850_checked

  · exact kid14_part856_checked

  · exact kid14_part862_checked

  · exact kid14_part845_checked

  · exact kid14_part851_checked

  · exact kid14_part857_checked

  · exact kid14_part863_checked

def kid14_part743 : Audit := .split 9 (4,true) (byMove [(kid14_part744),(kid14_part745),(kid14_part746),(kid14_part747),(kid14_part748),(kid14_part749),(kid14_part774),(kid14_part775),(kid14_part776),(kid14_part777),(kid14_part778),(kid14_part779),(kid14_part804),(kid14_part805),(kid14_part806),(kid14_part807),(kid14_part808),(kid14_part809),(kid14_part834),(kid14_part835),(kid14_part836),(kid14_part837),(kid14_part838),(kid14_part839)])

theorem kid14_part743_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (kid14_part743) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) 9 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid14_part744),(kid14_part745),(kid14_part746),(kid14_part747),(kid14_part748),(kid14_part749),(kid14_part774),(kid14_part775),(kid14_part776),(kid14_part777),(kid14_part778),(kid14_part779),(kid14_part804),(kid14_part805),(kid14_part806),(kid14_part807),(kid14_part808),(kid14_part809),(kid14_part834),(kid14_part835),(kid14_part836),(kid14_part837),(kid14_part838),(kid14_part839)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part744_checked

  · exact kid14_part774_checked

  · exact kid14_part804_checked

  · exact kid14_part834_checked

  · exact kid14_part745_checked

  · exact kid14_part775_checked

  · exact kid14_part805_checked

  · exact kid14_part835_checked

  · exact kid14_part746_checked

  · exact kid14_part776_checked

  · exact kid14_part806_checked

  · exact kid14_part836_checked

  · exact kid14_part747_checked

  · exact kid14_part777_checked

  · exact kid14_part807_checked

  · exact kid14_part837_checked

  · exact kid14_part748_checked

  · exact kid14_part778_checked

  · exact kid14_part808_checked

  · exact kid14_part838_checked

  · exact kid14_part749_checked

  · exact kid14_part779_checked

  · exact kid14_part809_checked

  · exact kid14_part839_checked

def kid14_part865 : Audit := .cycle 1 10 true (1)
theorem kid14_part865_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid14_part865) = true := by rfl

def kid14_part866 : Audit := .cycle 0 13 true (0)
theorem kid14_part866_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid14_part866) = true := by rfl

def kid14_part867 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 13 (4,false),
.last 14 (4,false),
.cycle 21 7 false (1),
.cycle 13 18 true (-2),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 11 2 true (2)
]),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 7 7 true (2),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 14 5 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 7 15 true (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 28 1 false (2),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 9 4 true (2)
]),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (2),
.last 18 (4,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid14_part867_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid14_part867) = true := by rfl

def kid14_part868 : Audit := .cycle 0 11 true (0)
theorem kid14_part868_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid14_part868) = true := by rfl

def kid14_part870 : Audit := .cycle 0 11 true (0)
theorem kid14_part870_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part870) = true := by rfl

def kid14_part871 : Audit := .cycle 1 10 true (1)
theorem kid14_part871_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part871) = true := by rfl

def kid14_part872 : Audit := .cycle 21 1 false (1)
theorem kid14_part872_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part872) = true := by rfl

def kid14_part873 : Audit := .cycle 1 13 true (0)
theorem kid14_part873_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part873) = true := by rfl

def kid14_part874 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.last 12 (5,false),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 12 (5,false)
])
theorem kid14_part874_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part874) = true := by rfl

def kid14_part875 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 11 2 true (0),
.cycle 0 13 true (0),
.last 14 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.last 14 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (1)
])
theorem kid14_part875_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part875) = true := by rfl

def kid14_part876 : Audit := .cycle 0 11 true (0)
theorem kid14_part876_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part876) = true := by rfl

def kid14_part877 : Audit := .cycle 1 10 true (1)
theorem kid14_part877_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part877) = true := by rfl

def kid14_part878 : Audit := .cycle 1 24 true (0)
theorem kid14_part878_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part878) = true := by rfl

def kid14_part879 : Audit := .cycle 20 1 false (2)
theorem kid14_part879_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part879) = true := by rfl

def kid14_part880 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 30 (5,false),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 12 (5,false)
])
theorem kid14_part880_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part880) = true := by rfl

def kid14_part881 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 13 true (3),
.cycle 1 24 true (0),
.last 12 (4,false),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 8 13 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 15 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (3)
])
theorem kid14_part881_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part881) = true := by rfl

def kid14_part882 : Audit := .cycle 17 5 false (1)
theorem kid14_part882_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part882) = true := by rfl

def kid14_part883 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 1 21 true (-1),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.cycle 11 16 true (-2),
.cycle 1 19 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 15 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 13 1 true (3),
.cycle 11 24 true (-2),
.cycle 11 11 true (-1),
.cycle 11 20 true (-2),
.cycle 1 15 true (1),
.cycle 15 12 true (-2),
.cycle 11 9 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 13 1 true (3)
])
theorem kid14_part883_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part883) = true := by rfl

def kid14_part884 : Audit := .cycle 0 13 true (0)
theorem kid14_part884_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part884) = true := by rfl

def kid14_part885 : Audit := .cycle 18 1 false (0)
theorem kid14_part885_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part885) = true := by rfl

def kid14_part886 : Audit := .split 11 (4,false) (byMove [
.last 15 (5,false),
.cycle 0 24 true (-1),
.last 13 (5,false),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 14 (5,false),
.cycle 13 6 false (1),
.cycle 19 6 false (1),
.last 21 (5,false),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid14_part886_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part886) = true := by rfl

def kid14_part887 : Audit := .split 11 (5,false) (byMove [
.cycle 1 16 true (0),
.cycle 0 24 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.last 14 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 15 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.last 13 (4,false),
.cycle 13 6 false (1),
.last 26 (4,false),
.cycle 13 12 true (-2),
.cycle 19 1 false (-1),
.last 14 (4,false),
.last 13 (4,false),
.cycle 1 12 true (1),
.last 17 (4,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 18 (4,false),
.last 15 (4,false)
])
theorem kid14_part887_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part887) = true := by rfl

def kid14_part888 : Audit := .cycle 0 11 true (0)
theorem kid14_part888_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part888) = true := by rfl

def kid14_part889 : Audit := .cycle 1 10 true (1)
theorem kid14_part889_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part889) = true := by rfl

def kid14_part890 : Audit := .cycle 2 9 true (1)
theorem kid14_part890_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part890) = true := by rfl

def kid14_part891 : Audit := .cycle 1 13 true (1)
theorem kid14_part891_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part891) = true := by rfl

def kid14_part892 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,false),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 12 (5,false)
])
theorem kid14_part892_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part892) = true := by rfl

def kid14_part893 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (2),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 9 4 true (2),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 11 1 true (3)
])
theorem kid14_part893_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part893) = true := by rfl

def kid14_part869 : Audit := .split 10 (4,true) (byMove [(kid14_part870),(kid14_part871),(kid14_part872),(kid14_part873),(kid14_part874),(kid14_part875),(kid14_part876),(kid14_part877),(kid14_part878),(kid14_part879),(kid14_part880),(kid14_part881),(kid14_part882),(kid14_part883),(kid14_part884),(kid14_part885),(kid14_part886),(kid14_part887),(kid14_part888),(kid14_part889),(kid14_part890),(kid14_part891),(kid14_part892),(kid14_part893)])

theorem kid14_part869_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid14_part869) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part870),(kid14_part871),(kid14_part872),(kid14_part873),(kid14_part874),(kid14_part875),(kid14_part876),(kid14_part877),(kid14_part878),(kid14_part879),(kid14_part880),(kid14_part881),(kid14_part882),(kid14_part883),(kid14_part884),(kid14_part885),(kid14_part886),(kid14_part887),(kid14_part888),(kid14_part889),(kid14_part890),(kid14_part891),(kid14_part892),(kid14_part893)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part870_checked

  · exact kid14_part876_checked

  · exact kid14_part882_checked

  · exact kid14_part888_checked

  · exact kid14_part871_checked

  · exact kid14_part877_checked

  · exact kid14_part883_checked

  · exact kid14_part889_checked

  · exact kid14_part872_checked

  · exact kid14_part878_checked

  · exact kid14_part884_checked

  · exact kid14_part890_checked

  · exact kid14_part873_checked

  · exact kid14_part879_checked

  · exact kid14_part885_checked

  · exact kid14_part891_checked

  · exact kid14_part874_checked

  · exact kid14_part880_checked

  · exact kid14_part886_checked

  · exact kid14_part892_checked

  · exact kid14_part875_checked

  · exact kid14_part881_checked

  · exact kid14_part887_checked

  · exact kid14_part893_checked

def kid14_part894 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 0 15 true (-1),
.cycle 11 2 true (0),
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
.last 19 (4,false),
.cycle 1 20 true (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (4,false),
.cycle 1 15 true (0),
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
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.cycle 17 7 false (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
]),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 1 15 true (-1),
.cycle 0 18 true (-2),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.cycle 14 5 true (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (0),
.cycle 0 16 true (0),
.cycle 11 3 true (0),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 15 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (0),
.last 18 (4,false),
.cycle 11 3 true (0),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 22 true (-2),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1),
.cycle 17 7 false (1),
.last 64 (4,true),
.cycle 15 5 false (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 14 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (1)
]),
.cycle 11 1 true (1)
])
theorem kid14_part894_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid14_part894) = true := by rfl

def kid14_part895 : Audit := .cycle 0 10 true (0)
theorem kid14_part895_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid14_part895) = true := by rfl

def kid14_part896 : Audit := .cycle 1 9 true (1)
theorem kid14_part896_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid14_part896) = true := by rfl

def kid14_part897 : Audit := .split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 22 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 8 24 true (2),
.cycle 11 11 true (2),
.last 22 (4,false),
.last 23 (4,false),
.cycle 7 16 true (2),
.cycle 16 10 true (3),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 22 (4,false),
.last 25 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 22 (4,false),
.cycle 20 2 true (5)
]),
.cycle 8 24 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.last 23 (4,true),
.cycle 20 2 true (6),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 8 24 true (2),
.cycle 11 11 true (2),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 7 16 true (2),
.cycle 19 4 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.cycle 1 24 true (1),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.split 21 (4,true) (byMove [
.cycle 23 5 true (5),
.cycle 0 25 true (0),
.cycle 12 11 true (2),
.cycle 7 24 true (2),
.last 22 (4,false),
.last 25 (4,false),
.cycle 1 22 true (1),
.cycle 0 25 true (0),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 17 17 true (3),
.cycle 16 7 true (3),
.cycle 8 15 true (2),
.cycle 1 24 true (1),
.cycle 13 9 true (2),
.last 22 (4,false),
.last 25 (4,false),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 9 13 true (2)
]),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.split 21 (4,false) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 9 13 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (2),
.cycle 3 19 true (1),
.cycle 21 1 true (7),
.cycle 20 2 true (6),
.cycle 6 16 true (2),
.cycle 16 6 true (3),
.cycle 8 14 true (2),
.cycle 1 23 true (1),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 21 1 true (7),
.cycle 20 2 true (6)
]),
.cycle 20 1 true (6)
])
theorem kid14_part897_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid14_part897) = true := by rfl

def kid14_part898 : Audit := .cycle 3 7 true (1)
theorem kid14_part898_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid14_part898) = true := by rfl

def kid14_part900 : Audit := .cycle 0 11 true (0)
theorem kid14_part900_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part900) = true := by rfl

def kid14_part901 : Audit := .cycle 1 10 true (1)
theorem kid14_part901_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part901) = true := by rfl

def kid14_part902 : Audit := .cycle 2 9 true (1)
theorem kid14_part902_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part902) = true := by rfl

def kid14_part903 : Audit := .cycle 1 13 true (1)
theorem kid14_part903_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part903) = true := by rfl

def kid14_part904 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (5,false),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.last 13 (5,false),
.cycle 21 7 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.last 13 (5,false)
])
theorem kid14_part904_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part904) = true := by rfl

def kid14_part905 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (3),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (3),
.cycle 11 1 true (3)
])
theorem kid14_part905_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part905) = true := by rfl

def kid14_part906 : Audit := .cycle 0 11 true (0)
theorem kid14_part906_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part906) = true := by rfl

def kid14_part907 : Audit := .cycle 1 10 true (1)
theorem kid14_part907_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part907) = true := by rfl

def kid14_part908 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.last 27 (5,false),
.cycle 0 25 true (0),
.last 22 (5,false),
.cycle 1 22 true (1),
.cycle 0 25 true (0),
.last 23 (5,false),
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 4, 64, 64],[2, 17, 32, 1, 16, 16, 64],96⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 128, 256, 2097152, 65536, 1048576, 1073741824, 128, 256, 134217728, 8388608, 67108864, 1073741824, 128, 256, 2097152, 268435456, 1048576, 1073741824, 1073741824],[128, 1, 2048, 1, 32, 16, 128, 65536, 2048, 4096, 131072, 65536, 128, 262144, 2048, 262144, 8388608, 4194304, 128, 16777216, 2048, 16777216, 536870912, 268435456, 128, 262144, 2048, 262144, 8388608, 4194304, 1073741824],1692552224⟩,
.cycle 7 21 true (2),
.cycle 8 15 true (2),
.cycle 1 24 true (1),
.cycle 4 25 true (1),
.cycle 8 15 true (2),
.last 22 (5,false),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.cycle 9 13 true (2)
])
theorem kid14_part908_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part908) = true := by rfl

def kid14_part909 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (5,false),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 8, 64, 64],[2, 17, 32, 1, 16, 16, 64],96⟩,
.last 20 (5,false),
.cycle 7 14 true (2),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 22 true (0),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.last 20 (5,false)
])
theorem kid14_part909_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part909) = true := by rfl

def kid14_part910 : Audit := .cycle 10 1 true (4)
theorem kid14_part910_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part910) = true := by rfl

def kid14_part911 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 22 1 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.last 18 (4,true),
.cycle 0 14 true (0),
.last 19 (4,true),
.cycle 9 4 true (3),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part911_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part911) = true := by rfl

def kid14_part912 : Audit := .cycle 7 5 true (2)
theorem kid14_part912_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part912) = true := by rfl

def kid14_part913 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (4),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 9 5 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.cycle 3 11 true (1),
.cycle 10 4 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 17 (4,true),
.cycle 8 6 true (2),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 18 (4,true),
.cycle 13 1 true (5)
])
theorem kid14_part913_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part913) = true := by rfl

def kid14_part914 : Audit := .cycle 0 13 true (0)
theorem kid14_part914_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part914) = true := by rfl

def kid14_part915 : Audit := .cycle 4 7 true (1)
theorem kid14_part915_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part915) = true := by rfl

def kid14_part916 : Audit := .split 12 (4,true) (byMove [
.cycle 14 7 true (2),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.cycle 1 30 true (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 26 1 false (6),
.last 15 (5,false),
.cycle 14 17 true (1),
.last 19 (5,false),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.last 15 (5,false)
])
theorem kid14_part916_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part916) = true := by rfl

def kid14_part917 : Audit := .split 11 (5,false) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (1),
.cycle 11 2 true (2),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 18 1 false (0),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.last 16 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3)
])
theorem kid14_part917_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part917) = true := by rfl

def kid14_part918 : Audit := .cycle 0 11 true (0)
theorem kid14_part918_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part918) = true := by rfl

def kid14_part919 : Audit := .cycle 1 10 true (1)
theorem kid14_part919_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part919) = true := by rfl

def kid14_part920 : Audit := .cycle 2 9 true (1)
theorem kid14_part920_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part920) = true := by rfl

def kid14_part921 : Audit := .cycle 1 13 true (1)
theorem kid14_part921_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part921) = true := by rfl

def kid14_part922 : Audit := .cycle 10 1 true (4)
theorem kid14_part922_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part922) = true := by rfl

def kid14_part923 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part923_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part923) = true := by rfl

def kid14_part899 : Audit := .split 10 (4,false) (byMove [(kid14_part900),(kid14_part901),(kid14_part902),(kid14_part903),(kid14_part904),(kid14_part905),(kid14_part906),(kid14_part907),(kid14_part908),(kid14_part909),(kid14_part910),(kid14_part911),(kid14_part912),(kid14_part913),(kid14_part914),(kid14_part915),(kid14_part916),(kid14_part917),(kid14_part918),(kid14_part919),(kid14_part920),(kid14_part921),(kid14_part922),(kid14_part923)])

theorem kid14_part899_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid14_part899) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part900),(kid14_part901),(kid14_part902),(kid14_part903),(kid14_part904),(kid14_part905),(kid14_part906),(kid14_part907),(kid14_part908),(kid14_part909),(kid14_part910),(kid14_part911),(kid14_part912),(kid14_part913),(kid14_part914),(kid14_part915),(kid14_part916),(kid14_part917),(kid14_part918),(kid14_part919),(kid14_part920),(kid14_part921),(kid14_part922),(kid14_part923)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part900_checked

  · exact kid14_part906_checked

  · exact kid14_part912_checked

  · exact kid14_part918_checked

  · exact kid14_part901_checked

  · exact kid14_part907_checked

  · exact kid14_part913_checked

  · exact kid14_part919_checked

  · exact kid14_part902_checked

  · exact kid14_part908_checked

  · exact kid14_part914_checked

  · exact kid14_part920_checked

  · exact kid14_part903_checked

  · exact kid14_part909_checked

  · exact kid14_part915_checked

  · exact kid14_part921_checked

  · exact kid14_part904_checked

  · exact kid14_part910_checked

  · exact kid14_part916_checked

  · exact kid14_part922_checked

  · exact kid14_part905_checked

  · exact kid14_part911_checked

  · exact kid14_part917_checked

  · exact kid14_part923_checked

def kid14_part924 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4, 8, 128, 256, 8, 128, 4, 4096, 4096],[128, 1, 2048, 1, 4096, 32, 128, 32, 2048, 1, 4096, 32, 4096],6144⟩,
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 10 2 true (3),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 20 2 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 13 (4,true)
]),
.cycle 17 1 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 4, 64],[2, 33, 32, 1, 64, 32, 64],80⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 64, 8, 64],[2, 33, 32, 1, 64, 32, 64],80⟩,
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 51, 16, 64],[2, 33, 32, 1, 64, 32, 64],64⟩,
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 4, 16, 64],[2, 33, 32, 1, 64, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 8, 16, 64],[2, 33, 32, 1, 64, 32, 64],64⟩,
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 35, 16, 64],[2, 33, 32, 1, 64, 32, 64],64⟩,
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4),
.cycle 7 5 true (2),
.cycle 9 8 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 11 (4,false) (byMove [
.last 16 (4,true),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 16 (4,true),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 13 7 true (2),
.cycle 5 9 true (1),
.cycle 1 19 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 20 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3)
]),
.cycle 26 1 false (6),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4)
])
theorem kid14_part924_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid14_part924) = true := by rfl

def kid14_part925 : Audit := .cycle 6 4 true (2)
theorem kid14_part925_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid14_part925) = true := by rfl

def kid14_part926 : Audit := .cycle 1 13 true (1)
theorem kid14_part926_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid14_part926) = true := by rfl

def kid14_part927 : Audit := .cycle 8 2 true (2)
theorem kid14_part927_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid14_part927) = true := by rfl

def kid14_part928 : Audit := .cycle 1 11 true (1)
theorem kid14_part928_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid14_part928) = true := by rfl

def kid14_part930 : Audit := .split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 12 8 true (1),
.cycle 13 2 true (3),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 12 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 19 true (2),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 14 1 true (4),
.cycle 12 9 true (2),
.cycle 12 13 true (1),
.cycle 12 7 true (2),
.cycle 1 16 true (1),
.cycle 12 5 true (2),
.cycle 12 11 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 14 1 true (4)
])
theorem kid14_part930_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid14_part930) = true := by rfl

def kid14_part931 : Audit := .cycle 0 14 true (0)
theorem kid14_part931_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid14_part931) = true := by rfl

def kid14_part932 : Audit := .cycle 21 1 false (1)
theorem kid14_part932_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid14_part932) = true := by rfl

def kid14_part933 : Audit := .split 16 (5,false) (byMove [
.cycle 1 17 true (0),
.cycle 27 1 false (1),
.cycle 15 2 true (3),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.cycle 0 44 true (0),
.cycle 7 29 true (0),
.cycle 3 14 true (0),
.last 17 (4,false),
.cycle 16 1 true (4),
.cycle 7 17 true (0),
.cycle 27 1 false (1),
.cycle 7 15 true (0),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.cycle 25 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.last 17 (4,false),
.cycle 16 1 true (4)
])
theorem kid14_part933_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid14_part933) = true := by rfl

def kid14_part934 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 18 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 7 6 true (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.last 12 (5,false),
.cycle 13 6 false (1),
.last 18 (5,false),
.cycle 12 8 true (-2),
.last 16 (5,false),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 24 true (-1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.last 12 (5,false)
])
theorem kid14_part934_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid14_part934) = true := by rfl

def kid14_part935 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.last 24 (4,false),
.cycle 11 2 true (0),
.cycle 0 18 true (0),
.last 14 (4,false),
.last 13 (4,false),
.cycle 7 6 true (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 14 (4,false),
.cycle 13 6 false (1),
.last 24 (4,false),
.cycle 12 8 true (-2),
.cycle 1 18 true (0),
.last 14 (4,false),
.last 13 (4,false),
.last 26 (4,false),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 12 (4,false),
.last 22 (4,false)
])
theorem kid14_part935_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid14_part935) = true := by rfl

def kid14_part936 : Audit := .cycle 1 11 true (1)
theorem kid14_part936_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid14_part936) = true := by rfl

def kid14_part937 : Audit := .cycle 0 14 true (0)
theorem kid14_part937_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid14_part937) = true := by rfl

def kid14_part938 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 39 1 false (7),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part938_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid14_part938) = true := by rfl

def kid14_part939 : Audit := .cycle 0 12 true (0)
theorem kid14_part939_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid14_part939) = true := by rfl

def kid14_part940 : Audit := .split 12 (4,false) (byMove [
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
.cycle 7 7 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid14_part940_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid14_part940) = true := by rfl

def kid14_part941 : Audit := .split 12 (4,false) (byMove [
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (5,false),
.last 15 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 11 2 true (2),
.cycle 21 7 false (1),
.cycle 19 16 true (-2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 9 4 true (2)
])
theorem kid14_part941_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid14_part941) = true := by rfl

def kid14_part942 : Audit := .cycle 17 5 false (1)
theorem kid14_part942_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid14_part942) = true := by rfl

def kid14_part943 : Audit := .cycle 15 12 true (-2)
theorem kid14_part943_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid14_part943) = true := by rfl

def kid14_part944 : Audit := .cycle 1 13 true (1)
theorem kid14_part944_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid14_part944) = true := by rfl

def kid14_part945 : Audit := .cycle 18 1 false (0)
theorem kid14_part945_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid14_part945) = true := by rfl

def kid14_part946 : Audit := .split 11 (4,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.last 13 (5,false),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (1),
.cycle 19 6 false (1),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.cycle 14 3 false (0)
])
theorem kid14_part946_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid14_part946) = true := by rfl

def kid14_part947 : Audit := .split 11 (5,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.last 14 (4,false),
.last 13 (4,false),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 13 (4,false),
.cycle 13 6 false (1),
.last 26 (4,false),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 14 (4,false),
.last 13 (4,false),
.last 26 (4,false),
.last 17 (4,false),
.last 22 (4,false),
.cycle 1 13 true (1),
.last 18 (4,false),
.last 15 (4,false)
])
theorem kid14_part947_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid14_part947) = true := by rfl

def kid14_part948 : Audit := .cycle 1 11 true (1)
theorem kid14_part948_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid14_part948) = true := by rfl

def kid14_part949 : Audit := .cycle 7 4 true (2)
theorem kid14_part949_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid14_part949) = true := by rfl

def kid14_part950 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 8 9 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 8 7 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (4)
])
theorem kid14_part950_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid14_part950) = true := by rfl

def kid14_part951 : Audit := .cycle 0 12 true (0)
theorem kid14_part951_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid14_part951) = true := by rfl

def kid14_part952 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 10 7 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 10 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 13 (5,false)
])
theorem kid14_part952_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid14_part952) = true := by rfl

def kid14_part953 : Audit := .cycle 9 2 true (2)
theorem kid14_part953_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid14_part953) = true := by rfl

def kid14_part929 : Audit := .split 10 (4,true) (byMove [(kid14_part930),(kid14_part931),(kid14_part932),(kid14_part933),(kid14_part934),(kid14_part935),(kid14_part936),(kid14_part937),(kid14_part938),(kid14_part939),(kid14_part940),(kid14_part941),(kid14_part942),(kid14_part943),(kid14_part944),(kid14_part945),(kid14_part946),(kid14_part947),(kid14_part948),(kid14_part949),(kid14_part950),(kid14_part951),(kid14_part952),(kid14_part953)])

theorem kid14_part929_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid14_part929) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid14_part930),(kid14_part931),(kid14_part932),(kid14_part933),(kid14_part934),(kid14_part935),(kid14_part936),(kid14_part937),(kid14_part938),(kid14_part939),(kid14_part940),(kid14_part941),(kid14_part942),(kid14_part943),(kid14_part944),(kid14_part945),(kid14_part946),(kid14_part947),(kid14_part948),(kid14_part949),(kid14_part950),(kid14_part951),(kid14_part952),(kid14_part953)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part930_checked

  · exact kid14_part936_checked

  · exact kid14_part942_checked

  · exact kid14_part948_checked

  · exact kid14_part931_checked

  · exact kid14_part937_checked

  · exact kid14_part943_checked

  · exact kid14_part949_checked

  · exact kid14_part932_checked

  · exact kid14_part938_checked

  · exact kid14_part944_checked

  · exact kid14_part950_checked

  · exact kid14_part933_checked

  · exact kid14_part939_checked

  · exact kid14_part945_checked

  · exact kid14_part951_checked

  · exact kid14_part934_checked

  · exact kid14_part940_checked

  · exact kid14_part946_checked

  · exact kid14_part952_checked

  · exact kid14_part935_checked

  · exact kid14_part941_checked

  · exact kid14_part947_checked

  · exact kid14_part953_checked

def kid14_part954 : Audit := .split 11 (5,false) (byMove [
.cycle 13 8 false (3),
.cycle 1 33 true (-1),
.cycle 11 2 true (0),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.cycle 1 17 true (-1),
.last 24 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 28 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 20 (4,false),
.last 20 (4,false),
.cycle 1 15 true (0),
.last 21 (4,false),
.last 13 (4,false),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (-1),
.cycle 6 6 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.last 17 (4,false),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 19 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 17 7 false (1),
.cycle 16 7 false (2),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 11 2 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (1),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 9 4 true (1)
]),
.cycle 10 2 true (1),
.cycle 13 6 false (1),
.cycle 18 6 false (2),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.split 12 (4,true) (byMove [
.last 21 (4,false),
.last 22 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 22 (4,false),
.last 17 (4,false),
.last 20 (4,false),
.last 16 (4,false),
.last 15 (4,false),
.last 19 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 14 (4,false),
.last 20 (4,false),
.last 18 (4,false),
.last 18 (4,false),
.cycle 5 8 true (0),
.last 16 (4,false),
.last 16 (4,false)
]),
.cycle 13 1 false (-1),
.cycle 16 7 false (2),
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.last 17 (4,false),
.cycle 13 10 true (-2),
.last 18 (4,false),
.cycle 7 8 true (1),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 17 (4,false),
.cycle 17 7 false (1),
.cycle 13 10 true (-2),
.cycle 15 5 false (1),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 1 13 true (1),
.cycle 16 7 false (2),
.last 15 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 14 5 false (2)
]),
.cycle 13 3 false (1)
])
theorem kid14_part954_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid14_part954) = true := by rfl

def kid14_part955 : Audit := .cycle 0 10 true (0)
theorem kid14_part955_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid14_part955) = true := by rfl

def kid14_part956 : Audit := .cycle 1 9 true (1)
theorem kid14_part956_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid14_part956) = true := by rfl

def kid14_part957 : Audit := .cycle 2 8 true (1)
theorem kid14_part957_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid14_part957) = true := by rfl

def kid14_part958 : Audit := .cycle 1 12 true (1)
theorem kid14_part958_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid14_part958) = true := by rfl

def kid14_part960 : Audit := .cycle 1 11 true (1)
theorem kid14_part960_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid14_part960) = true := by rfl

def kid14_part961 : Audit := .cycle 7 4 true (2)
theorem kid14_part961_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid14_part961) = true := by rfl

def kid14_part962 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 16 (4,true),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.cycle 12 1 true (4)
])
theorem kid14_part962_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid14_part962) = true := by rfl

def kid14_part963 : Audit := .cycle 0 12 true (0)
theorem kid14_part963_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid14_part963) = true := by rfl

def kid14_part964 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.last 12 (5,false)
])
theorem kid14_part964_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid14_part964) = true := by rfl

def kid14_part965 : Audit := .cycle 9 2 true (3)
theorem kid14_part965_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid14_part965) = true := by rfl

def kid14_part966 : Audit := .cycle 0 11 true (0)
theorem kid14_part966_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid14_part966) = true := by rfl

def kid14_part967 : Audit := .cycle 1 10 true (1)
theorem kid14_part967_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid14_part967) = true := by rfl

def kid14_part968 : Audit := .split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 22 (5,false),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.cycle 9 12 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 19, 4, 64, 64],[2, 17, 32, 1, 16, 16, 64],96⟩,
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 17 4 true (4),
.cycle 8 13 true (2),
.cycle 1 22 true (1),
.cycle 18 6 true (3),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.last 21 (5,false)
])
theorem kid14_part968_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid14_part968) = true := by rfl

def kid14_part969 : Audit := .cycle 3 8 true (1)
theorem kid14_part969_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid14_part969) = true := by rfl

def kid14_part970 : Audit := .cycle 10 1 true (4)
theorem kid14_part970_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid14_part970) = true := by rfl

def kid14_part971 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (4,true),
.last 20 (4,true),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 7 6 true (2),
.last 18 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 4 true (3),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part971_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid14_part971) = true := by rfl

def kid14_part972 : Audit := .cycle 6 5 true (2)
theorem kid14_part972_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid14_part972) = true := by rfl

def kid14_part973 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 21 true (-1),
.cycle 9 6 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.last 18 (5,false),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.cycle 8 7 true (2),
.cycle 1 16 true (1),
.cycle 25 8 false (3),
.cycle 13 2 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 10 5 true (2),
.last 15 (5,false)
])
theorem kid14_part973_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid14_part973) = true := by rfl

def kid14_part974 : Audit := .cycle 8 3 true (2)
theorem kid14_part974_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid14_part974) = true := by rfl

def kid14_part975 : Audit := .cycle 1 12 true (1)
theorem kid14_part975_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid14_part975) = true := by rfl

def kid14_part976 : Audit := .split 11 (4,true) (byMove [
.last 15 (5,false),
.cycle 7 9 true (1),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.cycle 9 3 true (3),
.cycle 6 11 true (2),
.cycle 5 9 true (1),
.cycle 8 7 true (2),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.cycle 11 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 9 3 true (3)
])
theorem kid14_part976_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid14_part976) = true := by rfl

def kid14_part977 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 20 (5,false),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 10 true (3),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 4 true (2),
.cycle 8 5 true (2),
.cycle 1 14 true (1),
.last 20 (5,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (3),
.last 13 (5,false)
])
theorem kid14_part977_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid14_part977) = true := by rfl

def kid14_part978 : Audit := .cycle 0 11 true (0)
theorem kid14_part978_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid14_part978) = true := by rfl

def kid14_part979 : Audit := .cycle 1 10 true (1)
theorem kid14_part979_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid14_part979) = true := by rfl

def kid14_part980 : Audit := .cycle 2 9 true (1)
theorem kid14_part980_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid14_part980) = true := by rfl

def kid14_part981 : Audit := .cycle 1 13 true (1)
theorem kid14_part981_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid14_part981) = true := by rfl

def kid14_part982 : Audit := .cycle 10 1 true (4)
theorem kid14_part982_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid14_part982) = true := by rfl

def kid14_part983 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 11 2 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.last 15 (4,true),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (4),
.cycle 11 1 true (5)
])
theorem kid14_part983_checked : zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid14_part983) = true := by rfl

def kid14_part959 : Audit := .split 10 (4,false) (byMove [(kid14_part960),(kid14_part961),(kid14_part962),(kid14_part963),(kid14_part964),(kid14_part965),(kid14_part966),(kid14_part967),(kid14_part968),(kid14_part969),(kid14_part970),(kid14_part971),(kid14_part972),(kid14_part973),(kid14_part974),(kid14_part975),(kid14_part976),(kid14_part977),(kid14_part978),(kid14_part979),(kid14_part980),(kid14_part981),(kid14_part982),(kid14_part983)])

theorem kid14_part959_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid14_part959) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid14_part960),(kid14_part961),(kid14_part962),(kid14_part963),(kid14_part964),(kid14_part965),(kid14_part966),(kid14_part967),(kid14_part968),(kid14_part969),(kid14_part970),(kid14_part971),(kid14_part972),(kid14_part973),(kid14_part974),(kid14_part975),(kid14_part976),(kid14_part977),(kid14_part978),(kid14_part979),(kid14_part980),(kid14_part981),(kid14_part982),(kid14_part983)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part960_checked

  · exact kid14_part966_checked

  · exact kid14_part972_checked

  · exact kid14_part978_checked

  · exact kid14_part961_checked

  · exact kid14_part967_checked

  · exact kid14_part973_checked

  · exact kid14_part979_checked

  · exact kid14_part962_checked

  · exact kid14_part968_checked

  · exact kid14_part974_checked

  · exact kid14_part980_checked

  · exact kid14_part963_checked

  · exact kid14_part969_checked

  · exact kid14_part975_checked

  · exact kid14_part981_checked

  · exact kid14_part964_checked

  · exact kid14_part970_checked

  · exact kid14_part976_checked

  · exact kid14_part982_checked

  · exact kid14_part965_checked

  · exact kid14_part971_checked

  · exact kid14_part977_checked

  · exact kid14_part983_checked

def kid14_part984 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 10 2 true (3),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 18 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 10 2 true (3)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 9 11 true (3),
.cycle 3 8 true (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 14 true (3),
.cycle 9 11 true (3),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 7 6 true (2),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.cycle 9 5 true (2),
.cycle 8 3 true (2),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 10 5 true (2),
.cycle 7 9 true (1),
.cycle 37 1 false (1),
.cycle 7 7 true (2),
.last 13 (4,false),
.last 18 (4,false),
.cycle 1 12 true (1),
.cycle 0 15 true (0),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 9 3 true (3),
.cycle 9 7 true (2),
.cycle 5 9 true (1),
.cycle 9 5 true (2),
.cycle 5 7 true (1),
.last 13 (4,false),
.cycle 9 5 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 9 3 true (3)
]),
.cycle 9 3 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 10 3 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 9 3 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 12 true (3),
.cycle 3 9 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4),
.cycle 6 6 true (2),
.cycle 9 6 true (3),
.cycle 8 4 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 9 4 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (5),
.cycle 10 2 true (4)
]),
.cycle 10 1 true (4)
])
theorem kid14_part984_checked : zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid14_part984) = true := by rfl

def kid14_part864 : Audit := .split 9 (5,true) (byMove [(kid14_part865),(kid14_part866),(kid14_part867),(kid14_part868),(kid14_part869),(kid14_part894),(kid14_part895),(kid14_part896),(kid14_part897),(kid14_part898),(kid14_part899),(kid14_part924),(kid14_part925),(kid14_part926),(kid14_part927),(kid14_part928),(kid14_part929),(kid14_part954),(kid14_part955),(kid14_part956),(kid14_part957),(kid14_part958),(kid14_part959),(kid14_part984)])

theorem kid14_part864_checked : zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (kid14_part864) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) 9 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨true,false,2⟩) (2,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid14_part865),(kid14_part866),(kid14_part867),(kid14_part868),(kid14_part869),(kid14_part894),(kid14_part895),(kid14_part896),(kid14_part897),(kid14_part898),(kid14_part899),(kid14_part924),(kid14_part925),(kid14_part926),(kid14_part927),(kid14_part928),(kid14_part929),(kid14_part954),(kid14_part955),(kid14_part956),(kid14_part957),(kid14_part958),(kid14_part959),(kid14_part984)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part865_checked

  · exact kid14_part895_checked

  · exact kid14_part925_checked

  · exact kid14_part955_checked

  · exact kid14_part866_checked

  · exact kid14_part896_checked

  · exact kid14_part926_checked

  · exact kid14_part956_checked

  · exact kid14_part867_checked

  · exact kid14_part897_checked

  · exact kid14_part927_checked

  · exact kid14_part957_checked

  · exact kid14_part868_checked

  · exact kid14_part898_checked

  · exact kid14_part928_checked

  · exact kid14_part958_checked

  · exact kid14_part869_checked

  · exact kid14_part899_checked

  · exact kid14_part929_checked

  · exact kid14_part959_checked

  · exact kid14_part894_checked

  · exact kid14_part924_checked

  · exact kid14_part954_checked

  · exact kid14_part984_checked

def kid14 : Audit := .split 8 (2,true) (byMove [(kid14_part1),(kid14_part2),(kid14_part3),(kid14_part4),(kid14_part5),(kid14_part126),(kid14_part247),(kid14_part248),(kid14_part249),(kid14_part250),(kid14_part251),(kid14_part372),(kid14_part493),(kid14_part494),(kid14_part495),(kid14_part496),(kid14_part497),(kid14_part618),(kid14_part739),(kid14_part740),(kid14_part741),(kid14_part742),(kid14_part743),(kid14_part864)])

theorem check14 : zipCheck 175 (child39 ⟨true,false,2⟩) (kid14) = true := by

  change (zipQueryOK 175 (child39 ⟨true,false,2⟩) 8 (2,true) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨true,false,2⟩) (2,true) (some mv)) (byMove [(kid14_part1),(kid14_part2),(kid14_part3),(kid14_part4),(kid14_part5),(kid14_part126),(kid14_part247),(kid14_part248),(kid14_part249),(kid14_part250),(kid14_part251),(kid14_part372),(kid14_part493),(kid14_part494),(kid14_part495),(kid14_part496),(kid14_part497),(kid14_part618),(kid14_part739),(kid14_part740),(kid14_part741),(kid14_part742),(kid14_part743),(kid14_part864)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid14_part1_checked

  · exact kid14_part247_checked

  · exact kid14_part493_checked

  · exact kid14_part739_checked

  · exact kid14_part2_checked

  · exact kid14_part248_checked

  · exact kid14_part494_checked

  · exact kid14_part740_checked

  · exact kid14_part3_checked

  · exact kid14_part249_checked

  · exact kid14_part495_checked

  · exact kid14_part741_checked

  · exact kid14_part4_checked

  · exact kid14_part250_checked

  · exact kid14_part496_checked

  · exact kid14_part742_checked

  · exact kid14_part5_checked

  · exact kid14_part251_checked

  · exact kid14_part497_checked

  · exact kid14_part743_checked

  · exact kid14_part126_checked

  · exact kid14_part372_checked

  · exact kid14_part618_checked

  · exact kid14_part864_checked

end BB6.Agent11Raw39
