import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid05_part1 : Audit := .cycle 0 9 true (0)
theorem kid05_part1_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,0⟩)) (kid05_part1) = true := by rfl

def kid05_part2 : Audit := .cycle 1 8 true (1)
theorem kid05_part2_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,1⟩)) (kid05_part2) = true := by rfl

def kid05_part3 : Audit := .cycle 17 1 false (1)
theorem kid05_part3_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,2⟩)) (kid05_part3) = true := by rfl

def kid05_part4 : Audit := .cycle 19 1 false (1)
theorem kid05_part4_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,3⟩)) (kid05_part4) = true := by rfl

def kid05_part6 : Audit := .cycle 0 19 false (3)
theorem kid05_part6_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part6) = true := by rfl

def kid05_part7 : Audit := .split 10 (1,true) (byMove [
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
.cycle 14 9 false (-2),
.cycle 13 9 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.last 39 (4,true),
.cycle 11 1 false (-1),
.cycle 23 9 false (-1),
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
.last 16 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 9 false (-1),
.cycle 11 1 false (-1),
.cycle 13 9 false (2),
.cycle 10 2 true (-1),
.cycle 15 1 false (1),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 14 9 false (-2),
.cycle 13 9 false (-1),
.cycle 15 9 false (2),
.cycle 12 1 false (-2),
.cycle 1 33 false (3),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.cycle 13 9 false (-1),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 14 9 false (3),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 13 9 false (2),
.cycle 10 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 0 12 true (0),
.cycle 1 20 true (0),
.cycle 14 9 false (2),
.cycle 12 9 false (2),
.cycle 1 12 true (0),
.cycle 11 1 true (1),
.cycle 12 9 false (1),
.last 14 (4,true),
.cycle 19 9 false (1),
.cycle 14 9 false (3),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 22 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid05_part7_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part7) = true := by rfl

def kid05_part8 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 12 true (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 11 1 true (-1),
.split 13 (1,true) (byMove [
.cycle 24 1 false (-2),
.cycle 25 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 15 false (3),
.last 14 (4,true),
.cycle 17 1 false (-3),
.cycle 31 1 false (-3),
.cycle 32 1 false (-2),
.cycle 24 1 false (-2),
.cycle 22 1 false (-2),
.cycle 24 1 false (-2),
.cycle 11 3 true (-2),
.cycle 19 1 false (-3),
.cycle 20 1 false (-4),
.cycle 10 4 false (0),
.cycle 25 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-3),
.last 26 (4,true),
.cycle 27 1 false (-3),
.cycle 2 12 false (3),
.cycle 34 1 false (-2),
.cycle 19 1 false (-3),
.last 18 (4,true)
]),
.cycle 17 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.cycle 26 1 false (-2),
.cycle 1 11 false (3),
.cycle 21 1 false (-1),
.cycle 24 1 false (0),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid05_part8_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part8) = true := by rfl

def kid05_part9 : Audit := .cycle 0 11 true (0)
theorem kid05_part9_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part9) = true := by rfl

def kid05_part10 : Audit := .split 10 (4,true) (byMove [
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
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 24 1 false (-2),
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
.last 13 (1,true),
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
.split 12 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.cycle 9 13 false (3),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 9 5 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (5,false),
.cycle 22 1 false (0),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 10 17 false (4),
.cycle 26 1 false (-2),
.cycle 2 11 false (3),
.cycle 9 15 false (3),
.cycle 18 1 false (-2),
.last 13 (5,false)
]),
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
.last 12 (1,true),
.cycle 15 1 false (1),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 22 1 false (0),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 2 11 false (3),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 0 13 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 21 1 false (1),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 20 1 false (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 9 12 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 9 4 true (0),
.cycle 11 1 true (1),
.cycle 15 1 false (-1),
.last 12 (1,true),
.last 17 (1,true),
.cycle 21 1 false (1),
.cycle 10 4 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 9 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid05_part10_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part10) = true := by rfl

def kid05_part11 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 10 10 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 0 13 false (3),
.cycle 10 10 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 12 1 true (-2),
.split 14 (1,true) (byMove [
.cycle 10 12 false (0),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.cycle 0 16 false (3),
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 8 17 false (2),
.cycle 10 17 false (1),
.cycle 10 12 false (0),
.cycle 10 10 false (0),
.cycle 10 9 false (0),
.cycle 12 3 true (-3),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 13 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 26 (4,true),
.last 25 (4,true),
.cycle 2 13 false (3),
.cycle 10 19 false (1),
.last 17 (4,true),
.last 19 (4,true)
]),
.cycle 10 5 false (0),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.split 24 (4,true) (byMove [
.cycle 0 25 false (3),
.cycle 10 22 false (2),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 11 14 false (2),
.cycle 12 13 false (2),
.cycle 0 25 false (3),
.cycle 10 22 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 11 14 true (-2),
.cycle 12 13 true (-2),
.last 26 (1,true),
.cycle 10 17 false (2),
.cycle 0 27 false (3),
.cycle 25 1 false (-3),
.last 28 (1,true),
.cycle 2 25 false (3),
.cycle 13 12 true (-2),
.cycle 1 24 false (3),
.cycle 10 21 false (2),
.cycle 10 24 true (-2),
.cycle 9 16 false (2),
.cycle 12 13 true (-2)
]),
.cycle 1 12 false (3),
.cycle 10 9 false (0),
.cycle 10 12 true (-2),
.cycle 9 4 false (1),
.cycle 12 1 true (-2)
])
theorem kid05_part11_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part11) = true := by rfl

def kid05_part12 : Audit := .cycle 0 10 true (0)
theorem kid05_part12_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part12) = true := by rfl

def kid05_part13 : Audit := .cycle 1 9 true (1)
theorem kid05_part13_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part13) = true := by rfl

def kid05_part14 : Audit := .cycle 20 1 false (2)
theorem kid05_part14_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part14) = true := by rfl

def kid05_part15 : Audit := .cycle 17 1 false (1)
theorem kid05_part15_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part15) = true := by rfl

def kid05_part16 : Audit := .cycle 9 1 true (1)
theorem kid05_part16_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part16) = true := by rfl

def kid05_part17 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 9 2 true (1),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 9 2 true (1),
.cycle 10 1 true (2),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 9 4 true (1),
.cycle 10 3 true (1),
.last 16 (4,true),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.last 17 (4,true)
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
.last 16 (1,true),
.cycle 15 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 16 5 false (0),
.cycle 15 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 23 5 false (3),
.cycle 9 6 true (0),
.last 16 (1,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 8 4 true (1),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid05_part17_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part17) = true := by rfl

def kid05_part19 : Audit := .cycle 10 11 false (1)
theorem kid05_part19_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part19) = true := by rfl

def kid05_part20 : Audit := .cycle 10 12 false (1)
theorem kid05_part20_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part20) = true := by rfl

def kid05_part21 : Audit := .split 17 (5,false) (byMove [
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
.last 31 (4,true),
.cycle 1 17 false (3),
.cycle 10 12 false (1),
.cycle 10 15 false (1),
.cycle 9 9 false (1),
.cycle 17 1 true (-3)
])
theorem kid05_part21_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part21) = true := by rfl

def kid05_part22 : Audit := .cycle 0 17 false (3)
theorem kid05_part22_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part22) = true := by rfl

def kid05_part23 : Audit := .split 16 (4,true) (byMove [
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
.cycle 16 14 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.last 17 (5,false)
])
theorem kid05_part23_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part23) = true := by rfl

def kid05_part24 : Audit := .cycle 12 4 false (0)
theorem kid05_part24_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part24) = true := by rfl

def kid05_part25 : Audit := .cycle 6 20 false (3)
theorem kid05_part25_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part25) = true := by rfl

def kid05_part26 : Audit := .cycle 10 11 true (-2)
theorem kid05_part26_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part26) = true := by rfl

def kid05_part27 : Audit := .cycle 10 11 false (1)
theorem kid05_part27_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part27) = true := by rfl

def kid05_part28 : Audit := .cycle 10 9 false (1)
theorem kid05_part28_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part28) = true := by rfl

def kid05_part29 : Audit := .cycle 13 3 true (-2)
theorem kid05_part29_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part29) = true := by rfl

def kid05_part30 : Audit := .split 16 (5,false) (byMove [
.last 30 (4,true),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.cycle 12 6 false (0),
.cycle 0 17 true (-2),
.cycle 10 12 true (-2),
.cycle 10 27 true (-3),
.cycle 10 11 false (1),
.cycle 13 4 true (-2),
.cycle 16 1 true (0),
.cycle 14 3 true (-2),
.last 20 (4,true),
.cycle 0 19 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.cycle 12 6 false (0),
.last 30 (4,true),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 14 true (-2),
.cycle 6 12 false (3),
.cycle 16 1 true (0)
])
theorem kid05_part30_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part30) = true := by rfl

def kid05_part31 : Audit := .cycle 10 6 false (1)
theorem kid05_part31_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part31) = true := by rfl

def kid05_part32 : Audit := .cycle 11 7 false (1)
theorem kid05_part32_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part32) = true := by rfl

def kid05_part33 : Audit := .split 17 (5,false) (byMove [
.last 40 (4,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.cycle 0 20 true (-3),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 11 9 false (1),
.last 21 (4,true),
.last 49 (4,true),
.cycle 10 10 false (1),
.cycle 9 9 false (1),
.last 20 (4,true)
])
theorem kid05_part33_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part33) = true := by rfl

def kid05_part34 : Audit := .cycle 10 12 true (-2)
theorem kid05_part34_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part34) = true := by rfl

def kid05_part35 : Audit := .split 16 (4,true) (byMove [
.cycle 0 22 false (3),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 1, 64, 64],[19, 16, 32, 19, 2, 16, 64],96⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 10 12 true (-2),
.cycle 13 5 false (-1),
.last 18 (5,false),
.cycle 0 18 true (-2),
.cycle 13 5 true (-2),
.cycle 12 5 false (0),
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
.cycle 9 14 false (1),
.last 19 (5,false)
])
theorem kid05_part35_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part35) = true := by rfl

def kid05_part36 : Audit := .cycle 12 4 false (0)
theorem kid05_part36_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part36) = true := by rfl

def kid05_part37 : Audit := .split 29 (4,true) (byMove [
.cycle 10 25 false (3),
.cycle 10 40 false (3),
.last 31 (5,false),
.cycle 0 31 false (3),
.cycle 13 18 false (3),
.cycle 12 18 false (3),
.cycle 6 34 false (3),
.cycle 10 25 true (-2),
.cycle 3 45 false (3),
.cycle 10 23 false (3),
.cycle 13 17 true (-2),
.last 30 (5,false),
.cycle 10 20 false (3),
.cycle 2 30 false (3),
.last 31 (5,false),
.cycle 10 26 true (-2),
.cycle 26 8 false (1),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[16, 4096, 35184372088832, 32768, 4096, 281474976710656, 282592498945088, 282592498945088, 282592633163328, 134217728, 16777216, 281474976710656, 1099511627776, 16, 1099511627776, 35184372088832, 4398046511104, 281474976710656, 17179869184, 268436480, 17179869184, 134217728, 16777216, 281474976710656, 282592498945088, 282592498945088, 282592633163328, 512, 64, 281474976710656, 536872960, 8388608, 512, 2097152, 262144, 281474976710656, 131072, 8388608, 134217728, 2097152, 262144, 281474976710656, 131072, 268435456, 262144, 134217728, 16777216, 281474976710656, 281474976710656],[4096, 131072, 32, 4096, 131072, 16, 282592498945088, 282592498945088, 2048, 282592498945088, 536870912, 1024, 16, 16, 2199023255552, 1099511627776, 140737488355328, 1099511627776, 268436480, 17179869184, 34359738368, 281474976710656, 536870912, 17179869184, 282592498945088, 282592498945088, 536870912, 282592498945088, 2048, 268435456, 8388608, 8388608, 2048, 262144, 8388608, 1024, 8388608, 8388608, 536870912, 262144, 8388608, 268435456, 268435456, 131072, 536870912, 4096, 536870912, 268435456, 281474976710656],508219047480800⟩,
.cycle 16 14 true (-1),
.cycle 1 42 false (3),
.cycle 2 28 false (3),
.cycle 10 27 true (-2),
.cycle 9 26 false (3),
.last 30 (5,false)
])
theorem kid05_part37_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part37) = true := by rfl

def kid05_part38 : Audit := .split 28 (4,true) (byMove [
.cycle 0 29 false (3),
.cycle 10 24 false (2),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 13 16 false (2),
.last 29 (5,false),
.cycle 0 29 false (3),
.cycle 10 24 true (-2),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 13 16 true (-2),
.last 29 (5,false),
.cycle 14 15 false (2),
.cycle 11 19 false (2),
.cycle 0 31 false (3),
.cycle 29 1 false (-3),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 17, 32, 17, 16, 16, 64],96⟩,
.last 29 (5,false),
.cycle 16 14 true (-2),
.cycle 1 28 false (3),
.cycle 10 23 false (2),
.cycle 10 26 true (-2),
.cycle 9 20 false (2),
.last 29 (5,false)
])
theorem kid05_part38_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part38) = true := by rfl

def kid05_part39 : Audit := .cycle 2 14 false (3)
theorem kid05_part39_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part39) = true := by rfl

def kid05_part40 : Audit := .cycle 10 13 true (-2)
theorem kid05_part40_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part40) = true := by rfl

def kid05_part41 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 false (3),
.cycle 10 16 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 13 8 false (0),
.last 21 (5,false),
.cycle 0 21 false (3),
.cycle 10 16 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 13 8 true (-2),
.last 21 (5,false),
.cycle 14 7 false (0),
.cycle 11 11 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 20 6 false (-2),
.last 21 (5,false),
.cycle 16 14 true (-2),
.cycle 1 20 false (3),
.cycle 10 15 false (1),
.cycle 10 18 true (-2),
.cycle 9 12 false (1),
.last 21 (5,false)
])
theorem kid05_part41_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part41) = true := by rfl

def kid05_part42 : Audit := .split 16 (5,false) (byMove [
.cycle 2 16 false (3),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.last 17 (4,true),
.last 18 (4,true),
.last 34 (4,true),
.cycle 10 12 true (-2),
.cycle 3 16 false (3),
.cycle 3 14 false (3),
.cycle 13 4 true (-2),
.cycle 16 1 true (0),
.last 20 (4,true),
.last 19 (4,true),
.cycle 11 6 false (1),
.cycle 10 13 true (-2),
.last 17 (4,true),
.last 18 (4,true),
.last 30 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.cycle 10 14 true (-2),
.last 21 (4,true),
.cycle 16 1 true (0)
])
theorem kid05_part42_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part42) = true := by rfl

def kid05_part18 : Audit := .split 15 (1,true) (byMove [(kid05_part19),(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28),(kid05_part29),(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42)])

theorem kid05_part18_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part18) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part19),(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28),(kid05_part29),(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part19_checked

  · exact kid05_part25_checked

  · exact kid05_part31_checked

  · exact kid05_part37_checked

  · exact kid05_part20_checked

  · exact kid05_part26_checked

  · exact kid05_part32_checked

  · exact kid05_part38_checked

  · exact kid05_part21_checked

  · exact kid05_part27_checked

  · exact kid05_part33_checked

  · exact kid05_part39_checked

  · exact kid05_part22_checked

  · exact kid05_part28_checked

  · exact kid05_part34_checked

  · exact kid05_part40_checked

  · exact kid05_part23_checked

  · exact kid05_part29_checked

  · exact kid05_part35_checked

  · exact kid05_part41_checked

  · exact kid05_part24_checked

  · exact kid05_part30_checked

  · exact kid05_part36_checked

  · exact kid05_part42_checked

def kid05_part44 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 22 4 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 4 false (-2),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 22 4 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 4 false (0),
.last 16 (5,false),
.cycle 24 4 false (0),
.cycle 16 4 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 16 4 false (-2),
.last 16 (5,false),
.cycle 0 30 true (-1),
.cycle 1 15 false (3),
.cycle 21 4 false (1),
.cycle 24 4 false (2),
.cycle 9 7 false (1),
.last 16 (5,false)
])
theorem kid05_part44_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part44) = true := by rfl

def kid05_part45 : Audit := .cycle 0 14 true (-1)
theorem kid05_part45_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part45) = true := by rfl

def kid05_part46 : Audit := .cycle 12 1 false (0)
theorem kid05_part46_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part46) = true := by rfl

def kid05_part47 : Audit := .cycle 11 1 false (-1)
theorem kid05_part47_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part47) = true := by rfl

def kid05_part48 : Audit := .cycle 11 4 false (-1)
theorem kid05_part48_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part48) = true := by rfl

def kid05_part49 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 14 4 false (0),
.cycle 12 4 false (1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.cycle 13 4 false (1),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 16 4 false (0),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 15 4 false (1),
.cycle 9 3 false (1),
.last 14 (4,true)
])
theorem kid05_part49_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part49) = true := by rfl

def kid05_part50 : Audit := .cycle 17 4 false (3)
theorem kid05_part50_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part50) = true := by rfl

def kid05_part51 : Audit := .cycle 18 4 false (4)
theorem kid05_part51_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part51) = true := by rfl

def kid05_part52 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 12 1 true (0),
.cycle 21 4 false (1),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 21 4 false (3),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid05_part52_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part52) = true := by rfl

def kid05_part53 : Audit := .cycle 0 12 true (0)
theorem kid05_part53_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part53) = true := by rfl

def kid05_part54 : Audit := .split 11 (4,true) (byMove [
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
.cycle 11 7 false (2),
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
])
theorem kid05_part54_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part54) = true := by rfl

def kid05_part55 : Audit := .cycle 11 4 false (1)
theorem kid05_part55_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part55) = true := by rfl

def kid05_part56 : Audit := .cycle 14 4 false (0)
theorem kid05_part56_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part56) = true := by rfl

def kid05_part57 : Audit := .cycle 11 4 false (0)
theorem kid05_part57_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part57) = true := by rfl

def kid05_part58 : Audit := .cycle 19 4 false (3)
theorem kid05_part58_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part58) = true := by rfl

def kid05_part59 : Audit := .cycle 11 1 false (-1)
theorem kid05_part59_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part59) = true := by rfl

def kid05_part60 : Audit := .cycle 11 4 false (-1)
theorem kid05_part60_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part60) = true := by rfl

def kid05_part61 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 7 18 false (3),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 0 16 true (-1),
.cycle 19 4 false (3),
.last 12 (4,true),
.cycle 12 4 false (0),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.last 25 (4,true),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part61_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part61) = true := by rfl

def kid05_part62 : Audit := .cycle 2 10 true (0)
theorem kid05_part62_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part62) = true := by rfl

def kid05_part63 : Audit := .cycle 1 11 true (0)
theorem kid05_part63_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part63) = true := by rfl

def kid05_part64 : Audit := .cycle 11 4 false (1)
theorem kid05_part64_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part64) = true := by rfl

def kid05_part65 : Audit := .cycle 0 12 true (0)
theorem kid05_part65_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part65) = true := by rfl

def kid05_part66 : Audit := .split 11 (4,true) (byMove [
.cycle 18 4 false (2),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 31 4 false (3),
.cycle 18 4 false (2),
.cycle 16 4 false (2),
.cycle 17 4 false (1),
.last 12 (5,false),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 19 4 false (3),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 35 4 false (3),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid05_part66_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part66) = true := by rfl

def kid05_part67 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.last 13 (5,false),
.last 15 (5,false),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 21 4 false (3),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid05_part67_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part67) = true := by rfl

def kid05_part43 : Audit := .split 10 (1,true) (byMove [(kid05_part44),(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66),(kid05_part67)])

theorem kid05_part43_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part43) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part44),(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66),(kid05_part67)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part44_checked

  · exact kid05_part50_checked

  · exact kid05_part56_checked

  · exact kid05_part62_checked

  · exact kid05_part45_checked

  · exact kid05_part51_checked

  · exact kid05_part57_checked

  · exact kid05_part63_checked

  · exact kid05_part46_checked

  · exact kid05_part52_checked

  · exact kid05_part58_checked

  · exact kid05_part64_checked

  · exact kid05_part47_checked

  · exact kid05_part53_checked

  · exact kid05_part59_checked

  · exact kid05_part65_checked

  · exact kid05_part48_checked

  · exact kid05_part54_checked

  · exact kid05_part60_checked

  · exact kid05_part66_checked

  · exact kid05_part49_checked

  · exact kid05_part55_checked

  · exact kid05_part61_checked

  · exact kid05_part67_checked

def kid05_part69 : Audit := .cycle 0 16 true (-2)
theorem kid05_part69_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part69) = true := by rfl

def kid05_part70 : Audit := .split 27 (4,true) (byMove [
.cycle 0 28 false (3),
.cycle 0 39 false (3),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 31 false (3),
.cycle 0 40 false (3),
.cycle 0 28 true (-3),
.cycle 0 39 true (-3),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 0 31 true (-3),
.cycle 0 40 true (-3),
.last 29 (1,true),
.cycle 0 34 false (3),
.cycle 0 30 true (-3),
.cycle 28 1 false (-2),
.cycle 0 42 true (-3),
.cycle 1 43 false (3),
.cycle 18 20 true (-3),
.cycle 1 27 false (3),
.cycle 0 38 true (-3),
.cycle 0 41 true (-3),
.cycle 9 19 false (1),
.last 29 (1,true)
])
theorem kid05_part70_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part70) = true := by rfl

def kid05_part71 : Audit := .cycle 13 1 false (-1)
theorem kid05_part71_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part71) = true := by rfl

def kid05_part72 : Audit := .cycle 12 1 false (-2)
theorem kid05_part72_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part72) = true := by rfl

def kid05_part73 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 false (3),
.cycle 0 31 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 23 false (3),
.cycle 0 24 false (3),
.cycle 0 20 true (-3),
.cycle 0 31 true (-3),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 0 23 true (-3),
.cycle 0 24 true (-3),
.last 21 (1,true),
.cycle 0 26 false (3),
.cycle 0 22 true (-3),
.cycle 20 1 false (-2),
.cycle 0 34 true (-3),
.last 25 (1,true),
.cycle 12 20 true (-3),
.cycle 1 19 false (3),
.cycle 0 30 true (-3),
.cycle 0 33 true (-3),
.cycle 9 11 false (1),
.cycle 19 2 true (-1)
])
theorem kid05_part73_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part73) = true := by rfl

def kid05_part74 : Audit := .cycle 11 1 false (-1)
theorem kid05_part74_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part74) = true := by rfl

def kid05_part75 : Audit := .split 13 (1,true) (byMove [
.cycle 0 25 true (-1),
.cycle 0 26 true (-2),
.cycle 0 16 true (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 0 18 true (-2),
.cycle 0 14 true (-1),
.cycle 0 25 true (-1),
.last 29 (4,true),
.cycle 0 23 true (-1),
.cycle 0 17 true (-1),
.cycle 0 15 true (-1),
.cycle 0 20 true (-2),
.last 25 (4,true),
.cycle 10 4 true (-1),
.cycle 0 26 true (-1),
.last 14 (4,true),
.cycle 12 6 true (-2),
.last 26 (4,true),
.last 32 (4,true),
.cycle 2 12 true (-1),
.cycle 0 27 true (-1),
.last 24 (4,true),
.cycle 0 15 true (-1)
])
theorem kid05_part75_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part75) = true := by rfl

def kid05_part76 : Audit := .cycle 0 18 true (-2)
theorem kid05_part76_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part76) = true := by rfl

def kid05_part77 : Audit := .cycle 0 14 true (-1)
theorem kid05_part77_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part77) = true := by rfl

def kid05_part78 : Audit := .cycle 12 1 false (0)
theorem kid05_part78_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part78) = true := by rfl

def kid05_part79 : Audit := .cycle 0 26 true (-1)
theorem kid05_part79_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part79) = true := by rfl

def kid05_part80 : Audit := .cycle 0 17 true (-1)
theorem kid05_part80_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part80) = true := by rfl

def kid05_part81 : Audit := .split 13 (1,true) (byMove [
.last 29 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M215.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M215.never m hm),
.cycle 10 4 false (0),
.last 19 (4,true),
.last 14 (4,true),
.last 37 (4,true),
.last 76 (4,true),
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.last 27 (4,true),
.cycle 0 28 true (-2),
.last 28 (4,true),
.last 41 (4,true),
.last 25 (4,true),
.cycle 10 4 false (0),
.cycle 0 18 true (-2),
.last 14 (4,true),
.cycle 12 6 true (-4),
.last 28 (4,true),
.last 17 (4,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.last 24 (4,true),
.last 18 (4,true)
])
theorem kid05_part81_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part81) = true := by rfl

def kid05_part82 : Audit := .split 37 (4,true) (byMove [
.last 88 (1,true),
.last 38 (1,true),
.cycle 0 46 false (5),
.cycle 3 63 false (5),
.proven (BB6.Agent11Raw39B1RCPumps.M216.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M216.never m hm),
.proven (BB6.Agent11Raw39B1RCPumps.M217.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M217.never m hm),
.cycle 18 20 true (-2),
.cycle 0 65 true (-4),
.cycle 55 1 false (1),
.cycle 50 26 false (3),
.cycle 0 49 true (-4),
.proven (BB6.Agent11Raw39B1RCPumps.M218.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M218.never m hm),
.proven (BB6.Agent11Raw39B1RCPumps.M219.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M219.never m hm),
.last 38 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M220.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M220.never m hm),
.cycle 13 32 true (-4),
.proven (BB6.Agent11Raw39B1RCPumps.M221.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M221.never m hm),
.last 43 (1,true),
.cycle 18 20 true (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M222.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M222.never m hm),
.proven (BB6.Agent11Raw39B1RCPumps.M223.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M223.never m hm),
.cycle 0 69 true (-4),
.proven (BB6.Agent11Raw39B1RCPumps.M224.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M224.never m hm),
.last 39 (1,true)
])
theorem kid05_part82_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part82) = true := by rfl

def kid05_part83 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.last 16 (4,true),
.cycle 0 20 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 1, 1, 8192, 16384, 8, 256, 1, 1, 33554432, 67108864, 2097152, 256, 1073741824, 1073741824, 8192, 16384, 8, 16384, 1, 1, 33554432, 67108864, 134217728, 1327513993, 1327513993, 1327513993, 1073741824],[256, 1, 128, 1, 1073741824, 128, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 1073741824, 1, 1073741824, 1073741824, 67108864, 16777216, 1327513993, 16777216, 1073741824, 1327513993, 1073741824],2132259662⟩,
.cycle 0 27 true (-2),
.last 31 (4,true),
.cycle 0 25 true (-2),
.cycle 0 19 true (-2),
.cycle 0 19 true (-2),
.cycle 0 22 true (-2),
.last 27 (4,true),
.cycle 10 6 true (-2),
.cycle 0 28 true (-2),
.last 16 (4,true),
.cycle 12 6 true (-2),
.last 28 (4,true),
.last 34 (4,true),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.last 26 (4,true),
.last 26 (4,true)
])
theorem kid05_part83_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part83) = true := by rfl

def kid05_part84 : Audit := .cycle 12 1 false (-2)
theorem kid05_part84_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part84) = true := by rfl

def kid05_part85 : Audit := .far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[131072, 256, 2097152, 512, 256, 1024, 4398046511104, 16, 274877906944, 2097152, 1048576, 4194304, 4398046511104, 131072, 134217728, 8589934592, 4294967296, 17179869184, 4398046511104, 268435456, 274877906944, 134217728, 67108864, 268435456, 5240866865152, 5240866865152, 5222881558528, 134217728, 67108864, 268435456, 4398046511104, 268435456, 4398046511104, 549755813888, 274877906944, 1099511627776, 4398046511104, 268435456, 274877906944, 134217728, 67108864, 268435456, 4398046511104],[256, 4398046511104, 32, 17179869184, 4398046511104, 16, 16, 4398046511104, 131072, 274877906944, 4398046511104, 65536, 131072, 4398046511104, 536870912, 4398046511104, 4398046511104, 268435456, 268435456, 4398046511104, 131072, 256, 4398046511104, 65536, 5240866865152, 4398046511104, 536870912, 5240329863168, 4398046511104, 268435456, 268435456, 4398046511104, 536870912, 17179869184, 4398046511104, 268435456, 268435456, 4398046511104, 131072, 67108864, 4398046511104, 65536, 4398046511104],7945551943744⟩
theorem kid05_part85_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part85) = true := by rfl

def kid05_part86 : Audit := .cycle 11 1 false (-1)
theorem kid05_part86_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part86) = true := by rfl

def kid05_part87 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 false (3),
.cycle 0 27 false (3),
.cycle 0 19 false (3),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 0 25 true (-1),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 0 17 true (-1),
.last 37 (4,true),
.last 17 (4,true),
.last 26 (4,true),
.last 23 (4,true),
.cycle 0 26 true (-1),
.last 14 (4,true),
.last 15 (4,true),
.last 26 (4,true),
.last 25 (4,true),
.last 31 (4,true),
.cycle 0 27 true (-1),
.last 17 (4,true),
.last 27 (4,true)
])
theorem kid05_part87_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part87) = true := by rfl

def kid05_part88 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.cycle 0 27 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 19 false (3),
.cycle 1 16 false (3),
.cycle 0 16 true (-1),
.cycle 0 27 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 0 19 true (-1),
.cycle 1 16 true (-1),
.last 17 (1,true),
.cycle 0 22 false (3),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 0 30 true (-3),
.last 17 (1,true),
.cycle 12 20 true (-3),
.cycle 1 15 false (3),
.cycle 0 26 true (-2),
.cycle 0 29 true (-1),
.cycle 9 7 false (1),
.cycle 12 20 true (-3)
])
theorem kid05_part88_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part88) = true := by rfl

def kid05_part89 : Audit := .cycle 0 14 true (-1)
theorem kid05_part89_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part89) = true := by rfl

def kid05_part90 : Audit := .cycle 0 20 true (-2)
theorem kid05_part90_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part90) = true := by rfl

def kid05_part91 : Audit := .cycle 9 3 false (1)
theorem kid05_part91_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part91) = true := by rfl

def kid05_part92 : Audit := .split 14 (4,true) (byMove [
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
.cycle 0 18 true (-1),
.cycle 15 1 true (1),
.cycle 0 21 false (3),
.last 15 (1,true),
.cycle 10 5 false (1),
.cycle 0 27 true (-1),
.cycle 0 25 false (3),
.last 20 (1,true),
.cycle 13 18 true (-1),
.cycle 1 33 false (3),
.cycle 2 13 false (3),
.cycle 0 28 true (-1),
.cycle 9 17 false (1),
.cycle 15 1 true (1)
])
theorem kid05_part92_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part92) = true := by rfl

def kid05_part68 : Audit := .split 11 (5,false) (byMove [(kid05_part69),(kid05_part70),(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91),(kid05_part92)])

theorem kid05_part68_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part68) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some mv)) (byMove [(kid05_part69),(kid05_part70),(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91),(kid05_part92)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part69_checked

  · exact kid05_part75_checked

  · exact kid05_part81_checked

  · exact kid05_part87_checked

  · exact kid05_part70_checked

  · exact kid05_part76_checked

  · exact kid05_part82_checked

  · exact kid05_part88_checked

  · exact kid05_part71_checked

  · exact kid05_part77_checked

  · exact kid05_part83_checked

  · exact kid05_part89_checked

  · exact kid05_part72_checked

  · exact kid05_part78_checked

  · exact kid05_part84_checked

  · exact kid05_part90_checked

  · exact kid05_part73_checked

  · exact kid05_part79_checked

  · exact kid05_part85_checked

  · exact kid05_part91_checked

  · exact kid05_part74_checked

  · exact kid05_part80_checked

  · exact kid05_part86_checked

  · exact kid05_part92_checked

def kid05_part93 : Audit := .cycle 20 1 false (0)
theorem kid05_part93_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part93) = true := by rfl

def kid05_part95 : Audit := .cycle 0 16 false (3)
theorem kid05_part95_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part95) = true := by rfl

def kid05_part96 : Audit := .cycle 0 14 true (-1)
theorem kid05_part96_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part96) = true := by rfl

def kid05_part97 : Audit := .cycle 12 1 false (0)
theorem kid05_part97_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part97) = true := by rfl

def kid05_part98 : Audit := .cycle 11 1 false (-1)
theorem kid05_part98_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part98) = true := by rfl

def kid05_part99 : Audit := .cycle 11 1 false (-1)
theorem kid05_part99_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part99) = true := by rfl

def kid05_part100 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 13 (1,true),
.cycle 1 16 false (3),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.cycle 16 1 false (-2)
])
theorem kid05_part100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part100) = true := by rfl

def kid05_part101 : Audit := .cycle 19 1 false (1)
theorem kid05_part101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part101) = true := by rfl

def kid05_part102 : Audit := .split 11 (1,true) (byMove [
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
.cycle 17 1 false (-1),
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
])
theorem kid05_part102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part102) = true := by rfl

def kid05_part103 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 21 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 true (0),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 23 1 false (1),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid05_part103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part103) = true := by rfl

def kid05_part104 : Audit := .cycle 0 12 true (0)
theorem kid05_part104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part104) = true := by rfl

def kid05_part105 : Audit := .cycle 12 1 false (2)
theorem kid05_part105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part105) = true := by rfl

def kid05_part106 : Audit := .cycle 12 1 false (0)
theorem kid05_part106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part106) = true := by rfl

def kid05_part107 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.cycle 22 1 false (-2),
.last 14 (5,false),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 6 20 false (3),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 17, 32, 17, 1, 16, 64],96⟩,
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 22 1 false (-2),
.cycle 8 5 false (2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 26 1 false (-2),
.cycle 0 33 true (-2),
.cycle 2 16 false (3),
.cycle 0 14 true (-1),
.cycle 25 1 false (-3),
.cycle 18 1 false (-2)
])
theorem kid05_part107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part107) = true := by rfl

def kid05_part108 : Audit := .cycle 14 1 false (-2)
theorem kid05_part108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part108) = true := by rfl

def kid05_part109 : Audit := .cycle 21 1 false (1)
theorem kid05_part109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part109) = true := by rfl

def kid05_part110 : Audit := .cycle 11 1 false (-1)
theorem kid05_part110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part110) = true := by rfl

def kid05_part111 : Audit := .cycle 11 1 false (-1)
theorem kid05_part111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part111) = true := by rfl

def kid05_part112 : Audit := .split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.cycle 24 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 12 (1,true),
.cycle 0 16 true (-1),
.cycle 21 1 false (1),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 2 16 false (3),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 5 20 false (3),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
])
theorem kid05_part112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part112) = true := by rfl

def kid05_part113 : Audit := .cycle 2 10 true (0)
theorem kid05_part113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part113) = true := by rfl

def kid05_part114 : Audit := .split 11 (1,true) (byMove [
.cycle 20 1 false (0),
.cycle 21 1 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.last 12 (5,false),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 13 (5,false),
.cycle 21 1 false (1),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 27 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid05_part114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part114) = true := by rfl

def kid05_part115 : Audit := .cycle 13 1 false (-1)
theorem kid05_part115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part115) = true := by rfl

def kid05_part116 : Audit := .cycle 0 12 true (0)
theorem kid05_part116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part116) = true := by rfl

def kid05_part117 : Audit := .cycle 9 3 true (0)
theorem kid05_part117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part117) = true := by rfl

def kid05_part118 : Audit := .split 13 (5,false) (byMove [
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.last 28 (1,true),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 12 8 true (0),
.cycle 13 1 true (1),
.cycle 17 1 false (-1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 23 1 false (1),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 31 true (0),
.cycle 9 5 true (0),
.cycle 13 1 true (1)
])
theorem kid05_part118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part118) = true := by rfl

def kid05_part94 : Audit := .split 10 (4,true) (byMove [(kid05_part95),(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116),(kid05_part117),(kid05_part118)])

theorem kid05_part94_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part94) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part95),(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116),(kid05_part117),(kid05_part118)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part95_checked

  · exact kid05_part101_checked

  · exact kid05_part107_checked

  · exact kid05_part113_checked

  · exact kid05_part96_checked

  · exact kid05_part102_checked

  · exact kid05_part108_checked

  · exact kid05_part114_checked

  · exact kid05_part97_checked

  · exact kid05_part103_checked

  · exact kid05_part109_checked

  · exact kid05_part115_checked

  · exact kid05_part98_checked

  · exact kid05_part104_checked

  · exact kid05_part110_checked

  · exact kid05_part116_checked

  · exact kid05_part99_checked

  · exact kid05_part105_checked

  · exact kid05_part111_checked

  · exact kid05_part117_checked

  · exact kid05_part100_checked

  · exact kid05_part106_checked

  · exact kid05_part112_checked

  · exact kid05_part118_checked

def kid05_part120 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 false (3),
.cycle 10 15 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.cycle 0 19 false (3),
.last 39 (1,true),
.cycle 10 15 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 7 false (-1),
.cycle 0 19 false (3),
.last 19 (1,true),
.cycle 10 10 false (0),
.last 41 (1,true),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.cycle 12 6 false (-1),
.last 39 (1,true),
.cycle 1 17 false (3),
.cycle 10 14 false (0),
.cycle 10 17 false (0),
.cycle 9 9 false (1),
.cycle 10 16 false (0)
])
theorem kid05_part120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part120) = true := by rfl

def kid05_part121 : Audit := .split 17 (1,true) (byMove [
.last 62 (4,true),
.last 47 (4,true),
.cycle 1 19 false (3),
.cycle 0 19 true (-3),
.last 18 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M229.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M229.never m hm),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[1099511627776, 131072, 35184372088832, 32768, 131072, 2, 281495151316096, 281495151316096, 281495285534336, 134217728, 536870912, 128, 17179869184, 16, 2147483648, 35184372088832, 140737488355328, 137438953472, 17179869184, 268436480, 2147483648, 134217728, 536870912, 2147483648, 282594662943872, 281495151316096, 281632724487808, 512, 2048, 33554432, 281474976710656, 8388608, 512, 2097152, 8388608, 128, 281474976710656, 8388608, 134217728, 2097152, 8388608, 33554432, 8388608, 268435456, 8388608, 134217728, 536870912, 33554432, 281474976710656],[131072, 8388608, 32, 8388608, 281474976710656, 16, 281495151316096, 281495151316096, 2048, 281495151316096, 281474976710656, 1024, 16, 137438953472, 2199023255552, 137438953472, 281474976710656, 1099511627776, 268436480, 2147483648, 34359738368, 2147483648, 281474976710656, 17179869184, 281495151316096, 281495151316096, 536870912, 281495151316096, 281474976710656, 268435456, 8388608, 8388608, 2048, 8388608, 281474976710656, 1024, 8388608, 8388608, 536870912, 8388608, 281474976710656, 268435456, 268435456, 131072, 536870912, 131072, 281474976710656, 268435456, 281474976710656],503681406012864⟩,
.cycle 7 45 false (4),
.last 35 (4,true),
.last 58 (4,true),
.cycle 146 50 true (-2),
.cycle 12 20 true (-3),
.proven (BB6.Agent11Raw39B1RCPumps.M231.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M231.never m hm),
.cycle 7 13 false (3),
.cycle 1 19 false (3),
.cycle 100 1 false (-6),
.last 18 (4,true),
.cycle 12 10 false (1),
.last 29 (4,true),
.last 28 (4,true),
.cycle 14 16 true (-3),
.cycle 4 51 false (4),
.last 20 (4,true),
.cycle 17 2 true (1)
])
theorem kid05_part121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part121) = true := by rfl

def kid05_part122 : Audit := .cycle 14 1 false (-2)
theorem kid05_part122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part122) = true := by rfl

def kid05_part123 : Audit := .cycle 13 1 false (-3)
theorem kid05_part123_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part123) = true := by rfl

def kid05_part124 : Audit := .cycle 11 2 false (-1)
theorem kid05_part124_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part124) = true := by rfl

def kid05_part125 : Audit := .cycle 12 1 false (-2)
theorem kid05_part125_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part125) = true := by rfl

def kid05_part126 : Audit := .cycle 0 16 true (-2)
theorem kid05_part126_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part126) = true := by rfl

def kid05_part127 : Audit := .split 13 (1,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 0 18 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 1, 2, 8192, 16384, 8, 256, 1, 2, 33554432, 67108864, 2097152, 256, 1073741824, 524288, 8192, 16384, 8, 16384, 1, 2, 33554432, 67108864, 134217728, 1140867072, 1090519040, 33554432, 1073741824],[256, 1, 256, 1, 1073741824, 128, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 16777216, 1140850688, 16777216, 1073741824, 1107296256, 1073741824],2140519278⟩,
.cycle 15 11 true (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.last 17 (4,true),
.cycle 14 12 true (0),
.cycle 10 8 false (0),
.cycle 10 6 false (0),
.cycle 0 28 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 27 (4,true),
.last 17 (4,true),
.cycle 0 16 true (-2),
.cycle 14 13 true (-2),
.cycle 9 5 false (1),
.cycle 14 12 true (0)
])
theorem kid05_part127_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part127) = true := by rfl

def kid05_part128 : Audit := .cycle 16 1 false (0)
theorem kid05_part128_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part128) = true := by rfl

def kid05_part129 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 18 1 false (0),
.cycle 0 17 true (-2),
.last 16 (4,true),
.cycle 0 20 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 1, 8, 8192, 16384, 8, 256, 1, 8, 33554432, 67108864, 2097152, 256, 1073741824, 2097152, 8192, 16384, 8, 16384, 1, 8, 33554432, 67108864, 134217728, 1140867072, 1090519040, 134217728, 1073741824],[256, 1, 1073758208, 1, 1073741824, 128, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 16777216, 1140867072, 16777216, 1073741824, 1107296256, 1073741824],2140519278⟩,
.cycle 0 27 true (-2),
.last 31 (4,true),
.cycle 0 25 true (-2),
.cycle 0 19 true (-2),
.last 31 (4,true),
.cycle 0 22 true (-2),
.last 27 (4,true),
.cycle 18 1 false (0),
.cycle 0 28 true (-2),
.last 16 (4,true),
.cycle 10 6 true (-2),
.last 27 (4,true),
.last 26 (4,true),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.last 18 (4,true),
.cycle 3 14 true (-2)
])
theorem kid05_part129_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part129) = true := by rfl

def kid05_part130 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 11 4 true (-2),
.last 15 (1,true),
.cycle 15 11 true (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.cycle 17 3 true (1),
.cycle 14 4 true (0),
.last 15 (1,true),
.cycle 10 6 false (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 15 (1,true),
.cycle 1 17 false (3),
.cycle 0 16 true (-2),
.cycle 14 13 true (-2),
.cycle 9 5 false (1),
.cycle 14 4 true (0)
])
theorem kid05_part130_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part130) = true := by rfl

def kid05_part131 : Audit := .cycle 10 3 false (0)
theorem kid05_part131_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part131) = true := by rfl

def kid05_part132 : Audit := .split 14 (1,true) (byMove [
.last 51 (4,true),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.last 23 (4,true),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 47 (4,true),
.last 65 (4,true),
.cycle 10 9 false (0),
.last 45 (4,true),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 34 (4,true),
.last 19 (4,true),
.last 17 (4,true),
.last 35 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part132_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part132) = true := by rfl

def kid05_part133 : Audit := .cycle 10 5 false (0)
theorem kid05_part133_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part133) = true := by rfl

def kid05_part134 : Audit := .split 36 (1,true) (byMove [
.cycle 42 12 true (0),
.cycle 39 12 true (-4),
.last 45 (4,true),
.last 45 (4,true),
.last 37 (4,true),
.cycle 37 12 true (-4),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 256, 1, 524288, 1048576, 32768, 256, 4097, 4096, 128, 256, 8, 1048576, 256, 1, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 1048576, 68719476736, 1073741824, 2147483648, 4294967296, 8589934592, 84825604096, 84825604096, 84825604096, 68719476736],[256, 1, 128, 1, 68719476736, 32768, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 1, 128, 1, 68719476736, 128, 4294967296, 16777216, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 4294967296, 1073741824, 84825604096, 1073741824, 68719476736, 84825604096, 68719476736],137301344332⟩,
.cycle 51 12 true (0),
.cycle 47 12 true (-3),
.cycle 40 12 true (0),
.last 37 (4,true),
.last 51 (4,true),
.cycle 37 12 true (-4),
.cycle 39 12 true (-5),
.cycle 31 6 true (-3),
.cycle 37 12 true (-3),
.last 37 (4,true),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 256, 1, 524288, 1048576, 32768, 256, 1, 1, 128, 256, 8, 1048576, 256, 1, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 1048576, 68719476736, 1073741824, 2147483648, 4294967296, 8589934592, 84825604096, 84825604096, 84825604096, 68719476736],[256, 256, 128, 1, 68719476736, 32768, 1048576, 1, 1048576, 4096, 68719476736, 68719476736, 256, 256, 128, 1, 68719476736, 128, 4294967296, 68719476736, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 68719476736, 68719476736, 1073741824, 68719476736, 68719476736, 4294967296, 84825604096, 84825604096, 1073741824, 68719476736, 84825604096, 68719476736],137301344332⟩,
.last 55 (4,true),
.last 41 (4,true),
.last 39 (4,true),
.cycle 54 12 true (-4),
.last 37 (4,true),
.last 38 (4,true)
])
theorem kid05_part134_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part134) = true := by rfl

def kid05_part135 : Audit := .cycle 13 1 false (-3)
theorem kid05_part135_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part135) = true := by rfl

def kid05_part136 : Audit := .cycle 11 2 false (-1)
theorem kid05_part136_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part136) = true := by rfl

def kid05_part137 : Audit := .cycle 12 1 false (-2)
theorem kid05_part137_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part137) = true := by rfl

def kid05_part138 : Audit := .cycle 0 16 true (-2)
theorem kid05_part138_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part138) = true := by rfl

def kid05_part139 : Audit := .split 13 (1,true) (byMove [
.cycle 10 11 false (0),
.cycle 10 12 false (0),
.cycle 1 15 false (3),
.last 19 (4,true),
.last 14 (4,true),
.cycle 10 4 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 4096, 128, 524288, 1048576, 32768, 67109120, 4096, 524288, 128, 256, 134217728, 68787634176, 1073741824, 128, 33554432, 67108864, 8589934592, 256, 68719476736, 33554432, 33554432, 67108864, 134217728, 68787634176, 68736258048, 33554432, 33554432, 67108864, 134217728, 1048576, 16777216, 33554432, 68719476736],[256, 1, 1048576, 1, 68719476736, 128, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 16777216, 67108864, 16777216, 68719476736, 128, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 68787634176, 16777216, 68719476736, 68753031296, 67108864, 16777216, 67108864, 16777216, 68719476736, 68719476736, 68719476736],128847833922⟩,
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.last 17 (4,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 131072, 128, 524288, 1048576, 32768, 67109120, 131072, 524288, 128, 256, 134217728, 68787634176, 34359738368, 128, 33554432, 67108864, 8589934592, 256, 68719476736, 33554432, 33554432, 67108864, 134217728, 68787634176, 69256478720, 33554432, 33554432, 67108864, 134217728, 1048576, 536870912, 33554432, 68719476736],[256, 32, 1048576, 1, 68719476736, 128, 1048576, 131072, 1048576, 4096, 68719476736, 68719476736, 256, 536870912, 67108864, 16777216, 68719476736, 128, 67108864, 34359738368, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 536870912, 68787634176, 16777216, 68719476736, 68753031296, 67108864, 536870912, 67108864, 16777216, 68719476736, 68719476736, 68719476736],128847833922⟩,
.cycle 10 6 false (0),
.cycle 10 7 false (0),
.last 19 (4,true),
.cycle 0 18 true (-2),
.last 14 (4,true),
.cycle 10 4 false (0),
.last 27 (4,true),
.last 17 (4,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.last 16 (4,true),
.last 27 (4,true)
])
theorem kid05_part139_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part139) = true := by rfl

def kid05_part140 : Audit := .cycle 10 4 false (0)
theorem kid05_part140_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part140) = true := by rfl

def kid05_part141 : Audit := .split 15 (1,true) (byMove [
.last 40 (4,true),
.cycle 1 16 false (3),
.last 44 (4,true),
.cycle 0 17 true (-2),
.last 16 (4,true),
.cycle 8 8 false (2),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 4096, 512, 524288, 1048576, 32768, 67109120, 4096, 2097152, 128, 256, 134217728, 68787634432, 1073741824, 512, 33554432, 67108864, 8589934592, 256, 68719476736, 134217728, 33554432, 67108864, 134217728, 68787634432, 68736258048, 134217728, 33554432, 67108864, 134217728, 1048576, 16777216, 134217728, 68719476736],[256, 1, 67109120, 1, 68719476736, 128, 1048576, 4096, 1048576, 4096, 68719476736, 68719476736, 256, 16777216, 256, 16777216, 68719476736, 128, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 68787634432, 16777216, 68719476736, 68753031296, 67108864, 16777216, 68787634432, 16777216, 68719476736, 68719476736, 68719476736],128847965026⟩,
.last 40 (4,true),
.last 31 (4,true),
.last 38 (4,true),
.last 32 (4,true),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[1099511627776, 131072, 35184372088832, 32768, 131072, 17179869184, 281492425016320, 282592481905664, 282592616123904, 134217728, 536870912, 282592481905664, 17179869184, 16, 17179869184, 35184372088832, 140737488355328, 17179869184, 17179869184, 268436480, 17179869184, 134217728, 536870912, 17179869184, 281492425016320, 282592481905664, 282592616123904, 512, 2048, 282592481905664, 281474976710656, 281474976710656, 512, 2097152, 8388608, 282592481905664, 281474976710656, 281474976710656, 134217728, 2097152, 8388608, 131072, 1099511627776, 268435456, 8388608, 134217728, 536870912, 281474976710656, 281474976710656],[131072, 8388608, 32, 8388608, 281474976710656, 16, 282592481905664, 282592481905664, 2048, 282592481905664, 281474976710656, 1024, 16, 131072, 2199023255552, 17179869184, 281474976710656, 1099511627776, 268436480, 536872960, 34359738368, 281474976710656, 281474976710656, 17179869184, 282592481905664, 282592481905664, 536870912, 282592481905664, 281474976710656, 268435456, 281474976710656, 8388608, 2048, 8388608, 281474976710656, 1024, 281474976710656, 8388608, 536870912, 8388608, 281474976710656, 268435456, 268435456, 8388608, 536870912, 131072, 281474976710656, 268435456, 281474976710656],501621969194432⟩,
.cycle 6 10 false (3),
.last 20 (4,true),
.cycle 4 14 false (3),
.last 131 (4,true),
.last 16 (4,true),
.cycle 8 8 false (2),
.last 27 (4,true),
.last 26 (4,true),
.last 61 (4,true),
.last 42 (4,true),
.last 18 (4,true),
.last 43 (4,true)
])
theorem kid05_part141_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part141) = true := by rfl

def kid05_part142 : Audit := .split 13 (4,true) (byMove [
.cycle 10 11 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 20 1 false (-2),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.last 15 (1,true),
.cycle 7 8 false (3),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.cycle 17 3 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 32, 1, 32, 16, 64],64⟩,
.cycle 10 6 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 0 18 true (-2),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.last 15 (1,true),
.cycle 1 32 false (3),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.cycle 9 8 false (1),
.cycle 13 6 true (-1)
])
theorem kid05_part142_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part142) = true := by rfl

def kid05_part143 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 10 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 28 1 true (-6),
.cycle 0 20 true (-2),
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 4 true (-2),
.cycle 19 1 true (1),
.last 16 (1,true),
.cycle 10 7 false (0),
.cycle 0 24 true (-3),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 12 3 false (-1),
.last 33 (1,true),
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 0 20 true (-2),
.cycle 9 6 false (1),
.cycle 19 1 true (1)
])
theorem kid05_part143_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part143) = true := by rfl

def kid05_part119 : Audit := .split 12 (5,false) (byMove [(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125),(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143)])

theorem kid05_part119_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part119) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125),(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part120_checked

  · exact kid05_part126_checked

  · exact kid05_part132_checked

  · exact kid05_part138_checked

  · exact kid05_part121_checked

  · exact kid05_part127_checked

  · exact kid05_part133_checked

  · exact kid05_part139_checked

  · exact kid05_part122_checked

  · exact kid05_part128_checked

  · exact kid05_part134_checked

  · exact kid05_part140_checked

  · exact kid05_part123_checked

  · exact kid05_part129_checked

  · exact kid05_part135_checked

  · exact kid05_part141_checked

  · exact kid05_part124_checked

  · exact kid05_part130_checked

  · exact kid05_part136_checked

  · exact kid05_part142_checked

  · exact kid05_part125_checked

  · exact kid05_part131_checked

  · exact kid05_part137_checked

  · exact kid05_part143_checked

def kid05_part144 : Audit := .cycle 0 10 true (0)
theorem kid05_part144_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part144) = true := by rfl

def kid05_part145 : Audit := .cycle 1 9 true (1)
theorem kid05_part145_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part145) = true := by rfl

def kid05_part146 : Audit := .cycle 2 8 true (1)
theorem kid05_part146_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part146) = true := by rfl

def kid05_part147 : Audit := .cycle 2 11 true (1)
theorem kid05_part147_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part147) = true := by rfl

def kid05_part148 : Audit := .cycle 9 1 true (1)
theorem kid05_part148_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part148) = true := by rfl

def kid05_part150 : Audit := .cycle 2 10 true (1)
theorem kid05_part150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part150) = true := by rfl

def kid05_part151 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 26 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 12 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 1 12 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 31 (4,true),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 14 12 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid05_part151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part151) = true := by rfl

def kid05_part152 : Audit := .cycle 18 1 false (-2)
theorem kid05_part152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part152) = true := by rfl

def kid05_part153 : Audit := .cycle 0 12 true (0)
theorem kid05_part153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part153) = true := by rfl

def kid05_part154 : Audit := .split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 9 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 26 true (-3),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid05_part154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part154) = true := by rfl

def kid05_part155 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 3 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 3 false (2),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 22 3 false (2),
.cycle 9 4 true (0),
.cycle 13 3 false (1)
])
theorem kid05_part155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part155) = true := by rfl

def kid05_part156 : Audit := .cycle 0 11 true (0)
theorem kid05_part156_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part156) = true := by rfl

def kid05_part157 : Audit := .cycle 1 10 true (1)
theorem kid05_part157_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part157) = true := by rfl

def kid05_part158 : Audit := .cycle 0 23 true (0)
theorem kid05_part158_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part158) = true := by rfl

def kid05_part159 : Audit := .cycle 3 8 true (1)
theorem kid05_part159_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part159) = true := by rfl

def kid05_part160 : Audit := .cycle 9 2 true (1)
theorem kid05_part160_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part160) = true := by rfl

def kid05_part161 : Audit := .cycle 10 1 true (2)
theorem kid05_part161_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part161) = true := by rfl

def kid05_part162 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 20 5 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 17 (1,true),
.cycle 0 15 true (0),
.cycle 20 5 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 5 false (2),
.last 17 (1,true),
.last 16 (1,true),
.cycle 16 5 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.last 17 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 22 5 false (3),
.cycle 9 6 true (0),
.cycle 15 5 false (1)
])
theorem kid05_part162_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part162) = true := by rfl

def kid05_part163 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 21 1 false (-3),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 12 7 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 36 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 7 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part163_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part163) = true := by rfl

def kid05_part164 : Audit := .split 20 (1,true) (byMove [
.cycle 11 16 true (-3),
.cycle 11 17 false (1),
.proven (BB6.Agent11Raw39B1RCPumps.M241.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M241.never m hm),
.last 26 (4,true),
.last 21 (4,true),
.cycle 12 9 false (0),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 385, 2048, 1, 8192, 16384, 8, 384, 131072, 1, 524288, 1048576, 512, 256, 8388608, 1, 524288, 1048576, 2097152, 18628608, 8388608, 17039360, 16777216],[256, 1, 128, 1, 16777216, 1, 16384, 1, 128, 1, 16777216, 17039360, 1048576, 64, 17301504, 64, 16777216, 16777216, 1048576, 262144, 17301504, 262144, 16777216, 17039360, 16777216],33370176⟩,
.cycle 7 15 false (3),
.cycle 0 23 true (-3),
.cycle 11 14 true (-3),
.last 23 (4,true),
.cycle 41 29 true (0),
.cycle 11 11 false (1),
.cycle 11 12 false (1),
.cycle 15 6 true (-3),
.cycle 50 17 true (2),
.last 21 (4,true),
.cycle 12 9 false (0),
.last 36 (4,true),
.last 24 (4,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1327513985, 2048, 1, 8192, 16384, 8, 256, 131072, 16385, 33554432, 67108864, 2097152, 256, 536870912, 16385, 8192, 16384, 8, 2097280, 131072, 1, 33554432, 67108864, 134217728, 1325416448, 536870912, 1157627904, 1073741824],[256, 256, 2097280, 1, 1073741824, 16385, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1241513984, 262144, 1073741824, 1073741824, 16384, 16384, 2097280, 1, 1073741824, 1157627904, 67108864, 67108864, 1241513984, 16777216, 1073741824, 1157627904, 1073741824],2132128590⟩,
.cycle 4 17 false (3),
.last 23 (4,true),
.cycle 10 11 false (2)
])
theorem kid05_part164_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part164) = true := by rfl

def kid05_part165 : Audit := .cycle 2 11 true (1)
theorem kid05_part165_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part165) = true := by rfl

def kid05_part166 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 15 4 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 33 true (-3),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.cycle 15 4 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 5 false (2),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 10 4 true (1)
])
theorem kid05_part166_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part166) = true := by rfl

def kid05_part167 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 3 false (3),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 15 3 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.cycle 9 7 true (0),
.cycle 13 3 false (1)
])
theorem kid05_part167_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part167) = true := by rfl

def kid05_part168 : Audit := .cycle 0 11 true (0)
theorem kid05_part168_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part168) = true := by rfl

def kid05_part169 : Audit := .cycle 1 10 true (1)
theorem kid05_part169_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part169) = true := by rfl

def kid05_part170 : Audit := .cycle 2 9 true (1)
theorem kid05_part170_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part170) = true := by rfl

def kid05_part171 : Audit := .cycle 2 12 true (1)
theorem kid05_part171_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part171) = true := by rfl

def kid05_part172 : Audit := .cycle 9 2 true (1)
theorem kid05_part172_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part172) = true := by rfl

def kid05_part173 : Audit := .cycle 10 1 true (2)
theorem kid05_part173_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part173) = true := by rfl

def kid05_part149 : Audit := .split 10 (5,false) (byMove [(kid05_part150),(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173)])

theorem kid05_part149_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part149) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part150),(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part150_checked

  · exact kid05_part156_checked

  · exact kid05_part162_checked

  · exact kid05_part168_checked

  · exact kid05_part151_checked

  · exact kid05_part157_checked

  · exact kid05_part163_checked

  · exact kid05_part169_checked

  · exact kid05_part152_checked

  · exact kid05_part158_checked

  · exact kid05_part164_checked

  · exact kid05_part170_checked

  · exact kid05_part153_checked

  · exact kid05_part159_checked

  · exact kid05_part165_checked

  · exact kid05_part171_checked

  · exact kid05_part154_checked

  · exact kid05_part160_checked

  · exact kid05_part166_checked

  · exact kid05_part172_checked

  · exact kid05_part155_checked

  · exact kid05_part161_checked

  · exact kid05_part167_checked

  · exact kid05_part173_checked

def kid05_part5 : Audit := .split 9 (4,false) (byMove [(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part43),(kid05_part68),(kid05_part93),(kid05_part94),(kid05_part119),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)])

theorem kid05_part5_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (kid05_part5) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part43),(kid05_part68),(kid05_part93),(kid05_part94),(kid05_part119),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part6_checked

  · exact kid05_part12_checked

  · exact kid05_part18_checked

  · exact kid05_part144_checked

  · exact kid05_part7_checked

  · exact kid05_part13_checked

  · exact kid05_part43_checked

  · exact kid05_part145_checked

  · exact kid05_part8_checked

  · exact kid05_part14_checked

  · exact kid05_part68_checked

  · exact kid05_part146_checked

  · exact kid05_part9_checked

  · exact kid05_part15_checked

  · exact kid05_part93_checked

  · exact kid05_part147_checked

  · exact kid05_part10_checked

  · exact kid05_part16_checked

  · exact kid05_part94_checked

  · exact kid05_part148_checked

  · exact kid05_part11_checked

  · exact kid05_part17_checked

  · exact kid05_part119_checked

  · exact kid05_part149_checked

def kid05_part175 : Audit := .cycle 0 19 false (3)
theorem kid05_part175_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part175) = true := by rfl

def kid05_part176 : Audit := .split 10 (1,true) (byMove [
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
.last 14 (4,true),
.cycle 13 9 false (-1),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 40 false (3),
.last 23 (4,true),
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
.cycle 16 9 false (-2),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 9 false (-1),
.cycle 13 9 false (2),
.cycle 10 2 true (-1),
.cycle 13 9 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 12 9 false (0),
.last 14 (4,true),
.cycle 13 9 false (-1),
.cycle 15 9 false (2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 33 false (3),
.cycle 2 11 false (3),
.last 13 (4,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 13 9 false (-1)
]),
.cycle 0 15 true (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 14 9 false (3),
.split 11 (4,false) (byMove [
.cycle 13 9 false (2),
.cycle 10 2 true (0),
.cycle 13 9 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 0 12 true (0),
.cycle 1 20 true (0),
.cycle 14 9 false (2),
.cycle 12 9 false (2),
.cycle 11 1 true (1),
.cycle 1 12 true (0),
.cycle 12 9 false (1),
.last 13 (4,true),
.cycle 13 9 false (0),
.cycle 14 9 false (3),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 22 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid05_part176_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part176) = true := by rfl

def kid05_part177 : Audit := .cycle 13 1 false (-1)
theorem kid05_part177_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part177) = true := by rfl

def kid05_part178 : Audit := .cycle 0 11 true (0)
theorem kid05_part178_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part178) = true := by rfl

def kid05_part180 : Audit := .cycle 0 11 false (3)
theorem kid05_part180_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part180) = true := by rfl

def kid05_part181 : Audit := .split 20 (4,false) (byMove [
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
.last 22 (1,true),
.cycle 17 5 false (1),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 32 (1,true),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 12 12 true (-2),
.cycle 20 1 true (-2),
.cycle 9 12 false (1)
])
theorem kid05_part181_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part181) = true := by rfl

def kid05_part182 : Audit := .cycle 12 1 false (0)
theorem kid05_part182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part182) = true := by rfl

def kid05_part183 : Audit := .cycle 11 1 false (-1)
theorem kid05_part183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part183) = true := by rfl

def kid05_part184 : Audit := .split 11 (4,false) (byMove [
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
.last 13 (1,true),
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
theorem kid05_part184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part184) = true := by rfl

def kid05_part185 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 14 false (2),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 11 12 true (-2),
.cycle 12 1 true (-2),
.cycle 9 4 false (1)
])
theorem kid05_part185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part185) = true := by rfl

def kid05_part186 : Audit := .cycle 0 11 true (0)
theorem kid05_part186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part186) = true := by rfl

def kid05_part187 : Audit := .split 20 (4,false) (byMove [
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
.last 22 (1,true),
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
theorem kid05_part187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part187) = true := by rfl

def kid05_part188 : Audit := .cycle 12 1 false (2)
theorem kid05_part188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part188) = true := by rfl

def kid05_part189 : Audit := .cycle 11 1 false (1)
theorem kid05_part189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part189) = true := by rfl

def kid05_part190 : Audit := .split 11 (4,false) (byMove [
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
.last 13 (1,true),
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
theorem kid05_part190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part190) = true := by rfl

def kid05_part191 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (1,true),
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
theorem kid05_part191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part191) = true := by rfl

def kid05_part192 : Audit := .split 12 (1,true) (byMove [
.last 22 (4,false),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 14 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 0 13 true (-1),
.last 22 (4,false),
.last 22 (4,false),
.last 20 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 23 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 29 (4,false),
.last 27 (4,false),
.cycle 2 11 false (3),
.last 24 (4,false),
.last 13 (4,false),
.last 19 (4,false)
])
theorem kid05_part192_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part192) = true := by rfl

def kid05_part193 : Audit := .split 15 (4,false) (byMove [
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
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 0 18 false (3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 27 (1,true),
.cycle 1 15 false (3),
.cycle 12 9 false (0),
.cycle 12 12 true (-3),
.cycle 15 1 true (-3),
.cycle 9 7 false (1)
])
theorem kid05_part193_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part193) = true := by rfl

def kid05_part194 : Audit := .cycle 0 13 true (-1)
theorem kid05_part194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part194) = true := by rfl

def kid05_part195 : Audit := .cycle 11 1 false (-1)
theorem kid05_part195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part195) = true := by rfl

def kid05_part196 : Audit := .split 11 (4,false) (byMove [
.cycle 0 19 false (3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 22 true (-1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.cycle 13 2 true (-2),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 0 26 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 2 11 false (3),
.last 12 (1,true),
.cycle 12 9 false (0),
.cycle 0 13 true (-1),
.cycle 10 3 false (0),
.cycle 9 7 false (1)
])
theorem kid05_part196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part196) = true := by rfl

def kid05_part197 : Audit := .split 12 (4,false) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M244.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M244.never m hm),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 14 (1,true),
.cycle 14 10 true (-3),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 14 (1,true),
.cycle 1 18 false (3),
.cycle 0 15 true (-2),
.cycle 13 12 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 0, 16, 64],64⟩,
.cycle 9 4 false (1)
])
theorem kid05_part197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part197) = true := by rfl

def kid05_part198 : Audit := .cycle 0 11 true (0)
theorem kid05_part198_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part198) = true := by rfl

def kid05_part199 : Audit := .cycle 1 10 true (0)
theorem kid05_part199_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part199) = true := by rfl

def kid05_part200 : Audit := .split 19 (4,false) (byMove [
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
.last 21 (1,true),
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
theorem kid05_part200_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part200) = true := by rfl

def kid05_part201 : Audit := .split 22 (4,false) (byMove [
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
.last 24 (1,true),
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
theorem kid05_part201_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part201) = true := by rfl

def kid05_part202 : Audit := .split 11 (4,false) (byMove [
.cycle 0 22 false (3),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.last 18 (1,true),
.last 12 (1,true),
.cycle 0 26 false (3),
.cycle 23 1 false (-1),
.cycle 10 3 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 12 true (1),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid05_part202_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part202) = true := by rfl

def kid05_part203 : Audit := .cycle 9 2 true (0)
theorem kid05_part203_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part203) = true := by rfl

def kid05_part179 : Audit := .split 10 (4,true) (byMove [(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187),(kid05_part188),(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203)])

theorem kid05_part179_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part179) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187),(kid05_part188),(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part180_checked

  · exact kid05_part186_checked

  · exact kid05_part192_checked

  · exact kid05_part198_checked

  · exact kid05_part181_checked

  · exact kid05_part187_checked

  · exact kid05_part193_checked

  · exact kid05_part199_checked

  · exact kid05_part182_checked

  · exact kid05_part188_checked

  · exact kid05_part194_checked

  · exact kid05_part200_checked

  · exact kid05_part183_checked

  · exact kid05_part189_checked

  · exact kid05_part195_checked

  · exact kid05_part201_checked

  · exact kid05_part184_checked

  · exact kid05_part190_checked

  · exact kid05_part196_checked

  · exact kid05_part202_checked

  · exact kid05_part185_checked

  · exact kid05_part191_checked

  · exact kid05_part197_checked

  · exact kid05_part203_checked

def kid05_part204 : Audit := .cycle 11 1 false (-1)
theorem kid05_part204_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part204) = true := by rfl

def kid05_part205 : Audit := .cycle 0 10 true (0)
theorem kid05_part205_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part205) = true := by rfl

def kid05_part206 : Audit := .cycle 1 9 true (1)
theorem kid05_part206_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part206) = true := by rfl

def kid05_part207 : Audit := .cycle 20 1 false (2)
theorem kid05_part207_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part207) = true := by rfl

def kid05_part208 : Audit := .cycle 17 1 false (1)
theorem kid05_part208_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part208) = true := by rfl

def kid05_part209 : Audit := .split 10 (4,false) (byMove [
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
.last 14 (1,true),
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
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 15 5 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.cycle 15 5 false (0),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 17 9 false (1),
.cycle 9 4 true (1)
]),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.cycle 19 1 false (-1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (1),
.cycle 23 1 false (3),
.cycle 15 1 false (3),
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 18 1 false (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.cycle 13 3 true (1),
.cycle 16 1 false (0)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 16 3 false (0),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.last 14 (1,true),
.cycle 16 7 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 3 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 9 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid05_part209_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part209) = true := by rfl

def kid05_part210 : Audit := .cycle 9 1 true (1)
theorem kid05_part210_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part210) = true := by rfl

def kid05_part211 : Audit := .split 15 (1,true) (byMove [
.cycle 10 11 false (1),
.cycle 10 12 false (1),
.cycle 13 4 false (-1),
.cycle 0 17 false (3),
.split 16 (4,true) (byMove [
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
.cycle 12 18 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.last 17 (4,false),
.cycle 9 8 false (1)
]),
.cycle 12 4 false (0),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 11 false (1),
.cycle 10 9 false (1),
.split 16 (4,false) (byMove [
.cycle 12 18 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.last 18 (4,true),
.cycle 9 8 false (1),
.cycle 0 17 true (-2),
.cycle 10 12 true (-2),
.cycle 10 27 true (-3),
.cycle 10 11 false (1),
.cycle 16 1 true (0),
.cycle 13 4 true (-2),
.cycle 14 3 true (-2),
.cycle 12 8 false (0),
.cycle 0 19 true (-2),
.cycle 10 9 false (1),
.last 18 (4,true),
.cycle 9 8 false (1),
.cycle 8 22 false (4),
.cycle 6 20 false (3),
.cycle 10 11 true (-2),
.cycle 10 14 true (-2),
.cycle 16 1 true (0),
.cycle 6 12 false (3)
]),
.cycle 13 3 true (-2),
.cycle 10 6 false (1),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.cycle 10 12 true (-2),
.split 16 (4,true) (byMove [
.cycle 12 9 false (0),
.last 38 (4,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 10 12 true (-2),
.last 18 (4,false),
.cycle 13 5 false (-1),
.cycle 0 18 true (-2),
.last 18 (4,false),
.cycle 12 5 false (0),
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
.last 18 (4,false),
.cycle 12 6 false (0)
]),
.cycle 12 4 false (0),
.cycle 12 18 false (3),
.cycle 12 16 false (2),
.cycle 2 14 false (3),
.cycle 10 13 true (-2),
.split 16 (4,false) (byMove [
.cycle 2 16 false (3),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 6 22 false (3),
.last 17 (4,true),
.cycle 12 6 false (0),
.cycle 12 22 false (4),
.cycle 10 12 true (-2),
.cycle 3 16 false (3),
.cycle 3 14 false (3),
.cycle 16 1 true (0),
.cycle 13 4 true (-2),
.cycle 12 8 false (0),
.last 18 (4,true),
.cycle 11 6 false (1),
.cycle 10 13 true (-2),
.last 17 (4,true),
.cycle 12 6 false (0),
.cycle 12 20 false (4),
.cycle 12 18 false (3),
.cycle 12 16 false (2),
.cycle 10 14 true (-2),
.cycle 16 1 true (0),
.cycle 12 10 false (1)
]),
.cycle 12 8 false (0)
])
theorem kid05_part211_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part211) = true := by rfl

def kid05_part212 : Audit := .split 10 (1,true) (byMove [
.cycle 15 4 false (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 14 (4,true),
.cycle 12 4 false (1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 4 false (0),
.last 14 (4,true),
.cycle 12 4 false (-1),
.last 16 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 14 (4,true),
.cycle 15 4 false (-1),
.cycle 0 14 true (-1),
.cycle 15 4 false (1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 4 false (-1),
.cycle 17 4 false (3),
.cycle 18 4 false (4),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
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
.last 14 (4,false),
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
]),
.cycle 11 4 false (1),
.cycle 14 4 false (0),
.cycle 11 4 false (0),
.cycle 19 4 false (3),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 16 4 false (-2),
.cycle 7 18 false (3),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 13 4 false (-1),
.cycle 19 4 false (3),
.last 12 (4,true),
.cycle 12 4 false (0),
.last 14 (4,true),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 15 4 false (-1),
.last 13 (4,true),
.cycle 12 4 false (0),
.cycle 25 4 false (-1),
.last 12 (4,true),
.cycle 13 4 false (-1)
]),
.cycle 11 4 false (-1),
.cycle 2 10 true (0),
.cycle 1 11 true (0),
.cycle 11 4 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 18 4 false (2),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 24 4 false (0),
.cycle 18 4 false (2),
.cycle 16 4 false (2),
.last 12 (4,false),
.cycle 16 4 false (0),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.cycle 13 4 false (-1),
.cycle 19 4 false (3),
.last 13 (4,false),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 26 4 false (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 12 4 false (0)
])
theorem kid05_part212_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part212) = true := by rfl

def kid05_part213 : Audit := .split 15 (1,true) (byMove [
.cycle 0 27 true (-2),
.cycle 0 28 true (-2),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 0 28 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.cycle 0 28 true (-2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 0 20 true (-2),
.cycle 14 3 false (1),
.cycle 0 23 false (3),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 31 true (-2),
.cycle 0 40 true (-2),
.cycle 1 16 true (-2),
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.last 17 (4,false),
.cycle 9 8 true (-2)
]),
.cycle 0 20 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 1, 15, 1, 64, 15, 64],80⟩,
.cycle 0 27 true (-2),
.cycle 0 35 true (-2),
.cycle 0 25 true (-2),
.split 16 (4,false) (byMove [
.cycle 0 40 true (-2),
.cycle 1 16 true (-2),
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.last 18 (4,true),
.cycle 9 8 true (-2),
.cycle 0 17 true (-2),
.cycle 0 28 true (-2),
.cycle 0 41 true (-2),
.cycle 0 35 true (-2),
.cycle 16 1 true (2),
.cycle 0 20 true (-2),
.cycle 14 3 true (0),
.cycle 0 24 true (-2),
.cycle 0 19 true (-2),
.cycle 0 25 true (-2),
.last 18 (4,true),
.last 24 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 360833, 64, 98689, 128, 256, 32768, 260, 64, 98689, 2, 4, 8, 33153, 1, 1, 262144],[256, 16, 33153, 1, 262144, 33153, 256, 65536, 33153, 4096, 262144, 33153, 4, 16, 33153, 1, 262144, 33153, 262144],287244⟩,
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 360851, 128, 98707, 128, 256, 32768, 260, 128, 98707, 2, 4, 8, 33154, 2, 1, 262144],[256, 16, 33154, 1, 262144, 33154, 256, 65536, 33154, 4096, 262144, 33154, 4, 16, 33154, 1, 262144, 33154, 262144],287244⟩,
.cycle 0 27 true (-2),
.cycle 0 30 true (-2),
.cycle 16 1 true (2),
.cycle 8 20 true (-2)
]),
.cycle 0 19 true (-2),
.cycle 0 22 true (-2),
.cycle 0 31 false (3),
.cycle 10 6 true (-2),
.cycle 0 28 true (-2),
.split 16 (4,true) (byMove [
.cycle 0 25 false (3),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 11 6 true (-2),
.cycle 0 28 true (-2),
.last 18 (4,false),
.cycle 0 21 true (-2),
.cycle 0 18 true (-2),
.last 18 (4,false),
.cycle 0 21 true (-2),
.cycle 14 3 false (1),
.cycle 0 31 false (3),
.cycle 0 30 true (-2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 26 true (-2),
.cycle 2 16 true (-2),
.cycle 15 2 true (0),
.cycle 0 22 true (-2),
.far true 1 ⟨0,[0, 0],[44, 44, 8, 8, 64, 4, 64],[44, 16, 32, 12, 44, 32, 64],80⟩,
.last 18 (4,false),
.cycle 0 22 true (-2)
]),
.cycle 11 6 true (-2),
.cycle 0 36 true (-2),
.cycle 0 38 true (-2),
.cycle 2 14 true (-2),
.cycle 0 29 true (-2),
.split 16 (4,false) (byMove [
.cycle 2 16 true (-2),
.cycle 15 2 true (1),
.cycle 0 22 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 296323, 295298, 34179, 128, 256, 32768, 260, 130, 34179, 2, 4, 8, 33154, 32776, 1, 262144],[256, 1024, 33154, 1, 262144, 33154, 256, 1024, 33154, 4096, 262144, 33154, 4, 16, 33154, 1, 262144, 33154, 262144],352796⟩,
.last 17 (4,true),
.cycle 0 22 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 296321, 1, 1, 128, 256, 32768, 256, 4096, 34177, 128, 256, 8, 33152, 1, 1, 262144],[256, 1024, 128, 1, 262144, 128, 256, 1024, 33152, 4096, 262144, 33152, 256, 1024, 37248, 1, 262144, 37248, 262144],278540⟩,
.cycle 0 28 true (-2),
.cycle 0 35 true (-2),
.cycle 3 14 true (-2),
.cycle 16 1 true (2),
.cycle 0 20 true (-2),
.cycle 0 24 true (-2),
.last 18 (4,true),
.cycle 0 30 true (-2),
.cycle 0 29 true (-2),
.last 17 (4,true),
.cycle 0 30 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 296385, 64, 34241, 128, 256, 32768, 260, 64, 34241, 2, 4, 8, 33216, 1, 1, 262144],[256, 1024, 33216, 1, 262144, 33216, 256, 1024, 33216, 4096, 262144, 33216, 4, 16, 33216, 1, 262144, 33216, 262144],287244⟩,
.cycle 0 36 true (-2),
.cycle 0 38 true (-2),
.cycle 0 30 true (-2),
.cycle 16 1 true (2),
.cycle 0 28 true (-2)
]),
.cycle 0 30 true (-2)
])
theorem kid05_part213_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part213) = true := by rfl

def kid05_part214 : Audit := .cycle 20 1 false (0)
theorem kid05_part214_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part214) = true := by rfl

def kid05_part216 : Audit := .split 17 (4,false) (byMove [
.cycle 11 7 false (1),
.cycle 8 28 false (2),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 15 10 true (-3),
.last 18 (1,true),
.cycle 16 3 false (-2),
.cycle 0 19 false (3),
.cycle 0 19 false (3),
.cycle 15 3 false (-1),
.last 19 (1,true),
.cycle 15 5 false (-1),
.cycle 15 12 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 2 17 false (3),
.last 18 (1,true),
.cycle 15 4 false (-1),
.cycle 14 20 false (2),
.cycle 15 11 false (-1),
.cycle 14 4 false (0)
])
theorem kid05_part216_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part216) = true := by rfl

def kid05_part217 : Audit := .cycle 0 14 true (-1)
theorem kid05_part217_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part217) = true := by rfl

def kid05_part218 : Audit := .cycle 12 1 false (0)
theorem kid05_part218_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part218) = true := by rfl

def kid05_part219 : Audit := .cycle 11 1 false (-1)
theorem kid05_part219_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part219) = true := by rfl

def kid05_part220 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.last 32 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 13 (1,true),
.last 17 (1,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 14 1 true (0),
.cycle 12 3 false (0),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 16 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid05_part220_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part220) = true := by rfl

def kid05_part221 : Audit := .split 12 (4,false) (byMove [
.cycle 11 7 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 16 true (-2),
.last 13 (1,true),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.last 14 (1,true),
.cycle 11 5 false (-1),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[131072, 1024, 2097152, 512, 256, 1024, 4398046511104, 32, 274877906944, 2097152, 1048576, 4194304, 536870944, 131072, 134217728, 8589934592, 4294967296, 17179869184, 4398046511104, 536870912, 0, 134217728, 67108864, 268435456, 5240867914752, 5240867914752, 5222882607104, 134217728, 67108864, 268435456, 4398046511104, 536870912, 4398046511104, 549755813888, 274877906944, 1099511627776, 4398046511104, 536870912, 274877906944, 134217728, 67108864, 268435456, 4398046511104],[1024, 4398046511104, 32, 17179869184, 32, 32, 32, 4398046511104, 131072, 1048576, 131072, 131072, 131072, 4398046511104, 536870912, 4398046511104, 536870912, 536870912, 536870912, 4398046511104, 131072, 1024, 131072, 131072, 5240867914752, 4398046511104, 536870912, 5240330912768, 536870912, 536870912, 536870912, 4398046511104, 536870912, 17179869184, 536870912, 536870912, 536870912, 4398046511104, 131072, 268435456, 131072, 131072, 4398046511104],7945551943744⟩,
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 16 true (-2),
.last 13 (1,true),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part221_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part221) = true := by rfl

def kid05_part222 : Audit := .split 20 (4,false) (byMove [
.cycle 18 7 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 11 10 true (0),
.last 21 (1,true),
.cycle 19 3 false (1),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 18 3 false (2),
.last 22 (1,true),
.cycle 17 5 false (3),
.cycle 11 12 true (-1),
.cycle 21 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 2 false (1),
.cycle 2 20 true (0),
.last 21 (1,true),
.cycle 17 4 false (3),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 18 4 false (2)
])
theorem kid05_part222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part222) = true := by rfl

def kid05_part223 : Audit := .split 11 (1,true) (byMove [
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
.last 18 (4,false),
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
theorem kid05_part223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part223) = true := by rfl

def kid05_part224 : Audit := .split 13 (4,false) (byMove [
.cycle 12 7 false (0),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 12 10 true (-1),
.last 14 (1,true),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 16 1 false (2),
.cycle 12 3 false (0),
.last 15 (1,true),
.cycle 12 5 false (0),
.cycle 12 12 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 12 4 false (0),
.cycle 0 15 true (-1),
.cycle 12 11 false (2),
.cycle 12 4 false (0)
])
theorem kid05_part224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part224) = true := by rfl

def kid05_part225 : Audit := .cycle 0 12 true (0)
theorem kid05_part225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part225) = true := by rfl

def kid05_part226 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.last 23 (1,true),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 12 1 true (2),
.cycle 13 3 false (3),
.last 14 (1,true),
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
theorem kid05_part226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part226) = true := by rfl

def kid05_part227 : Audit := .split 13 (4,false) (byMove [
.cycle 11 7 false (1),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 10 true (-1),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 12 3 true (-1),
.cycle 11 3 false (1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 11 4 false (1),
.cycle 0 15 true (-1),
.cycle 12 3 true (-1),
.cycle 11 4 false (1)
])
theorem kid05_part227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part227) = true := by rfl

def kid05_part228 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (-1),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 22 (4,false),
.last 23 (4,false),
.cycle 9 5 false (1),
.cycle 0 14 true (-1),
.last 16 (4,false),
.cycle 8 5 false (2),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 27 (4,false),
.last 29 (4,false),
.last 17 (4,false),
.cycle 0 14 true (-1),
.last 19 (4,false),
.last 17 (4,false)
])
theorem kid05_part228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part228) = true := by rfl

def kid05_part229 : Audit := .split 15 (4,false) (byMove [
.cycle 13 7 false (-1),
.last 26 (1,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 10 true (-3),
.last 16 (1,true),
.cycle 14 3 false (-2),
.cycle 0 25 false (3),
.cycle 10 6 false (0),
.cycle 13 3 false (-1),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 12 12 true (-4),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 2 15 false (3),
.last 16 (1,true),
.cycle 12 4 false (0),
.cycle 8 13 false (2),
.last 17 (1,true),
.cycle 13 4 false (-1)
])
theorem kid05_part229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part229) = true := by rfl

def kid05_part230 : Audit := .split 22 (4,false) (byMove [
.cycle 20 7 false (2),
.cycle 0 26 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 13 10 true (0),
.last 23 (1,true),
.cycle 21 3 false (1),
.cycle 0 24 true (-1),
.cycle 0 26 true (-1),
.cycle 20 3 false (2),
.last 24 (1,true),
.cycle 19 5 false (3),
.cycle 11 12 true (-1),
.cycle 23 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 2 false (1),
.cycle 2 22 true (-1),
.last 23 (1,true),
.cycle 19 4 false (3),
.cycle 0 24 true (-1),
.cycle 21 4 false (1),
.cycle 20 4 false (2)
])
theorem kid05_part230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part230) = true := by rfl

def kid05_part231 : Audit := .cycle 11 1 false (-1)
theorem kid05_part231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part231) = true := by rfl

def kid05_part232 : Audit := .split 11 (4,false) (byMove [
.cycle 11 7 false (0),
.cycle 0 28 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 12 10 true (-2),
.last 12 (1,true),
.cycle 11 3 false (0),
.cycle 0 24 true (-1),
.cycle 10 2 true (-1),
.cycle 11 3 false (0),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 13 12 true (-3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 2 17 false (3),
.last 12 (1,true),
.cycle 11 4 false (0),
.cycle 0 24 true (-1),
.cycle 10 3 false (0),
.cycle 11 4 false (0)
])
theorem kid05_part232_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part232) = true := by rfl

def kid05_part233 : Audit := .split 12 (4,false) (byMove [
.cycle 11 7 false (-1),
.last 21 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 13 10 true (-3),
.last 13 (1,true),
.cycle 11 3 false (-1),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 14 12 true (-4),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 2 18 false (3),
.last 13 (1,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part233_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part233) = true := by rfl

def kid05_part234 : Audit := .cycle 2 10 true (0)
theorem kid05_part234_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part234) = true := by rfl

def kid05_part235 : Audit := .split 11 (1,true) (byMove [
.last 21 (4,false),
.last 22 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 14 (4,false),
.cycle 0 12 true (0),
.last 21 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.last 17 (4,false),
.last 14 (4,false),
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
theorem kid05_part235_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part235) = true := by rfl

def kid05_part236 : Audit := .split 14 (4,false) (byMove [
.cycle 12 7 false (0),
.last 33 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 10 true (-2),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 16 true (-2),
.cycle 11 10 true (-2),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 11 5 false (1),
.cycle 11 12 true (-3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 2 14 false (3),
.last 15 (1,true),
.cycle 11 4 false (1),
.cycle 7 20 false (3),
.cycle 2 14 false (3),
.cycle 12 4 false (0)
])
theorem kid05_part236_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part236) = true := by rfl

def kid05_part237 : Audit := .cycle 0 12 true (0)
theorem kid05_part237_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part237) = true := by rfl

def kid05_part238 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 18 1 false (-2),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.last 23 (1,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 12 1 true (2),
.cycle 8 7 true (0),
.last 20 (1,true),
.last 13 (1,true),
.cycle 13 12 true (-3),
.cycle 30 1 false (-2),
.cycle 10 3 true (0),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 26 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid05_part238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part238) = true := by rfl

def kid05_part239 : Audit := .split 14 (4,false) (byMove [
.cycle 11 7 false (1),
.last 33 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 10 true (-2),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 16 true (-2),
.cycle 9 7 false (1),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 12 12 true (-3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 2 14 false (3),
.last 15 (1,true),
.cycle 12 4 false (0),
.cycle 8 20 false (3),
.cycle 11 8 false (1),
.cycle 11 4 false (1)
])
theorem kid05_part239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part239) = true := by rfl

def kid05_part215 : Audit := .split 10 (4,true) (byMove [(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part237),(kid05_part238),(kid05_part239)])

theorem kid05_part215_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part215) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part237),(kid05_part238),(kid05_part239)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part216_checked

  · exact kid05_part222_checked

  · exact kid05_part228_checked

  · exact kid05_part234_checked

  · exact kid05_part217_checked

  · exact kid05_part223_checked

  · exact kid05_part229_checked

  · exact kid05_part235_checked

  · exact kid05_part218_checked

  · exact kid05_part224_checked

  · exact kid05_part230_checked

  · exact kid05_part236_checked

  · exact kid05_part219_checked

  · exact kid05_part225_checked

  · exact kid05_part231_checked

  · exact kid05_part237_checked

  · exact kid05_part220_checked

  · exact kid05_part226_checked

  · exact kid05_part232_checked

  · exact kid05_part238_checked

  · exact kid05_part221_checked

  · exact kid05_part227_checked

  · exact kid05_part233_checked

  · exact kid05_part239_checked

def kid05_part240 : Audit := .cycle 11 1 false (-1)
theorem kid05_part240_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part240) = true := by rfl

def kid05_part241 : Audit := .cycle 0 10 true (0)
theorem kid05_part241_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part241) = true := by rfl

def kid05_part242 : Audit := .cycle 1 9 true (1)
theorem kid05_part242_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part242) = true := by rfl

def kid05_part243 : Audit := .cycle 2 8 true (1)
theorem kid05_part243_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part243) = true := by rfl

def kid05_part244 : Audit := .cycle 2 11 true (1)
theorem kid05_part244_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part244) = true := by rfl

def kid05_part245 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 9 3 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 11 8 true (-2),
.cycle 24 1 false (0),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
]),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 9 3 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 19 (1,true),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 6 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
]),
.cycle 12 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1),
.cycle 14 5 false (0),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 5 false (1)
]),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 17 1 false (-1),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 6 false (1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 10 3 true (1),
.cycle 13 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid05_part245_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part245) = true := by rfl

def kid05_part246 : Audit := .cycle 9 1 true (1)
theorem kid05_part246_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part246) = true := by rfl

def kid05_part174 : Audit := .split 9 (5,false) (byMove [(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212),(kid05_part213),(kid05_part214),(kid05_part215),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246)])

theorem kid05_part174_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (kid05_part174) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212),(kid05_part213),(kid05_part214),(kid05_part215),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part175_checked

  · exact kid05_part205_checked

  · exact kid05_part211_checked

  · exact kid05_part241_checked

  · exact kid05_part176_checked

  · exact kid05_part206_checked

  · exact kid05_part212_checked

  · exact kid05_part242_checked

  · exact kid05_part177_checked

  · exact kid05_part207_checked

  · exact kid05_part213_checked

  · exact kid05_part243_checked

  · exact kid05_part178_checked

  · exact kid05_part208_checked

  · exact kid05_part214_checked

  · exact kid05_part244_checked

  · exact kid05_part179_checked

  · exact kid05_part209_checked

  · exact kid05_part215_checked

  · exact kid05_part245_checked

  · exact kid05_part204_checked

  · exact kid05_part210_checked

  · exact kid05_part240_checked

  · exact kid05_part246_checked

def kid05_part247 : Audit := .cycle 0 9 true (0)
theorem kid05_part247_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,0⟩)) (kid05_part247) = true := by rfl

def kid05_part248 : Audit := .cycle 1 8 true (1)
theorem kid05_part248_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,1⟩)) (kid05_part248) = true := by rfl

def kid05_part249 : Audit := .cycle 29 1 false (7)
theorem kid05_part249_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,2⟩)) (kid05_part249) = true := by rfl

def kid05_part250 : Audit := .cycle 16 1 false (2)
theorem kid05_part250_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,3⟩)) (kid05_part250) = true := by rfl

def kid05_part252 : Audit := .cycle 0 10 true (0)
theorem kid05_part252_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part252) = true := by rfl

def kid05_part253 : Audit := .cycle 1 9 true (1)
theorem kid05_part253_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part253) = true := by rfl

def kid05_part254 : Audit := .cycle 20 1 false (2)
theorem kid05_part254_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part254) = true := by rfl

def kid05_part255 : Audit := .cycle 17 1 false (1)
theorem kid05_part255_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part255) = true := by rfl

def kid05_part256 : Audit := .split 12 (4,true) (byMove [
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
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 28 1 false (0),
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
.last 15 (1,true),
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
.split 14 (1,true) (byMove [
.cycle 23 1 false (1),
.cycle 24 1 false (0),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 12 3 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 9 15 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 10 5 false (2),
.last 15 (5,false),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (5,false),
.cycle 24 1 false (2),
.cycle 12 3 false (0),
.cycle 12 4 true (-1),
.cycle 10 21 false (4),
.cycle 30 1 false (0),
.cycle 2 13 false (3),
.cycle 9 17 false (3),
.cycle 20 1 false (0),
.last 15 (5,false)
]),
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
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.cycle 15 1 false (1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 24 1 false (2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 2 13 false (3),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 12 4 true (-1),
.cycle 10 5 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 11 2 true (0),
.split 13 (5,false) (byMove [
.cycle 22 1 false (2),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 9 14 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 10 4 true (0),
.cycle 13 1 true (1),
.cycle 17 1 false (1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 23 1 false (3),
.cycle 10 6 true (0),
.cycle 12 3 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 9 16 true (0),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
])
])
theorem kid05_part256_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part256) = true := by rfl

def kid05_part257 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 13 2 false (1),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 9 2 true (2),
.cycle 10 1 true (2),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 18 9 false (2),
.cycle 10 3 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 19 11 false (2),
.cycle 18 13 false (2)
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
.last 17 (4,true),
.cycle 17 5 false (2),
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
.last 17 (4,true),
.cycle 13 4 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 2 false (1),
.split 13 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
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
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 2 13 true (0),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 16 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 8 4 true (2),
.cycle 10 1 true (2)
])
theorem kid05_part257_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part257) = true := by rfl

def kid05_part258 : Audit := .cycle 0 10 true (0)
theorem kid05_part258_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part258) = true := by rfl

def kid05_part259 : Audit := .cycle 1 9 true (1)
theorem kid05_part259_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part259) = true := by rfl

def kid05_part260 : Audit := .split 22 (5,false) (byMove [
.cycle 0 61 true (0),
.cycle 55 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.split 24 (1,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 37 true (0),
.cycle 0 48 true (0),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 0 29 true (0),
.cycle 6 44 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 1, 64],[4, 2, 6, 1, 64, 16, 64],64⟩,
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 8 17 true (0),
.cycle 0 31 true (0),
.cycle 0 41 true (0),
.cycle 21 4 true (2),
.cycle 31 1 false (7),
.last 25 (4,true),
.last 26 (4,true),
.cycle 2 24 true (0),
.cycle 1 25 true (0),
.cycle 2 40 true (0),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 0 42 true (0)
]),
.cycle 39 1 false (9),
.cycle 35 1 false (9),
.cycle 23 1 false (3),
.cycle 31 1 false (7),
.split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 28 1 false (6),
.cycle 26 1 true (4),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 27 1 false (7),
.cycle 26 1 false (6),
.cycle 28 1 false (8),
.cycle 26 1 true (6),
.last 27 (1,true),
.cycle 31 1 false (7),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 28 1 true (4),
.cycle 30 1 false (8),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 35 1 false (9),
.cycle 38 1 false (10),
.cycle 37 1 true (7),
.cycle 26 1 true (6)
]),
.split 24 (1,true) (byMove [
.cycle 61 1 false (7),
.cycle 47 1 false (9),
.cycle 21 4 false (3),
.cycle 0 36 true (0),
.last 25 (4,true),
.cycle 39 1 false (9),
.cycle 6 48 true (0),
.cycle 7 60 true (0),
.cycle 0 66 true (0),
.cycle 55 1 false (7),
.cycle 25 20 true (2),
.last 29 (4,true),
.cycle 41 1 false (9),
.cycle 18 9 false (3),
.cycle 21 4 false (3),
.cycle 0 111 true (0),
.last 25 (4,true),
.last 26 (4,true),
.cycle 2 26 true (0),
.cycle 1 32 true (0),
.cycle 2 61 true (0),
.cycle 4 68 true (0),
.cycle 0 34 true (0),
.cycle 26 28 true (2)
]),
.cycle 39 1 false (9),
.split 26 (1,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 41 true (0),
.cycle 0 56 true (0),
.cycle 0 31 true (0),
.last 27 (4,true),
.cycle 0 33 true (0),
.cycle 6 48 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 4, 15, 64],[4, 2, 15, 1, 64, 16, 64],64⟩,
.cycle 0 48 true (0),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 8 19 true (0),
.cycle 0 35 true (0),
.cycle 0 47 true (0),
.cycle 21 6 true (1),
.cycle 33 1 false (7),
.last 27 (4,true),
.last 28 (4,true),
.cycle 2 26 true (0),
.cycle 1 27 true (0),
.cycle 2 44 true (0),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 0 53 true (0)
]),
.cycle 23 1 false (1),
.cycle 20 3 false (3),
.cycle 22 1 false (2),
.split 24 (1,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 38 true (0),
.cycle 0 30 true (0),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 0 29 true (0),
.cycle 6 44 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 1, 64],[4, 2, 6, 1, 64, 16, 64],64⟩,
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 8 17 true (0),
.cycle 0 31 true (0),
.cycle 18 10 true (1),
.cycle 0 37 true (0),
.cycle 5 20 true (0),
.last 25 (4,true),
.last 26 (4,true),
.cycle 2 24 true (0),
.cycle 1 25 true (0),
.cycle 2 40 true (0),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 0 42 true (0)
]),
.cycle 1 28 true (0),
.cycle 0 91 true (0),
.cycle 43 1 false (9),
.cycle 26 12 true (4),
.split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 0 59 true (0),
.cycle 37 1 true (5),
.cycle 26 1 true (4),
.cycle 0 26 true (0),
.last 53 (1,true),
.cycle 26 15 true (3),
.cycle 35 1 true (5),
.cycle 9 17 true (0),
.cycle 26 1 true (6),
.last 27 (1,true),
.cycle 28 15 true (3),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 28 1 true (4),
.cycle 26 15 true (4),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 7 44 true (0),
.cycle 0 83 true (0),
.cycle 37 1 true (7),
.cycle 26 1 true (6)
])
])
theorem kid05_part260_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part260) = true := by rfl

def kid05_part261 : Audit := .cycle 29 1 false (7)
theorem kid05_part261_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part261) = true := by rfl

def kid05_part262 : Audit := .cycle 9 1 true (3)
theorem kid05_part262_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part262) = true := by rfl

def kid05_part263 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 34 1 false (6),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 34 1 false (8),
.cycle 24 1 false (6),
.cycle 23 1 false (5),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.last 24 (1,true),
.cycle 29 1 false (5),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 28 1 false (6),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 33 1 false (7),
.cycle 36 1 false (8),
.cycle 35 1 false (7),
.cycle 27 1 false (3)
]),
.cycle 22 1 false (4),
.cycle 9 2 true (3),
.cycle 16 1 false (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 24 (4,true) (byMove [
.cycle 0 55 true (0),
.cycle 0 130 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 0 31 true (0),
.cycle 39 1 false (11),
.cycle 31 1 false (9),
.last 25 (1,true),
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.last 26 (1,true),
.cycle 37 1 false (9),
.cycle 33 1 false (9),
.cycle 25 1 false (3),
.cycle 36 1 false (10),
.cycle 41 1 false (11),
.cycle 2 42 true (0),
.last 25 (1,true),
.cycle 32 1 false (10),
.cycle 5 46 true (0),
.cycle 26 14 true (6),
.cycle 59 16 true (11)
]),
.split 22 (4,true) (byMove [
.cycle 0 40 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
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
.cycle 30 1 false (8),
.cycle 35 1 false (9),
.cycle 2 22 true (0),
.last 23 (1,true),
.cycle 27 1 false (7),
.cycle 0 24 true (0),
.cycle 22 30 true (4),
.cycle 46 1 false (12)
]),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 20 4 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.cycle 8 10 true (2),
.cycle 24 4 false (6),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 6 8 true (2)
]),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 31 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 31 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (1,true),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (6),
.cycle 33 1 false (7),
.cycle 30 1 false (6),
.cycle 33 1 false (7)
]),
.cycle 8 4 true (2),
.split 15 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 0 60 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
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
.cycle 28 1 false (6),
.cycle 16 1 false (0),
.cycle 0 35 true (0),
.last 16 (1,true),
.cycle 29 1 false (7),
.cycle 5 11 true (0),
.cycle 17 6 true (3),
.cycle 25 3 true (5)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part263_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part263) = true := by rfl

def kid05_part265 : Audit := .cycle 2 11 true (1)
theorem kid05_part265_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part265) = true := by rfl

def kid05_part266 : Audit := .cycle 1 12 true (1)
theorem kid05_part266_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part266) = true := by rfl

def kid05_part267 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 19 5 false (1),
.cycle 13 1 true (1),
.cycle 18 4 false (1),
.cycle 16 1 false (0),
.cycle 0 24 true (-2),
.cycle 28 1 false (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 21 9 false (1),
.cycle 13 1 true (1)
])
theorem kid05_part267_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part267) = true := by rfl

def kid05_part268 : Audit := .cycle 0 13 true (0)
theorem kid05_part268_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part268) = true := by rfl

def kid05_part269 : Audit := .split 12 (4,true) (byMove [
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
.cycle 21 7 false (-1),
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
])
theorem kid05_part269_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part269) = true := by rfl

def kid05_part270 : Audit := .cycle 8 4 true (2)
theorem kid05_part270_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part270) = true := by rfl

def kid05_part271 : Audit := .cycle 0 12 true (0)
theorem kid05_part271_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part271) = true := by rfl

def kid05_part272 : Audit := .cycle 1 11 true (1)
theorem kid05_part272_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part272) = true := by rfl

def kid05_part273 : Audit := .split 24 (5,false) (byMove [
.cycle 2 24 true (1),
.cycle 43 1 false (3),
.cycle 53 1 false (1),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 8 17 true (2),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.cycle 9 16 true (2),
.cycle 24 1 true (4),
.cycle 6 19 true (2),
.cycle 7 22 true (2),
.cycle 10 19 true (1),
.cycle 2 25 true (1),
.last 25 (4,true),
.last 26 (4,true),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 6 20 true (2),
.cycle 24 1 true (4)
])
theorem kid05_part273_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part273) = true := by rfl

def kid05_part274 : Audit := .cycle 3 9 true (1)
theorem kid05_part274_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part274) = true := by rfl

def kid05_part275 : Audit := .cycle 9 3 true (2)
theorem kid05_part275_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part275) = true := by rfl

def kid05_part276 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 8 15 true (2),
.cycle 9 4 true (2),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 12 true (2),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part276_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part276) = true := by rfl

def kid05_part277 : Audit := .cycle 6 6 true (2)
theorem kid05_part277_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part277) = true := by rfl

def kid05_part278 : Audit := .cycle 19 7 false (1)
theorem kid05_part278_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part278) = true := by rfl

def kid05_part279 : Audit := .split 13 (5,false) (byMove [
.cycle 0 48 true (-1),
.cycle 24 13 false (2),
.cycle 17 1 false (-1),
.cycle 29 1 false (-1),
.last 14 (4,true),
.cycle 19 1 false (-1),
.cycle 10 4 true (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 19 5 false (1),
.cycle 8 7 true (1),
.cycle 18 4 false (1),
.cycle 0 20 true (-1),
.cycle 14 6 true (-2),
.cycle 0 18 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 19 9 false (2),
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 21 9 false (1),
.last 38 (4,true)
])
theorem kid05_part279_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part279) = true := by rfl

def kid05_part280 : Audit := .cycle 2 12 true (1)
theorem kid05_part280_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part280) = true := by rfl

def kid05_part281 : Audit := .split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 23 5 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 9 5 true (2),
.cycle 8 5 true (2),
.cycle 20 3 false (1),
.cycle 21 7 false (-1),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 6 9 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part281_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part281) = true := by rfl

def kid05_part282 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 23 5 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 30 (5,false),
.cycle 41 1 false (7),
.cycle 9 5 true (2),
.last 14 (5,false),
.cycle 10 4 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 23 5 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.last 14 (5,false)
])
theorem kid05_part282_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part282) = true := by rfl

def kid05_part283 : Audit := .cycle 0 12 true (0)
theorem kid05_part283_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part283) = true := by rfl

def kid05_part284 : Audit := .cycle 1 11 true (1)
theorem kid05_part284_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part284) = true := by rfl

def kid05_part285 : Audit := .cycle 2 10 true (1)
theorem kid05_part285_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part285) = true := by rfl

def kid05_part286 : Audit := .cycle 2 13 true (1)
theorem kid05_part286_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part286) = true := by rfl

def kid05_part287 : Audit := .cycle 6 7 true (2)
theorem kid05_part287_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part287) = true := by rfl

def kid05_part288 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 3 10 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 8 6 true (2),
.cycle 8 10 true (2),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part288_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part288) = true := by rfl

def kid05_part264 : Audit := .split 11 (1,true) (byMove [(kid05_part265),(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273),(kid05_part274),(kid05_part275),(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288)])

theorem kid05_part264_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part264) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part265),(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273),(kid05_part274),(kid05_part275),(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part265_checked

  · exact kid05_part271_checked

  · exact kid05_part277_checked

  · exact kid05_part283_checked

  · exact kid05_part266_checked

  · exact kid05_part272_checked

  · exact kid05_part278_checked

  · exact kid05_part284_checked

  · exact kid05_part267_checked

  · exact kid05_part273_checked

  · exact kid05_part279_checked

  · exact kid05_part285_checked

  · exact kid05_part268_checked

  · exact kid05_part274_checked

  · exact kid05_part280_checked

  · exact kid05_part286_checked

  · exact kid05_part269_checked

  · exact kid05_part275_checked

  · exact kid05_part281_checked

  · exact kid05_part287_checked

  · exact kid05_part270_checked

  · exact kid05_part276_checked

  · exact kid05_part282_checked

  · exact kid05_part288_checked

def kid05_part289 : Audit := .cycle 7 4 true (2)
theorem kid05_part289_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part289) = true := by rfl

def kid05_part290 : Audit := .cycle 0 12 true (0)
theorem kid05_part290_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part290) = true := by rfl

def kid05_part291 : Audit := .cycle 17 1 false (1)
theorem kid05_part291_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part291) = true := by rfl

def kid05_part293 : Audit := .cycle 10 7 false (2)
theorem kid05_part293_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part293) = true := by rfl

def kid05_part294 : Audit := .cycle 9 11 false (3)
theorem kid05_part294_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part294) = true := by rfl

def kid05_part295 : Audit := .cycle 14 1 false (0)
theorem kid05_part295_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part295) = true := by rfl

def kid05_part296 : Audit := .cycle 13 1 false (-1)
theorem kid05_part296_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part296) = true := by rfl

def kid05_part297 : Audit := .cycle 13 1 false (-1)
theorem kid05_part297_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part297) = true := by rfl

def kid05_part298 : Audit := .split 13 (5,false) (byMove [
.cycle 27 1 false (-1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 20 1 false (4),
.last 15 (1,true),
.cycle 17 1 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.cycle 11 3 false (1),
.cycle 28 1 false (0)
])
theorem kid05_part298_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part298) = true := by rfl

def kid05_part299 : Audit := .cycle 16 1 false (2)
theorem kid05_part299_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part299) = true := by rfl

def kid05_part300 : Audit := .split 13 (1,true) (byMove [
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (3),
.cycle 24 1 false (6),
.last 15 (5,false),
.cycle 23 1 false (5),
.cycle 16 1 false (4),
.cycle 24 1 false (6),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 2 20 true (0),
.cycle 1 15 true (0),
.cycle 16 1 false (2),
.cycle 5 24 true (0),
.cycle 14 3 true (2),
.cycle 32 5 true (4)
])
theorem kid05_part300_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part300) = true := by rfl

def kid05_part301 : Audit := .split 14 (5,false) (byMove [
.cycle 43 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 16 (1,true),
.cycle 18 1 false (2),
.cycle 25 1 false (5),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 19 1 false (5),
.last 16 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 16 (1,true),
.cycle 10 8 true (0),
.cycle 26 12 true (0),
.cycle 20 1 false (2),
.cycle 11 4 true (0),
.cycle 35 7 true (3)
])
theorem kid05_part301_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part301) = true := by rfl

def kid05_part302 : Audit := .cycle 17 1 false (3)
theorem kid05_part302_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part302) = true := by rfl

def kid05_part303 : Audit := .cycle 16 1 false (4)
theorem kid05_part303_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part303) = true := by rfl

def kid05_part304 : Audit := .cycle 16 1 false (4)
theorem kid05_part304_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part304) = true := by rfl

def kid05_part305 : Audit := .split 14 (1,true) (byMove [
.cycle 9 13 false (3),
.cycle 24 1 false (0),
.last 16 (5,false),
.cycle 0 25 true (-1),
.cycle 12 3 false (0),
.cycle 16 1 false (0),
.cycle 6 9 false (3),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 17, 32, 17, 1, 17, 64],96⟩,
.last 16 (5,false),
.cycle 9 11 false (3),
.cycle 36 1 false (0),
.cycle 8 11 true (-1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (5,false),
.cycle 19 1 false (1),
.cycle 12 3 false (0),
.cycle 12 4 true (-1),
.cycle 24 1 false (0),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 17, 32, 17, 1, 17, 64],96⟩,
.cycle 10 7 false (2),
.cycle 26 1 false (0),
.cycle 10 9 false (2),
.cycle 32 1 false (0)
])
theorem kid05_part305_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part305) = true := by rfl

def kid05_part306 : Audit := .cycle 16 1 false (0)
theorem kid05_part306_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part306) = true := by rfl

def kid05_part307 : Audit := .cycle 18 1 false (2)
theorem kid05_part307_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part307) = true := by rfl

def kid05_part308 : Audit := .cycle 13 1 false (-1)
theorem kid05_part308_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part308) = true := by rfl

def kid05_part309 : Audit := .cycle 13 1 false (-1)
theorem kid05_part309_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part309) = true := by rfl

def kid05_part310 : Audit := .split 13 (5,false) (byMove [
.cycle 10 8 false (2),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 14 (1,true),
.cycle 21 1 false (3),
.cycle 18 1 false (2),
.cycle 12 2 true (-1),
.cycle 24 1 false (4),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 5 9 false (3),
.cycle 12 4 true (-1),
.cycle 14 13 true (0)
])
theorem kid05_part310_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part310) = true := by rfl

def kid05_part311 : Audit := .cycle 10 6 true (0)
theorem kid05_part311_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part311) = true := by rfl

def kid05_part312 : Audit := .split 13 (1,true) (byMove [
.cycle 26 12 true (0),
.cycle 23 1 false (1),
.last 15 (5,false),
.cycle 0 21 true (0),
.cycle 10 8 true (0),
.cycle 15 1 false (1),
.cycle 6 8 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.last 15 (5,false),
.cycle 24 10 true (0),
.cycle 1 20 true (0),
.cycle 1 15 true (0),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.last 15 (5,false),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 15 true (0),
.cycle 10 6 true (0),
.cycle 5 24 true (0),
.cycle 14 3 true (2),
.cycle 1 15 true (0)
])
theorem kid05_part312_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part312) = true := by rfl

def kid05_part313 : Audit := .cycle 15 1 false (1)
theorem kid05_part313_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part313) = true := by rfl

def kid05_part314 : Audit := .cycle 5 8 true (0)
theorem kid05_part314_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part314) = true := by rfl

def kid05_part315 : Audit := .cycle 14 3 true (2)
theorem kid05_part315_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part315) = true := by rfl

def kid05_part316 : Audit := .split 21 (5,false) (byMove [
.cycle 18 18 true (2),
.last 22 (1,true),
.cycle 29 1 false (-1),
.cycle 0 23 true (0),
.cycle 20 2 true (4),
.cycle 8 14 true (0),
.cycle 0 22 true (0),
.cycle 18 18 true (2),
.cycle 12 24 true (0),
.cycle 18 16 true (2),
.cycle 16 6 true (2),
.cycle 21 1 true (5),
.cycle 6 16 true (0),
.last 22 (1,true),
.last 31 (1,true),
.cycle 12 26 true (0),
.cycle 14 8 true (2),
.cycle 19 3 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 18 20 true (2),
.cycle 14 9 true (2),
.cycle 21 1 true (5)
])
theorem kid05_part316_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part316) = true := by rfl

def kid05_part292 : Audit := .split 12 (4,true) (byMove [(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316)])

theorem kid05_part292_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part292) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part293_checked

  · exact kid05_part299_checked

  · exact kid05_part305_checked

  · exact kid05_part311_checked

  · exact kid05_part294_checked

  · exact kid05_part300_checked

  · exact kid05_part306_checked

  · exact kid05_part312_checked

  · exact kid05_part295_checked

  · exact kid05_part301_checked

  · exact kid05_part307_checked

  · exact kid05_part313_checked

  · exact kid05_part296_checked

  · exact kid05_part302_checked

  · exact kid05_part308_checked

  · exact kid05_part314_checked

  · exact kid05_part297_checked

  · exact kid05_part303_checked

  · exact kid05_part309_checked

  · exact kid05_part315_checked

  · exact kid05_part298_checked

  · exact kid05_part304_checked

  · exact kid05_part310_checked

  · exact kid05_part316_checked

def kid05_part318 : Audit := .cycle 0 20 true (0)
theorem kid05_part318_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part318) = true := by rfl

def kid05_part319 : Audit := .cycle 0 14 true (0)
theorem kid05_part319_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part319) = true := by rfl

def kid05_part320 : Audit := .cycle 21 1 false (1)
theorem kid05_part320_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part320) = true := by rfl

def kid05_part321 : Audit := .cycle 0 16 true (0)
theorem kid05_part321_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part321) = true := by rfl

def kid05_part322 : Audit := .split 13 (4,true) (byMove [
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
.cycle 17 3 true (3),
.cycle 13 2 true (1)
])
theorem kid05_part322_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part322) = true := by rfl

def kid05_part323 : Audit := .cycle 14 1 false (0)
theorem kid05_part323_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part323) = true := by rfl

def kid05_part324 : Audit := .cycle 2 10 true (1)
theorem kid05_part324_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part324) = true := by rfl

def kid05_part325 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 17 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 1 12 true (1),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 17 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 1 12 true (1)
])
theorem kid05_part325_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part325) = true := by rfl

def kid05_part326 : Audit := .cycle 41 1 false (7)
theorem kid05_part326_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part326) = true := by rfl

def kid05_part327 : Audit := .cycle 0 12 true (0)
theorem kid05_part327_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part327) = true := by rfl

def kid05_part328 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 3 false (1),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (7),
.cycle 35 1 false (7),
.cycle 9 3 true (2),
.cycle 9 4 true (2),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 17 3 false (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 3 true (3),
.cycle 9 4 true (2)
])
theorem kid05_part328_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part328) = true := by rfl

def kid05_part329 : Audit := .cycle 8 3 true (2)
theorem kid05_part329_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part329) = true := by rfl

def kid05_part330 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.cycle 16 4 false (0),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 18 5 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 19 9 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 16 4 false (0),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 34 (4,true)
])
theorem kid05_part330_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part330) = true := by rfl

def kid05_part331 : Audit := .split 16 (1,true) (byMove [
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
.last 17 (4,true),
.last 18 (4,true),
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
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid05_part331_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part331) = true := by rfl

def kid05_part332 : Audit := .cycle 2 12 true (1)
theorem kid05_part332_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part332) = true := by rfl

def kid05_part333 : Audit := .cycle 18 1 false (0)
theorem kid05_part333_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part333) = true := by rfl

def kid05_part334 : Audit := .split 13 (4,true) (byMove [
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
.cycle 15 3 true (3),
.cycle 13 8 true (1)
])
theorem kid05_part334_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part334) = true := by rfl

def kid05_part335 : Audit := .split 13 (4,true) (byMove [
.cycle 11 8 true (0),
.cycle 27 12 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 18 1 false (2),
.last 14 (1,true),
.cycle 15 1 false (1),
.cycle 24 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.last 15 (1,true),
.cycle 18 1 false (0),
.cycle 20 1 false (2),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 2 20 true (0),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 5 24 true (0),
.cycle 15 3 true (3),
.cycle 14 3 true (2)
])
theorem kid05_part335_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part335) = true := by rfl

def kid05_part336 : Audit := .cycle 2 10 true (1)
theorem kid05_part336_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part336) = true := by rfl

def kid05_part337 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.cycle 20 13 false (2),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 1 12 true (1)
])
theorem kid05_part337_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part337) = true := by rfl

def kid05_part338 : Audit := .cycle 7 4 true (2)
theorem kid05_part338_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part338) = true := by rfl

def kid05_part339 : Audit := .cycle 0 12 true (0)
theorem kid05_part339_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part339) = true := by rfl

def kid05_part340 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 15 4 false (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 4, 16, 64],[4, 64, 4, 1, 4, 16, 64],64⟩,
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 11 4 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 2 18 true (1),
.cycle 2 12 true (1),
.cycle 15 4 false (1),
.cycle 10 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 3 true (3),
.cycle 11 4 true (3)
])
theorem kid05_part340_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part340) = true := by rfl

def kid05_part341 : Audit := .cycle 8 3 true (2)
theorem kid05_part341_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part341) = true := by rfl

def kid05_part317 : Audit := .split 10 (5,false) (byMove [(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336),(kid05_part337),(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341)])

theorem kid05_part317_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part317) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336),(kid05_part337),(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part318_checked

  · exact kid05_part324_checked

  · exact kid05_part330_checked

  · exact kid05_part336_checked

  · exact kid05_part319_checked

  · exact kid05_part325_checked

  · exact kid05_part331_checked

  · exact kid05_part337_checked

  · exact kid05_part320_checked

  · exact kid05_part326_checked

  · exact kid05_part332_checked

  · exact kid05_part338_checked

  · exact kid05_part321_checked

  · exact kid05_part327_checked

  · exact kid05_part333_checked

  · exact kid05_part339_checked

  · exact kid05_part322_checked

  · exact kid05_part328_checked

  · exact kid05_part334_checked

  · exact kid05_part340_checked

  · exact kid05_part323_checked

  · exact kid05_part329_checked

  · exact kid05_part335_checked

  · exact kid05_part341_checked

def kid05_part342 : Audit := .cycle 0 10 true (0)
theorem kid05_part342_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part342) = true := by rfl

def kid05_part343 : Audit := .cycle 1 9 true (1)
theorem kid05_part343_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part343) = true := by rfl

def kid05_part344 : Audit := .cycle 2 8 true (1)
theorem kid05_part344_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part344) = true := by rfl

def kid05_part345 : Audit := .cycle 2 11 true (1)
theorem kid05_part345_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part345) = true := by rfl

def kid05_part346 : Audit := .cycle 9 1 true (3)
theorem kid05_part346_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part346) = true := by rfl

def kid05_part347 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 36 1 false (4),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 9 3 true (3),
.cycle 1 12 true (1),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 36 1 false (4),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 17 4 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 42 12 true (4),
.cycle 22 12 true (2),
.cycle 9 3 true (3),
.cycle 9 4 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 8 5 true (2),
.cycle 17 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 8 12 true (2),
.cycle 3 8 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 22 (4,true),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 19 7 false (1),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 8 10 true (2),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.last 20 (4,true),
.last 14 (4,true),
.last 18 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.split 16 (1,true) (byMove [
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 8 9 true (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 39 true (0),
.cycle 3 14 true (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 330032, 2048, 65553, 128, 256, 32768, 260, 2048, 65552, 2, 4, 8, 2208, 32, 1, 262144],[256, 16, 2208, 1, 262144, 16, 256, 65536, 2080, 4096, 262144, 65536, 4, 16, 2080, 1, 262144, 16, 262144],287244⟩,
.cycle 0 20 true (0),
.cycle 6 11 true (1),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[128, 256, 8, 16779280, 2048, 1, 8192, 16384, 8, 256, 131072, 16, 8192, 16384, 2097152, 256, 131072, 16, 128, 256, 8, 2048, 2048, 1, 16777216],[256, 2048, 2176, 1, 16777216, 16, 16384, 16, 2048, 1, 16777216, 16, 16384, 16777216, 2048, 262144, 16777216, 4194304, 256, 2048, 2048, 1, 16777216, 16, 16777216],18383630⟩,
.cycle 11 6 true (1),
.cycle 2 17 true (1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 331056, 2048, 65553, 128, 256, 32768, 260, 2048, 66576, 2, 4, 8, 2208, 32, 1, 262144],[256, 1024, 2208, 1, 262144, 16, 256, 1024, 2080, 4096, 262144, 65536, 4, 16, 2080, 1, 262144, 16, 262144],287244⟩,
.last 37 (4,true)
]),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 32, 1, 32, 16, 64],64⟩,
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 8 7 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2),
.last 13 (1,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.cycle 29 1 false (3),
.cycle 8 8 true (2),
.cycle 19 6 false (1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 37 1 false (5),
.cycle 36 1 false (4),
.cycle 9 4 true (3),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 0 26 true (0),
.cycle 9 4 true (3),
.cycle 24 1 false (6),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 32 1 false (4),
.cycle 8 6 true (2),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part347_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part347) = true := by rfl

def kid05_part251 : Audit := .split 9 (4,false) (byMove [(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part289),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part317),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347)])

theorem kid05_part251_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (kid05_part251) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part289),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part317),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part252_checked

  · exact kid05_part258_checked

  · exact kid05_part264_checked

  · exact kid05_part342_checked

  · exact kid05_part253_checked

  · exact kid05_part259_checked

  · exact kid05_part289_checked

  · exact kid05_part343_checked

  · exact kid05_part254_checked

  · exact kid05_part260_checked

  · exact kid05_part290_checked

  · exact kid05_part344_checked

  · exact kid05_part255_checked

  · exact kid05_part261_checked

  · exact kid05_part291_checked

  · exact kid05_part345_checked

  · exact kid05_part256_checked

  · exact kid05_part262_checked

  · exact kid05_part292_checked

  · exact kid05_part346_checked

  · exact kid05_part257_checked

  · exact kid05_part263_checked

  · exact kid05_part317_checked

  · exact kid05_part347_checked

def kid05_part349 : Audit := .cycle 0 10 true (0)
theorem kid05_part349_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part349) = true := by rfl

def kid05_part350 : Audit := .cycle 1 9 true (1)
theorem kid05_part350_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part350) = true := by rfl

def kid05_part351 : Audit := .cycle 20 1 false (2)
theorem kid05_part351_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part351) = true := by rfl

def kid05_part352 : Audit := .cycle 17 1 false (1)
theorem kid05_part352_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part352) = true := by rfl

def kid05_part354 : Audit := .cycle 0 11 true (0)
theorem kid05_part354_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part354) = true := by rfl

def kid05_part355 : Audit := .cycle 1 10 true (1)
theorem kid05_part355_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part355) = true := by rfl

def kid05_part356 : Audit := .cycle 21 1 false (1)
theorem kid05_part356_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part356) = true := by rfl

def kid05_part357 : Audit := .cycle 23 1 false (1)
theorem kid05_part357_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part357) = true := by rfl

def kid05_part358 : Audit := .split 12 (4,true) (byMove [
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
.last 14 (1,true),
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
])
theorem kid05_part358_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part358) = true := by rfl

def kid05_part359 : Audit := .split 12 (4,true) (byMove [
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
.cycle 15 2 false (1),
.cycle 11 2 true (0)
])
theorem kid05_part359_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part359) = true := by rfl

def kid05_part360 : Audit := .cycle 0 11 true (0)
theorem kid05_part360_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part360) = true := by rfl

def kid05_part361 : Audit := .cycle 1 10 true (1)
theorem kid05_part361_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part361) = true := by rfl

def kid05_part362 : Audit := .cycle 35 1 false (7)
theorem kid05_part362_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part362) = true := by rfl

def kid05_part363 : Audit := .cycle 20 1 false (2)
theorem kid05_part363_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part363) = true := by rfl

def kid05_part364 : Audit := .cycle 10 1 true (2)
theorem kid05_part364_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part364) = true := by rfl

def kid05_part365 : Audit := .cycle 9 2 true (2)
theorem kid05_part365_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part365) = true := by rfl

def kid05_part366 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.cycle 15 5 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 10 3 true (1),
.cycle 18 9 false (2),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 15 5 false (1),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 6 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 18 13 false (2),
.last 14 (4,true)
])
theorem kid05_part366_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part366) = true := by rfl

def kid05_part367 : Audit := .split 16 (1,true) (byMove [
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
.last 17 (4,true),
.cycle 17 5 false (2),
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
.last 17 (4,true),
.cycle 13 4 true (0)
])
theorem kid05_part367_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part367) = true := by rfl

def kid05_part368 : Audit := .cycle 0 13 true (0)
theorem kid05_part368_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part368) = true := by rfl

def kid05_part369 : Audit := .cycle 18 1 false (0)
theorem kid05_part369_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part369) = true := by rfl

def kid05_part370 : Audit := .split 12 (4,true) (byMove [
.cycle 11 7 false (1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 23 1 false (3),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 2 18 true (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 22 true (0),
.cycle 13 3 true (1),
.cycle 8 6 true (0)
])
theorem kid05_part370_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part370) = true := by rfl

def kid05_part371 : Audit := .split 12 (4,true) (byMove [
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
.cycle 17 2 false (3),
.cycle 11 2 true (0)
])
theorem kid05_part371_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part371) = true := by rfl

def kid05_part372 : Audit := .cycle 0 11 true (0)
theorem kid05_part372_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part372) = true := by rfl

def kid05_part373 : Audit := .cycle 1 10 true (1)
theorem kid05_part373_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part373) = true := by rfl

def kid05_part374 : Audit := .cycle 2 9 true (1)
theorem kid05_part374_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part374) = true := by rfl

def kid05_part375 : Audit := .cycle 2 12 true (1)
theorem kid05_part375_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part375) = true := by rfl

def kid05_part376 : Audit := .cycle 10 1 true (2)
theorem kid05_part376_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part376) = true := by rfl

def kid05_part377 : Audit := .split 12 (4,true) (byMove [
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
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩,
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 3 true (2),
.cycle 11 2 true (2)
])
theorem kid05_part377_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part377) = true := by rfl

def kid05_part353 : Audit := .split 10 (4,false) (byMove [(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part360),(kid05_part361),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371),(kid05_part372),(kid05_part373),(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part377)])

theorem kid05_part353_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part353) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part360),(kid05_part361),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371),(kid05_part372),(kid05_part373),(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part377)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part354_checked

  · exact kid05_part360_checked

  · exact kid05_part366_checked

  · exact kid05_part372_checked

  · exact kid05_part355_checked

  · exact kid05_part361_checked

  · exact kid05_part367_checked

  · exact kid05_part373_checked

  · exact kid05_part356_checked

  · exact kid05_part362_checked

  · exact kid05_part368_checked

  · exact kid05_part374_checked

  · exact kid05_part357_checked

  · exact kid05_part363_checked

  · exact kid05_part369_checked

  · exact kid05_part375_checked

  · exact kid05_part358_checked

  · exact kid05_part364_checked

  · exact kid05_part370_checked

  · exact kid05_part376_checked

  · exact kid05_part359_checked

  · exact kid05_part365_checked

  · exact kid05_part371_checked

  · exact kid05_part377_checked

def kid05_part378 : Audit := .cycle 13 1 false (1)
theorem kid05_part378_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part378) = true := by rfl

def kid05_part379 : Audit := .cycle 0 10 true (0)
theorem kid05_part379_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part379) = true := by rfl

def kid05_part380 : Audit := .cycle 1 9 true (1)
theorem kid05_part380_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part380) = true := by rfl

def kid05_part381 : Audit := .cycle 35 1 false (9)
theorem kid05_part381_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part381) = true := by rfl

def kid05_part382 : Audit := .cycle 29 1 false (7)
theorem kid05_part382_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part382) = true := by rfl

def kid05_part384 : Audit := .cycle 0 11 true (0)
theorem kid05_part384_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part384) = true := by rfl

def kid05_part385 : Audit := .cycle 1 10 true (1)
theorem kid05_part385_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part385) = true := by rfl

def kid05_part386 : Audit := .split 21 (4,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (3),
.cycle 33 1 false (7),
.last 22 (1,true),
.cycle 26 1 false (4),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.cycle 26 1 false (6),
.last 23 (1,true),
.cycle 33 1 false (5),
.cycle 35 1 false (7),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 20 2 true (2),
.cycle 2 21 true (0),
.last 22 (1,true),
.cycle 27 1 false (5),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 47 1 false (9)
])
theorem kid05_part386_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part386) = true := by rfl

def kid05_part387 : Audit := .split 19 (4,true) (byMove [
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
.last 21 (1,true),
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
theorem kid05_part387_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part387) = true := by rfl

def kid05_part388 : Audit := .split 14 (4,true) (byMove [
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
.last 16 (1,true),
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
theorem kid05_part388_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part388) = true := by rfl

def kid05_part389 : Audit := .cycle 9 2 true (3)
theorem kid05_part389_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part389) = true := by rfl

def kid05_part390 : Audit := .cycle 0 11 true (0)
theorem kid05_part390_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part390) = true := by rfl

def kid05_part391 : Audit := .cycle 1 10 true (1)
theorem kid05_part391_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part391) = true := by rfl

def kid05_part392 : Audit := .split 23 (4,true) (byMove [
.cycle 0 54 true (0),
.cycle 0 127 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.cycle 36 1 false (8),
.cycle 0 29 true (0),
.last 24 (1,true),
.cycle 34 1 false (8),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.cycle 30 1 false (10),
.last 25 (1,true),
.cycle 45 1 false (9),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 38 1 false (8),
.cycle 22 2 true (2),
.cycle 0 29 true (0),
.last 24 (1,true),
.cycle 33 1 false (9),
.cycle 5 19 true (0),
.cycle 26 11 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 16, 64],[4, 64, 20, 1, 32, 32, 64],64⟩
])
theorem kid05_part392_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part392) = true := by rfl

def kid05_part393 : Audit := .split 21 (4,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 91 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 35 1 false (9),
.cycle 27 1 false (7),
.last 22 (1,true),
.cycle 0 26 true (0),
.cycle 33 1 false (9),
.cycle 25 1 false (7),
.cycle 26 1 false (8),
.last 23 (1,true),
.cycle 37 1 false (7),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 29 1 false (7),
.cycle 20 2 true (2),
.cycle 2 36 true (0),
.last 22 (1,true),
.cycle 35 1 false (9),
.cycle 5 40 true (0),
.cycle 3 22 true (0),
.cycle 8 15 true (0)
])
theorem kid05_part393_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part393) = true := by rfl

def kid05_part394 : Audit := .cycle 10 1 true (4)
theorem kid05_part394_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part394) = true := by rfl

def kid05_part395 : Audit := .cycle 9 2 true (3)
theorem kid05_part395_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part395) = true := by rfl

def kid05_part396 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 25 5 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.last 18 (4,true),
.last 26 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 9 4 true (3)
])
theorem kid05_part396_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part396) = true := by rfl

def kid05_part397 : Audit := .cycle 7 5 true (2)
theorem kid05_part397_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part397) = true := by rfl

def kid05_part398 : Audit := .cycle 0 13 true (0)
theorem kid05_part398_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part398) = true := by rfl

def kid05_part399 : Audit := .split 19 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 30 1 false (6),
.last 20 (1,true),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 23 1 false (5),
.last 21 (1,true),
.cycle 30 1 false (4),
.cycle 32 1 false (6),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 2 19 true (0),
.last 20 (1,true),
.cycle 24 1 false (4),
.cycle 0 21 true (0),
.cycle 19 24 true (3),
.cycle 40 1 false (8)
])
theorem kid05_part399_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part399) = true := by rfl

def kid05_part400 : Audit := .split 14 (4,true) (byMove [
.cycle 0 27 true (-1),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 29 1 false (7),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 21 1 false (5),
.cycle 19 1 false (5),
.cycle 20 1 false (6),
.last 16 (1,true),
.cycle 39 1 false (5),
.cycle 33 1 false (7),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 2 19 true (0),
.last 15 (1,true),
.cycle 31 1 false (7),
.cycle 14 32 true (0),
.cycle 17 3 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 48, 1, 32, 32, 64],64⟩
])
theorem kid05_part400_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part400) = true := by rfl

def kid05_part401 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 23 3 false (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 42 1 false (8),
.cycle 37 1 false (9),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 26 3 false (6),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3)
])
theorem kid05_part401_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part401) = true := by rfl

def kid05_part402 : Audit := .cycle 0 11 true (0)
theorem kid05_part402_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part402) = true := by rfl

def kid05_part403 : Audit := .cycle 1 10 true (1)
theorem kid05_part403_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part403) = true := by rfl

def kid05_part404 : Audit := .cycle 2 9 true (1)
theorem kid05_part404_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part404) = true := by rfl

def kid05_part405 : Audit := .cycle 2 12 true (1)
theorem kid05_part405_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part405) = true := by rfl

def kid05_part406 : Audit := .cycle 10 1 true (4)
theorem kid05_part406_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part406) = true := by rfl

def kid05_part407 : Audit := .cycle 9 2 true (3)
theorem kid05_part407_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part407) = true := by rfl

def kid05_part383 : Audit := .split 10 (4,false) (byMove [(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407)])

theorem kid05_part383_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part383) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part384_checked

  · exact kid05_part390_checked

  · exact kid05_part396_checked

  · exact kid05_part402_checked

  · exact kid05_part385_checked

  · exact kid05_part391_checked

  · exact kid05_part397_checked

  · exact kid05_part403_checked

  · exact kid05_part386_checked

  · exact kid05_part392_checked

  · exact kid05_part398_checked

  · exact kid05_part404_checked

  · exact kid05_part387_checked

  · exact kid05_part393_checked

  · exact kid05_part399_checked

  · exact kid05_part405_checked

  · exact kid05_part388_checked

  · exact kid05_part394_checked

  · exact kid05_part400_checked

  · exact kid05_part406_checked

  · exact kid05_part389_checked

  · exact kid05_part395_checked

  · exact kid05_part401_checked

  · exact kid05_part407_checked

def kid05_part408 : Audit := .cycle 9 1 true (3)
theorem kid05_part408_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part408) = true := by rfl

def kid05_part409 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
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
.last 21 (4,false),
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
]),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 19 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 20 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 6 8 true (2)
]),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.last 14 (4,false),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (2),
.cycle 20 3 false (1),
.last 21 (4,false),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 17 4 false (1),
.cycle 2 12 true (1),
.cycle 11 2 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (2)
]),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 18 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 6 8 true (2)
]),
.cycle 6 7 true (2)
])
theorem kid05_part409_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part409) = true := by rfl

def kid05_part410 : Audit := .cycle 7 4 true (2)
theorem kid05_part410_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part410) = true := by rfl

def kid05_part411 : Audit := .cycle 0 12 true (0)
theorem kid05_part411_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part411) = true := by rfl

def kid05_part412 : Audit := .cycle 17 1 false (1)
theorem kid05_part412_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part412) = true := by rfl

def kid05_part414 : Audit := .cycle 0 20 true (0)
theorem kid05_part414_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part414) = true := by rfl

def kid05_part415 : Audit := .cycle 0 14 true (0)
theorem kid05_part415_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part415) = true := by rfl

def kid05_part416 : Audit := .cycle 21 1 false (1)
theorem kid05_part416_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part416) = true := by rfl

def kid05_part417 : Audit := .cycle 0 16 true (0)
theorem kid05_part417_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part417) = true := by rfl

def kid05_part418 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.last 14 (1,true),
.cycle 17 1 false (-1),
.last 25 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩
])
theorem kid05_part418_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part418) = true := by rfl

def kid05_part419 : Audit := .split 12 (4,true) (byMove [
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
.cycle 19 2 false (1),
.cycle 17 2 false (1)
])
theorem kid05_part419_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part419) = true := by rfl

def kid05_part420 : Audit := .cycle 2 10 true (1)
theorem kid05_part420_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part420) = true := by rfl

def kid05_part421 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 43 1 false (9),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 9 3 true (2),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 13 (4,true)
])
theorem kid05_part421_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part421) = true := by rfl

def kid05_part422 : Audit := .split 16 (4,true) (byMove [
.cycle 12 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 17 3 false (-1),
.cycle 25 3 false (3),
.last 17 (1,true),
.cycle 17 3 false (1),
.cycle 0 18 true (0),
.cycle 20 1 false (4),
.cycle 18 3 false (2),
.last 18 (1,true),
.cycle 20 3 false (0),
.cycle 27 3 false (3),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 2 16 true (0),
.last 17 (1,true),
.cycle 19 3 false (1),
.cycle 0 18 true (0),
.cycle 0 39 true (0),
.cycle 12 6 true (0)
])
theorem kid05_part422_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part422) = true := by rfl

def kid05_part423 : Audit := .cycle 0 12 true (0)
theorem kid05_part423_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part423) = true := by rfl

def kid05_part424 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 43 1 false (9),
.cycle 35 1 false (7),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.last 13 (1,true),
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
.cycle 8 6 true (2)
])
theorem kid05_part424_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part424) = true := by rfl

def kid05_part425 : Audit := .cycle 8 3 true (2)
theorem kid05_part425_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part425) = true := by rfl

def kid05_part426 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.cycle 15 5 false (1),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 18 5 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.cycle 15 5 false (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 8 7 true (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 34 22 true (2)
])
theorem kid05_part426_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part426) = true := by rfl

def kid05_part427 : Audit := .split 16 (1,true) (byMove [
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
.last 17 (4,true),
.cycle 19 5 false (4),
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
.last 17 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 32, 32, 128, 256, 8, 256, 32, 4096, 4096],[256, 2048, 4128, 1, 4096, 32, 256, 2048, 32, 1, 4096, 32, 4096],6144⟩
])
theorem kid05_part427_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part427) = true := by rfl

def kid05_part428 : Audit := .cycle 2 12 true (1)
theorem kid05_part428_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part428) = true := by rfl

def kid05_part429 : Audit := .cycle 18 1 false (0)
theorem kid05_part429_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part429) = true := by rfl

def kid05_part430 : Audit := .split 12 (4,true) (byMove [
.cycle 11 7 false (1),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 true (0),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩
])
theorem kid05_part430_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part430) = true := by rfl

def kid05_part431 : Audit := .split 12 (4,true) (byMove [
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
.cycle 8 10 true (0),
.cycle 25 2 false (5)
])
theorem kid05_part431_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part431) = true := by rfl

def kid05_part432 : Audit := .cycle 2 10 true (1)
theorem kid05_part432_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part432) = true := by rfl

def kid05_part433 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,true),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 14 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 13 (4,true)
])
theorem kid05_part433_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part433) = true := by rfl

def kid05_part434 : Audit := .cycle 7 4 true (2)
theorem kid05_part434_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part434) = true := by rfl

def kid05_part435 : Audit := .cycle 0 12 true (0)
theorem kid05_part435_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part435) = true := by rfl

def kid05_part436 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 18 true (2),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 0 20 true (-1),
.cycle 2 12 true (1),
.cycle 15 3 false (1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 8 6 true (2)
])
theorem kid05_part436_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part436) = true := by rfl

def kid05_part437 : Audit := .cycle 8 3 true (2)
theorem kid05_part437_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part437) = true := by rfl

def kid05_part413 : Audit := .split 10 (4,false) (byMove [(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420),(kid05_part421),(kid05_part422),(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427),(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part436),(kid05_part437)])

theorem kid05_part413_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part413) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420),(kid05_part421),(kid05_part422),(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427),(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part436),(kid05_part437)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part414_checked

  · exact kid05_part420_checked

  · exact kid05_part426_checked

  · exact kid05_part432_checked

  · exact kid05_part415_checked

  · exact kid05_part421_checked

  · exact kid05_part427_checked

  · exact kid05_part433_checked

  · exact kid05_part416_checked

  · exact kid05_part422_checked

  · exact kid05_part428_checked

  · exact kid05_part434_checked

  · exact kid05_part417_checked

  · exact kid05_part423_checked

  · exact kid05_part429_checked

  · exact kid05_part435_checked

  · exact kid05_part418_checked

  · exact kid05_part424_checked

  · exact kid05_part430_checked

  · exact kid05_part436_checked

  · exact kid05_part419_checked

  · exact kid05_part425_checked

  · exact kid05_part431_checked

  · exact kid05_part437_checked

def kid05_part438 : Audit := .cycle 16 1 false (4)
theorem kid05_part438_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part438) = true := by rfl

def kid05_part439 : Audit := .cycle 0 10 true (0)
theorem kid05_part439_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part439) = true := by rfl

def kid05_part440 : Audit := .cycle 1 9 true (1)
theorem kid05_part440_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part440) = true := by rfl

def kid05_part441 : Audit := .cycle 2 8 true (1)
theorem kid05_part441_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part441) = true := by rfl

def kid05_part442 : Audit := .cycle 2 11 true (1)
theorem kid05_part442_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part442) = true := by rfl

def kid05_part443 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 19 (4,true),
.cycle 0 16 true (0),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 27 1 false (1),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 30 true (0),
.cycle 0 23 true (0),
.cycle 17 1 false (1),
.cycle 9 3 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 32 1 false (4),
.cycle 15 1 false (-1),
.cycle 8 7 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 9 13 true (3),
.cycle 0 22 true (0),
.cycle 39 1 false (3),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 16, 32, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 9 16 true (3),
.cycle 2 21 true (1),
.cycle 9 18 true (3),
.cycle 8 14 true (2),
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
.split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 19 7 false (1),
.last 20 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.last 18 (4,true),
.last 16 (4,true),
.cycle 2 13 true (1),
.last 19 (4,true),
.last 17 (4,true),
.last 13 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.split 20 (4,true) (byMove [
.cycle 0 98 true (0),
.last 21 (1,true),
.cycle 21 3 false (1),
.last 23 (1,true),
.cycle 32 3 false (2),
.cycle 28 3 false (5),
.cycle 6 15 true (0),
.last 21 (1,true),
.cycle 31 10 true (2),
.cycle 0 88 true (0),
.cycle 0 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 53, 16, 64],[4, 64, 53, 1, 32, 32, 64],64⟩,
.cycle 34 3 false (5),
.last 21 (1,true),
.cycle 21 3 false (1),
.cycle 36 3 false (7),
.cycle 46 3 false (5),
.cycle 25 3 false (6),
.cycle 2 32 true (0),
.last 21 (1,true),
.cycle 2 23 true (0),
.cycle 5 40 true (0),
.cycle 22 5 true (3),
.cycle 8 14 true (0)
]),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 27 1 false (1),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.cycle 28 3 false (5),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.cycle 8 4 true (2),
.last 13 (1,true),
.last 17 (1,true),
.cycle 2 13 true (1),
.cycle 27 1 false (3),
.cycle 15 1 false (-1),
.cycle 8 8 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 8 4 true (2)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part443_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part443) = true := by rfl

def kid05_part444 : Audit := .cycle 9 1 true (3)
theorem kid05_part444_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part444) = true := by rfl

def kid05_part348 : Audit := .split 9 (5,false) (byMove [(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444)])

theorem kid05_part348_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (kid05_part348) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part349_checked

  · exact kid05_part379_checked

  · exact kid05_part409_checked

  · exact kid05_part439_checked

  · exact kid05_part350_checked

  · exact kid05_part380_checked

  · exact kid05_part410_checked

  · exact kid05_part440_checked

  · exact kid05_part351_checked

  · exact kid05_part381_checked

  · exact kid05_part411_checked

  · exact kid05_part441_checked

  · exact kid05_part352_checked

  · exact kid05_part382_checked

  · exact kid05_part412_checked

  · exact kid05_part442_checked

  · exact kid05_part353_checked

  · exact kid05_part383_checked

  · exact kid05_part413_checked

  · exact kid05_part443_checked

  · exact kid05_part378_checked

  · exact kid05_part408_checked

  · exact kid05_part438_checked

  · exact kid05_part444_checked

def kid05_part446 : Audit := .cycle 2 10 true (1)
theorem kid05_part446_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part446) = true := by rfl

def kid05_part447 : Audit := .cycle 11 11 false (1)
theorem kid05_part447_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part447) = true := by rfl

def kid05_part448 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 16 2 true (-3),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 11 21 false (1),
.cycle 1 17 false (3),
.cycle 11 12 false (1),
.cycle 11 15 false (1),
.cycle 17 1 true (-3),
.last 19 (4,true)
]),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 true (-2),
.cycle 0 18 true (-2),
.cycle 11 13 true (-2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 19 (4,true),
.cycle 11 21 false (3),
.cycle 1 17 false (3),
.cycle 11 12 true (-2),
.cycle 11 15 true (-2),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
]),
.cycle 16 1 true (-2),
.cycle 13 4 false (0),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 11 12 false (1),
.last 38 (4,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 11 13 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 11 15 false (1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 2 17 false (3),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 7 23 false (3),
.last 18 (4,true),
.cycle 11 9 false (1)
]),
.cycle 16 1 false (-2),
.cycle 11 20 false (2),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.split 17 (4,false) (byMove [
.cycle 11 13 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 7 22 false (3),
.cycle 11 13 true (-2),
.cycle 11 13 false (1),
.cycle 11 11 false (1),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2),
.cycle 11 8 false (1),
.cycle 20 1 false (-2),
.cycle 15 3 false (-1),
.cycle 11 14 true (-2),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 11 24 false (3),
.cycle 11 20 false (2),
.cycle 2 16 false (3),
.cycle 11 15 true (-2),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
]),
.cycle 16 1 true (-2)
])
theorem kid05_part448_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part448) = true := by rfl

def kid05_part449 : Audit := .cycle 0 12 true (0)
theorem kid05_part449_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part449) = true := by rfl

def kid05_part451 : Audit := .cycle 0 23 false (3)
theorem kid05_part451_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part451) = true := by rfl

def kid05_part452 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 14 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 14 11 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.last 14 (5,false),
.cycle 14 11 false (-1),
.cycle 15 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 17 11 false (2),
.cycle 13 1 true (-1),
.last 14 (5,false)
])
theorem kid05_part452_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part452) = true := by rfl

def kid05_part453 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 13 1 true (-1),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 32 1 false (-2),
.cycle 1 13 false (3),
.cycle 25 1 false (-1),
.cycle 28 1 false (0),
.last 14 (4,false),
.cycle 13 1 true (-1)
])
theorem kid05_part453_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part453) = true := by rfl

def kid05_part454 : Audit := .cycle 0 13 true (0)
theorem kid05_part454_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part454) = true := by rfl

def kid05_part455 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 14 true (-1),
.cycle 12 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.last 14 (5,false),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 11 15 false (3),
.cycle 1 13 false (3),
.cycle 12 11 false (1),
.cycle 12 14 true (-1),
.cycle 13 1 true (-1),
.last 14 (5,false)
])
theorem kid05_part455_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part455) = true := by rfl

def kid05_part456 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 12 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 16 1 true (-2),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 12 20 false (2),
.cycle 1 16 false (3),
.cycle 12 11 false (0),
.cycle 12 14 true (-2),
.last 17 (4,false),
.cycle 16 1 true (-2)
])
theorem kid05_part456_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part456) = true := by rfl

def kid05_part457 : Audit := .cycle 0 12 true (0)
theorem kid05_part457_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part457) = true := by rfl

def kid05_part458 : Audit := .cycle 1 11 true (1)
theorem kid05_part458_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part458) = true := by rfl

def kid05_part459 : Audit := .cycle 24 1 false (2)
theorem kid05_part459_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part459) = true := by rfl

def kid05_part460 : Audit := .cycle 21 1 false (1)
theorem kid05_part460_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part460) = true := by rfl

def kid05_part461 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 15 1 false (1),
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
.cycle 17 1 false (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid05_part461_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part461) = true := by rfl

def kid05_part462 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 18 1 false (0),
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
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid05_part462_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part462) = true := by rfl

def kid05_part463 : Audit := .cycle 15 3 false (0)
theorem kid05_part463_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part463) = true := by rfl

def kid05_part464 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 6 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 14 6 false (1),
.cycle 14 6 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 15 6 false (1),
.last 14 (5,false),
.cycle 14 6 false (-1),
.cycle 14 6 false (-1),
.cycle 16 6 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 5 false (2),
.cycle 18 6 false (0),
.cycle 0 16 true (-1),
.cycle 17 6 false (1),
.cycle 16 6 false (0),
.last 14 (5,false)
])
theorem kid05_part464_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part464) = true := by rfl

def kid05_part465 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 0 39 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 0 19 true (-1),
.cycle 0 22 true (-2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 0 21 true (-1),
.cycle 0 31 false (3),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[96, 352, 32768, 512, 16777216, 128, 256, 64, 320, 32768, 16777216, 8192, 256, 64, 320, 32768, 16777216, 8192, 64, 96, 32768, 512, 16777216, 128, 16777216],[352, 16, 32, 448, 256, 64, 64, 16, 32, 448, 16384, 4096, 64, 4194304, 8388608, 256, 16384, 4096, 96, 16, 32, 320, 256, 64, 16777216],21038096⟩,
.cycle 0 21 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.cycle 0 25 false (3),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.last 14 (4,false),
.cycle 0 27 false (3)
])
theorem kid05_part465_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part465) = true := by rfl

def kid05_part466 : Audit := .cycle 24 1 false (0)
theorem kid05_part466_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part466) = true := by rfl

def kid05_part467 : Audit := .split 13 (4,false) (byMove [
.cycle 12 11 false (0),
.cycle 0 32 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 14 12 true (-2),
.cycle 17 14 true (-2),
.last 15 (5,false),
.cycle 0 28 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 15 14 true (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 2 23 false (3),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 0 28 true (-1),
.cycle 11 3 false (1),
.cycle 12 8 false (0)
])
theorem kid05_part467_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part467) = true := by rfl

def kid05_part468 : Audit := .split 16 (5,false) (byMove [
.cycle 12 11 false (0),
.last 62 (4,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 0 20 true (-2),
.last 18 (4,false),
.cycle 20 1 false (0),
.cycle 0 23 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 52 14 true (0),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 0 20 true (-2),
.cycle 14 3 false (0),
.cycle 12 6 false (0),
.cycle 6 46 false (4),
.cycle 11 6 false (1),
.cycle 12 8 false (0)
])
theorem kid05_part468_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part468) = true := by rfl

def kid05_part469 : Audit := .cycle 0 12 true (0)
theorem kid05_part469_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part469) = true := by rfl

def kid05_part470 : Audit := .cycle 1 11 true (1)
theorem kid05_part470_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part470) = true := by rfl

def kid05_part471 : Audit := .cycle 2 10 true (1)
theorem kid05_part471_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part471) = true := by rfl

def kid05_part472 : Audit := .cycle 2 13 true (1)
theorem kid05_part472_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part472) = true := by rfl

def kid05_part473 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 14 false (1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.last 13 (5,false),
.cycle 16 7 false (1),
.cycle 13 9 false (1),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 11 3 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid05_part473_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part473) = true := by rfl

def kid05_part474 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 17 (4,false),
.cycle 22 1 false (-2),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.last 17 (4,false),
.cycle 15 8 true (-3),
.cycle 2 13 true (1),
.cycle 17 9 false (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid05_part474_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part474) = true := by rfl

def kid05_part450 : Audit := .split 11 (4,true) (byMove [(kid05_part451),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part458),(kid05_part459),(kid05_part460),(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474)])

theorem kid05_part450_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part450) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part451),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part458),(kid05_part459),(kid05_part460),(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part451_checked

  · exact kid05_part457_checked

  · exact kid05_part463_checked

  · exact kid05_part469_checked

  · exact kid05_part452_checked

  · exact kid05_part458_checked

  · exact kid05_part464_checked

  · exact kid05_part470_checked

  · exact kid05_part453_checked

  · exact kid05_part459_checked

  · exact kid05_part465_checked

  · exact kid05_part471_checked

  · exact kid05_part454_checked

  · exact kid05_part460_checked

  · exact kid05_part466_checked

  · exact kid05_part472_checked

  · exact kid05_part455_checked

  · exact kid05_part461_checked

  · exact kid05_part467_checked

  · exact kid05_part473_checked

  · exact kid05_part456_checked

  · exact kid05_part462_checked

  · exact kid05_part468_checked

  · exact kid05_part474_checked

def kid05_part475 : Audit := .cycle 14 3 false (0)
theorem kid05_part475_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part475) = true := by rfl

def kid05_part476 : Audit := .cycle 0 11 true (0)
theorem kid05_part476_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part476) = true := by rfl

def kid05_part477 : Audit := .cycle 1 10 true (1)
theorem kid05_part477_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part477) = true := by rfl

def kid05_part478 : Audit := .cycle 0 23 true (0)
theorem kid05_part478_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part478) = true := by rfl

def kid05_part479 : Audit := .cycle 3 8 true (1)
theorem kid05_part479_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part479) = true := by rfl

def kid05_part481 : Audit := .cycle 0 12 true (0)
theorem kid05_part481_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part481) = true := by rfl

def kid05_part482 : Audit := .cycle 1 11 true (1)
theorem kid05_part482_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part482) = true := by rfl

def kid05_part483 : Audit := .cycle 2 10 true (1)
theorem kid05_part483_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part483) = true := by rfl

def kid05_part484 : Audit := .cycle 2 13 true (1)
theorem kid05_part484_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part484) = true := by rfl

def kid05_part485 : Audit := .split 13 (4,true) (byMove [
.cycle 0 27 false (3),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.last 14 (5,false),
.cycle 17 5 false (1),
.cycle 15 8 false (1),
.last 15 (5,false),
.cycle 28 1 false (0),
.cycle 15 1 false (-1),
.last 18 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 2 true (1),
.last 14 (5,false)
])
theorem kid05_part485_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part485) = true := by rfl

def kid05_part486 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.cycle 22 1 false (-2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 16 7 false (1),
.last 14 (4,true),
.cycle 15 8 true (-3),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 24 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 17 9 false (1),
.cycle 12 1 true (2)
])
theorem kid05_part486_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part486) = true := by rfl

def kid05_part487 : Audit := .cycle 0 12 true (0)
theorem kid05_part487_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part487) = true := by rfl

def kid05_part488 : Audit := .cycle 1 11 true (1)
theorem kid05_part488_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part488) = true := by rfl

def kid05_part489 : Audit := .split 25 (5,false) (byMove [
.cycle 0 30 true (0),
.cycle 1 38 true (1),
.cycle 0 38 true (0),
.cycle 2 42 true (1),
.cycle 14 14 true (1),
.cycle 30 19 false (3),
.cycle 9 17 true (1),
.cycle 7 20 true (1),
.cycle 0 28 true (0),
.cycle 14 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 4, 16, 8192, 16384, 8, 256, 4, 16, 128, 256, 8, 256, 4, 16, 262144],[256, 16, 4, 1, 262144, 16, 16384, 16, 4, 1, 262144, 4, 256, 16, 8, 1, 262144, 8, 262144],262144⟩,
.cycle 8 19 true (1),
.cycle 9 22 true (1),
.cycle 30 23 false (3),
.cycle 9 19 true (1),
.cycle 0 36 true (0),
.last 29 (4,true),
.last 40 (4,true),
.cycle 9 17 true (1),
.cycle 6 23 true (1),
.cycle 0 28 true (0),
.cycle 4 22 true (1),
.cycle 26 14 true (4),
.cycle 6 25 true (1)
])
theorem kid05_part489_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part489) = true := by rfl

def kid05_part490 : Audit := .cycle 0 23 true (0)
theorem kid05_part490_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part490) = true := by rfl

def kid05_part491 : Audit := .cycle 11 1 true (3)
theorem kid05_part491_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part491) = true := by rfl

def kid05_part492 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 18 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,true),
.last 27 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (1),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 8 14 true (1),
.cycle 8 6 true (1),
.last 25 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part492_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part492) = true := by rfl

def kid05_part493 : Audit := .cycle 9 3 true (1)
theorem kid05_part493_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part493) = true := by rfl

def kid05_part494 : Audit := .cycle 16 9 false (2)
theorem kid05_part494_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part494) = true := by rfl

def kid05_part495 : Audit := .cycle 0 14 true (0)
theorem kid05_part495_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part495) = true := by rfl

def kid05_part496 : Audit := .cycle 4 8 true (1)
theorem kid05_part496_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part496) = true := by rfl

def kid05_part497 : Audit := .split 13 (4,true) (byMove [
.cycle 0 48 true (0),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 33 1 false (1),
.cycle 15 1 false (-1),
.last 20 (5,false),
.cycle 6 8 true (1),
.cycle 1 15 true (1),
.last 15 (5,false),
.cycle 2 14 true (1),
.cycle 25 1 false (5),
.last 18 (5,false),
.cycle 45 22 false (0),
.cycle 15 8 false (1),
.last 15 (5,false),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (5,false),
.cycle 17 11 false (2),
.cycle 1 15 true (1),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 14 3 true (2),
.cycle 17 9 false (1)
])
theorem kid05_part497_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part497) = true := by rfl

def kid05_part498 : Audit := .split 12 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.cycle 22 1 false (-2),
.cycle 9 5 true (1),
.last 13 (4,true),
.cycle 16 5 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 0 31 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.last 14 (4,true),
.last 25 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 24 (4,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 11 false (2)
])
theorem kid05_part498_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part498) = true := by rfl

def kid05_part499 : Audit := .cycle 0 12 true (0)
theorem kid05_part499_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part499) = true := by rfl

def kid05_part500 : Audit := .cycle 1 11 true (1)
theorem kid05_part500_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part500) = true := by rfl

def kid05_part501 : Audit := .cycle 2 10 true (1)
theorem kid05_part501_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part501) = true := by rfl

def kid05_part502 : Audit := .cycle 2 13 true (1)
theorem kid05_part502_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part502) = true := by rfl

def kid05_part503 : Audit := .cycle 11 1 true (3)
theorem kid05_part503_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part503) = true := by rfl

def kid05_part504 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 26 1 false (-2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 19 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.last 14 (4,true),
.cycle 6 15 false (4),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part504_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part504) = true := by rfl

def kid05_part480 : Audit := .split 11 (4,false) (byMove [(kid05_part481),(kid05_part482),(kid05_part483),(kid05_part484),(kid05_part485),(kid05_part486),(kid05_part487),(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504)])

theorem kid05_part480_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part480) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part481),(kid05_part482),(kid05_part483),(kid05_part484),(kid05_part485),(kid05_part486),(kid05_part487),(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part481_checked

  · exact kid05_part487_checked

  · exact kid05_part493_checked

  · exact kid05_part499_checked

  · exact kid05_part482_checked

  · exact kid05_part488_checked

  · exact kid05_part494_checked

  · exact kid05_part500_checked

  · exact kid05_part483_checked

  · exact kid05_part489_checked

  · exact kid05_part495_checked

  · exact kid05_part501_checked

  · exact kid05_part484_checked

  · exact kid05_part490_checked

  · exact kid05_part496_checked

  · exact kid05_part502_checked

  · exact kid05_part485_checked

  · exact kid05_part491_checked

  · exact kid05_part497_checked

  · exact kid05_part503_checked

  · exact kid05_part486_checked

  · exact kid05_part492_checked

  · exact kid05_part498_checked

  · exact kid05_part504_checked

def kid05_part505 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.cycle 23 1 false (-3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 16 7 false (1),
.cycle 8 6 true (1),
.cycle 13 16 false (1),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 16 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.last 14 (4,true)
]),
.cycle 16 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.last 15 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.last 24 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 9 4 true (1),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 22 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 9 3 true (1),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 12 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.cycle 23 1 false (-3),
.cycle 9 5 true (1),
.last 13 (4,true),
.cycle 16 5 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 8 9 true (1),
.last 36 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 44 22 false (0),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 11 false (2)
]),
.cycle 44 22 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 19 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (1),
.cycle 8 6 true (1),
.last 33 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 8 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid05_part505_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part505) = true := by rfl

def kid05_part506 : Audit := .cycle 14 5 false (1)
theorem kid05_part506_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part506) = true := by rfl

def kid05_part507 : Audit := .cycle 11 6 false (1)
theorem kid05_part507_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part507) = true := by rfl

def kid05_part508 : Audit := .split 16 (5,false) (byMove [
.cycle 288 116 false (-4),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 11 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 11 12 false (1),
.last 46 (4,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.last 20 (4,true),
.cycle 16 2 true (-3),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 11 14 false (1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 11 15 false (1),
.last 46 (4,true),
.cycle 11 12 false (1),
.last 50 (4,true),
.last 20 (4,true),
.last 19 (4,true)
]),
.cycle 16 1 false (-2),
.cycle 13 4 true (-2),
.cycle 11 7 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.split 17 (4,false) (byMove [
.cycle 11 12 false (1),
.cycle 0 29 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 true (-2),
.cycle 0 21 true (-2),
.cycle 0 29 true (-2),
.cycle 0 23 true (-2),
.cycle 0 25 true (-2),
.last 18 (4,true),
.cycle 12 6 true (-2),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.cycle 0 23 true (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 19 (4,true),
.cycle 0 21 true (-2),
.cycle 14 4 true (-2),
.cycle 11 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 8, 16, 64],[4, 15, 15, 1, 64, 15, 64],64⟩,
.last 18 (4,true),
.cycle 11 9 false (1)
]),
.cycle 12 6 true (-2),
.cycle 13 4 false (0),
.cycle 11 7 false (1),
.cycle 13 6 true (-3),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 11 12 false (1),
.cycle 13 16 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.last 46 (4,true),
.cycle 13 8 true (-3),
.cycle 15 3 false (-1),
.cycle 13 6 true (-3),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 13 5 false (0),
.cycle 11 8 false (1),
.last 56 (4,true),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.last 46 (4,true),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.last 23 (4,true),
.last 18 (4,true),
.cycle 11 9 false (1)
]),
.cycle 16 1 false (-2),
.cycle 9 8 false (2),
.cycle 11 10 false (1),
.cycle 0 25 true (-2),
.cycle 11 9 false (1),
.split 17 (4,false) (byMove [
.cycle 0 29 true (-2),
.cycle 13 8 true (-3),
.cycle 15 3 false (-1),
.cycle 13 6 true (-2),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.cycle 0 29 true (-2),
.cycle 0 23 true (-2),
.cycle 0 25 true (-2),
.last 18 (4,true),
.cycle 8 10 false (2),
.cycle 11 8 false (1),
.cycle 11 11 false (1),
.cycle 15 3 false (-1),
.cycle 11 9 false (1),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.cycle 10 8 false (2),
.cycle 11 10 false (1),
.cycle 68 20 false (0),
.last 18 (4,true),
.cycle 11 12 false (1)
]),
.cycle 11 12 false (1)
])
theorem kid05_part508_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part508) = true := by rfl

def kid05_part509 : Audit := .cycle 2 11 true (1)
theorem kid05_part509_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part509) = true := by rfl

def kid05_part511 : Audit := .cycle 0 15 true (0)
theorem kid05_part511_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part511) = true := by rfl

def kid05_part512 : Audit := .split 13 (4,false) (byMove [
.cycle 83 30 false (0),
.cycle 0 23 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 17 true (-1),
.cycle 12 2 true (-1),
.last 15 (5,false),
.cycle 0 21 true (-1),
.cycle 0 35 true (-2),
.cycle 0 27 true (-2),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 1, 64, 64],[19, 16, 32, 19, 2, 1, 64],96⟩,
.cycle 6 116 false (6),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 17 true (-1),
.cycle 0 25 true (-2),
.cycle 16 43 true (-4),
.cycle 0 21 true (-1),
.cycle 11 3 false (1),
.cycle 18 45 true (-4)
])
theorem kid05_part512_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part512) = true := by rfl

def kid05_part513 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 25 1 false (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 21 1 false (1),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 27 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 0 19 true (-1),
.last 14 (4,false),
.cycle 30 1 false (-2)
])
theorem kid05_part513_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part513) = true := by rfl

def kid05_part514 : Audit := .cycle 16 1 false (0)
theorem kid05_part514_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part514) = true := by rfl

def kid05_part515 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 21 4 true (-2),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.last 14 (5,false),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 23 6 true (-3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 19 false (2),
.cycle 0 17 true (-1),
.cycle 0 33 true (-2),
.cycle 0 19 true (-1),
.cycle 20 1 true (-2),
.last 14 (5,false)
])
theorem kid05_part515_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part515) = true := by rfl

def kid05_part516 : Audit := .split 16 (5,false) (byMove [
.cycle 289 116 false (-5),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 13 4 true (-2),
.cycle 12 7 false (0),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 12 6 true (-2),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 13 6 true (-3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 9 8 false (2),
.cycle 12 10 false (0),
.cycle 0 25 true (-2),
.cycle 12 9 false (0),
.last 17 (4,false),
.cycle 12 12 false (0)
])
theorem kid05_part516_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part516) = true := by rfl

def kid05_part517 : Audit := .cycle 2 11 true (1)
theorem kid05_part517_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part517) = true := by rfl

def kid05_part518 : Audit := .split 13 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 27 true (-2),
.last 15 (5,false),
.cycle 20 1 false (0),
.cycle 22 1 false (0),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 12 2 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 8 6 true (1),
.cycle 17 5 false (0),
.cycle 14 8 false (0),
.last 15 (5,false),
.cycle 23 1 false (-1),
.cycle 16 1 false (0),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 10 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 17 9 false (1)
])
theorem kid05_part518_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part518) = true := by rfl

def kid05_part519 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (3),
.last 15 (4,false),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 13 1 true (1),
.cycle 17 5 false (0),
.last 15 (4,false),
.cycle 0 25 true (-2),
.cycle 28 1 false (0),
.last 17 (4,false),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 14 (4,false),
.cycle 13 1 true (1)
])
theorem kid05_part519_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part519) = true := by rfl

def kid05_part520 : Audit := .cycle 0 13 true (0)
theorem kid05_part520_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part520) = true := by rfl

def kid05_part521 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 30 (5,false),
.cycle 41 1 false (7),
.cycle 13 1 true (3),
.last 14 (5,false),
.cycle 9 5 true (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (4),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid05_part521_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part521) = true := by rfl

def kid05_part522 : Audit := .cycle 8 4 true (1)
theorem kid05_part522_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part522) = true := by rfl

def kid05_part523 : Audit := .cycle 15 3 false (0)
theorem kid05_part523_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part523) = true := by rfl

def kid05_part524 : Audit := .split 13 (4,false) (byMove [
.cycle 19 6 false (-1),
.cycle 27 6 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 15 6 false (1),
.cycle 12 2 true (-1),
.last 15 (5,false),
.cycle 16 6 false (2),
.cycle 14 6 false (0),
.cycle 14 6 false (0),
.cycle 14 6 false (-1),
.cycle 14 6 false (-1),
.cycle 17 6 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 18 6 false (0),
.cycle 14 6 false (0),
.cycle 14 6 false (0),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.cycle 16 6 false (0)
])
theorem kid05_part524_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part524) = true := by rfl

def kid05_part525 : Audit := .split 13 (5,false) (byMove [
.cycle 16 13 true (0),
.cycle 28 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 18 13 true (-1),
.cycle 0 25 true (-2),
.cycle 14 13 true (0),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 20 13 true (-1),
.cycle 20 13 true (0),
.cycle 36 13 true (0),
.cycle 20 13 true (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.cycle 97 13 true (1),
.cycle 14 13 true (0),
.cycle 0 27 true (-2),
.last 14 (4,false),
.cycle 103 13 true (1)
])
theorem kid05_part525_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part525) = true := by rfl

def kid05_part526 : Audit := .cycle 19 1 false (-1)
theorem kid05_part526_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part526) = true := by rfl

def kid05_part527 : Audit := .split 13 (4,false) (byMove [
.cycle 12 11 false (0),
.cycle 50 15 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 12 7 false (1),
.cycle 13 2 true (-1),
.last 15 (5,false),
.cycle 14 13 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.cycle 12 4 false (0),
.cycle 12 7 false (0),
.cycle 12 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 12 10 false (1),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.cycle 12 8 false (0)
])
theorem kid05_part527_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part527) = true := by rfl

def kid05_part528 : Audit := .split 16 (5,false) (byMove [
.cycle 12 11 false (0),
.last 28 (4,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.last 18 (4,false),
.cycle 0 32 true (-2),
.cycle 0 29 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 13 4 false (0),
.cycle 12 7 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 12 10 false (0),
.cycle 14 3 false (0),
.cycle 12 6 false (0),
.cycle 5 12 false (3),
.cycle 11 6 false (1),
.cycle 12 8 false (0)
])
theorem kid05_part528_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part528) = true := by rfl

def kid05_part529 : Audit := .cycle 2 11 true (1)
theorem kid05_part529_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part529) = true := by rfl

def kid05_part530 : Audit := .cycle 10 2 true (1)
theorem kid05_part530_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part530) = true := by rfl

def kid05_part531 : Audit := .cycle 15 5 false (1)
theorem kid05_part531_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part531) = true := by rfl

def kid05_part532 : Audit := .cycle 0 13 true (0)
theorem kid05_part532_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part532) = true := by rfl

def kid05_part533 : Audit := .split 13 (4,false) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (1),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 28 (5,false),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.last 14 (5,false),
.cycle 17 11 false (2),
.cycle 11 5 true (1),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 11 3 true (1),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid05_part533_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part533) = true := by rfl

def kid05_part534 : Audit := .cycle 15 7 false (1)
theorem kid05_part534_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part534) = true := by rfl

def kid05_part510 : Audit := .split 11 (4,true) (byMove [(kid05_part511),(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534)])

theorem kid05_part510_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part510) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part511),(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part511_checked

  · exact kid05_part517_checked

  · exact kid05_part523_checked

  · exact kid05_part529_checked

  · exact kid05_part512_checked

  · exact kid05_part518_checked

  · exact kid05_part524_checked

  · exact kid05_part530_checked

  · exact kid05_part513_checked

  · exact kid05_part519_checked

  · exact kid05_part525_checked

  · exact kid05_part531_checked

  · exact kid05_part514_checked

  · exact kid05_part520_checked

  · exact kid05_part526_checked

  · exact kid05_part532_checked

  · exact kid05_part515_checked

  · exact kid05_part521_checked

  · exact kid05_part527_checked

  · exact kid05_part533_checked

  · exact kid05_part516_checked

  · exact kid05_part522_checked

  · exact kid05_part528_checked

  · exact kid05_part534_checked

def kid05_part535 : Audit := .cycle 14 3 false (0)
theorem kid05_part535_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part535) = true := by rfl

def kid05_part536 : Audit := .cycle 0 11 true (0)
theorem kid05_part536_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part536) = true := by rfl

def kid05_part537 : Audit := .cycle 1 10 true (1)
theorem kid05_part537_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part537) = true := by rfl

def kid05_part538 : Audit := .cycle 2 9 true (1)
theorem kid05_part538_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part538) = true := by rfl

def kid05_part539 : Audit := .cycle 2 12 true (1)
theorem kid05_part539_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part539) = true := by rfl

def kid05_part540 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.cycle 16 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 15 1 false (-1),
.cycle 12 12 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.last 13 (5,false)
]),
.cycle 15 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 24 (5,false) (byMove [
.cycle 2 24 true (1),
.cycle 10 15 true (2),
.cycle 28 21 false (3),
.cycle 0 26 true (0),
.last 25 (4,true),
.cycle 28 23 false (3),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 4, 16, 8192, 16384, 8, 256, 4, 16, 128, 256, 8, 256, 4, 16, 262144],[256, 1024, 4, 1, 262144, 66560, 16384, 65536, 4, 1, 262144, 4, 256, 1024, 8, 1, 262144, 8, 262144],262144⟩,
.cycle 24 1 true (4),
.cycle 28 25 false (3),
.last 26 (4,true),
.cycle 0 85 true (-2),
.cycle 2 25 true (1),
.last 25 (4,true),
.cycle 0 91 true (-2),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 11 14 true (2),
.cycle 24 1 true (4)
]),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 17 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 28 (4,true),
.cycle 8 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (1),
.cycle 17 13 false (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 6 true (1),
.last 36 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
]),
.cycle 15 9 false (2),
.split 13 (4,true) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (2),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.cycle 14 11 false (2),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 28 (5,false),
.cycle 3 11 true (1),
.cycle 19 15 false (3),
.last 14 (5,false),
.cycle 17 11 false (2),
.cycle 12 2 true (2),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.cycle 14 11 false (2),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 11 3 true (2),
.last 14 (5,false)
]),
.cycle 15 5 false (1),
.cycle 2 12 true (1),
.split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.last 20 (5,false),
.cycle 9 5 true (1),
.cycle 15 1 false (-1),
.cycle 16 5 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 32 1 false (6),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 12 2 true (1),
.last 20 (5,false),
.cycle 5 8 true (1),
.cycle 15 1 false (-1),
.cycle 12 12 false (2),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 11 3 true (2),
.cycle 16 11 false (2)
]),
.cycle 15 7 false (1),
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
.last 13 (4,true),
.cycle 16 11 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 27 31 false (5),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 16 13 false (3),
.last 14 (4,true),
.cycle 16 9 false (2),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 16 11 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
])
theorem kid05_part540_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part540) = true := by rfl

def kid05_part541 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 15 false (2),
.last 21 (4,false),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 16 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 16 7 false (1),
.cycle 17 9 false (1),
.last 21 (4,false),
.cycle 2 13 true (1),
.last 15 (4,false),
.cycle 13 14 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 11 2 true (2)
]),
.cycle 15 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 9 4 true (1),
.cycle 17 13 false (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 15 9 false (2),
.cycle 16 11 false (2),
.cycle 15 5 false (1),
.cycle 2 12 true (1),
.split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 21 18 true (0),
.last 21 (4,false),
.cycle 9 5 true (1),
.last 15 (4,false),
.cycle 16 5 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.last 21 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 17 9 false (1),
.last 21 (4,false),
.cycle 5 8 true (1),
.last 15 (4,false),
.cycle 13 14 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 16 11 false (2)
]),
.cycle 15 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 16 11 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 16 13 false (3),
.cycle 17 15 false (3),
.cycle 16 9 false (2),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 16 11 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid05_part541_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part541) = true := by rfl

def kid05_part445 : Audit := .split 10 (1,true) (byMove [(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510),(kid05_part535),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part541)])

theorem kid05_part445_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (kid05_part445) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510),(kid05_part535),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part541)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part446_checked

  · exact kid05_part476_checked

  · exact kid05_part506_checked

  · exact kid05_part536_checked

  · exact kid05_part447_checked

  · exact kid05_part477_checked

  · exact kid05_part507_checked

  · exact kid05_part537_checked

  · exact kid05_part448_checked

  · exact kid05_part478_checked

  · exact kid05_part508_checked

  · exact kid05_part538_checked

  · exact kid05_part449_checked

  · exact kid05_part479_checked

  · exact kid05_part509_checked

  · exact kid05_part539_checked

  · exact kid05_part450_checked

  · exact kid05_part480_checked

  · exact kid05_part510_checked

  · exact kid05_part540_checked

  · exact kid05_part475_checked

  · exact kid05_part505_checked

  · exact kid05_part535_checked

  · exact kid05_part541_checked

def kid05_part543 : Audit := .cycle 9 5 false (2)
theorem kid05_part543_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part543) = true := by rfl

def kid05_part544 : Audit := .cycle 0 16 true (-1)
theorem kid05_part544_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part544) = true := by rfl

def kid05_part545 : Audit := .cycle 14 1 false (0)
theorem kid05_part545_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part545) = true := by rfl

def kid05_part546 : Audit := .cycle 13 1 false (-1)
theorem kid05_part546_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part546) = true := by rfl

def kid05_part548 : Audit := .cycle 0 18 true (-2)
theorem kid05_part548_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part548) = true := by rfl

def kid05_part549 : Audit := .cycle 20 3 false (0)
theorem kid05_part549_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part549) = true := by rfl

def kid05_part550 : Audit := .cycle 15 1 false (-1)
theorem kid05_part550_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part550) = true := by rfl

def kid05_part551 : Audit := .cycle 14 1 false (-2)
theorem kid05_part551_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part551) = true := by rfl

def kid05_part552 : Audit := .cycle 13 1 false (-1)
theorem kid05_part552_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part552) = true := by rfl

def kid05_part553 : Audit := .split 14 (5,false) (byMove [
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
.cycle 17 3 false (1),
.last 17 (4,true),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 20 (4,true),
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 0 20 true (-2),
.cycle 16 3 false (-2),
.last 19 (4,true)
])
theorem kid05_part553_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part553) = true := by rfl

def kid05_part554 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 23 3 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.last 17 (5,false),
.cycle 0 17 true (-1),
.cycle 23 3 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 0 18 true (-1),
.last 17 (5,false),
.cycle 14 3 false (1),
.cycle 17 3 false (0),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 24 3 false (2),
.last 17 (5,false),
.cycle 14 17 true (0),
.cycle 1 16 true (-1),
.cycle 22 3 false (2),
.cycle 25 3 false (3),
.cycle 0 18 true (-1),
.last 17 (5,false)
])
theorem kid05_part554_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part554) = true := by rfl

def kid05_part555 : Audit := .cycle 14 3 false (1)
theorem kid05_part555_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part555) = true := by rfl

def kid05_part556 : Audit := .cycle 0 16 true (-1)
theorem kid05_part556_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part556) = true := by rfl

def kid05_part557 : Audit := .cycle 14 1 false (0)
theorem kid05_part557_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part557) = true := by rfl

def kid05_part558 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 true (0),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 22 3 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 16 1 true (2),
.last 16 (5,false),
.cycle 15 3 false (1),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 14 2 true (0),
.last 16 (5,false),
.cycle 15 17 true (1),
.cycle 1 15 true (-1),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 16 1 true (2),
.last 16 (5,false)
])
theorem kid05_part558_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part558) = true := by rfl

def kid05_part559 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 14 1 false (0),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 18 1 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 15 3 false (1),
.last 17 (4,true),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 16 3 false (0),
.cycle 14 1 false (0),
.cycle 2 14 true (-1),
.last 16 (4,true),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 11 4 true (-1)
])
theorem kid05_part559_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part559) = true := by rfl

def kid05_part560 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 23 3 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 9 9 false (2),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.last 17 (5,false),
.cycle 14 3 false (-1),
.cycle 17 3 false (-2),
.cycle 9 11 false (2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 18 17 true (-2),
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 0 22 true (-2),
.cycle 19 3 false (-1),
.last 17 (5,false)
])
theorem kid05_part560_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part560) = true := by rfl

def kid05_part561 : Audit := .cycle 14 3 false (-1)
theorem kid05_part561_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part561) = true := by rfl

def kid05_part562 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 false (3),
.cycle 25 3 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 22 true (-2),
.last 19 (5,false),
.cycle 0 19 true (-2),
.cycle 25 3 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 0 22 true (-2),
.last 19 (5,false),
.cycle 16 3 false (1),
.cycle 19 3 false (0),
.cycle 0 21 true (-2),
.cycle 19 1 false (-1),
.cycle 28 3 false (2),
.last 19 (5,false),
.cycle 16 17 true (0),
.cycle 1 18 true (-2),
.cycle 24 3 false (2),
.cycle 27 3 false (3),
.last 21 (5,false),
.last 19 (5,false)
])
theorem kid05_part562_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part562) = true := by rfl

def kid05_part563 : Audit := .cycle 14 1 false (-2)
theorem kid05_part563_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part563) = true := by rfl

def kid05_part564 : Audit := .cycle 13 1 false (-1)
theorem kid05_part564_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part564) = true := by rfl

def kid05_part565 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.last 20 (4,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 12 3 false (0),
.cycle 18 1 false (0),
.last 18 (4,true),
.last 15 (4,true),
.cycle 15 3 false (-1),
.last 17 (4,true),
.cycle 15 3 false (-2),
.last 41 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.last 16 (4,true),
.cycle 15 3 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 11 4 false (1)
])
theorem kid05_part565_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part565) = true := by rfl

def kid05_part566 : Audit := .split 16 (4,true) (byMove [
.cycle 23 3 false (1),
.cycle 39 3 false (-1),
.last 18 (5,false),
.cycle 0 18 true (-1),
.cycle 28 7 false (1),
.cycle 17 3 false (-1),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 2 32 true (-1),
.last 17 (5,false),
.cycle 18 3 false (0),
.cycle 12 5 false (1),
.last 18 (5,false),
.cycle 24 3 false (2),
.cycle 10 10 false (2),
.cycle 17 3 false (-1),
.cycle 14 17 true (0),
.cycle 9 21 false (3),
.cycle 2 15 false (3),
.cycle 7 21 false (3),
.cycle 20 14 true (1),
.last 17 (5,false)
])
theorem kid05_part566_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part566) = true := by rfl

def kid05_part567 : Audit := .cycle 9 5 false (2)
theorem kid05_part567_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part567) = true := by rfl

def kid05_part568 : Audit := .cycle 0 16 true (-1)
theorem kid05_part568_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part568) = true := by rfl

def kid05_part569 : Audit := .cycle 17 3 false (1)
theorem kid05_part569_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part569) = true := by rfl

def kid05_part570 : Audit := .split 15 (4,true) (byMove [
.cycle 2 15 false (3),
.cycle 24 3 false (0),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.cycle 18 1 true (-2),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 32 3 false (1),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 16 1 true (2),
.last 16 (5,false),
.cycle 10 7 false (2),
.cycle 18 3 false (-1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 16 3 false (0),
.cycle 11 5 false (1),
.cycle 15 17 true (1),
.cycle 9 25 false (4),
.cycle 0 30 true (-1),
.cycle 37 3 false (1),
.cycle 16 1 true (2),
.last 16 (5,false)
])
theorem kid05_part570_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part570) = true := by rfl

def kid05_part571 : Audit := .split 14 (5,false) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.cycle 18 1 false (-2),
.last 18 (4,true),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 7 17 false (3),
.last 33 (4,true),
.cycle 23 3 false (1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 21 (4,true),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 15 3 false (-1),
.last 27 (4,true),
.last 16 (4,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.last 17 (4,true)
])
theorem kid05_part571_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part571) = true := by rfl

def kid05_part547 : Audit := .split 13 (4,false) (byMove [(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564),(kid05_part565),(kid05_part566),(kid05_part567),(kid05_part568),(kid05_part569),(kid05_part570),(kid05_part571)])

theorem kid05_part547_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part547) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564),(kid05_part565),(kid05_part566),(kid05_part567),(kid05_part568),(kid05_part569),(kid05_part570),(kid05_part571)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part548_checked

  · exact kid05_part554_checked

  · exact kid05_part560_checked

  · exact kid05_part566_checked

  · exact kid05_part549_checked

  · exact kid05_part555_checked

  · exact kid05_part561_checked

  · exact kid05_part567_checked

  · exact kid05_part550_checked

  · exact kid05_part556_checked

  · exact kid05_part562_checked

  · exact kid05_part568_checked

  · exact kid05_part551_checked

  · exact kid05_part557_checked

  · exact kid05_part563_checked

  · exact kid05_part569_checked

  · exact kid05_part552_checked

  · exact kid05_part558_checked

  · exact kid05_part564_checked

  · exact kid05_part570_checked

  · exact kid05_part553_checked

  · exact kid05_part559_checked

  · exact kid05_part565_checked

  · exact kid05_part571_checked

def kid05_part572 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
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
.last 17 (4,true),
.cycle 13 2 true (-2),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 20 3 false (-2),
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 0 20 true (-2),
.last 17 (4,true),
.last 16 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 16 3 false (0),
.cycle 14 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 2 true (-1),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 19 1 false (3),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 15 3 false (1),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 16 (4,true),
.cycle 2 14 true (-1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 11 4 true (-1)
]),
.cycle 15 3 false (1),
.cycle 16 3 false (-2),
.cycle 14 3 false (-1),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[160, 8388768, 32768, 512, 256, 1024, 128, 128, 16512, 32768, 16384, 65536, 128, 128, 16512, 32768, 16384, 65536, 32, 8388640, 32768, 512, 256, 1024, 16777216],[8388768, 32, 32, 1152, 16777216, 128, 128, 32, 32, 1152, 16777216, 8192, 128, 8388608, 8388608, 128, 16777216, 8192, 8388640, 32, 32, 128, 16777216, 128, 16777216],16777216⟩,
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 0 18 true (-2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 8 10 false (2),
.last 15 (4,true),
.cycle 11 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.split 14 (4,false) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 7 17 false (3),
.cycle 33 3 false (-1),
.cycle 3 17 false (3),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 27 3 false (-1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 17 3 false (-1)
]),
.cycle 17 3 false (-1)
])
theorem kid05_part572_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part572) = true := by rfl

def kid05_part573 : Audit := .cycle 19 3 false (3)
theorem kid05_part573_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part573) = true := by rfl

def kid05_part574 : Audit := .cycle 20 3 false (4)
theorem kid05_part574_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part574) = true := by rfl

def kid05_part575 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.split 15 (4,false) (byMove [
.cycle 0 16 false (3),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 0 16 true (-1),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 true (-1),
.cycle 14 2 true (-1),
.cycle 24 3 false (0),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 31 (4,true),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.cycle 15 1 true (-1),
.last 17 (4,true)
]),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 22 3 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 14 2 true (0),
.cycle 0 16 true (0),
.cycle 22 3 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 true (1),
.cycle 14 2 true (0),
.cycle 24 3 false (2),
.cycle 16 3 false (1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.cycle 15 1 true (1),
.cycle 14 2 true (0)
]),
.cycle 14 1 true (0),
.cycle 23 3 false (1),
.cycle 15 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.split 15 (4,false) (byMove [
.cycle 9 8 false (2),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 22 3 false (2),
.cycle 18 1 false (2),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.last 16 (4,true),
.cycle 16 3 false (0),
.last 20 (4,true),
.cycle 16 3 false (-1),
.cycle 24 3 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 2 15 false (3),
.cycle 23 3 false (1),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.last 16 (4,true),
.cycle 11 5 false (1)
]),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.split 15 (4,false) (byMove [
.cycle 22 3 false (2),
.cycle 18 1 false (2),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 7 18 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 15 1 true (1),
.cycle 14 2 true (0),
.cycle 17 3 false (1),
.cycle 12 4 true (0),
.cycle 13 3 false (1),
.cycle 23 3 false (3),
.last 16 (4,true),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 7 20 true (0),
.cycle 15 1 true (1),
.cycle 14 2 true (0)
]),
.cycle 14 1 true (0)
])
theorem kid05_part575_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part575) = true := by rfl

def kid05_part576 : Audit := .cycle 0 14 true (0)
theorem kid05_part576_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part576) = true := by rfl

def kid05_part578 : Audit := .cycle 0 14 true (0)
theorem kid05_part578_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part578) = true := by rfl

def kid05_part579 : Audit := .cycle 20 3 false (2)
theorem kid05_part579_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part579) = true := by rfl

def kid05_part580 : Audit := .cycle 15 1 false (1)
theorem kid05_part580_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part580) = true := by rfl

def kid05_part581 : Audit := .cycle 14 1 false (0)
theorem kid05_part581_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part581) = true := by rfl

def kid05_part582 : Audit := .split 14 (4,false) (byMove [
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
.cycle 14 3 true (-1),
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
theorem kid05_part582_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part582) = true := by rfl

def kid05_part583 : Audit := .split 14 (5,false) (byMove [
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
.last 17 (4,false),
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
theorem kid05_part583_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part583) = true := by rfl

def kid05_part584 : Audit := .cycle 0 14 true (0)
theorem kid05_part584_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part584) = true := by rfl

def kid05_part585 : Audit := .cycle 20 3 false (4)
theorem kid05_part585_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part585) = true := by rfl

def kid05_part586 : Audit := .cycle 15 1 false (3)
theorem kid05_part586_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part586) = true := by rfl

def kid05_part587 : Audit := .cycle 14 1 false (2)
theorem kid05_part587_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part587) = true := by rfl

def kid05_part588 : Audit := .split 14 (4,false) (byMove [
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
.cycle 14 3 true (1),
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
theorem kid05_part588_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part588) = true := by rfl

def kid05_part589 : Audit := .split 14 (5,false) (byMove [
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
.last 17 (4,false),
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
theorem kid05_part589_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part589) = true := by rfl

def kid05_part590 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 22 3 false (2),
.cycle 25 3 false (3),
.cycle 13 5 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 7 22 true (0),
.cycle 24 3 false (2),
.cycle 22 3 false (2),
.cycle 16 1 true (2),
.last 17 (5,false),
.cycle 14 3 true (0),
.cycle 9 8 true (0),
.cycle 0 19 true (0),
.cycle 20 3 false (2),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 16, 64, 64],[19, 19, 32, 19, 1, 2, 64],96⟩,
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 7 18 true (0),
.cycle 7 24 true (0),
.cycle 16 1 true (2),
.last 17 (5,false)
])
theorem kid05_part590_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part590) = true := by rfl

def kid05_part591 : Audit := .cycle 14 3 false (1)
theorem kid05_part591_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part591) = true := by rfl

def kid05_part592 : Audit := .cycle 0 16 true (0)
theorem kid05_part592_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part592) = true := by rfl

def kid05_part593 : Audit := .cycle 14 1 false (0)
theorem kid05_part593_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part593) = true := by rfl

def kid05_part594 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 21 3 false (3),
.cycle 23 3 false (5),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 15 3 false (1),
.cycle 20 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 1 16 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 13 3 false (1),
.cycle 11 4 true (0)
])
theorem kid05_part594_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part594) = true := by rfl

def kid05_part595 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 21 3 false (3),
.last 16 (4,false),
.cycle 18 1 false (2),
.cycle 0 16 true (0),
.cycle 13 2 true (0),
.cycle 15 3 false (1),
.cycle 20 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 2 14 true (0),
.last 16 (4,false),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 16 3 false (0),
.cycle 11 4 true (0)
])
theorem kid05_part595_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part595) = true := by rfl

def kid05_part596 : Audit := .cycle 0 14 true (0)
theorem kid05_part596_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part596) = true := by rfl

def kid05_part597 : Audit := .cycle 1 13 true (0)
theorem kid05_part597_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part597) = true := by rfl

def kid05_part598 : Audit := .cycle 19 3 false (3)
theorem kid05_part598_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part598) = true := by rfl

def kid05_part599 : Audit := .cycle 22 3 false (4)
theorem kid05_part599_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part599) = true := by rfl

def kid05_part600 : Audit := .split 14 (4,false) (byMove [
.cycle 21 3 false (3),
.cycle 23 3 false (3),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.cycle 14 1 true (2),
.last 15 (5,false),
.cycle 16 3 false (2),
.cycle 12 3 true (0),
.last 16 (5,false),
.cycle 22 3 false (4),
.cycle 13 3 true (1),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid05_part600_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part600) = true := by rfl

def kid05_part601 : Audit := .split 14 (5,false) (byMove [
.cycle 21 3 false (3),
.last 16 (4,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 7 17 true (0),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.last 15 (4,false),
.cycle 14 1 true (2),
.cycle 16 3 false (2),
.cycle 12 3 true (0),
.last 21 (4,false),
.cycle 22 3 false (4),
.cycle 11 5 true (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid05_part601_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part601) = true := by rfl

def kid05_part577 : Audit := .split 13 (4,true) (byMove [(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592),(kid05_part593),(kid05_part594),(kid05_part595),(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part599),(kid05_part600),(kid05_part601)])

theorem kid05_part577_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part577) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) 13 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592),(kid05_part593),(kid05_part594),(kid05_part595),(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part599),(kid05_part600),(kid05_part601)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part578_checked

  · exact kid05_part584_checked

  · exact kid05_part590_checked

  · exact kid05_part596_checked

  · exact kid05_part579_checked

  · exact kid05_part585_checked

  · exact kid05_part591_checked

  · exact kid05_part597_checked

  · exact kid05_part580_checked

  · exact kid05_part586_checked

  · exact kid05_part592_checked

  · exact kid05_part598_checked

  · exact kid05_part581_checked

  · exact kid05_part587_checked

  · exact kid05_part593_checked

  · exact kid05_part599_checked

  · exact kid05_part582_checked

  · exact kid05_part588_checked

  · exact kid05_part594_checked

  · exact kid05_part600_checked

  · exact kid05_part583_checked

  · exact kid05_part589_checked

  · exact kid05_part595_checked

  · exact kid05_part601_checked

def kid05_part602 : Audit := .cycle 13 3 false (1)
theorem kid05_part602_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part602) = true := by rfl

def kid05_part603 : Audit := .cycle 16 3 false (0)
theorem kid05_part603_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part603) = true := by rfl

def kid05_part604 : Audit := .cycle 13 3 false (0)
theorem kid05_part604_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part604) = true := by rfl

def kid05_part605 : Audit := .cycle 21 3 false (3)
theorem kid05_part605_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part605) = true := by rfl

def kid05_part606 : Audit := .cycle 13 1 false (-1)
theorem kid05_part606_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part606) = true := by rfl

def kid05_part608 : Audit := .cycle 9 6 false (2)
theorem kid05_part608_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part608) = true := by rfl

def kid05_part609 : Audit := .cycle 7 22 false (3)
theorem kid05_part609_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part609) = true := by rfl

def kid05_part610 : Audit := .cycle 15 1 false (-1)
theorem kid05_part610_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part610) = true := by rfl

def kid05_part611 : Audit := .cycle 14 1 false (-2)
theorem kid05_part611_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part611) = true := by rfl

def kid05_part612 : Audit := .cycle 13 1 false (-1)
theorem kid05_part612_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part612) = true := by rfl

def kid05_part613 : Audit := .split 14 (5,false) (byMove [
.last 37 (4,true),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 17 (4,true),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 13 2 true (-2),
.cycle 16 3 false (0),
.last 17 (4,true),
.cycle 15 3 false (-2),
.last 19 (4,true),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.last 17 (4,true),
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 18 3 false (0),
.cycle 16 3 false (-2),
.last 18 (4,true)
])
theorem kid05_part613_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part613) = true := by rfl

def kid05_part614 : Audit := .cycle 15 3 false (1)
theorem kid05_part614_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part614) = true := by rfl

def kid05_part615 : Audit := .cycle 12 2 true (-1)
theorem kid05_part615_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part615) = true := by rfl

def kid05_part616 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.last 18 (4,true),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 21 1 false (3),
.cycle 17 3 false (1),
.last 18 (4,true),
.cycle 16 3 false (-1),
.last 20 (4,true),
.cycle 16 1 false (-2),
.cycle 13 3 false (0),
.cycle 15 1 false (-1),
.last 18 (4,true),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.cycle 3 19 false (3),
.last 19 (4,true)
])
theorem kid05_part616_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part616) = true := by rfl

def kid05_part617 : Audit := .cycle 21 3 false (3)
theorem kid05_part617_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part617) = true := by rfl

def kid05_part618 : Audit := .split 14 (4,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 18 1 true (0),
.last 15 (5,false),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 16 1 true (2),
.cycle 15 3 false (1),
.cycle 14 3 false (0),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.last 15 (5,false),
.cycle 2 14 true (-1),
.cycle 14 2 true (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 16 1 true (2),
.cycle 11 4 true (-1)
])
theorem kid05_part618_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part618) = true := by rfl

def kid05_part619 : Audit := .cycle 14 3 false (0)
theorem kid05_part619_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part619) = true := by rfl

def kid05_part620 : Audit := .split 16 (4,true) (byMove [
.cycle 9 9 false (2),
.cycle 7 17 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 18 3 false (0),
.cycle 12 5 false (0),
.last 18 (5,false),
.cycle 19 3 false (1),
.cycle 18 5 true (0),
.cycle 17 3 false (-1),
.cycle 14 3 false (-1),
.cycle 17 3 false (-2),
.cycle 20 3 false (0),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 10 8 false (2),
.cycle 15 2 true (-2),
.cycle 17 3 false (-1),
.cycle 5 12 false (3),
.cycle 17 8 true (-1),
.cycle 11 6 false (1)
])
theorem kid05_part620_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part620) = true := by rfl

def kid05_part621 : Audit := .cycle 14 3 false (-1)
theorem kid05_part621_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part621) = true := by rfl

def kid05_part622 : Audit := .cycle 17 3 false (1)
theorem kid05_part622_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part622) = true := by rfl

def kid05_part623 : Audit := .cycle 14 1 false (-2)
theorem kid05_part623_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part623) = true := by rfl

def kid05_part624 : Audit := .cycle 13 1 false (-1)
theorem kid05_part624_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part624) = true := by rfl

def kid05_part625 : Audit := .split 14 (5,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 25 3 false (3),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 15 3 false (-1),
.last 17 (4,true),
.cycle 15 3 false (-2),
.cycle 18 3 false (0),
.cycle 15 1 false (-3),
.cycle 13 2 false (-1),
.cycle 14 1 false (-2),
.cycle 10 6 false (2),
.last 16 (4,true),
.cycle 15 3 false (-1),
.cycle 5 10 false (3),
.last 15 (4,true),
.cycle 11 4 false (1)
])
theorem kid05_part625_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part625) = true := by rfl

def kid05_part626 : Audit := .cycle 10 5 false (2)
theorem kid05_part626_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part626) = true := by rfl

def kid05_part627 : Audit := .split 15 (4,true) (byMove [
.cycle 9 8 false (2),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 9 8 false (2),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 12 4 true (-1),
.last 17 (5,false),
.cycle 23 3 false (3),
.cycle 1 18 true (-1),
.cycle 16 3 false (0),
.cycle 14 3 false (0),
.cycle 16 3 false (-1),
.cycle 19 3 false (1),
.cycle 16 1 false (-2),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 10 7 false (2),
.cycle 14 2 true (-1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 14 16 true (-1),
.cycle 11 5 false (1)
])
theorem kid05_part627_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part627) = true := by rfl

def kid05_part628 : Audit := .cycle 14 3 false (0)
theorem kid05_part628_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part628) = true := by rfl

def kid05_part629 : Audit := .cycle 7 17 false (3)
theorem kid05_part629_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part629) = true := by rfl

def kid05_part630 : Audit := .split 14 (4,true) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 19 1 false (-1),
.cycle 23 1 true (-3),
.cycle 15 3 false (-1),
.cycle 7 17 false (3),
.cycle 12 22 true (-1),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 16 1 true (2),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 13 3 false (0),
.cycle 15 3 false (-1),
.cycle 10 19 false (3),
.cycle 14 2 true (0),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 16 1 true (2),
.cycle 11 7 false (1)
])
theorem kid05_part630_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part630) = true := by rfl

def kid05_part631 : Audit := .cycle 11 3 false (1)
theorem kid05_part631_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part631) = true := by rfl

def kid05_part607 : Audit := .split 13 (4,false) (byMove [(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619),(kid05_part620),(kid05_part621),(kid05_part622),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631)])

theorem kid05_part607_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part607) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619),(kid05_part620),(kid05_part621),(kid05_part622),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part608_checked

  · exact kid05_part614_checked

  · exact kid05_part620_checked

  · exact kid05_part626_checked

  · exact kid05_part609_checked

  · exact kid05_part615_checked

  · exact kid05_part621_checked

  · exact kid05_part627_checked

  · exact kid05_part610_checked

  · exact kid05_part616_checked

  · exact kid05_part622_checked

  · exact kid05_part628_checked

  · exact kid05_part611_checked

  · exact kid05_part617_checked

  · exact kid05_part623_checked

  · exact kid05_part629_checked

  · exact kid05_part612_checked

  · exact kid05_part618_checked

  · exact kid05_part624_checked

  · exact kid05_part630_checked

  · exact kid05_part613_checked

  · exact kid05_part619_checked

  · exact kid05_part625_checked

  · exact kid05_part631_checked

def kid05_part632 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 37 3 false (-3),
.cycle 21 3 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 16 (4,true),
.cycle 13 2 true (-2),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 19 3 false (-1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 6 false (1),
.cycle 9 6 false (2),
.cycle 7 22 false (3),
.cycle 18 3 false (0),
.last 16 (4,true),
.last 16 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.cycle 12 2 true (-1),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.split 14 (4,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 21 3 false (3),
.cycle 24 3 false (4),
.last 17 (4,false),
.cycle 0 16 true (-1),
.last 16 (4,false),
.cycle 15 3 false (1),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 23 3 false (3),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 13 2 true (-1),
.cycle 2 14 true (-1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.last 16 (4,false),
.cycle 11 4 true (-1)
]),
.cycle 14 3 false (0),
.cycle 16 3 false (-2),
.cycle 14 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 7 15 false (3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 17 3 false (1),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 18 3 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 10 6 false (2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 5 10 false (3),
.last 15 (4,true),
.cycle 11 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.cycle 15 3 false (-1),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.split 14 (4,true) (byMove [
.cycle 0 18 true (-1),
.cycle 12 3 false (0),
.last 17 (4,false),
.cycle 18 3 false (0),
.last 16 (4,false),
.cycle 15 3 false (-1),
.cycle 7 17 false (3),
.cycle 33 3 false (-1),
.last 17 (4,false),
.cycle 0 16 true (-1),
.last 16 (4,false),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.cycle 12 3 false (0),
.last 17 (4,false),
.cycle 17 3 false (1),
.last 16 (4,false),
.cycle 15 3 false (-1),
.cycle 27 3 false (-1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 16 (4,false),
.cycle 17 3 false (-1)
]),
.cycle 11 3 false (1)
])
theorem kid05_part632_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part632) = true := by rfl

def kid05_part633 : Audit := .cycle 2 12 true (0)
theorem kid05_part633_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part633) = true := by rfl

def kid05_part634 : Audit := .cycle 1 13 true (0)
theorem kid05_part634_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part634) = true := by rfl

def kid05_part635 : Audit := .cycle 13 3 false (1)
theorem kid05_part635_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part635) = true := by rfl

def kid05_part636 : Audit := .cycle 0 14 true (0)
theorem kid05_part636_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part636) = true := by rfl

def kid05_part638 : Audit := .cycle 20 3 false (2)
theorem kid05_part638_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part638) = true := by rfl

def kid05_part639 : Audit := .split 15 (4,false) (byMove [
.cycle 22 3 false (2),
.cycle 14 2 true (0),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 23 3 false (1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 7 18 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 15 1 true (1),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 12 4 true (0),
.last 17 (5,false),
.cycle 23 3 false (3),
.cycle 0 20 true (-1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 7 20 true (0),
.cycle 15 1 true (1),
.last 16 (5,false)
])
theorem kid05_part639_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part639) = true := by rfl

def kid05_part640 : Audit := .split 15 (5,false) (byMove [
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
.last 18 (4,false),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 30 3 false (0),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.last 16 (4,false),
.cycle 15 1 true (-1)
])
theorem kid05_part640_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part640) = true := by rfl

def kid05_part641 : Audit := .cycle 0 15 true (0)
theorem kid05_part641_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part641) = true := by rfl

def kid05_part642 : Audit := .split 15 (4,false) (byMove [
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
.cycle 10 10 false (2),
.cycle 16 3 false (-1),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.cycle 13 17 false (3),
.cycle 1 15 false (3),
.cycle 21 3 false (1),
.cycle 24 3 false (2),
.cycle 15 1 true (-1),
.last 16 (5,false)
])
theorem kid05_part642_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part642) = true := by rfl

def kid05_part643 : Audit := .cycle 14 3 false (0)
theorem kid05_part643_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part643) = true := by rfl

def kid05_part644 : Audit := .cycle 0 14 true (0)
theorem kid05_part644_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part644) = true := by rfl

def kid05_part645 : Audit := .cycle 7 16 true (0)
theorem kid05_part645_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part645) = true := by rfl

def kid05_part646 : Audit := .cycle 20 3 false (2)
theorem kid05_part646_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part646) = true := by rfl

def kid05_part647 : Audit := .cycle 18 3 false (2)
theorem kid05_part647_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part647) = true := by rfl

def kid05_part648 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 17 1 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 7 20 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.cycle 14 1 true (2),
.last 15 (5,false),
.cycle 10 9 true (0),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 3 false (2),
.cycle 19 1 false (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 7 16 true (0),
.cycle 7 22 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid05_part648_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part648) = true := by rfl

def kid05_part649 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.last 15 (4,false),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 7 20 true (0),
.cycle 22 3 false (2),
.cycle 20 3 false (2),
.last 15 (4,false),
.cycle 14 1 true (2),
.last 17 (4,false),
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 18 3 false (2),
.last 15 (4,false),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 7 16 true (0),
.cycle 7 22 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid05_part649_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part649) = true := by rfl

def kid05_part650 : Audit := .cycle 15 3 false (1)
theorem kid05_part650_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part650) = true := by rfl

def kid05_part651 : Audit := .cycle 12 2 true (0)
theorem kid05_part651_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part651) = true := by rfl

def kid05_part652 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 3 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.last 18 (4,false),
.cycle 16 3 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 3 false (1),
.last 18 (4,false),
.cycle 16 3 false (-1),
.last 20 (4,false),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.last 18 (4,false),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 19 3 false (1),
.last 16 (4,false),
.cycle 20 3 false (0)
])
theorem kid05_part652_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part652) = true := by rfl

def kid05_part653 : Audit := .cycle 21 3 false (3)
theorem kid05_part653_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part653) = true := by rfl

def kid05_part654 : Audit := .split 15 (4,false) (byMove [
.cycle 9 8 false (2),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 12 4 true (-1),
.last 17 (5,false),
.cycle 23 3 false (3),
.cycle 14 2 true (-1),
.cycle 16 3 false (0),
.cycle 13 6 false (1),
.cycle 16 3 false (-1),
.cycle 19 3 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (5,false),
.cycle 10 7 false (2),
.cycle 13 5 false (1),
.cycle 16 3 false (0),
.cycle 7 19 false (3),
.cycle 13 3 false (1),
.cycle 11 5 false (1)
])
theorem kid05_part654_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part654) = true := by rfl

def kid05_part655 : Audit := .cycle 14 3 false (0)
theorem kid05_part655_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part655) = true := by rfl

def kid05_part656 : Audit := .cycle 0 14 true (0)
theorem kid05_part656_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part656) = true := by rfl

def kid05_part657 : Audit := .cycle 1 13 true (0)
theorem kid05_part657_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part657) = true := by rfl

def kid05_part658 : Audit := .cycle 2 12 true (0)
theorem kid05_part658_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part658) = true := by rfl

def kid05_part659 : Audit := .cycle 7 18 true (0)
theorem kid05_part659_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part659) = true := by rfl

def kid05_part660 : Audit := .split 14 (4,false) (byMove [
.cycle 2 14 true (0),
.cycle 14 2 true (1),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 11 4 true (0),
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
.cycle 13 3 true (1),
.cycle 13 5 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.cycle 14 1 true (2),
.last 15 (5,false)
])
theorem kid05_part660_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part660) = true := by rfl

def kid05_part661 : Audit := .split 14 (5,false) (byMove [
.cycle 2 14 true (0),
.last 16 (4,false),
.cycle 15 3 false (1),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.cycle 11 4 true (0),
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
.cycle 11 5 true (0),
.cycle 11 7 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 7 19 true (0),
.last 15 (4,false),
.cycle 14 1 true (2)
])
theorem kid05_part661_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part661) = true := by rfl

def kid05_part637 : Audit := .split 13 (4,true) (byMove [(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650),(kid05_part651),(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661)])

theorem kid05_part637_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part637) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) 13 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650),(kid05_part651),(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part638_checked

  · exact kid05_part644_checked

  · exact kid05_part650_checked

  · exact kid05_part656_checked

  · exact kid05_part639_checked

  · exact kid05_part645_checked

  · exact kid05_part651_checked

  · exact kid05_part657_checked

  · exact kid05_part640_checked

  · exact kid05_part646_checked

  · exact kid05_part652_checked

  · exact kid05_part658_checked

  · exact kid05_part641_checked

  · exact kid05_part647_checked

  · exact kid05_part653_checked

  · exact kid05_part659_checked

  · exact kid05_part642_checked

  · exact kid05_part648_checked

  · exact kid05_part654_checked

  · exact kid05_part660_checked

  · exact kid05_part643_checked

  · exact kid05_part649_checked

  · exact kid05_part655_checked

  · exact kid05_part661_checked

def kid05_part662 : Audit := .cycle 11 2 true (0)
theorem kid05_part662_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part662) = true := by rfl

def kid05_part542 : Audit := .split 12 (1,true) (byMove [(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part546),(kid05_part547),(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part662)])

theorem kid05_part542_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (kid05_part542) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part546),(kid05_part547),(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part662)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part543_checked

  · exact kid05_part573_checked

  · exact kid05_part603_checked

  · exact kid05_part633_checked

  · exact kid05_part544_checked

  · exact kid05_part574_checked

  · exact kid05_part604_checked

  · exact kid05_part634_checked

  · exact kid05_part545_checked

  · exact kid05_part575_checked

  · exact kid05_part605_checked

  · exact kid05_part635_checked

  · exact kid05_part546_checked

  · exact kid05_part576_checked

  · exact kid05_part606_checked

  · exact kid05_part636_checked

  · exact kid05_part547_checked

  · exact kid05_part577_checked

  · exact kid05_part607_checked

  · exact kid05_part637_checked

  · exact kid05_part572_checked

  · exact kid05_part602_checked

  · exact kid05_part632_checked

  · exact kid05_part662_checked

def kid05_part663 : Audit := .cycle 0 11 true (0)
theorem kid05_part663_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,2⟩)) (kid05_part663) = true := by rfl

def kid05_part664 : Audit := .cycle 14 1 false (0)
theorem kid05_part664_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,3⟩)) (kid05_part664) = true := by rfl

def kid05_part666 : Audit := .cycle 0 13 true (0)
theorem kid05_part666_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part666) = true := by rfl

def kid05_part668 : Audit := .cycle 0 15 true (-1)
theorem kid05_part668_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part668) = true := by rfl

def kid05_part669 : Audit := .cycle 0 38 true (-2)
theorem kid05_part669_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part669) = true := by rfl

def kid05_part670 : Audit := .cycle 12 1 false (0)
theorem kid05_part670_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part670) = true := by rfl

def kid05_part671 : Audit := .cycle 11 1 false (-1)
theorem kid05_part671_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part671) = true := by rfl

def kid05_part672 : Audit := .split 28 (4,true) (byMove [
.cycle 1 53 false (3),
.cycle 128 47 true (-2),
.cycle 28 15 false (0),
.cycle 14 15 false (2),
.cycle 1 29 false (3),
.last 29 (5,false),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 16, 32, 18, 18, 16, 64],96⟩,
.cycle 21 45 true (-3),
.last 30 (5,false),
.cycle 0 30 true (-3),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 16, 32, 18, 18, 16, 64],96⟩,
.last 123 (5,false),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 2, 64, 64],[19, 16, 32, 19, 1, 16, 64],96⟩,
.cycle 7 23 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M284.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M284.never m hm),
.cycle 28 13 false (0),
.far true 1 ⟨0,[0, 0],[16, 18, 26, 8, 2, 64, 64],[18, 16, 32, 18, 16, 16, 64],96⟩,
.last 29 (5,false),
.cycle 1 39 false (3),
.cycle 1 41 false (3),
.cycle 13 59 true (-4),
.cycle 1 43 false (5),
.cycle 1 35 false (3),
.cycle 27 2 true (0)
])
theorem kid05_part672_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part672) = true := by rfl

def kid05_part673 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.last 28 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 62 28 false (0),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 32 true (-2),
.cycle 0 19 true (-1),
.last 38 (4,true),
.last 38 (4,true),
.last 18 (4,true),
.cycle 12 1 false (-2),
.last 20 (4,true),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 0 30 true (-2),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.last 15 (4,true)
])
theorem kid05_part673_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part673) = true := by rfl

def kid05_part674 : Audit := .cycle 0 13 true (0)
theorem kid05_part674_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part674) = true := by rfl

def kid05_part675 : Audit := .cycle 0 18 true (-1)
theorem kid05_part675_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part675) = true := by rfl

def kid05_part676 : Audit := .cycle 0 13 true (0)
theorem kid05_part676_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part676) = true := by rfl

def kid05_part677 : Audit := .cycle 11 1 false (1)
theorem kid05_part677_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part677) = true := by rfl

def kid05_part678 : Audit := .cycle 0 15 true (0)
theorem kid05_part678_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part678) = true := by rfl

def kid05_part679 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 44 true (-2),
.cycle 11 1 false (1),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 15 1 false (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 17 true (0),
.cycle 8 6 true (0),
.last 25 (4,true),
.cycle 0 26 true (0),
.cycle 12 1 false (0),
.cycle 0 28 true (-1),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part679_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part679) = true := by rfl

def kid05_part680 : Audit := .split 24 (4,true) (byMove [
.cycle 6 45 false (3),
.cycle 52 37 true (-4),
.cycle 78 1 false (-4),
.cycle 13 15 false (2),
.cycle 1 25 false (3),
.last 25 (5,false),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 2, 64, 64],[19, 1, 32, 19, 19, 16, 64],96⟩,
.cycle 12 40 false (4),
.last 26 (5,false),
.cycle 0 26 true (-3),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 2, 64, 64],[19, 1, 32, 19, 19, 16, 64],96⟩,
.cycle 54 39 true (-4),
.cycle 6 21 false (3),
.cycle 7 19 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M288.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M288.never m hm),
.cycle 75 1 false (-5),
.cycle 70 71 true (-4),
.last 25 (5,false),
.cycle 6 31 false (3),
.cycle 12 38 false (4),
.cycle 12 36 false (4),
.cycle 19 24 true (-1),
.cycle 12 40 false (4),
.cycle 23 2 true (0)
])
theorem kid05_part680_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part680) = true := by rfl

def kid05_part681 : Audit := .split 22 (4,true) (byMove [
.cycle 7 41 false (3),
.cycle 42 57 true (-5),
.cycle 7 32 false (3),
.cycle 12 15 false (2),
.cycle 1 23 false (3),
.last 23 (5,false),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 2, 32, 18, 18, 16, 64],96⟩,
.cycle 41 54 false (1),
.last 24 (5,false),
.cycle 0 24 true (-3),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 2, 32, 18, 18, 16, 64],96⟩,
.cycle 44 65 true (-5),
.cycle 7 37 false (3),
.cycle 7 17 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M291.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M291.never m hm),
.cycle 7 30 false (3),
.cycle 138 86 false (-4),
.last 23 (5,false),
.cycle 7 27 false (3),
.cycle 7 19 false (3),
.cycle 39 52 false (1),
.cycle 17 22 true (-1),
.cycle 7 21 false (3),
.cycle 21 2 true (0)
])
theorem kid05_part681_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part681) = true := by rfl

def kid05_part682 : Audit := .split 16 (5,false) (byMove [
.cycle 0 21 true (-1),
.cycle 1 32 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 34 (4,true),
.cycle 16 1 false (0),
.cycle 13 4 true (0),
.cycle 0 24 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 0 21 true (-1),
.cycle 0 23 true (-1),
.cycle 13 4 false (2),
.last 28 (4,true),
.cycle 11 6 true (-1),
.cycle 17 1 false (-1),
.cycle 9 16 false (2),
.cycle 16 1 false (0),
.cycle 7 24 false (3),
.last 20 (4,true),
.cycle 0 19 true (-1),
.cycle 0 26 true (-1),
.cycle 9 8 true (-1),
.last 19 (4,true)
])
theorem kid05_part682_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part682) = true := by rfl

def kid05_part683 : Audit := .cycle 11 1 false (-1)
theorem kid05_part683_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part683) = true := by rfl

def kid05_part684 : Audit := .split 17 (4,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 21 true (-2),
.cycle 11 15 false (2),
.cycle 17 15 false (2),
.cycle 1 18 false (3),
.last 18 (5,false),
.cycle 0 30 true (-2),
.cycle 0 23 true (-2),
.last 19 (5,false),
.cycle 0 19 true (-2),
.cycle 0 32 true (-2),
.cycle 0 23 true (-2),
.cycle 11 16 false (2),
.cycle 7 12 false (3),
.cycle 0 32 true (-2),
.cycle 11 13 false (2),
.cycle 0 34 true (-2),
.last 18 (5,false),
.cycle 2 17 true (-2),
.cycle 16 2 true (1),
.cycle 0 24 true (-2),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 16, 32, 18, 18, 16, 64],96⟩,
.cycle 16 4 true (1),
.cycle 17 2 true (1)
])
theorem kid05_part684_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part684) = true := by rfl

def kid05_part685 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 34 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M293.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M293.never m hm),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.cycle 10 2 true (-1),
.cycle 15 1 false (1),
.cycle 0 32 true (-1),
.last 12 (4,true),
.cycle 0 36 true (-2),
.last 30 (4,true),
.last 44 (4,true),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.far false 9 ⟨0,[0, 6, 3, 7, 1, 8, 3, 3, 7, 6, 4, 4, 5, 2, 8, 3, 7, 7],[137438953472, 274877906944, 8, 0, 8589934592, 16777216, 8796093022208, 17592186044416, 2097152, 137438953472, 35184372088832, 18014398526521344, 562949953421312, 1125899906842624, 512, 67108864, 18014407101513728, 18014398509481984, 524288, 1048576, 2097152, 18041199106981888, 20266206915198976, 18300271549743104, 137438953472, 274877906944, 35184372088832, 18032265574481920, 18049582881570816, 18014398509744128, 33554432, 67108864, 134217728, 18023332041981952, 512, 16777216, 8192, 16384, 8589934592, 274878955520, 8589934592, 18014398509481984, 524288, 1048576, 2251799813685248, 18041199106981888, 20266206915198976, 18295873486454784, 8796093022208, 17592186044416, 35184372088832, 18041199106981888, 18014398511579136, 18018796573032448, 18014398509481984],[274877906944, 274877906944, 137438953472, 1, 18014398509481984, 16777216, 17592186044416, 18014398509481984, 18014398509481984, 262144, 18014398509481984, 18014398526521344, 1125899906842624, 18014398509481984, 18014398509481984, 64, 18014398509481984, 18014398509481984, 1048576, 18032265574481920, 18023332041981952, 262144, 18014398509481984, 18300271549743104, 274877906944, 274877906944, 137438953472, 4398046511104, 18014398509481984, 18014398509744128, 67108864, 18014398509481984, 18014398509481984, 16777216, 18014398509481984, 16777216, 16384, 18014673388437504, 18014535948959744, 1073741824, 18014398509481984, 18014398509481984, 1048576, 18014673388437504, 18014535948959744, 281474976710656, 18014398509481984, 18295873486454784, 17592186044416, 18031990696574976, 18023194603028480, 4398046511104, 18014398509481984, 18018796573032448, 18014398509481984],36028608023608786⟩,
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.proven (BB6.Agent11Raw39B1RCPumps.M295.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M295.never m hm),
.last 22 (4,true),
.cycle 8 7 false (2),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part685_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part685) = true := by rfl

def kid05_part686 : Audit := .cycle 0 13 true (0)
theorem kid05_part686_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part686) = true := by rfl

def kid05_part687 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 45 false (4),
.last 15 (5,false),
.cycle 0 27 true (0),
.cycle 1 15 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 0 29 true (0),
.cycle 0 20 true (-1),
.cycle 27 11 false (3),
.cycle 23 17 true (0),
.cycle 0 29 true (-1),
.cycle 15 1 false (-1),
.cycle 0 31 true (-2),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 1 15 true (0),
.cycle 0 21 true (-2),
.cycle 0 16 true (0),
.cycle 1 17 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part687_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part687) = true := by rfl

def kid05_part688 : Audit := .cycle 0 13 true (0)
theorem kid05_part688_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part688) = true := by rfl

def kid05_part689 : Audit := .cycle 0 20 true (-1)
theorem kid05_part689_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part689) = true := by rfl

def kid05_part690 : Audit := .cycle 9 2 true (0)
theorem kid05_part690_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part690) = true := by rfl

def kid05_part691 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 10 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 12 (4,true),
.last 21 (4,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.last 57 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (0),
.last 25 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 20 true (-1),
.last 12 (4,true),
.cycle 0 24 true (-2),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part691_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part691) = true := by rfl

def kid05_part667 : Audit := .split 10 (1,true) (byMove [(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675),(kid05_part676),(kid05_part677),(kid05_part678),(kid05_part679),(kid05_part680),(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691)])

theorem kid05_part667_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part667) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675),(kid05_part676),(kid05_part677),(kid05_part678),(kid05_part679),(kid05_part680),(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part668_checked

  · exact kid05_part674_checked

  · exact kid05_part680_checked

  · exact kid05_part686_checked

  · exact kid05_part669_checked

  · exact kid05_part675_checked

  · exact kid05_part681_checked

  · exact kid05_part687_checked

  · exact kid05_part670_checked

  · exact kid05_part676_checked

  · exact kid05_part682_checked

  · exact kid05_part688_checked

  · exact kid05_part671_checked

  · exact kid05_part677_checked

  · exact kid05_part683_checked

  · exact kid05_part689_checked

  · exact kid05_part672_checked

  · exact kid05_part678_checked

  · exact kid05_part684_checked

  · exact kid05_part690_checked

  · exact kid05_part673_checked

  · exact kid05_part679_checked

  · exact kid05_part685_checked

  · exact kid05_part691_checked

def kid05_part692 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.split 16 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.last 19 (1,true),
.cycle 27 1 false (1),
.last 17 (1,true),
.cycle 0 19 true (-1),
.cycle 0 18 true (-1),
.cycle 20 1 false (2),
.cycle 20 1 false (0),
.last 18 (1,true),
.cycle 22 1 false (-2),
.cycle 29 1 false (1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 23 1 false (-1),
.cycle 2 16 true (-1),
.last 17 (1,true),
.cycle 21 1 false (-1),
.cycle 0 18 true (-1),
.cycle 23 1 false (-1),
.cycle 15 2 true (0)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.split 13 (1,true) (byMove [
.cycle 24 1 false (-2),
.cycle 25 1 false (-3),
.cycle 10 4 false (0),
.cycle 0 19 true (-2),
.last 14 (4,true),
.cycle 17 1 false (-3),
.last 18 (4,true),
.cycle 0 17 true (-2),
.cycle 24 1 false (-2),
.cycle 22 1 false (-2),
.cycle 24 1 false (-2),
.last 24 (4,true),
.cycle 19 1 false (-3),
.cycle 20 1 false (-4),
.cycle 10 4 false (0),
.cycle 25 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-3),
.last 18 (4,true),
.cycle 0 17 true (-2),
.cycle 2 12 false (3),
.cycle 0 19 true (-2),
.cycle 19 1 false (-3),
.last 18 (4,true)
]),
.cycle 17 1 false (-3),
.split 18 (4,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 22 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.last 23 (1,true),
.cycle 29 1 false (1),
.last 19 (1,true),
.cycle 0 23 true (-2),
.cycle 0 20 true (-2),
.cycle 22 1 false (2),
.cycle 22 1 false (0),
.last 20 (1,true),
.cycle 24 1 false (-2),
.cycle 31 1 false (1),
.cycle 19 1 false (-1),
.cycle 21 1 false (-1),
.cycle 27 1 false (-1),
.cycle 2 18 true (-2),
.last 19 (1,true),
.cycle 23 1 false (-1),
.last 37 (1,true),
.cycle 25 1 false (-1),
.cycle 17 2 true (0)
]),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.split 16 (4,true) (byMove [
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
.cycle 29 1 false (-1),
.cycle 8 9 false (2),
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
.cycle 28 1 false (-2),
.cycle 15 2 true (0)
]),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.split 15 (4,true) (byMove [
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 20 1 false (-2),
.last 18 (1,true),
.cycle 20 1 false (-2),
.cycle 25 1 false (-3),
.cycle 0 42 true (-2),
.last 16 (1,true),
.cycle 17 1 true (1),
.cycle 0 17 true (-1),
.cycle 3 17 false (3),
.cycle 22 1 false (-2),
.last 21 (1,true),
.last 16 (1,true),
.cycle 20 1 false (-2),
.cycle 5 11 false (3),
.cycle 20 1 false (-2),
.cycle 16 3 false (0),
.cycle 0 46 true (-2),
.last 16 (1,true),
.cycle 26 1 false (-2),
.cycle 0 17 true (-1),
.cycle 32 1 false (-2),
.cycle 14 2 true (1)
])
])
theorem kid05_part692_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part692) = true := by rfl

def kid05_part693 : Audit := .split 12 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 24 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 24 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 14 1 true (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 0 17 true (0),
.cycle 14 1 true (0)
]),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
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
.cycle 15 1 false (-1),
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
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 13 1 true (3),
.cycle 11 3 true (1),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.cycle 9 5 true (0),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 27 true (0),
.cycle 32 1 false (0),
.cycle 0 16 true (0),
.cycle 13 1 true (3)
]),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
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
.cycle 18 1 false (0),
.cycle 11 4 false (2),
.cycle 19 1 false (-3),
.cycle 10 6 true (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 14 1 false (0),
.cycle 20 1 false (-2),
.last 18 (4,true),
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 9 6 true (0),
.last 17 (4,true)
]),
.cycle 23 1 false (1),
.split 13 (4,true) (byMove [
.cycle 13 5 false (2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 14 (5,false),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.cycle 16 1 false (0),
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
.cycle 0 17 true (0),
.cycle 13 2 true (1)
]),
.cycle 15 1 false (-1),
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
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 0 28 true (0),
.cycle 13 15 true (1),
.cycle 3 11 true (0),
.cycle 0 31 true (0),
.cycle 13 1 true (3),
.last 17 (4,true),
.last 16 (4,true),
.cycle 17 1 false (-1),
.cycle 0 29 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 30 true (0),
.cycle 0 16 true (0),
.cycle 13 1 true (3)
])
])
theorem kid05_part693_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part693) = true := by rfl

def kid05_part695 : Audit := .cycle 0 15 true (-1)
theorem kid05_part695_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part695) = true := by rfl

def kid05_part696 : Audit := .cycle 19 1 false (-1)
theorem kid05_part696_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part696) = true := by rfl

def kid05_part697 : Audit := .cycle 12 1 false (0)
theorem kid05_part697_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part697) = true := by rfl

def kid05_part698 : Audit := .cycle 11 1 false (-1)
theorem kid05_part698_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part698) = true := by rfl

def kid05_part699 : Audit := .cycle 11 1 false (-1)
theorem kid05_part699_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part699) = true := by rfl

def kid05_part700 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 19 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 23 (1,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 9 3 false (1),
.cycle 23 1 false (-3)
])
theorem kid05_part700_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part700) = true := by rfl

def kid05_part701 : Audit := .split 12 (1,true) (byMove [
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 37 1 false (3),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 14 (5,false),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 39 1 false (3),
.cycle 0 15 true (0),
.last 13 (5,false)
])
theorem kid05_part701_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part701) = true := by rfl

def kid05_part702 : Audit := .cycle 14 1 false (0)
theorem kid05_part702_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part702) = true := by rfl

def kid05_part703 : Audit := .cycle 0 13 true (0)
theorem kid05_part703_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part703) = true := by rfl

def kid05_part704 : Audit := .cycle 11 1 false (1)
theorem kid05_part704_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part704) = true := by rfl

def kid05_part705 : Audit := .cycle 11 1 false (1)
theorem kid05_part705_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part705) = true := by rfl

def kid05_part706 : Audit := .split 11 (5,false) (byMove [
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 20 1 false (2),
.last 12 (1,true),
.cycle 15 1 false (3),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.cycle 13 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 15 1 false (1)
])
theorem kid05_part706_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part706) = true := by rfl

def kid05_part707 : Audit := .split 12 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 14 (5,false),
.cycle 0 25 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 9 5 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (5,false),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 80 1 false (-4),
.cycle 20 1 false (-2),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.cycle 18 1 false (-2),
.last 13 (5,false)
])
theorem kid05_part707_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part707) = true := by rfl

def kid05_part708 : Audit := .cycle 14 1 false (-2)
theorem kid05_part708_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part708) = true := by rfl

def kid05_part709 : Audit := .split 14 (1,true) (byMove [
.cycle 23 1 false (1),
.cycle 24 1 false (0),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.cycle 43 1 false (3),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 0 20 true (-1),
.last 15 (5,false),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.last 16 (5,false),
.cycle 24 1 false (2),
.cycle 26 1 false (2),
.cycle 16 1 false (0),
.cycle 28 1 false (0),
.last 26 (5,false),
.cycle 2 13 true (-1),
.cycle 45 1 false (3),
.last 18 (5,false),
.last 15 (5,false)
])
theorem kid05_part709_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part709) = true := by rfl

def kid05_part710 : Audit := .cycle 11 1 false (-1)
theorem kid05_part710_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part710) = true := by rfl

def kid05_part711 : Audit := .cycle 11 1 false (-1)
theorem kid05_part711_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part711) = true := by rfl

def kid05_part712 : Audit := .split 11 (5,false) (byMove [
.cycle 10 6 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.last 14 (1,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
])
theorem kid05_part712_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part712) = true := by rfl

def kid05_part713 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.cycle 2 28 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 2 16 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 2 29 true (0),
.cycle 2 13 true (0),
.cycle 2 18 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 2 30 true (0),
.cycle 0 15 true (0),
.last 13 (5,false)
])
theorem kid05_part713_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part713) = true := by rfl

def kid05_part714 : Audit := .split 15 (1,true) (byMove [
.cycle 24 1 false (0),
.cycle 25 1 false (-1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 30 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 1 18 true (0),
.last 16 (5,false),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.last 17 (5,false),
.cycle 25 1 false (1),
.cycle 14 2 true (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 0 32 true (0),
.cycle 1 17 true (0),
.last 16 (5,false)
])
theorem kid05_part714_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part714) = true := by rfl

def kid05_part715 : Audit := .cycle 0 13 true (0)
theorem kid05_part715_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part715) = true := by rfl

def kid05_part716 : Audit := .cycle 16 1 false (0)
theorem kid05_part716_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part716) = true := by rfl

def kid05_part717 : Audit := .cycle 9 2 true (0)
theorem kid05_part717_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part717) = true := by rfl

def kid05_part718 : Audit := .split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.last 25 (1,true),
.last 12 (1,true),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 12 4 true (2),
.cycle 8 4 true (0),
.cycle 15 1 false (-1),
.last 12 (1,true),
.last 17 (1,true),
.cycle 16 1 false (0),
.cycle 12 2 true (0),
.cycle 13 1 false (-1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 12 2 true (1)
])
theorem kid05_part718_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part718) = true := by rfl

def kid05_part694 : Audit := .split 10 (4,true) (byMove [(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part704),(kid05_part705),(kid05_part706),(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718)])

theorem kid05_part694_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part694) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part704),(kid05_part705),(kid05_part706),(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part695_checked

  · exact kid05_part701_checked

  · exact kid05_part707_checked

  · exact kid05_part713_checked

  · exact kid05_part696_checked

  · exact kid05_part702_checked

  · exact kid05_part708_checked

  · exact kid05_part714_checked

  · exact kid05_part697_checked

  · exact kid05_part703_checked

  · exact kid05_part709_checked

  · exact kid05_part715_checked

  · exact kid05_part698_checked

  · exact kid05_part704_checked

  · exact kid05_part710_checked

  · exact kid05_part716_checked

  · exact kid05_part699_checked

  · exact kid05_part705_checked

  · exact kid05_part711_checked

  · exact kid05_part717_checked

  · exact kid05_part700_checked

  · exact kid05_part706_checked

  · exact kid05_part712_checked

  · exact kid05_part718_checked

def kid05_part720 : Audit := .split 18 (1,true) (byMove [
.last 56 (4,true),
.cycle 2 29 false (3),
.last 32 (4,true),
.cycle 0 20 true (-3),
.last 19 (4,true),
.cycle 2 21 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M296.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M296.never m hm),
.cycle 10 26 true (-3),
.cycle 10 16 true (-3),
.last 54 (4,true),
.last 58 (4,true),
.last 31 (4,true),
.cycle 2 23 false (3),
.last 25 (4,true),
.last 48 (4,true),
.last 59 (4,true),
.last 19 (4,true),
.cycle 2 21 false (3),
.last 30 (4,true),
.last 29 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M297.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M297.never m hm),
.cycle 10 28 true (-3),
.last 21 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M298.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M298.never m hm)
])
theorem kid05_part720_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part720) = true := by rfl

def kid05_part721 : Audit := .cycle 10 10 false (0)
theorem kid05_part721_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part721) = true := by rfl

def kid05_part722 : Audit := .cycle 14 1 false (-2)
theorem kid05_part722_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part722) = true := by rfl

def kid05_part723 : Audit := .cycle 13 1 false (-3)
theorem kid05_part723_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part723) = true := by rfl

def kid05_part724 : Audit := .cycle 11 2 false (-1)
theorem kid05_part724_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part724) = true := by rfl

def kid05_part725 : Audit := .cycle 12 1 false (-2)
theorem kid05_part725_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part725) = true := by rfl

def kid05_part726 : Audit := .split 14 (1,true) (byMove [
.cycle 10 12 true (-2),
.cycle 10 13 false (0),
.cycle 0 21 true (-2),
.last 20 (4,true),
.last 15 (4,true),
.cycle 10 5 false (0),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 385, 128, 1, 8192, 16384, 8, 256, 128, 1, 524288, 1048576, 32768, 385, 17301504, 4096, 524288, 1048576, 2097152, 18612224, 17301504, 262144, 16777216],[256, 1, 128, 1, 16777216, 1, 16384, 1, 128, 1, 16777216, 16777216, 1048576, 4096, 17301504, 4096, 16777216, 17039360, 1048576, 262144, 17301504, 262144, 16777216, 17039360, 16777216],33501248⟩,
.cycle 7 9 false (3),
.cycle 0 17 true (-2),
.cycle 10 10 true (-2),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719542272, 128, 1, 524288, 1048576, 32768, 256, 128, 4096, 128, 256, 8, 128, 128, 1, 2147483648, 4294967296, 134217728, 256, 68719476736, 16777216, 2147483648, 4294967296, 8589934592, 128, 2147483648, 1073741824, 2147483648, 4294967296, 8589934592, 92341862400, 70866960384, 1073741824, 68719476736],[256, 16, 128, 1, 68719476736, 65536, 1048576, 65536, 128, 4096, 68719476736, 68719476736, 256, 16, 128, 1, 68719476736, 65536, 4294967296, 268435456, 68719476736, 16777216, 68719476736, 68719476736, 4294967296, 17179869184, 2147483648, 1073741824, 68719476736, 68719476736, 4294967296, 17179869184, 70866960384, 1073741824, 68719476736, 85899345920, 68719476736],137301344332⟩,
.cycle 0 29 true (-2),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 true (-2),
.cycle 0 19 true (-2),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 28 (4,true),
.last 18 (4,true),
.cycle 0 17 true (-2),
.cycle 4 11 false (3),
.last 17 (4,true),
.last 42 (4,true)
])
theorem kid05_part726_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part726) = true := by rfl

def kid05_part727 : Audit := .cycle 10 5 false (0)
theorem kid05_part727_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part727) = true := by rfl

def kid05_part728 : Audit := .split 16 (1,true) (byMove [
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.cycle 20 1 false (2),
.cycle 0 18 true (-2),
.last 17 (4,true),
.cycle 0 22 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 393, 8, 4, 8192, 16384, 8, 392, 136, 4, 524288, 1048576, 512, 256, 16777216, 256, 524288, 1048576, 2097152, 20725760, 19398656, 1048576, 16777216],[256, 1, 8, 1, 16777216, 1, 16384, 1, 136, 1, 16777216, 16777216, 1048576, 64, 16777216, 64, 16777216, 16777216, 1048576, 262144, 19398656, 262144, 16777216, 17039360, 16777216],33370176⟩,
.cycle 0 29 true (-2),
.cycle 10 14 true (-2),
.cycle 0 27 true (-2),
.cycle 10 16 true (-2),
.cycle 8 25 true (-2),
.cycle 0 24 true (-2),
.cycle 10 10 true (-2),
.cycle 0 21 true (-2),
.cycle 0 30 true (-2),
.last 17 (4,true),
.cycle 0 34 true (-2),
.last 28 (4,true),
.last 27 (4,true),
.cycle 2 15 true (-2),
.cycle 0 31 true (-2),
.last 19 (4,true),
.cycle 17 19 true (-1)
])
theorem kid05_part728_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part728) = true := by rfl

def kid05_part729 : Audit := .cycle 13 1 false (-1)
theorem kid05_part729_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part729) = true := by rfl

def kid05_part730 : Audit := .cycle 11 2 true (-2)
theorem kid05_part730_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part730) = true := by rfl

def kid05_part731 : Audit := .cycle 10 4 true (-2)
theorem kid05_part731_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part731) = true := by rfl

def kid05_part732 : Audit := .split 14 (1,true) (byMove [
.cycle 10 12 false (0),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.last 20 (4,true),
.last 15 (4,true),
.cycle 10 5 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 4096, 524288, 1048576, 32768, 67109120, 128, 128, 128, 256, 134217728, 77562155392, 1048576, 1073741824, 33554432, 67108864, 8589934592, 256, 68719476736, 68719476736, 33554432, 67108864, 134217728, 77562155392, 77562155392, 77562155392, 33554432, 67108864, 134217728, 128, 68719476736, 16777216, 68719476736],[256, 1, 128, 1, 68719476736, 4096, 1048576, 4096, 128, 4096, 68719476736, 68719476736, 256, 16777216, 1048576, 16777216, 68719476736, 4096, 67108864, 1073741824, 68719476736, 1073741824, 68719476736, 68719476736, 67108864, 16777216, 77562155392, 16777216, 68719476736, 77562155392, 67108864, 16777216, 68719476736, 16777216, 68719476736, 68719476736, 68719476736],128847897410⟩,
.cycle 7 9 false (3),
.cycle 10 16 true (-3),
.cycle 10 10 false (0),
.cycle 10 9 false (0),
.last 21 (4,true),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.last 71 (4,true),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 30 (4,true),
.last 18 (4,true),
.last 33 (4,true),
.cycle 4 11 false (3),
.last 17 (4,true),
.last 19 (4,true)
])
theorem kid05_part732_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part732) = true := by rfl

def kid05_part733 : Audit := .cycle 10 5 false (0)
theorem kid05_part733_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part733) = true := by rfl

def kid05_part734 : Audit := .split 16 (1,true) (byMove [
.cycle 10 14 true (-3),
.cycle 10 15 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M303.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M303.never m hm),
.last 22 (4,true),
.last 17 (4,true),
.cycle 10 7 false (0),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 385, 128, 1, 8192, 16384, 8, 384, 128, 1, 524288, 1048576, 512, 256, 16777216, 1, 524288, 1048576, 2097152, 18628608, 17301504, 17039360, 16777216],[256, 1, 128, 1, 16777216, 1, 16384, 1, 128, 1, 16777216, 16777216, 1048576, 64, 16777216, 64, 16777216, 16777216, 1048576, 262144, 17301504, 262144, 16777216, 17039360, 16777216],33370176⟩,
.cycle 7 11 false (3),
.cycle 0 19 true (-3),
.cycle 10 12 true (-3),
.cycle 12 8 true (-3),
.cycle 35 25 true (0),
.cycle 10 9 false (0),
.cycle 10 10 false (0),
.cycle 12 6 true (-3),
.cycle 42 15 true (2),
.last 17 (4,true),
.cycle 10 7 false (0),
.last 30 (4,true),
.last 20 (4,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1075855745, 2097280, 1, 8192, 16384, 8, 256, 2097280, 16385, 33554432, 67108864, 2097152, 256, 1073741824, 16385, 8192, 16384, 8, 2097280, 2097280, 1, 33554432, 67108864, 134217728, 1325416448, 1241513984, 1157627904, 1073741824],[256, 256, 2097280, 1, 1073741824, 16385, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1073741824, 262144, 1073741824, 1073741824, 16384, 16384, 2097280, 1, 1073741824, 1073741824, 67108864, 67108864, 1241513984, 16777216, 1073741824, 1157627904, 1073741824],2132128590⟩,
.cycle 4 13 false (3),
.last 19 (4,true),
.cycle 10 9 false (1)
])
theorem kid05_part734_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part734) = true := by rfl

def kid05_part735 : Audit := .cycle 13 1 false (-3)
theorem kid05_part735_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part735) = true := by rfl

def kid05_part736 : Audit := .cycle 11 2 false (-1)
theorem kid05_part736_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part736) = true := by rfl

def kid05_part737 : Audit := .cycle 12 1 false (-2)
theorem kid05_part737_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part737) = true := by rfl

def kid05_part738 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 false (3),
.cycle 10 14 false (0),
.cycle 10 6 false (0),
.last 20 (4,true),
.last 15 (4,true),
.last 16 (4,true),
.last 32 (4,true),
.last 20 (4,true),
.cycle 0 17 true (-2),
.cycle 3 12 false (3),
.last 32 (4,true),
.last 28 (4,true),
.last 18 (4,true),
.cycle 10 9 false (0),
.cycle 10 6 false (0),
.cycle 0 19 true (-2),
.last 15 (4,true),
.last 16 (4,true),
.last 28 (4,true),
.last 18 (4,true),
.cycle 0 17 true (-2),
.last 22 (4,true),
.last 17 (4,true),
.last 26 (4,true)
])
theorem kid05_part738_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part738) = true := by rfl

def kid05_part739 : Audit := .split 16 (4,true) (byMove [
.cycle 13 5 false (0),
.last 45 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 1 54 false (5),
.cycle 12 5 false (0),
.cycle 10 14 true (-2),
.last 17 (1,true),
.cycle 1 18 false (3),
.cycle 0 24 true (-2),
.cycle 0 23 true (-2),
.cycle 10 7 false (0),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 10 16 true (-3),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.last 18 (1,true),
.cycle 2 16 false (3),
.last 17 (1,true),
.cycle 10 8 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 1048576, 128, 524288, 1048576, 32768, 67109120, 1048576, 524288, 128, 256, 134217728, 77562118272, 67108864, 128, 33554432, 67108864, 8589934592, 256, 128, 33554432, 33554432, 67108864, 134217728, 77562118272, 77562118272, 33554432, 33554432, 67108864, 134217728, 1048576, 67108864, 33554432, 68719476736],[256, 68719476736, 1048576, 1, 512, 128, 1048576, 68719476736, 1048576, 4096, 2097152, 4096, 256, 68719476736, 67108864, 16777216, 512, 128, 67108864, 68719476736, 128, 1073741824, 134217728, 1073741824, 67108864, 68719476736, 77562118272, 16777216, 134217728, 77562118272, 67108864, 68719476736, 67108864, 16777216, 134217728, 68719476736, 68719476736],128843639618⟩,
.cycle 15 4 true (-2),
.cycle 15 2 true (-2)
])
theorem kid05_part739_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part739) = true := by rfl

def kid05_part740 : Audit := .split 16 (1,true) (byMove [
.cycle 0 29 true (-2),
.cycle 0 30 true (-2),
.cycle 0 30 true (-2),
.cycle 0 18 true (-2),
.last 17 (4,true),
.cycle 0 22 true (-2),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[4194304, 2199023255552, 35184372088832, 32768, 32, 2199023255552, 281475249341440, 281510145952768, 281510280171008, 134217728, 2048, 281510145952768, 4194304, 65536, 0, 35184372088832, 2199023255552, 65536, 4194304, 268436480, 0, 134217728, 34359738368, 268436480, 281475249341440, 281510145952768, 281510280171008, 512, 536870912, 281510145952768, 281474976710656, 0, 512, 2097152, 2048, 0, 281474976710656, 0, 134217728, 2097152, 536870912, 0, 0, 4194304, 0, 134217728, 536870912, 4194304, 281474976710656],[2199023255552, 34359738368, 32, 34359738368, 281474976710656, 65536, 281510145952768, 281510145952768, 2048, 281510145952768, 281474976710656, 268435456, 65536, 0, 2199023255552, 0, 281474976710656, 70368744177664, 268436480, 0, 34359738368, 0, 281474976710656, 268435456, 281510145952768, 281510145952768, 536870912, 281510145952768, 281474976710656, 1024, 0, 34359738368, 2048, 34359738368, 281474976710656, 4194304, 0, 34359738368, 536870912, 34359738368, 281474976710656, 4194304, 4194304, 2199023255552, 536870912, 2199023255552, 281474976710656, 268435456, 281474976710656],353031137267136⟩,
.cycle 0 29 true (-2),
.cycle 10 14 true (-2),
.cycle 0 27 true (-2),
.cycle 2 17 true (-2),
.cycle 0 29 true (-2),
.cycle 0 24 true (-2),
.cycle 7 12 false (3),
.cycle 0 21 true (-2),
.cycle 0 30 true (-2),
.last 17 (4,true),
.cycle 0 34 true (-2),
.last 28 (4,true),
.last 27 (4,true),
.cycle 2 15 true (-2),
.cycle 0 31 true (-2),
.last 19 (4,true),
.last 27 (4,true)
])
theorem kid05_part740_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part740) = true := by rfl

def kid05_part741 : Audit := .cycle 10 7 false (0)
theorem kid05_part741_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part741) = true := by rfl

def kid05_part742 : Audit := .cycle 9 4 false (1)
theorem kid05_part742_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part742) = true := by rfl

def kid05_part743 : Audit := .split 15 (4,true) (byMove [
.last 20 (1,true),
.last 16 (1,true),
.cycle 10 13 false (0),
.last 18 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 0, 64],64⟩,
.cycle 10 6 false (0),
.cycle 0 19 true (-2),
.last 16 (1,true),
.cycle 23 1 true (1),
.last 18 (1,true),
.cycle 24 1 true (2),
.cycle 8 8 false (2),
.cycle 10 8 false (0),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 10 9 false (0),
.cycle 11 6 false (0),
.cycle 10 6 false (0),
.cycle 0 19 true (-2),
.last 16 (1,true),
.cycle 10 10 false (0),
.last 18 (1,true),
.cycle 14 4 true (-1),
.cycle 14 2 true (-1)
])
theorem kid05_part743_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part743) = true := by rfl

def kid05_part719 : Audit := .split 12 (5,false) (byMove [(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727),(kid05_part728),(kid05_part729),(kid05_part730),(kid05_part731),(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743)])

theorem kid05_part719_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part719) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727),(kid05_part728),(kid05_part729),(kid05_part730),(kid05_part731),(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part720_checked

  · exact kid05_part726_checked

  · exact kid05_part732_checked

  · exact kid05_part738_checked

  · exact kid05_part721_checked

  · exact kid05_part727_checked

  · exact kid05_part733_checked

  · exact kid05_part739_checked

  · exact kid05_part722_checked

  · exact kid05_part728_checked

  · exact kid05_part734_checked

  · exact kid05_part740_checked

  · exact kid05_part723_checked

  · exact kid05_part729_checked

  · exact kid05_part735_checked

  · exact kid05_part741_checked

  · exact kid05_part724_checked

  · exact kid05_part730_checked

  · exact kid05_part736_checked

  · exact kid05_part742_checked

  · exact kid05_part725_checked

  · exact kid05_part731_checked

  · exact kid05_part737_checked

  · exact kid05_part743_checked

def kid05_part744 : Audit := .cycle 2 9 true (1)
theorem kid05_part744_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part744) = true := by rfl

def kid05_part745 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.cycle 14 6 false (0),
.cycle 12 6 false (0),
.cycle 0 24 true (-2),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 26 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
]),
.split 16 (4,true) (byMove [
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 7 false (1),
.last 17 (5,false),
.cycle 22 7 false (3),
.cycle 17 7 false (1),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 24 7 false (5),
.cycle 17 7 false (1),
.cycle 17 7 false (0),
.cycle 18 7 false (0),
.cycle 24 7 false (3),
.cycle 17 1 false (-1),
.cycle 17 7 false (0),
.last 17 (5,false),
.cycle 2 16 true (0),
.cycle 17 7 false (1),
.cycle 17 7 false (1),
.cycle 0 18 true (0),
.cycle 6 25 true (0),
.cycle 15 2 true (0)
]),
.split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 5 false (1),
.last 15 (5,false),
.cycle 21 5 false (3),
.cycle 15 5 false (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 23 5 false (5),
.cycle 15 5 false (1),
.cycle 17 5 false (-1),
.cycle 15 5 false (0),
.cycle 23 5 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 16 5 false (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 7 21 true (0),
.cycle 13 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 0 40 true (-2),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 14 6 false (0),
.cycle 12 6 false (0),
.cycle 0 35 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 1 11 true (1),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 14 (4,true),
.last 33 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
])
])
theorem kid05_part745_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part745) = true := by rfl

def kid05_part746 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (3),
.cycle 13 11 false (2),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (0),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 16 11 false (3),
.cycle 16 11 false (2),
.cycle 11 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 26 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 26 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.last 14 (1,true),
.cycle 21 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 27 1 false (1),
.cycle 11 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 41 1 false (7),
.cycle 11 1 true (1),
.split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 0 21 false (3),
.last 20 (4,true),
.cycle 14 6 false (0),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 12 31 true (-3),
.cycle 17 3 true (-2),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 12 14 true (-2),
.last 20 (4,true),
.cycle 14 6 false (0),
.last 35 (4,true),
.last 34 (4,true),
.cycle 2 18 false (3),
.cycle 12 15 true (-2),
.cycle 3 20 false (3),
.last 24 (4,true)
]),
.split 12 (1,true) (byMove [
.last 17 (4,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 13 6 false (-1),
.cycle 19 6 false (3),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 6 false (1),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 21 6 false (3),
.cycle 13 1 false (-1),
.cycle 13 6 false (0),
.cycle 13 6 false (-1),
.cycle 2 12 true (0),
.cycle 1 13 true (0),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
]),
.split 17 (1,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 32 true (-2),
.cycle 0 22 true (-2),
.cycle 0 19 true (-2),
.last 18 (4,true),
.cycle 0 24 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073758208, 4, 1, 8192, 16384, 8, 256, 4, 1, 33554432, 67108864, 2097152, 256, 1048576, 1073741824, 8192, 16384, 8, 16384, 4, 1, 33554432, 67108864, 134217728, 1327513993, 67108864, 1327513993, 1073741824],[256, 1, 128, 1, 1073741824, 128, 16384, 1, 16384, 1, 1073741824, 1073741824, 67108864, 262144, 1073741824, 262144, 1073741824, 1073741824, 16384, 1, 1073741824, 1, 1073741824, 1073741824, 67108864, 16777216, 1327513993, 16777216, 1073741824, 1327513993, 1073741824],2136455006⟩,
.cycle 0 31 true (-2),
.last 35 (4,true),
.cycle 0 29 true (-2),
.last 37 (4,true),
.cycle 0 21 true (-2),
.cycle 0 26 true (-2),
.last 31 (4,true),
.cycle 12 6 true (-2),
.cycle 0 32 true (-2),
.last 18 (4,true),
.cycle 12 8 true (-2),
.last 32 (4,true),
.last 40 (4,true),
.cycle 2 16 true (-2),
.cycle 0 33 true (-2),
.cycle 0 39 true (-2),
.last 30 (4,true)
]),
.cycle 24 1 false (0),
.split 12 (4,true) (byMove [
.cycle 12 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.cycle 13 3 false (-1),
.cycle 21 3 false (2),
.last 13 (1,true),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 16 1 false (4),
.cycle 14 3 false (1),
.last 14 (1,true),
.cycle 16 3 false (-1),
.cycle 23 3 false (2),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 3 false (-1),
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 15 3 false (0),
.cycle 0 14 true (0),
.cycle 0 31 true (0),
.cycle 12 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 0 27 true (0),
.cycle 11 1 true (1)
])
theorem kid05_part746_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part746) = true := by rfl

def kid05_part747 : Audit := .cycle 0 11 true (0)
theorem kid05_part747_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part747) = true := by rfl

def kid05_part748 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 11 1 true (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 true (-2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.cycle 15 1 false (-1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 26 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 13 1 true (3),
.last 13 (5,false),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 13 1 true (3),
.last 13 (5,false)
]),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 12 4 true (-2),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.cycle 16 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 12 (1,true),
.last 19 (1,true),
.cycle 2 12 true (1),
.cycle 12 2 true (2),
.cycle 14 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid05_part748_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part748) = true := by rfl

def kid05_part749 : Audit := .cycle 8 2 true (1)
theorem kid05_part749_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part749) = true := by rfl

def kid05_part751 : Audit := .cycle 0 35 true (-2)
theorem kid05_part751_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part751) = true := by rfl

def kid05_part752 : Audit := .cycle 10 12 false (1)
theorem kid05_part752_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part752) = true := by rfl

def kid05_part753 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (3),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 22 (4,true),
.last 95 (4,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 12 8 true (-3),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.last 24 (4,true),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.last 22 (4,true),
.last 41 (4,true),
.cycle 10 12 false (1),
.last 107 (4,true),
.cycle 9 9 false (1),
.last 21 (4,true)
])
theorem kid05_part753_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part753) = true := by rfl

def kid05_part754 : Audit := .split 24 (4,true) (byMove [
.cycle 20 5 false (2),
.cycle 0 28 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 17 9 false (2),
.last 25 (5,false),
.cycle 0 40 true (-2),
.cycle 26 1 false (0),
.last 26 (5,false),
.cycle 0 26 true (-2),
.cycle 0 30 true (-2),
.cycle 0 33 true (-2),
.cycle 0 31 true (-2),
.cycle 11 15 false (2),
.cycle 0 42 true (-2),
.cycle 25 1 false (-1),
.cycle 0 35 true (-2),
.last 25 (5,false),
.cycle 2 24 true (-2),
.cycle 0 27 true (-2),
.cycle 0 34 true (-2),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 8, 32, 17, 17, 16, 64],96⟩,
.cycle 22 6 true (0),
.cycle 23 2 true (0)
])
theorem kid05_part754_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part754) = true := by rfl

def kid05_part755 : Audit := .split 16 (4,true) (byMove [
.cycle 39 5 false (-1),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 0 40 true (-2),
.cycle 11 7 false (1),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.last 17 (5,false),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 50 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 0 41 true (-2),
.cycle 1 22 false (3),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.last 17 (5,false)
])
theorem kid05_part755_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part755) = true := by rfl

def kid05_part756 : Audit := .cycle 12 4 false (0)
theorem kid05_part756_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part756) = true := by rfl

def kid05_part757 : Audit := .cycle 0 19 true (-2)
theorem kid05_part757_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part757) = true := by rfl

def kid05_part758 : Audit := .cycle 18 12 true (-1)
theorem kid05_part758_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part758) = true := by rfl

def kid05_part759 : Audit := .split 17 (5,false) (byMove [
.cycle 10 13 false (1),
.cycle 20 1 false (0),
.cycle 21 1 false (-3),
.cycle 0 23 true (-2),
.last 18 (4,true),
.cycle 12 6 false (0),
.last 22 (4,true),
.cycle 0 21 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 0 23 true (-2),
.cycle 25 1 true (1),
.cycle 10 8 false (1),
.cycle 11 11 false (1),
.cycle 10 19 false (1),
.cycle 10 14 true (-2),
.last 18 (4,true),
.cycle 12 6 false (0),
.last 22 (4,true),
.cycle 0 21 true (-2),
.cycle 2 16 false (3),
.cycle 0 23 true (-2),
.last 22 (4,true),
.last 21 (4,true)
])
theorem kid05_part759_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part759) = true := by rfl

def kid05_part760 : Audit := .cycle 0 29 true (-2)
theorem kid05_part760_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part760) = true := by rfl

def kid05_part761 : Audit := .split 16 (4,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.cycle 9 8 false (1),
.last 17 (5,false),
.cycle 17 3 true (1),
.cycle 18 12 true (-1),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.cycle 21 3 true (2),
.last 17 (5,false),
.cycle 23 3 true (1),
.cycle 11 11 false (1),
.cycle 19 3 true (1),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.last 17 (5,false),
.cycle 17 3 true (1),
.cycle 21 3 true (1),
.cycle 0 19 true (-2),
.cycle 17 14 true (-1),
.cycle 6 12 false (3),
.last 17 (5,false)
])
theorem kid05_part761_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part761) = true := by rfl

def kid05_part762 : Audit := .cycle 8 8 false (2)
theorem kid05_part762_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part762) = true := by rfl

def kid05_part763 : Audit := .cycle 10 6 false (1)
theorem kid05_part763_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part763) = true := by rfl

def kid05_part764 : Audit := .cycle 11 7 false (1)
theorem kid05_part764_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part764) = true := by rfl

def kid05_part765 : Audit := .split 17 (5,false) (byMove [
.last 48 (4,true),
.cycle 10 13 false (1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 393, 1, 4, 8192, 16384, 8, 256, 136, 4, 33554432, 67108864, 2097152, 256, 1073741824, 1048576, 33554432, 67108864, 2097152, 393, 1090781184, 1048576, 33554432, 67108864, 134217728, 1325662208, 1258553344, 67108864, 1073741824],[256, 1, 8, 1, 1073741824, 257, 16384, 1, 136, 1, 1073741824, 1073741824, 67108864, 1, 1073741824, 262144, 1073741824, 1073741824, 67108864, 262144, 2097152, 262144, 1073741824, 1140850688, 67108864, 1090781184, 1241513984, 16777216, 1073741824, 1157890048, 1073741824],2135765056⟩,
.cycle 18 1 false (-2),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 13 5 false (-1),
.cycle 17 1 false (-3),
.cycle 11 9 false (1),
.last 21 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M312.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M312.never m hm),
.cycle 10 10 false (1),
.cycle 9 9 false (1),
.last 20 (4,true)
])
theorem kid05_part765_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part765) = true := by rfl

def kid05_part766 : Audit := .cycle 10 7 false (1)
theorem kid05_part766_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part766) = true := by rfl

def kid05_part767 : Audit := .split 16 (4,true) (byMove [
.cycle 16 5 false (-1),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 1, 64, 64],[19, 16, 32, 19, 2, 16, 64],96⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 10 7 false (1),
.cycle 13 5 false (-1),
.last 18 (5,false),
.cycle 0 21 true (-2),
.cycle 23 5 true (1),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.last 17 (5,false),
.cycle 2 20 false (3),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 17 6 true (-1),
.cycle 16 2 true (-2)
])
theorem kid05_part767_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part767) = true := by rfl

def kid05_part768 : Audit := .cycle 12 4 false (0)
theorem kid05_part768_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part768) = true := by rfl

def kid05_part769 : Audit := .cycle 0 19 true (-2)
theorem kid05_part769_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part769) = true := by rfl

def kid05_part770 : Audit := .split 20 (4,true) (byMove [
.cycle 0 24 true (-2),
.cycle 16 39 false (3),
.cycle 58 1 false (-4),
.cycle 119 1 false (-1),
.cycle 20 46 false (0),
.last 23 (5,false),
.cycle 0 49 true (-2),
.cycle 0 48 true (-2),
.last 22 (5,false),
.cycle 0 22 true (-2),
.cycle 24 18 true (1),
.cycle 12 15 false (2),
.cycle 14 11 false (2),
.cycle 15 23 true (-1),
.cycle 11 10 false (2),
.cycle 5 16 false (3),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 17, 32, 17, 16, 16, 64],96⟩,
.last 23 (5,false),
.cycle 0 37 true (-2),
.cycle 16 19 true (0),
.cycle 21 22 false (1),
.cycle 16 26 true (-1),
.cycle 18 6 true (0),
.cycle 19 2 true (0)
])
theorem kid05_part770_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part770) = true := by rfl

def kid05_part771 : Audit := .split 18 (4,true) (byMove [
.cycle 16 5 false (0),
.cycle 20 30 true (-2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 2 58 false (5),
.last 19 (5,false),
.cycle 10 14 true (-2),
.cycle 10 14 true (-2),
.last 20 (5,false),
.cycle 0 26 true (-2),
.cycle 0 25 true (-2),
.cycle 12 7 false (0),
.cycle 14 5 false (0),
.cycle 11 9 false (1),
.cycle 10 16 true (-3),
.cycle 19 1 false (-3),
.cycle 13 6 false (0),
.last 19 (5,false),
.cycle 2 18 false (3),
.cycle 2 18 false (3),
.cycle 11 8 false (1),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 17, 32, 17, 17, 16, 64],96⟩,
.cycle 16 6 true (-2),
.cycle 17 2 true (-2)
])
theorem kid05_part771_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part771) = true := by rfl

def kid05_part772 : Audit := .split 50 (4,true) (byMove [
.cycle 4 52 true (-2),
.cycle 0 77 true (-2),
.last 52 (5,false),
.cycle 0 74 true (-2),
.cycle 46 48 false (4),
.last 57 (5,false),
.cycle 16 37 true (0),
.cycle 18 48 true (2),
.last 52 (5,false),
.cycle 4 50 true (-2),
.cycle 13 39 true (-2),
.cycle 51 21 false (3),
.cycle 51 19 false (3),
.cycle 16 39 true (0),
.last 52 (5,false),
.cycle 116 1 false (-6),
.cycle 46 30 false (5),
.last 57 (5,false),
.cycle 16 37 true (0),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 17, 32, 17, 17, 16, 64],96⟩,
.cycle 51 18 false (3),
.cycle 77 36 false (4),
.cycle 46 6 true (2),
.cycle 49 2 true (2)
])
theorem kid05_part772_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part772) = true := by rfl

def kid05_part773 : Audit := .split 16 (4,true) (byMove [
.cycle 2 16 false (3),
.far true 1 ⟨0,[0, 0],[19, 19, 27, 8, 1, 64, 64],[19, 19, 32, 19, 2, 16, 64],96⟩,
.cycle 11 6 false (1),
.cycle 0 28 true (-2),
.cycle 18 8 false (-2),
.last 19 (5,false),
.cycle 17 40 true (1),
.cycle 9 17 false (2),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.cycle 20 9 true (2),
.last 17 (5,false),
.cycle 14 7 false (0),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 13 6 false (0),
.last 19 (5,false),
.cycle 0 40 true (-2),
.cycle 18 6 true (0),
.cycle 0 19 true (-2),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 1, 64, 64],[17, 17, 32, 17, 17, 16, 64],96⟩,
.cycle 16 6 true (-1),
.last 17 (5,false)
])
theorem kid05_part773_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part773) = true := by rfl

def kid05_part774 : Audit := .split 17 (4,true) (byMove [
.last 23 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.last 22 (5,false),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.last 19 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.last 28 (5,false),
.cycle 8 10 false (2),
.cycle 10 8 false (1),
.cycle 11 11 false (1),
.last 19 (5,false),
.cycle 10 9 false (1),
.cycle 13 6 false (0),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.last 19 (5,false),
.cycle 11 10 false (1),
.last 21 (5,false),
.cycle 16 6 true (-1),
.cycle 16 2 true (-1)
])
theorem kid05_part774_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part774) = true := by rfl

def kid05_part750 : Audit := .split 15 (1,true) (byMove [(kid05_part751),(kid05_part752),(kid05_part753),(kid05_part754),(kid05_part755),(kid05_part756),(kid05_part757),(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774)])

theorem kid05_part750_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part750) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part751),(kid05_part752),(kid05_part753),(kid05_part754),(kid05_part755),(kid05_part756),(kid05_part757),(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part751_checked

  · exact kid05_part757_checked

  · exact kid05_part763_checked

  · exact kid05_part769_checked

  · exact kid05_part752_checked

  · exact kid05_part758_checked

  · exact kid05_part764_checked

  · exact kid05_part770_checked

  · exact kid05_part753_checked

  · exact kid05_part759_checked

  · exact kid05_part765_checked

  · exact kid05_part771_checked

  · exact kid05_part754_checked

  · exact kid05_part760_checked

  · exact kid05_part766_checked

  · exact kid05_part772_checked

  · exact kid05_part755_checked

  · exact kid05_part761_checked

  · exact kid05_part767_checked

  · exact kid05_part773_checked

  · exact kid05_part756_checked

  · exact kid05_part762_checked

  · exact kid05_part768_checked

  · exact kid05_part774_checked

def kid05_part776 : Audit := .split 15 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 7 24 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 4 false (-2),
.last 16 (5,false),
.cycle 0 19 true (-1),
.cycle 0 21 true (-1),
.last 17 (5,false),
.cycle 25 4 false (3),
.cycle 17 4 false (1),
.cycle 16 4 false (0),
.cycle 7 26 false (3),
.cycle 16 4 false (-1),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.cycle 16 4 false (-2),
.last 16 (5,false),
.cycle 0 19 true (-1),
.cycle 23 4 false (1),
.cycle 16 4 false (0),
.cycle 12 16 true (-1),
.cycle 0 50 true (-2),
.cycle 14 2 true (-1)
])
theorem kid05_part776_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part776) = true := by rfl

def kid05_part777 : Audit := .cycle 0 34 true (-2)
theorem kid05_part777_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part777) = true := by rfl

def kid05_part778 : Audit := .cycle 12 1 false (0)
theorem kid05_part778_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part778) = true := by rfl

def kid05_part779 : Audit := .cycle 11 1 false (-1)
theorem kid05_part779_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part779) = true := by rfl

def kid05_part780 : Audit := .cycle 11 4 false (-1)
theorem kid05_part780_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part780) = true := by rfl

def kid05_part781 : Audit := .split 11 (5,false) (byMove [
.cycle 30 4 false (-2),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 14 4 false (0),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.cycle 13 4 false (1),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 16 4 false (0),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 34 true (-2),
.cycle 15 4 false (1),
.cycle 9 3 false (1),
.last 14 (4,true)
])
theorem kid05_part781_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part781) = true := by rfl

def kid05_part782 : Audit := .cycle 12 4 false (2)
theorem kid05_part782_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part782) = true := by rfl

def kid05_part783 : Audit := .cycle 19 4 false (5)
theorem kid05_part783_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part783) = true := by rfl

def kid05_part784 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 12 1 false (0),
.cycle 21 4 false (3),
.cycle 13 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (1),
.cycle 14 4 false (2),
.cycle 0 17 true (-1),
.cycle 13 4 false (0),
.cycle 23 4 false (3),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.cycle 12 1 false (0),
.cycle 0 31 true (0),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 9 4 true (0),
.last 15 (4,true)
])
theorem kid05_part784_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part784) = true := by rfl

def kid05_part785 : Audit := .cycle 18 4 false (4)
theorem kid05_part785_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part785) = true := by rfl

def kid05_part786 : Audit := .split 11 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 18 4 false (4),
.cycle 13 4 false (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 4 false (3),
.cycle 12 4 false (2),
.cycle 23 4 false (1),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.cycle 12 4 false (0),
.last 12 (5,false),
.cycle 2 11 true (0),
.cycle 11 6 true (1),
.cycle 12 4 false (2),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 11 2 true (1)
])
theorem kid05_part786_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part786) = true := by rfl

def kid05_part787 : Audit := .cycle 11 4 false (1)
theorem kid05_part787_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part787) = true := by rfl

def kid05_part788 : Audit := .cycle 14 4 false (0)
theorem kid05_part788_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part788) = true := by rfl

def kid05_part789 : Audit := .cycle 11 4 false (0)
theorem kid05_part789_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part789) = true := by rfl

def kid05_part790 : Audit := .cycle 14 4 false (2)
theorem kid05_part790_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part790) = true := by rfl

def kid05_part791 : Audit := .cycle 11 1 false (-1)
theorem kid05_part791_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part791) = true := by rfl

def kid05_part792 : Audit := .cycle 11 4 false (-1)
theorem kid05_part792_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part792) = true := by rfl

def kid05_part793 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.last 22 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 22 4 false (4),
.cycle 14 4 false (2),
.last 12 (4,true),
.cycle 12 4 false (0),
.cycle 14 4 false (-2),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 12 4 false (-2),
.cycle 11 1 false (-1),
.last 15 (4,true),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 5 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part793_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part793) = true := by rfl

def kid05_part794 : Audit := .split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.last 15 (5,false),
.cycle 21 4 false (3),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 16 4 false (2),
.cycle 15 4 false (1),
.cycle 32 4 false (0),
.cycle 15 4 false (0),
.cycle 23 4 false (3),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.cycle 2 17 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part794_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part794) = true := by rfl

def kid05_part795 : Audit := .cycle 1 12 true (0)
theorem kid05_part795_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part795) = true := by rfl

def kid05_part796 : Audit := .cycle 11 4 false (1)
theorem kid05_part796_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part796) = true := by rfl

def kid05_part797 : Audit := .split 24 (4,true) (byMove [
.cycle 21 5 false (2),
.cycle 11 20 true (-1),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 25 4 false (-1),
.last 25 (5,false),
.cycle 0 28 true (0),
.cycle 29 4 false (3),
.last 26 (5,false),
.cycle 11 18 true (0),
.cycle 26 4 false (2),
.cycle 25 4 false (1),
.cycle 11 20 true (-1),
.cycle 25 4 false (0),
.cycle 0 30 true (-1),
.cycle 25 1 false (-1),
.cycle 25 4 false (-1),
.last 25 (5,false),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 25 4 false (1),
.cycle 11 18 true (0),
.cycle 9 17 true (0),
.cycle 23 2 true (0)
])
theorem kid05_part797_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part797) = true := by rfl

def kid05_part798 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 4 true (0),
.last 13 (5,false),
.cycle 0 19 true (0),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 0 28 true (0),
.cycle 9 21 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 7 8 true (0),
.cycle 8 4 true (0),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.last 13 (5,false),
.cycle 14 4 false (2),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 15 4 false (1),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 11 2 true (1)
])
theorem kid05_part798_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part798) = true := by rfl

def kid05_part799 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 38 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 14 4 false (2),
.last 17 (5,false),
.last 14 (5,false),
.cycle 20 4 false (4),
.cycle 15 4 false (3),
.cycle 13 4 false (1),
.cycle 18 4 false (0),
.cycle 13 4 false (0),
.cycle 16 4 false (2),
.cycle 13 1 false (-1),
.cycle 13 4 false (-1),
.last 13 (5,false),
.cycle 2 16 true (0),
.last 17 (5,false),
.cycle 13 4 false (1),
.last 30 (5,false),
.cycle 13 5 true (1),
.cycle 11 2 true (0)
])
theorem kid05_part799_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part799) = true := by rfl

def kid05_part775 : Audit := .split 10 (1,true) (byMove [(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781),(kid05_part782),(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799)])

theorem kid05_part775_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part775) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781),(kid05_part782),(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part776_checked

  · exact kid05_part782_checked

  · exact kid05_part788_checked

  · exact kid05_part794_checked

  · exact kid05_part777_checked

  · exact kid05_part783_checked

  · exact kid05_part789_checked

  · exact kid05_part795_checked

  · exact kid05_part778_checked

  · exact kid05_part784_checked

  · exact kid05_part790_checked

  · exact kid05_part796_checked

  · exact kid05_part779_checked

  · exact kid05_part785_checked

  · exact kid05_part791_checked

  · exact kid05_part797_checked

  · exact kid05_part780_checked

  · exact kid05_part786_checked

  · exact kid05_part792_checked

  · exact kid05_part798_checked

  · exact kid05_part781_checked

  · exact kid05_part787_checked

  · exact kid05_part793_checked

  · exact kid05_part799_checked

def kid05_part801 : Audit := .cycle 14 11 true (0)
theorem kid05_part801_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part801) = true := by rfl

def kid05_part802 : Audit := .cycle 24 11 true (0)
theorem kid05_part802_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part802) = true := by rfl

def kid05_part803 : Audit := .cycle 13 1 false (-1)
theorem kid05_part803_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part803) = true := by rfl

def kid05_part804 : Audit := .cycle 12 1 false (-2)
theorem kid05_part804_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part804) = true := by rfl

def kid05_part805 : Audit := .split 19 (4,true) (byMove [
.cycle 15 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.last 24 (1,true),
.cycle 11 9 false (1),
.cycle 69 11 true (3),
.last 20 (1,true),
.cycle 13 35 true (-3),
.last 22 (1,true),
.cycle 21 11 true (0),
.cycle 77 11 true (3),
.last 21 (1,true),
.last 30 (1,true),
.cycle 73 11 true (3),
.cycle 20 1 false (-2),
.cycle 109 11 true (3),
.last 25 (1,true),
.cycle 13 29 true (-3),
.last 20 (1,true),
.cycle 101 11 true (3),
.last 22 (1,true),
.cycle 28 11 true (0),
.cycle 18 2 true (-1)
])
theorem kid05_part805_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part805) = true := by rfl

def kid05_part806 : Audit := .cycle 11 1 false (-1)
theorem kid05_part806_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part806) = true := by rfl

def kid05_part807 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 29 true (-2),
.last 20 (4,true),
.cycle 0 18 true (-1),
.last 14 (4,true),
.cycle 0 21 true (-2),
.cycle 14 11 true (1),
.cycle 16 11 true (2),
.cycle 0 16 true (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 8 6 true (-1),
.cycle 0 23 true (-2),
.cycle 22 11 true (0),
.cycle 10 4 true (-1),
.cycle 14 11 true (-1),
.last 14 (4,true),
.cycle 0 27 true (-2),
.cycle 29 11 true (1),
.last 26 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part807_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part807) = true := by rfl

def kid05_part808 : Audit := .cycle 0 21 true (-2)
theorem kid05_part808_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part808) = true := by rfl

def kid05_part809 : Audit := .cycle 12 11 true (0)
theorem kid05_part809_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part809) = true := by rfl

def kid05_part810 : Audit := .cycle 12 1 false (0)
theorem kid05_part810_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part810) = true := by rfl

def kid05_part811 : Audit := .cycle 14 11 true (-1)
theorem kid05_part811_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part811) = true := by rfl

def kid05_part812 : Audit := .cycle 16 11 true (-1)
theorem kid05_part812_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part812) = true := by rfl

def kid05_part813 : Audit := .split 13 (1,true) (byMove [
.cycle 26 11 true (0),
.cycle 38 11 true (0),
.cycle 10 4 false (0),
.last 19 (4,true),
.last 14 (4,true),
.cycle 30 11 true (0),
.cycle 16 11 true (1),
.cycle 7 8 false (3),
.cycle 14 11 true (0),
.cycle 24 11 true (0),
.cycle 16 11 true (-1),
.cycle 26 11 true (-1),
.cycle 32 11 true (0),
.cycle 7 21 false (3),
.cycle 10 4 false (0),
.cycle 16 11 true (0),
.last 14 (4,true),
.cycle 36 11 true (0),
.last 27 (4,true),
.last 17 (4,true),
.cycle 14 11 true (0),
.cycle 4 10 false (3),
.cycle 22 11 true (-1),
.last 18 (4,true)
])
theorem kid05_part813_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part813) = true := by rfl

def kid05_part814 : Audit := .cycle 30 11 true (0)
theorem kid05_part814_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part814) = true := by rfl

def kid05_part815 : Audit := .split 15 (1,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.last 24 (4,true),
.cycle 0 20 true (-2),
.last 16 (4,true),
.cycle 0 23 true (-2),
.cycle 16 11 true (1),
.cycle 18 11 true (2),
.cycle 0 38 true (-2),
.cycle 0 17 true (-2),
.last 16 (4,true),
.cycle 8 8 true (-2),
.cycle 0 25 true (-2),
.cycle 24 11 true (0),
.cycle 10 6 true (-2),
.cycle 16 11 true (-1),
.last 16 (4,true),
.cycle 0 29 true (-2),
.cycle 31 11 true (1),
.last 28 (4,true),
.last 18 (4,true),
.cycle 12 23 true (-2),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid05_part815_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part815) = true := by rfl

def kid05_part816 : Audit := .cycle 12 1 false (-2)
theorem kid05_part816_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part816) = true := by rfl

def kid05_part817 : Audit := .cycle 16 11 true (0)
theorem kid05_part817_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part817) = true := by rfl

def kid05_part818 : Audit := .cycle 11 1 false (-1)
theorem kid05_part818_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part818) = true := by rfl

def kid05_part819 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (-1),
.last 101 (4,true),
.last 77 (4,true),
.cycle 0 18 true (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 14 11 true (1),
.cycle 16 11 true (2),
.last 28 (4,true),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 22 11 true (0),
.last 17 (4,true),
.cycle 24 11 true (-1),
.cycle 20 11 true (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true),
.last 25 (4,true),
.last 26 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part819_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part819) = true := by rfl

def kid05_part820 : Audit := .split 15 (4,true) (byMove [
.cycle 12 5 false (1),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 20 (1,true),
.cycle 11 5 false (1),
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 0 21 true (-1),
.last 18 (1,true),
.cycle 17 11 true (0),
.cycle 0 23 true (-2),
.last 17 (1,true),
.last 26 (1,true),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M319.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M319.never m hm),
.last 17 (1,true),
.cycle 0 19 true (-1),
.last 16 (1,true),
.cycle 84 11 true (1),
.last 18 (1,true),
.cycle 24 11 true (0),
.cycle 14 2 true (-1)
])
theorem kid05_part820_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part820) = true := by rfl

def kid05_part821 : Audit := .cycle 12 11 true (0)
theorem kid05_part821_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part821) = true := by rfl

def kid05_part822 : Audit := .cycle 0 23 true (-2)
theorem kid05_part822_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part822) = true := by rfl

def kid05_part823 : Audit := .cycle 9 3 false (1)
theorem kid05_part823_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part823) = true := by rfl

def kid05_part824 : Audit := .split 14 (4,true) (byMove [
.cycle 16 11 true (0),
.last 15 (1,true),
.cycle 38 11 true (0),
.last 17 (1,true),
.last 28 (1,true),
.cycle 20 11 true (0),
.cycle 6 9 false (3),
.last 15 (1,true),
.cycle 21 1 true (1),
.cycle 15 11 true (1),
.cycle 0 20 true (-1),
.cycle 8 7 false (2),
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
.cycle 35 11 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part824_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part824) = true := by rfl

def kid05_part800 : Audit := .split 11 (5,false) (byMove [(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806),(kid05_part807),(kid05_part808),(kid05_part809),(kid05_part810),(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824)])

theorem kid05_part800_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part800) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some mv)) (byMove [(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806),(kid05_part807),(kid05_part808),(kid05_part809),(kid05_part810),(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part801_checked

  · exact kid05_part807_checked

  · exact kid05_part813_checked

  · exact kid05_part819_checked

  · exact kid05_part802_checked

  · exact kid05_part808_checked

  · exact kid05_part814_checked

  · exact kid05_part820_checked

  · exact kid05_part803_checked

  · exact kid05_part809_checked

  · exact kid05_part815_checked

  · exact kid05_part821_checked

  · exact kid05_part804_checked

  · exact kid05_part810_checked

  · exact kid05_part816_checked

  · exact kid05_part822_checked

  · exact kid05_part805_checked

  · exact kid05_part811_checked

  · exact kid05_part817_checked

  · exact kid05_part823_checked

  · exact kid05_part806_checked

  · exact kid05_part812_checked

  · exact kid05_part818_checked

  · exact kid05_part824_checked

def kid05_part825 : Audit := .cycle 15 1 false (-1)
theorem kid05_part825_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part825) = true := by rfl

def kid05_part826 : Audit := .split 10 (4,true) (byMove [
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 29 1 false (-3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (-3),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 13 (1,true),
.cycle 10 5 false (1),
.cycle 23 9 false (2),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.cycle 16 1 false (-2)
]),
.cycle 14 1 false (0),
.split 11 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 22 1 false (2),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 25 3 true (3),
.last 15 (5,false)
]),
.split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.last 14 (1,true),
.cycle 1 18 true (0),
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 9 4 true (0),
.cycle 17 1 true (1)
]),
.cycle 20 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (0),
.split 12 (1,true) (byMove [
.cycle 25 11 false (2),
.cycle 22 1 false (-2),
.last 14 (5,false),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 6 7 false (3),
.far true 1 ⟨0,[0, 0],[17, 17, 25, 8, 16, 64, 64],[17, 17, 32, 17, 1, 16, 64],96⟩,
.last 14 (5,false),
.cycle 23 9 false (2),
.cycle 37 1 false (-3),
.cycle 8 5 false (2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 20 1 false (-2),
.cycle 32 1 false (-2),
.cycle 10 5 false (1),
.cycle 28 1 false (-2),
.cycle 10 7 false (1),
.cycle 18 1 false (-2)
]),
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
.last 12 (1,true),
.cycle 24 1 false (2),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.last 13 (1,true),
.cycle 15 1 false (-3),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.last 12 (1,true),
.cycle 14 1 false (-2),
.cycle 5 7 false (3),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
]),
.cycle 2 14 true (0),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 21 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 1 18 true (0),
.cycle 13 1 false (-1),
.cycle 6 18 true (0),
.far true 1 ⟨0,[0, 0],[0, 16, 24, 8, 16, 64, 64],[16, 16, 32, 16, 0, 16, 64],96⟩,
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 8 4 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 13 (5,false),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 15 (5,false)
]),
.cycle 13 1 false (-1),
.cycle 5 18 true (0),
.cycle 11 3 true (1),
.cycle 10 2 true (0)
])
theorem kid05_part826_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part826) = true := by rfl

def kid05_part828 : Audit := .split 17 (4,true) (byMove [
.cycle 13 5 false (-1),
.last 22 (1,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.last 24 (1,true),
.cycle 44 27 true (0),
.last 18 (1,true),
.cycle 0 20 false (3),
.last 20 (1,true),
.cycle 11 8 true (-3),
.cycle 10 8 false (0),
.last 19 (1,true),
.cycle 10 10 false (0),
.cycle 50 27 true (-2),
.cycle 18 1 false (-4),
.cycle 11 7 false (-1),
.cycle 12 6 false (-1),
.cycle 44 27 true (0),
.last 18 (1,true),
.cycle 10 9 false (0),
.last 20 (1,true),
.cycle 24 5 true (0),
.cycle 16 2 true (-3)
])
theorem kid05_part828_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part828) = true := by rfl

def kid05_part829 : Audit := .split 21 (1,true) (byMove [
.cycle 78 45 true (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M322.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M322.never m hm),
.cycle 23 1 false (-3),
.cycle 22 1 false (-4),
.last 31 (4,true),
.last 122 (4,true),
.cycle 88 47 false (6),
.cycle 39 42 true (-1),
.cycle 22 27 true (-2),
.cycle 22 1 false (-2),
.cycle 11 11 false (1),
.cycle 12 31 true (-3),
.last 112 (4,true),
.last 129 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M323.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M323.never m hm),
.cycle 22 1 false (-4),
.proven (BB6.Agent11Raw39B1RCPumps.M324.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M324.never m hm),
.cycle 18 10 false (0),
.last 46 (4,true),
.last 25 (4,true),
.cycle 14 27 true (-3),
.cycle 43 46 true (-1),
.cycle 9 13 false (1),
.cycle 20 2 true (-3)
])
theorem kid05_part829_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part829) = true := by rfl

def kid05_part830 : Audit := .cycle 14 1 false (-2)
theorem kid05_part830_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part830) = true := by rfl

def kid05_part831 : Audit := .cycle 13 1 false (-3)
theorem kid05_part831_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part831) = true := by rfl

def kid05_part832 : Audit := .cycle 11 2 false (-1)
theorem kid05_part832_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part832) = true := by rfl

def kid05_part833 : Audit := .cycle 12 1 false (-2)
theorem kid05_part833_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part833) = true := by rfl

def kid05_part834 : Audit := .cycle 10 5 false (0)
theorem kid05_part834_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part834) = true := by rfl

def kid05_part835 : Audit := .split 13 (1,true) (byMove [
.last 18 (4,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 10 7 false (0),
.cycle 0 23 true (-2),
.cycle 15 12 true (1),
.cycle 0 27 true (-2),
.cycle 0 22 true (-2),
.last 14 (4,true),
.cycle 10 4 true (-2),
.cycle 10 8 false (0),
.cycle 10 6 false (0),
.cycle 0 27 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 17 (4,true),
.last 27 (4,true),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part835_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part835) = true := by rfl

def kid05_part836 : Audit := .cycle 0 26 true (-2)
theorem kid05_part836_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part836) = true := by rfl

def kid05_part837 : Audit := .cycle 0 23 true (-2)
theorem kid05_part837_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part837) = true := by rfl

def kid05_part838 : Audit := .split 13 (4,true) (byMove [
.cycle 13 5 false (0),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 11 4 true (-2),
.cycle 0 23 true (-2),
.last 14 (1,true),
.cycle 30 1 false (4),
.cycle 0 22 true (-2),
.cycle 16 3 true (2),
.cycle 10 4 true (-2),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 0 27 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.cycle 0 21 true (-2),
.last 14 (1,true),
.cycle 10 5 false (0),
.cycle 5 9 false (3),
.cycle 14 5 true (0),
.cycle 13 2 true (-1)
])
theorem kid05_part838_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part838) = true := by rfl

def kid05_part839 : Audit := .cycle 10 3 false (0)
theorem kid05_part839_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part839) = true := by rfl

def kid05_part840 : Audit := .split 14 (1,true) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M325.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M325.never m hm),
.cycle 10 13 false (0),
.cycle 12 4 false (-2),
.cycle 0 28 true (-3),
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 6 9 false (3),
.cycle 16 14 true (0),
.cycle 10 9 false (0),
.proven (BB6.Agent11Raw39B1RCPumps.M326.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M326.never m hm),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 10 7 false (0),
.cycle 10 8 false (0),
.cycle 12 4 false (-2),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 18 (4,true),
.last 29 (4,true),
.last 17 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part840_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part840) = true := by rfl

def kid05_part841 : Audit := .cycle 10 5 false (0)
theorem kid05_part841_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part841) = true := by rfl

def kid05_part842 : Audit := .cycle 10 7 false (0)
theorem kid05_part842_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part842) = true := by rfl

def kid05_part843 : Audit := .cycle 13 1 false (-3)
theorem kid05_part843_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part843) = true := by rfl

def kid05_part844 : Audit := .cycle 11 2 false (-1)
theorem kid05_part844_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part844) = true := by rfl

def kid05_part845 : Audit := .cycle 12 1 false (-2)
theorem kid05_part845_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part845) = true := by rfl

def kid05_part846 : Audit := .split 16 (4,true) (byMove [
.cycle 14 5 false (0),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 23 (1,true),
.last 19 (1,true),
.cycle 20 14 true (1),
.last 17 (1,true),
.last 48 (1,true),
.last 19 (1,true),
.cycle 2 33 true (-2),
.cycle 10 7 false (0),
.last 18 (1,true),
.cycle 10 9 false (0),
.cycle 20 16 true (0),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.cycle 12 5 false (0),
.cycle 0 81 true (-2),
.last 17 (1,true),
.cycle 10 8 false (0),
.last 19 (1,true),
.cycle 22 5 true (0),
.cycle 15 2 true (-2)
])
theorem kid05_part846_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part846) = true := by rfl

def kid05_part847 : Audit := .split 13 (1,true) (byMove [
.cycle 0 26 true (-2),
.cycle 10 12 false (0),
.last 27 (4,true),
.cycle 0 24 true (-2),
.last 14 (4,true),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.cycle 15 12 true (1),
.last 19 (4,true),
.cycle 0 22 true (-2),
.last 14 (4,true),
.cycle 8 6 false (2),
.cycle 10 6 false (0),
.cycle 10 7 false (0),
.last 19 (4,true),
.cycle 10 7 false (0),
.last 14 (4,true),
.cycle 10 4 false (0),
.last 17 (4,true),
.last 27 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part847_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part847) = true := by rfl

def kid05_part848 : Audit := .cycle 10 4 false (0)
theorem kid05_part848_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part848) = true := by rfl

def kid05_part849 : Audit := .cycle 5 8 false (3)
theorem kid05_part849_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part849) = true := by rfl

def kid05_part850 : Audit := .split 13 (4,true) (byMove [
.cycle 0 26 true (-2),
.last 14 (1,true),
.cycle 9 7 false (1),
.last 16 (1,true),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.last 14 (1,true),
.cycle 9 12 false (1),
.cycle 0 22 true (-2),
.cycle 16 3 true (2),
.cycle 8 6 false (2),
.cycle 10 6 false (0),
.last 14 (1,true),
.cycle 9 7 false (1),
.cycle 10 7 false (0),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.cycle 0 21 true (-2),
.last 14 (1,true),
.cycle 10 8 false (0),
.cycle 5 16 false (3),
.cycle 14 5 true (0),
.cycle 13 2 true (-1)
])
theorem kid05_part850_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part850) = true := by rfl

def kid05_part851 : Audit := .split 14 (4,true) (byMove [
.cycle 13 5 false (-1),
.last 25 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 10 9 false (0),
.cycle 10 7 false (0),
.last 15 (1,true),
.cycle 31 1 true (1),
.cycle 0 27 true (-2),
.cycle 17 5 true (1),
.cycle 10 5 false (0),
.last 16 (1,true),
.cycle 10 7 false (0),
.cycle 10 9 false (0),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 12 3 false (-1),
.cycle 0 87 true (-2),
.last 15 (1,true),
.cycle 10 6 false (0),
.cycle 5 10 false (3),
.cycle 16 5 true (0),
.cycle 13 2 true (-2)
])
theorem kid05_part851_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part851) = true := by rfl

def kid05_part827 : Audit := .split 12 (5,false) (byMove [(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832),(kid05_part833),(kid05_part834),(kid05_part835),(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851)])

theorem kid05_part827_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part827) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832),(kid05_part833),(kid05_part834),(kid05_part835),(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part828_checked

  · exact kid05_part834_checked

  · exact kid05_part840_checked

  · exact kid05_part846_checked

  · exact kid05_part829_checked

  · exact kid05_part835_checked

  · exact kid05_part841_checked

  · exact kid05_part847_checked

  · exact kid05_part830_checked

  · exact kid05_part836_checked

  · exact kid05_part842_checked

  · exact kid05_part848_checked

  · exact kid05_part831_checked

  · exact kid05_part837_checked

  · exact kid05_part843_checked

  · exact kid05_part849_checked

  · exact kid05_part832_checked

  · exact kid05_part838_checked

  · exact kid05_part844_checked

  · exact kid05_part850_checked

  · exact kid05_part833_checked

  · exact kid05_part839_checked

  · exact kid05_part845_checked

  · exact kid05_part851_checked

def kid05_part852 : Audit := .cycle 2 9 true (1)
theorem kid05_part852_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part852) = true := by rfl

def kid05_part854 : Audit := .cycle 2 10 true (1)
theorem kid05_part854_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part854) = true := by rfl

def kid05_part855 : Audit := .cycle 11 11 false (1)
theorem kid05_part855_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part855) = true := by rfl

def kid05_part856 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 1 17 false (3),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 17 false (3),
.cycle 16 1 true (-2),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 30 (4,true),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.last 30 (4,true),
.cycle 16 1 true (-2)
])
theorem kid05_part856_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part856) = true := by rfl

def kid05_part857 : Audit := .cycle 0 12 true (0)
theorem kid05_part857_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part857) = true := by rfl

def kid05_part858 : Audit := .split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.cycle 1 13 false (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 13 false (3),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.last 12 (5,false),
.cycle 16 3 false (0),
.cycle 17 6 false (-1),
.last 13 (5,false),
.cycle 24 1 false (0),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 12 (5,false)
])
theorem kid05_part858_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part858) = true := by rfl

def kid05_part859 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.last 13 (5,false),
.cycle 20 3 false (2),
.last 14 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 15 3 false (-1),
.cycle 22 3 false (2),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 2 12 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.cycle 11 2 true (0)
])
theorem kid05_part859_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part859) = true := by rfl

def kid05_part860 : Audit := .cycle 0 11 true (0)
theorem kid05_part860_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part860) = true := by rfl

def kid05_part861 : Audit := .cycle 1 10 true (1)
theorem kid05_part861_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part861) = true := by rfl

def kid05_part862 : Audit := .cycle 0 23 true (0)
theorem kid05_part862_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part862) = true := by rfl

def kid05_part863 : Audit := .cycle 3 8 true (1)
theorem kid05_part863_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part863) = true := by rfl

def kid05_part864 : Audit := .cycle 1 11 true (1)
theorem kid05_part864_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part864) = true := by rfl

def kid05_part865 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
])
theorem kid05_part865_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part865) = true := by rfl

def kid05_part866 : Audit := .split 14 (4,true) (byMove [
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.last 15 (5,false),
.cycle 20 5 false (3),
.cycle 17 5 false (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 15 5 false (1),
.cycle 16 5 false (0),
.cycle 16 5 false (0),
.cycle 22 5 false (3),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 15 5 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part866_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part866) = true := by rfl

def kid05_part867 : Audit := .cycle 11 6 false (1)
theorem kid05_part867_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part867) = true := by rfl

def kid05_part868 : Audit := .split 16 (5,false) (byMove [
.last 58 (4,true),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 46 (4,true),
.cycle 16 1 false (-2),
.cycle 14 4 true (-2),
.cycle 11 7 false (1),
.cycle 0 25 true (-2),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.cycle 14 4 false (0),
.cycle 11 7 false (1),
.cycle 14 6 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.cycle 10 8 false (2),
.last 20 (4,true),
.cycle 0 25 true (-2),
.cycle 11 9 false (1),
.cycle 9 8 false (2),
.last 19 (4,true)
])
theorem kid05_part868_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part868) = true := by rfl

def kid05_part869 : Audit := .cycle 2 11 true (1)
theorem kid05_part869_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part869) = true := by rfl

def kid05_part870 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 25 true (-2),
.last 13 (5,false),
.cycle 16 1 false (0),
.cycle 0 17 true (-1),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 13 true (1),
.cycle 8 4 true (1),
.cycle 16 3 false (0),
.cycle 13 6 false (0),
.last 13 (5,false),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 1 13 true (1),
.cycle 11 2 true (1)
])
theorem kid05_part870_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part870) = true := by rfl

def kid05_part871 : Audit := .split 12 (4,true) (byMove [
.cycle 11 5 false (1),
.cycle 26 13 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.last 13 (5,false),
.cycle 15 3 false (1),
.last 14 (5,false),
.last 14 (5,false),
.cycle 21 3 false (3),
.cycle 1 15 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 2 16 true (0),
.cycle 13 3 false (1),
.cycle 14 3 false (0),
.cycle 5 24 true (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0)
])
theorem kid05_part871_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part871) = true := by rfl

def kid05_part872 : Audit := .cycle 0 11 true (0)
theorem kid05_part872_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part872) = true := by rfl

def kid05_part873 : Audit := .cycle 1 10 true (1)
theorem kid05_part873_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part873) = true := by rfl

def kid05_part874 : Audit := .cycle 2 9 true (1)
theorem kid05_part874_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part874) = true := by rfl

def kid05_part875 : Audit := .cycle 2 12 true (1)
theorem kid05_part875_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part875) = true := by rfl

def kid05_part876 : Audit := .cycle 1 11 true (1)
theorem kid05_part876_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part876) = true := by rfl

def kid05_part877 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3)
])
theorem kid05_part877_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part877) = true := by rfl

def kid05_part853 : Audit := .split 10 (1,true) (byMove [(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857),(kid05_part858),(kid05_part859),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877)])

theorem kid05_part853_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part853) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857),(kid05_part858),(kid05_part859),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part854_checked

  · exact kid05_part860_checked

  · exact kid05_part866_checked

  · exact kid05_part872_checked

  · exact kid05_part855_checked

  · exact kid05_part861_checked

  · exact kid05_part867_checked

  · exact kid05_part873_checked

  · exact kid05_part856_checked

  · exact kid05_part862_checked

  · exact kid05_part868_checked

  · exact kid05_part874_checked

  · exact kid05_part857_checked

  · exact kid05_part863_checked

  · exact kid05_part869_checked

  · exact kid05_part875_checked

  · exact kid05_part858_checked

  · exact kid05_part864_checked

  · exact kid05_part870_checked

  · exact kid05_part876_checked

  · exact kid05_part859_checked

  · exact kid05_part865_checked

  · exact kid05_part871_checked

  · exact kid05_part877_checked

def kid05_part878 : Audit := .split 12 (4,true) (byMove [
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
.last 15 (1,true),
.cycle 15 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.cycle 15 3 false (1),
.last 15 (1,true),
.cycle 15 3 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 9 5 false (2),
.cycle 17 3 false (-1)
]),
.cycle 19 3 false (3),
.split 13 (1,true) (byMove [
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
.cycle 17 3 false (1),
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
.split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 21 3 false (1),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 21 3 false (3),
.cycle 14 1 true (0),
.last 16 (1,true),
.cycle 16 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 23 3 false (3),
.cycle 2 14 true (0),
.cycle 14 1 true (0)
]),
.cycle 0 14 true (0),
.cycle 20 3 false (4),
.cycle 13 3 false (1),
.split 14 (1,true) (byMove [
.cycle 0 18 true (-1),
.cycle 22 3 false (0),
.last 16 (5,false),
.cycle 0 19 true (-1),
.cycle 12 3 false (0),
.cycle 15 3 false (-1),
.cycle 7 17 false (3),
.cycle 7 21 false (4),
.last 16 (5,false),
.cycle 0 16 true (-1),
.cycle 34 3 false (0),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.cycle 17 3 false (-1),
.last 16 (5,false),
.cycle 17 3 false (1),
.cycle 12 3 false (0),
.cycle 15 3 false (-1),
.cycle 28 3 false (0),
.cycle 25 11 false (3),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 10 7 false (2),
.cycle 18 3 false (0)
]),
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
.last 14 (1,true),
.cycle 0 18 true (-1),
.cycle 21 3 false (3),
.cycle 12 2 true (-1),
.cycle 14 3 false (0),
.last 15 (1,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.last 14 (1,true),
.cycle 14 3 false (0),
.cycle 7 17 false (3),
.cycle 15 3 false (-1),
.cycle 11 3 false (1)
]),
.cycle 2 12 true (0),
.split 13 (1,true) (byMove [
.cycle 20 3 false (2),
.cycle 21 3 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 7 16 true (0),
.last 14 (5,false),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.last 15 (5,false),
.cycle 21 3 false (3),
.cycle 12 2 true (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 7 18 true (0),
.cycle 2 13 true (0),
.last 14 (5,false)
]),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 2 13 true (0),
.cycle 11 2 true (0)
])
theorem kid05_part878_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part878) = true := by rfl

def kid05_part879 : Audit := .cycle 0 11 true (0)
theorem kid05_part879_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part879) = true := by rfl

def kid05_part881 : Audit := .cycle 2 10 true (1)
theorem kid05_part881_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part881) = true := by rfl

def kid05_part882 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 24 1 true (-2),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 13 (5,false),
.cycle 24 1 false (0),
.cycle 0 16 true (-1),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (2),
.last 12 (5,false)
])
theorem kid05_part882_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part882) = true := by rfl

def kid05_part883 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 17 1 true (-3),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 true (-1),
.cycle 16 1 true (-2),
.last 18 (1,true),
.cycle 11 7 false (1),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.cycle 32 1 false (-2),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 17 1 true (-1),
.cycle 16 1 true (-2)
])
theorem kid05_part883_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part883) = true := by rfl

def kid05_part884 : Audit := .cycle 0 12 true (0)
theorem kid05_part884_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part884) = true := by rfl

def kid05_part885 : Audit := .cycle 13 1 true (-1)
theorem kid05_part885_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part885) = true := by rfl

def kid05_part886 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 21 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 3 false (-1),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 16 3 false (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.cycle 15 3 false (1),
.last 15 (1,true),
.cycle 16 3 false (-2),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 18 3 false (0),
.cycle 9 5 false (2),
.cycle 16 3 false (0)
])
theorem kid05_part886_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part886) = true := by rfl

def kid05_part887 : Audit := .cycle 0 11 true (0)
theorem kid05_part887_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part887) = true := by rfl

def kid05_part888 : Audit := .cycle 1 10 true (1)
theorem kid05_part888_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part888) = true := by rfl

def kid05_part889 : Audit := .cycle 0 23 true (0)
theorem kid05_part889_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part889) = true := by rfl

def kid05_part890 : Audit := .cycle 3 8 true (1)
theorem kid05_part890_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part890) = true := by rfl

def kid05_part891 : Audit := .cycle 11 1 true (3)
theorem kid05_part891_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part891) = true := by rfl

def kid05_part892 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (2),
.cycle 15 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 28 true (0),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.last 13 (1,true),
.cycle 8 8 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.cycle 8 13 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
theorem kid05_part892_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part892) = true := by rfl

def kid05_part893 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (-1),
.cycle 23 5 false (0),
.last 18 (5,false),
.cycle 0 21 true (-1),
.cycle 14 3 false (0),
.cycle 17 5 false (-1),
.cycle 6 21 false (3),
.cycle 6 27 false (4),
.last 18 (5,false),
.cycle 0 18 true (-1),
.cycle 20 1 true (2),
.cycle 8 9 false (2),
.cycle 17 5 false (0),
.cycle 19 5 false (-1),
.last 18 (5,false),
.cycle 18 5 false (1),
.cycle 14 3 false (0),
.cycle 17 5 false (-1),
.cycle 30 5 false (0),
.cycle 29 11 false (3),
.cycle 12 5 false (2),
.cycle 0 18 true (-1),
.cycle 10 7 false (2),
.cycle 18 5 false (0)
])
theorem kid05_part893_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part893) = true := by rfl

def kid05_part894 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 9 11 false (2),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 16 7 false (0),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 13 (5,false),
.cycle 19 1 false (-1),
.cycle 16 3 false (-1),
.last 16 (5,false),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 13 8 false (1)
])
theorem kid05_part894_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part894) = true := by rfl

def kid05_part895 : Audit := .split 16 (5,false) (byMove [
.last 22 (1,true),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 30 (1,true),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 11 7 false (1),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.last 18 (1,true),
.cycle 11 7 false (1),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 11 18 true (-3),
.last 20 (1,true),
.cycle 11 9 false (1),
.cycle 9 8 false (2),
.cycle 14 5 false (0)
])
theorem kid05_part895_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part895) = true := by rfl

def kid05_part896 : Audit := .cycle 2 11 true (1)
theorem kid05_part896_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part896) = true := by rfl

def kid05_part897 : Audit := .cycle 11 3 false (1)
theorem kid05_part897_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part897) = true := by rfl

def kid05_part898 : Audit := .split 13 (5,false) (byMove [
.cycle 11 6 false (1),
.cycle 8 14 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 9 6 false (2),
.cycle 13 1 false (-1),
.cycle 16 3 false (0),
.last 14 (1,true),
.cycle 25 3 false (3),
.cycle 17 3 false (1),
.cycle 12 2 true (-1),
.cycle 14 3 false (0),
.last 15 (1,true),
.cycle 16 3 false (-2),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.last 14 (1,true),
.cycle 15 3 false (-1),
.cycle 5 9 false (3),
.cycle 14 3 false (0),
.cycle 11 3 false (1)
])
theorem kid05_part898_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part898) = true := by rfl

def kid05_part899 : Audit := .cycle 0 11 true (0)
theorem kid05_part899_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part899) = true := by rfl

def kid05_part900 : Audit := .cycle 1 10 true (1)
theorem kid05_part900_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part900) = true := by rfl

def kid05_part901 : Audit := .cycle 2 9 true (1)
theorem kid05_part901_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part901) = true := by rfl

def kid05_part902 : Audit := .cycle 2 12 true (1)
theorem kid05_part902_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part902) = true := by rfl

def kid05_part903 : Audit := .cycle 11 1 true (3)
theorem kid05_part903_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part903) = true := by rfl

def kid05_part904 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 12 2 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 14 2 true (1),
.last 12 (1,true),
.cycle 13 2 true (0),
.cycle 2 12 true (1),
.cycle 12 2 true (2),
.cycle 12 2 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
theorem kid05_part904_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part904) = true := by rfl

def kid05_part880 : Audit := .split 10 (4,true) (byMove [(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part894),(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904)])

theorem kid05_part880_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part880) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part894),(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part881_checked

  · exact kid05_part887_checked

  · exact kid05_part893_checked

  · exact kid05_part899_checked

  · exact kid05_part882_checked

  · exact kid05_part888_checked

  · exact kid05_part894_checked

  · exact kid05_part900_checked

  · exact kid05_part883_checked

  · exact kid05_part889_checked

  · exact kid05_part895_checked

  · exact kid05_part901_checked

  · exact kid05_part884_checked

  · exact kid05_part890_checked

  · exact kid05_part896_checked

  · exact kid05_part902_checked

  · exact kid05_part885_checked

  · exact kid05_part891_checked

  · exact kid05_part897_checked

  · exact kid05_part903_checked

  · exact kid05_part886_checked

  · exact kid05_part892_checked

  · exact kid05_part898_checked

  · exact kid05_part904_checked

def kid05_part906 : Audit := .cycle 0 15 true (0)
theorem kid05_part906_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part906) = true := by rfl

def kid05_part907 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 44 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 15 true (0),
.cycle 0 22 true (-1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 0 19 true (0),
.last 13 (5,false),
.cycle 58 43 true (-4),
.cycle 50 63 true (-5),
.last 18 (5,false),
.cycle 13 1 false (-1),
.cycle 0 25 true (-2),
.last 13 (5,false),
.cycle 0 15 true (0),
.cycle 0 20 true (-1),
.cycle 0 15 true (0),
.cycle 0 24 true (-1),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid05_part907_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part907) = true := by rfl

def kid05_part908 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 18 1 false (-2),
.cycle 13 1 false (-1),
.cycle 20 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 28 1 false (0),
.cycle 21 1 false (1),
.last 15 (1,true),
.cycle 21 1 false (-3),
.cycle 22 1 false (0),
.cycle 14 1 false (-2),
.cycle 18 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 0 19 true (-1),
.cycle 21 1 false (-1),
.cycle 24 1 false (-2)
])
theorem kid05_part908_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part908) = true := by rfl

def kid05_part909 : Audit := .split 14 (1,true) (byMove [
.cycle 26 1 false (0),
.cycle 27 1 false (-1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.last 16 (5,false),
.last 15 (5,false),
.cycle 21 1 false (-1),
.cycle 22 1 false (-2),
.last 16 (5,false),
.cycle 27 1 false (1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 33 true (0),
.last 16 (5,false),
.last 15 (5,false)
])
theorem kid05_part909_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part909) = true := by rfl

def kid05_part910 : Audit := .split 14 (5,false) (byMove [
.last 32 (1,true),
.last 15 (1,true),
.cycle 18 1 false (-2),
.last 25 (1,true),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.last 16 (1,true),
.cycle 7 9 false (3),
.cycle 0 17 true (-1),
.last 28 (1,true),
.cycle 21 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 0, 64],64⟩,
.cycle 12 8 false (0),
.last 15 (1,true),
.last 20 (1,true),
.cycle 0 19 true (-1),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.last 16 (1,true),
.cycle 10 7 false (2),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.cycle 29 2 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 0, 64],64⟩
])
theorem kid05_part910_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part910) = true := by rfl

def kid05_part911 : Audit := .split 16 (5,false) (byMove [
.last 22 (1,true),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 4 false (-1),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 12 7 false (0),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.last 18 (1,true),
.cycle 12 7 false (0),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 18 (1,true),
.cycle 14 5 false (0),
.last 20 (1,true),
.cycle 12 9 false (0),
.cycle 9 8 false (2),
.cycle 10 8 false (2)
])
theorem kid05_part911_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part911) = true := by rfl

def kid05_part912 : Audit := .cycle 2 11 true (1)
theorem kid05_part912_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part912) = true := by rfl

def kid05_part913 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 17 9 false (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
theorem kid05_part913_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part913) = true := by rfl

def kid05_part914 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 2 true (1),
.cycle 13 1 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 28 1 false (0),
.cycle 14 5 false (1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 13 2 true (1),
.cycle 13 1 true (1)
])
theorem kid05_part914_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part914) = true := by rfl

def kid05_part915 : Audit := .cycle 0 13 true (0)
theorem kid05_part915_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part915) = true := by rfl

def kid05_part916 : Audit := .split 14 (5,false) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 8 7 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 18 true (1),
.cycle 3 12 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4),
.cycle 6 9 true (1),
.last 15 (1,true),
.last 20 (1,true),
.cycle 2 15 true (1),
.cycle 11 4 true (1),
.cycle 11 8 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4)
])
theorem kid05_part916_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part916) = true := by rfl

def kid05_part917 : Audit := .cycle 8 4 true (1)
theorem kid05_part917_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part917) = true := by rfl

def kid05_part918 : Audit := .split 19 (1,true) (byMove [
.cycle 0 41 true (-2),
.cycle 12 14 false (1),
.last 21 (5,false),
.cycle 0 35 true (-2),
.cycle 17 3 false (-1),
.cycle 14 6 false (0),
.cycle 0 23 true (-2),
.cycle 22 14 true (-1),
.last 21 (5,false),
.cycle 0 35 true (-2),
.last 32 (5,false),
.cycle 8 12 false (2),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.last 21 (5,false),
.cycle 12 9 false (1),
.cycle 17 3 false (-1),
.cycle 14 6 false (0),
.cycle 0 23 true (-2),
.cycle 16 11 false (2),
.cycle 16 5 false (0),
.cycle 59 23 false (3),
.cycle 16 7 false (0),
.cycle 10 10 false (2)
])
theorem kid05_part918_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part918) = true := by rfl

def kid05_part919 : Audit := .split 12 (1,true) (byMove [
.cycle 16 6 false (0),
.cycle 0 40 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 14 6 false (2),
.cycle 21 6 false (5),
.last 14 (5,false),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 13 6 false (1),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 16 6 false (2),
.cycle 13 1 false (-1),
.cycle 13 6 false (0),
.last 13 (5,false),
.cycle 15 6 false (1),
.cycle 1 14 true (0),
.cycle 13 6 false (1),
.cycle 27 6 false (1),
.cycle 11 2 true (0),
.cycle 13 6 false (1)
])
theorem kid05_part919_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part919) = true := by rfl

def kid05_part920 : Audit := .split 13 (5,false) (byMove [
.cycle 16 13 true (0),
.cycle 28 13 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 87 13 true (3),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 0 25 true (-2),
.cycle 14 13 true (0),
.cycle 14 1 false (0),
.cycle 18 13 true (-1),
.cycle 20 13 true (-1),
.last 15 (1,true),
.cycle 36 13 true (0),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 20 13 true (0),
.cycle 13 1 false (-1),
.last 15 (1,true),
.cycle 0 23 true (-2),
.cycle 14 13 true (0),
.cycle 0 27 true (-2),
.cycle 9 5 false (2),
.cycle 10 5 false (2)
])
theorem kid05_part920_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part920) = true := by rfl

def kid05_part921 : Audit := .cycle 19 1 false (-1)
theorem kid05_part921_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part921) = true := by rfl

def kid05_part922 : Audit := .cycle 12 3 false (0)
theorem kid05_part922_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part922) = true := by rfl

def kid05_part923 : Audit := .split 16 (5,false) (byMove [
.cycle 14 6 false (0),
.last 27 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 4 false (-1),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.last 17 (1,true),
.cycle 0 32 true (-2),
.cycle 0 29 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.last 18 (1,true),
.cycle 12 7 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.cycle 14 5 false (0),
.last 17 (1,true),
.cycle 12 6 false (0),
.cycle 5 12 false (3),
.cycle 11 6 false (1),
.cycle 14 3 false (0)
])
theorem kid05_part923_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part923) = true := by rfl

def kid05_part924 : Audit := .cycle 2 11 true (1)
theorem kid05_part924_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part924) = true := by rfl

def kid05_part925 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 7 false (1),
.cycle 13 8 false (1),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
theorem kid05_part925_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part925) = true := by rfl

def kid05_part926 : Audit := .cycle 13 5 false (1)
theorem kid05_part926_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part926) = true := by rfl

def kid05_part927 : Audit := .cycle 0 13 true (0)
theorem kid05_part927_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part927) = true := by rfl

def kid05_part928 : Audit := .split 14 (5,false) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 10 6 true (1),
.cycle 0 16 true (0),
.cycle 12 3 true (2),
.cycle 10 5 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 18 true (1),
.cycle 3 12 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4),
.cycle 10 7 true (1),
.last 15 (1,true),
.cycle 9 10 true (1),
.cycle 2 15 true (1),
.cycle 11 4 true (1),
.cycle 11 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4)
])
theorem kid05_part928_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part928) = true := by rfl

def kid05_part929 : Audit := .cycle 10 2 true (1)
theorem kid05_part929_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part929) = true := by rfl

def kid05_part905 : Audit := .split 11 (4,true) (byMove [(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917),(kid05_part918),(kid05_part919),(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929)])

theorem kid05_part905_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part905) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some mv)) (byMove [(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917),(kid05_part918),(kid05_part919),(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part906_checked

  · exact kid05_part912_checked

  · exact kid05_part918_checked

  · exact kid05_part924_checked

  · exact kid05_part907_checked

  · exact kid05_part913_checked

  · exact kid05_part919_checked

  · exact kid05_part925_checked

  · exact kid05_part908_checked

  · exact kid05_part914_checked

  · exact kid05_part920_checked

  · exact kid05_part926_checked

  · exact kid05_part909_checked

  · exact kid05_part915_checked

  · exact kid05_part921_checked

  · exact kid05_part927_checked

  · exact kid05_part910_checked

  · exact kid05_part916_checked

  · exact kid05_part922_checked

  · exact kid05_part928_checked

  · exact kid05_part911_checked

  · exact kid05_part917_checked

  · exact kid05_part923_checked

  · exact kid05_part929_checked

def kid05_part665 : Audit := .split 9 (4,false) (byMove [(kid05_part666),(kid05_part667),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part719),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part775),(kid05_part800),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part852),(kid05_part853),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part905)])

theorem kid05_part665_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (kid05_part665) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part666),(kid05_part667),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part719),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part775),(kid05_part800),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part852),(kid05_part853),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part905)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part666_checked

  · exact kid05_part744_checked

  · exact kid05_part750_checked

  · exact kid05_part852_checked

  · exact kid05_part667_checked

  · exact kid05_part745_checked

  · exact kid05_part775_checked

  · exact kid05_part853_checked

  · exact kid05_part692_checked

  · exact kid05_part746_checked

  · exact kid05_part800_checked

  · exact kid05_part878_checked

  · exact kid05_part693_checked

  · exact kid05_part747_checked

  · exact kid05_part825_checked

  · exact kid05_part879_checked

  · exact kid05_part694_checked

  · exact kid05_part748_checked

  · exact kid05_part826_checked

  · exact kid05_part880_checked

  · exact kid05_part719_checked

  · exact kid05_part749_checked

  · exact kid05_part827_checked

  · exact kid05_part905_checked

def kid05_part931 : Audit := .cycle 0 13 true (0)
theorem kid05_part931_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part931) = true := by rfl

def kid05_part932 : Audit := .split 10 (1,true) (byMove [
.cycle 0 15 true (-1),
.cycle 0 38 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.last 69 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 43 (4,true),
.cycle 0 33 true (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (4,true),
.last 27 (4,true),
.last 14 (4,true),
.last 82 (4,true),
.cycle 0 35 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 121 (4,true),
.last 49 (4,true),
.cycle 0 15 true (-1),
.last 25 (4,true),
.cycle 0 17 true (-1),
.last 14 (4,true),
.cycle 9 3 false (1)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 15, 15, 1, 64, 15, 64],80⟩,
.cycle 0 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 33 true (-2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 44 true (-2),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 26 true (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 17 true (0),
.last 14 (4,true),
.cycle 0 42 true (-2),
.cycle 0 26 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 0 28 true (-1),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 30 true (-1)
]),
.cycle 0 15 true (0),
.cycle 70 71 true (-4),
.cycle 138 86 false (-4),
.cycle 1 32 false (3),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 35 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 27 (4,true),
.cycle 0 15 true (-1),
.cycle 10 2 true (-1),
.last 75 (4,true),
.last 15 (4,true),
.last 12 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.proven (BB6.Agent11Raw39B1RCPumps.M330.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M330.never m hm),
.cycle 0 15 true (-1),
.last 13 (4,true),
.last 131 (4,true),
.last 15 (4,true),
.last 12 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M331.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M331.never m hm)
]),
.cycle 0 34 true (-2),
.cycle 0 13 true (0),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.cycle 0 20 true (-1),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 10 2 true (0),
.last 1881 (4,true),
.cycle 0 17 true (0),
.last 12 (4,true),
.cycle 0 38 true (-2),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.last 60 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (0),
.cycle 0 42 true (-2),
.last 13 (4,true),
.last 28 (4,true),
.cycle 0 20 true (-1),
.last 12 (4,true),
.cycle 0 24 true (-2),
.cycle 2 11 true (0),
.cycle 1 13 true (0),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 26 true (-2)
]),
.cycle 9 2 true (0)
])
theorem kid05_part932_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part932) = true := by rfl

def kid05_part933 : Audit := .cycle 13 1 false (-1)
theorem kid05_part933_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part933) = true := by rfl

def kid05_part934 : Audit := .split 12 (1,true) (byMove [
.cycle 22 1 false (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
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
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.last 15 (4,true),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 30 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 13 1 true (3),
.cycle 22 1 false (0),
.cycle 11 3 true (1),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 20 1 false (0),
.last 15 (4,true),
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
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.split 13 (4,true) (byMove [
.cycle 20 1 false (-2),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 15 1 false (-1),
.cycle 23 1 false (1),
.last 15 (4,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 16 1 false (0),
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
.last 15 (4,false),
.cycle 17 1 false (-1)
]),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 29 true (0),
.split 13 (4,false) (byMove [
.cycle 2 13 true (0),
.cycle 12 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 0 28 true (0),
.cycle 0 30 true (0),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.cycle 0 31 true (0),
.cycle 19 1 false (-1),
.last 15 (4,true),
.cycle 17 1 false (-1),
.cycle 0 29 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 30 true (0),
.cycle 13 1 true (3),
.cycle 0 16 true (0)
]),
.cycle 0 15 true (0)
])
theorem kid05_part934_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part934) = true := by rfl

def kid05_part936 : Audit := .cycle 0 15 true (-1)
theorem kid05_part936_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part936) = true := by rfl

def kid05_part937 : Audit := .split 20 (4,false) (byMove [
.last 26 (1,true),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 22 (1,true),
.cycle 17 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-1),
.cycle 10 12 true (-2),
.cycle 19 2 true (-2),
.last 22 (1,true),
.cycle 17 5 false (1),
.last 24 (1,true),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.last 22 (1,true),
.cycle 18 6 false (0),
.last 24 (1,true),
.cycle 14 7 false (1),
.last 23 (1,true),
.cycle 9 12 false (1)
])
theorem kid05_part937_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part937) = true := by rfl

def kid05_part938 : Audit := .cycle 12 1 false (0)
theorem kid05_part938_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part938) = true := by rfl

def kid05_part939 : Audit := .cycle 11 1 false (-1)
theorem kid05_part939_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part939) = true := by rfl

def kid05_part940 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 20 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 true (1),
.cycle 11 2 true (-1),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 24 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 21 (1,true),
.cycle 0 15 true (-1),
.last 24 (1,true),
.cycle 0 17 true (-1),
.cycle 18 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid05_part940_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part940) = true := by rfl

def kid05_part941 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 39 (1,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 152 (1,true),
.cycle 18 7 false (1),
.cycle 19 6 false (-1),
.cycle 9 4 false (1)
])
theorem kid05_part941_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part941) = true := by rfl

def kid05_part942 : Audit := .split 12 (1,true) (byMove [
.last 22 (4,false),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 20 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 23 (4,false),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 24 (4,false),
.last 13 (4,false),
.cycle 0 15 true (0)
])
theorem kid05_part942_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part942) = true := by rfl

def kid05_part943 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 17 (1,true),
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 12 12 true (-1),
.cycle 14 2 true (-1),
.last 17 (1,true),
.cycle 11 5 false (2),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.last 17 (1,true),
.cycle 13 6 false (1),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 12 12 true (-1),
.cycle 9 7 false (2)
])
theorem kid05_part943_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part943) = true := by rfl

def kid05_part944 : Audit := .cycle 0 13 true (0)
theorem kid05_part944_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part944) = true := by rfl

def kid05_part945 : Audit := .cycle 11 1 false (1)
theorem kid05_part945_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part945) = true := by rfl

def kid05_part946 : Audit := .split 11 (4,false) (byMove [
.last 122 (1,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.last 23 (1,true),
.last 12 (1,true),
.cycle 16 1 false (2),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 13 2 true (0),
.last 13 (1,true),
.cycle 11 5 false (1),
.last 27 (1,true),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 0 18 true (-1),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 9 7 false (2)
])
theorem kid05_part946_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part946) = true := by rfl

def kid05_part947 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 14 (1,true),
.cycle 11 5 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 1 true (2),
.cycle 11 2 true (0),
.last 14 (1,true),
.cycle 11 5 false (1),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.last 14 (1,true),
.cycle 11 6 false (2),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 16 1 true (2),
.cycle 9 4 true (0)
])
theorem kid05_part947_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part947) = true := by rfl

def kid05_part948 : Audit := .split 12 (1,true) (byMove [
.last 22 (4,false),
.last 23 (4,false),
.last 15 (4,false),
.last 20 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 0 15 true (-1),
.last 20 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 17 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 33 (4,false),
.last 19 (4,false),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 13 (4,false),
.last 19 (4,false)
])
theorem kid05_part948_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part948) = true := by rfl

def kid05_part949 : Audit := .split 15 (4,false) (byMove [
.cycle 2 26 false (3),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 0 39 true (-3),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 14 2 true (-3),
.last 17 (1,true),
.cycle 11 5 false (0),
.last 19 (1,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 17 (1,true),
.cycle 13 6 false (-1),
.last 130 (1,true),
.cycle 12 7 false (0),
.last 18 (1,true),
.cycle 9 7 false (1)
])
theorem kid05_part949_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part949) = true := by rfl

def kid05_part950 : Audit := .split 14 (1,true) (byMove [
.last 24 (4,false),
.last 25 (4,false),
.last 17 (4,false),
.cycle 0 16 true (-1),
.cycle 0 18 true (-1),
.last 17 (4,false),
.cycle 0 15 true (-1),
.last 24 (4,false),
.last 24 (4,false),
.last 22 (4,false),
.last 15 (4,false),
.last 16 (4,false),
.last 19 (4,false),
.last 20 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.last 27 (4,false),
.last 17 (4,false),
.last 29 (4,false),
.last 27 (4,false),
.cycle 2 13 true (-1),
.last 26 (4,false),
.last 15 (4,false),
.last 19 (4,false)
])
theorem kid05_part950_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part950) = true := by rfl

def kid05_part951 : Audit := .cycle 11 1 false (-1)
theorem kid05_part951_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part951) = true := by rfl

def kid05_part952 : Audit := .split 11 (4,false) (byMove [
.last 38 (1,true),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 10 2 true (-1),
.cycle 13 2 true (-2),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 0 17 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 0 15 true (-1),
.last 12 (1,true),
.last 130 (1,true),
.last 14 (1,true),
.cycle 10 3 false (0),
.cycle 9 7 false (1)
])
theorem kid05_part952_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part952) = true := by rfl

def kid05_part953 : Audit := .split 12 (4,false) (byMove [
.last 18 (1,true),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 14 (1,true),
.cycle 11 5 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.last 14 (1,true),
.cycle 11 5 false (-1),
.last 16 (1,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 14 (1,true),
.cycle 11 6 false (0),
.last 16 (1,true),
.cycle 11 7 false (0),
.cycle 11 6 false (0),
.cycle 9 4 false (1)
])
theorem kid05_part953_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part953) = true := by rfl

def kid05_part954 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (0),
.last 24 (4,false),
.last 16 (4,false),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 13 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 19 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.cycle 2 13 true (0),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 24 (4,false),
.last 13 (4,false),
.cycle 0 15 true (0)
])
theorem kid05_part954_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part954) = true := by rfl

def kid05_part955 : Audit := .split 16 (4,false) (byMove [
.last 114 (1,true),
.cycle 14 10 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.last 18 (1,true),
.cycle 14 5 false (0),
.cycle 0 31 true (-2),
.cycle 17 1 false (-1),
.last 19 (1,true),
.cycle 15 2 true (-2),
.last 18 (1,true),
.cycle 14 5 false (0),
.last 20 (1,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.last 18 (1,true),
.cycle 11 6 false (2),
.cycle 0 31 true (-2),
.cycle 14 7 false (0),
.last 19 (1,true),
.cycle 9 8 false (2)
])
theorem kid05_part955_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part955) = true := by rfl

def kid05_part956 : Audit := .cycle 0 13 true (0)
theorem kid05_part956_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part956) = true := by rfl

def kid05_part957 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 19 (1,true),
.cycle 14 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 11 14 true (-1),
.cycle 16 2 true (-1),
.last 19 (1,true),
.cycle 14 5 false (2),
.last 21 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.last 19 (1,true),
.cycle 15 6 false (1),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 11 14 true (-1),
.cycle 9 9 false (2)
])
theorem kid05_part957_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part957) = true := by rfl

def kid05_part958 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.last 23 (1,true),
.last 12 (1,true),
.last 29 (1,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 8 4 true (0),
.last 18 (1,true),
.last 12 (1,true),
.last 27 (1,true),
.cycle 18 1 false (-2),
.cycle 13 3 true (1),
.cycle 13 2 false (-1),
.cycle 2 11 true (0),
.last 12 (1,true),
.cycle 0 31 true (-2),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 9 8 false (2)
])
theorem kid05_part958_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part958) = true := by rfl

def kid05_part959 : Audit := .cycle 9 2 true (0)
theorem kid05_part959_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part959) = true := by rfl

def kid05_part935 : Audit := .split 10 (4,true) (byMove [(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943),(kid05_part944),(kid05_part945),(kid05_part946),(kid05_part947),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959)])

theorem kid05_part935_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part935) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943),(kid05_part944),(kid05_part945),(kid05_part946),(kid05_part947),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part936_checked

  · exact kid05_part942_checked

  · exact kid05_part948_checked

  · exact kid05_part954_checked

  · exact kid05_part937_checked

  · exact kid05_part943_checked

  · exact kid05_part949_checked

  · exact kid05_part955_checked

  · exact kid05_part938_checked

  · exact kid05_part944_checked

  · exact kid05_part950_checked

  · exact kid05_part956_checked

  · exact kid05_part939_checked

  · exact kid05_part945_checked

  · exact kid05_part951_checked

  · exact kid05_part957_checked

  · exact kid05_part940_checked

  · exact kid05_part946_checked

  · exact kid05_part952_checked

  · exact kid05_part958_checked

  · exact kid05_part941_checked

  · exact kid05_part947_checked

  · exact kid05_part953_checked

  · exact kid05_part959_checked

def kid05_part960 : Audit := .cycle 11 1 false (-1)
theorem kid05_part960_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part960) = true := by rfl

def kid05_part961 : Audit := .cycle 2 9 true (1)
theorem kid05_part961_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part961) = true := by rfl

def kid05_part962 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 26 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 12 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 0 22 true (-2),
.cycle 24 1 false (0),
.last 12 (4,true),
.cycle 13 3 false (0),
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
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
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
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1),
.cycle 16 7 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 0 17 true (-1),
.last 15 (4,true),
.last 12 (4,true),
.cycle 12 7 false (0),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 0 25 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.last 13 (4,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 5 false (1)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (1),
.last 13 (4,true),
.cycle 7 8 true (1),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid05_part962_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part962) = true := by rfl

def kid05_part963 : Audit := .cycle 24 1 false (2)
theorem kid05_part963_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part963) = true := by rfl

def kid05_part964 : Audit := .cycle 0 11 true (0)
theorem kid05_part964_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part964) = true := by rfl

def kid05_part966 : Audit := .cycle 0 11 true (0)
theorem kid05_part966_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part966) = true := by rfl

def kid05_part967 : Audit := .cycle 1 10 true (1)
theorem kid05_part967_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part967) = true := by rfl

def kid05_part968 : Audit := .cycle 21 1 false (1)
theorem kid05_part968_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part968) = true := by rfl

def kid05_part969 : Audit := .cycle 23 1 false (1)
theorem kid05_part969_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part969) = true := by rfl

def kid05_part970 : Audit := .split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 15 2 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 30 true (-1),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1)
])
theorem kid05_part970_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part970) = true := by rfl

def kid05_part971 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (1,true),
.cycle 16 7 false (0),
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
theorem kid05_part971_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part971) = true := by rfl

def kid05_part972 : Audit := .cycle 0 11 true (0)
theorem kid05_part972_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part972) = true := by rfl

def kid05_part973 : Audit := .cycle 1 10 true (1)
theorem kid05_part973_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part973) = true := by rfl

def kid05_part974 : Audit := .cycle 35 1 false (7)
theorem kid05_part974_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part974) = true := by rfl

def kid05_part975 : Audit := .cycle 20 1 false (2)
theorem kid05_part975_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part975) = true := by rfl

def kid05_part976 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 35 1 false (7),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 13 (1,true),
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
theorem kid05_part976_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part976) = true := by rfl

def kid05_part977 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 32 1 false (6),
.cycle 26 1 false (4),
.cycle 18 1 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 40 1 false (10),
.cycle 34 1 false (8),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 14 (1,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 29 1 false (5),
.cycle 30 1 false (6),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part977_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part977) = true := by rfl

def kid05_part978 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 21 (4,false),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 16 7 false (0),
.cycle 13 8 false (1),
.last 21 (4,false),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.last 14 (4,false)
])
theorem kid05_part978_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part978) = true := by rfl

def kid05_part979 : Audit := .cycle 14 5 false (0)
theorem kid05_part979_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part979) = true := by rfl

def kid05_part980 : Audit := .cycle 0 13 true (0)
theorem kid05_part980_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part980) = true := by rfl

def kid05_part981 : Audit := .cycle 18 1 false (0)
theorem kid05_part981_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part981) = true := by rfl

def kid05_part982 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 15 2 true (-2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 47 1 false (7),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 16 13 true (-1),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.cycle 13 5 false (1)
])
theorem kid05_part982_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part982) = true := by rfl

def kid05_part983 : Audit := .cycle 9 2 true (1)
theorem kid05_part983_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part983) = true := by rfl

def kid05_part984 : Audit := .cycle 0 11 true (0)
theorem kid05_part984_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part984) = true := by rfl

def kid05_part985 : Audit := .cycle 1 10 true (1)
theorem kid05_part985_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part985) = true := by rfl

def kid05_part986 : Audit := .cycle 2 9 true (1)
theorem kid05_part986_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part986) = true := by rfl

def kid05_part987 : Audit := .cycle 2 12 true (1)
theorem kid05_part987_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part987) = true := by rfl

def kid05_part988 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 4, 16, 64],[4, 64, 4, 1, 16, 16, 64],64⟩,
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 2 16 true (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid05_part988_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part988) = true := by rfl

def kid05_part989 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 4 true (4),
.cycle 9 13 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 14 (1,true),
.cycle 15 4 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 14 4 true (1),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part989_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part989) = true := by rfl

def kid05_part965 : Audit := .split 10 (4,true) (byMove [(kid05_part966),(kid05_part967),(kid05_part968),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977),(kid05_part978),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989)])

theorem kid05_part965_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part965) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part966),(kid05_part967),(kid05_part968),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977),(kid05_part978),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part966_checked

  · exact kid05_part972_checked

  · exact kid05_part978_checked

  · exact kid05_part984_checked

  · exact kid05_part967_checked

  · exact kid05_part973_checked

  · exact kid05_part979_checked

  · exact kid05_part985_checked

  · exact kid05_part968_checked

  · exact kid05_part974_checked

  · exact kid05_part980_checked

  · exact kid05_part986_checked

  · exact kid05_part969_checked

  · exact kid05_part975_checked

  · exact kid05_part981_checked

  · exact kid05_part987_checked

  · exact kid05_part970_checked

  · exact kid05_part976_checked

  · exact kid05_part982_checked

  · exact kid05_part988_checked

  · exact kid05_part971_checked

  · exact kid05_part977_checked

  · exact kid05_part983_checked

  · exact kid05_part989_checked

def kid05_part990 : Audit := .cycle 8 2 true (1)
theorem kid05_part990_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part990) = true := by rfl

def kid05_part991 : Audit := .split 15 (1,true) (byMove [
.cycle 0 35 true (-2),
.cycle 10 12 false (1),
.cycle 13 4 false (-1),
.cycle 0 35 true (-2),
.split 16 (4,true) (byMove [
.cycle 2 76 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 0 35 true (-2),
.cycle 11 7 false (1),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 13 4 true (-2),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 0 45 true (-3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 1, 64],[33, 16, 32, 33, 33, 32, 64],80⟩,
.cycle 12 8 false (0),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.last 17 (4,false),
.cycle 9 8 false (1)
]),
.cycle 12 4 false (0),
.cycle 0 19 true (-2),
.cycle 18 12 true (-1),
.cycle 9 8 false (1),
.cycle 0 29 true (-2),
.split 16 (4,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 10 14 true (-2),
.last 17 (4,false),
.cycle 9 8 false (1),
.last 19 (4,false),
.cycle 18 12 true (-1),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.last 17 (4,false),
.last 24 (4,false),
.last 19 (4,false),
.cycle 12 8 false (0),
.last 21 (4,false),
.cycle 10 9 false (1),
.last 17 (4,false),
.cycle 9 8 false (1),
.last 19 (4,false),
.cycle 8 12 false (2),
.cycle 0 19 true (-2),
.cycle 17 14 true (-1),
.last 17 (4,false),
.cycle 6 12 false (3)
]),
.cycle 8 8 false (2),
.cycle 10 6 false (1),
.cycle 11 7 false (1),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.split 16 (4,true) (byMove [
.cycle 12 9 false (0),
.last 41 (4,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 10 7 false (1),
.last 18 (4,false),
.cycle 13 5 false (-1),
.cycle 0 21 true (-2),
.last 19 (4,false),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.cycle 11 7 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 12 8 false (0),
.cycle 15 2 true (-2),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.last 19 (4,false),
.cycle 12 6 false (0)
]),
.cycle 12 4 false (0),
.cycle 0 19 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 2, 15, 1, 64, 15, 64],80⟩,
.cycle 12 6 false (0),
.cycle 45 30 false (5),
.split 16 (4,true) (byMove [
.cycle 2 16 false (3),
.last 18 (4,false),
.cycle 11 6 false (1),
.cycle 8 14 false (2),
.last 19 (4,false),
.cycle 12 6 false (0),
.last 19 (4,false),
.last 30 (4,false),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 17 (4,false),
.last 24 (4,false),
.cycle 12 8 false (0),
.cycle 15 2 true (-1),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.last 19 (4,false),
.cycle 12 6 false (0),
.last 19 (4,false),
.last 30 (4,false),
.cycle 0 19 true (-2),
.last 34 (4,false),
.last 17 (4,false),
.cycle 20 8 false (0)
]),
.cycle 12 6 false (0)
])
theorem kid05_part991_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part991) = true := by rfl

def kid05_part992 : Audit := .split 10 (1,true) (byMove [
.cycle 15 4 false (-1),
.cycle 0 34 true (-2),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 30 (4,true),
.cycle 18 4 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 14 (4,true),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 12 4 false (0),
.last 14 (4,true),
.cycle 12 4 false (-1),
.last 16 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.last 14 (4,true),
.cycle 15 4 false (-1),
.cycle 0 34 true (-2),
.cycle 15 4 false (1),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 11 4 false (-1),
.cycle 12 4 false (2),
.cycle 19 4 false (5),
.cycle 12 4 false (0),
.cycle 18 4 false (4),
.split 11 (4,true) (byMove [
.cycle 16 4 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 18 4 false (4),
.last 13 (4,false),
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 12 4 false (2),
.last 17 (4,false),
.cycle 12 4 false (1),
.cycle 20 4 false (4),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 12 4 false (0),
.cycle 2 11 true (0),
.last 13 (4,false),
.cycle 12 4 false (2),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 13 4 false (1)
]),
.cycle 11 4 false (1),
.cycle 14 4 false (0),
.cycle 11 4 false (0),
.cycle 14 4 false (2),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 16 4 false (-2),
.cycle 22 4 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 13 4 false (1),
.cycle 10 2 true (-1),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.last 12 (4,true),
.cycle 12 4 false (0),
.last 14 (4,true),
.cycle 12 4 false (-1),
.cycle 15 4 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 4 false (-2),
.cycle 15 4 false (-1),
.last 13 (4,true),
.cycle 12 4 false (0),
.cycle 5 7 false (3),
.last 12 (4,true),
.cycle 13 4 false (-1)
]),
.cycle 11 4 false (-1),
.cycle 14 4 false (0),
.cycle 1 12 true (0),
.cycle 11 4 false (1),
.cycle 24 4 false (0),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 13 4 false (-1),
.last 15 (4,false),
.last 13 (4,false),
.cycle 12 4 false (0),
.cycle 24 4 false (0),
.last 13 (4,false),
.cycle 22 4 false (2),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (0),
.cycle 13 4 false (1),
.cycle 10 2 true (0),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.last 13 (4,false),
.cycle 12 4 false (0),
.cycle 2 11 true (0),
.last 13 (4,false),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 14 4 false (0)
]),
.cycle 12 4 false (0)
])
theorem kid05_part992_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part992) = true := by rfl

def kid05_part993 : Audit := .split 15 (1,true) (byMove [
.cycle 0 19 true (-2),
.cycle 0 31 true (-2),
.cycle 27 11 true (-2),
.cycle 0 20 true (-2),
.split 16 (4,true) (byMove [
.cycle 0 21 true (-2),
.cycle 0 31 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 27 11 true (-2),
.cycle 0 20 true (-2),
.cycle 18 11 true (-1),
.cycle 0 19 true (-2),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 17 11 true (0),
.cycle 14 3 false (1),
.cycle 92 11 true (1),
.cycle 0 24 true (-2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 23 true (-2),
.cycle 54 11 true (2),
.cycle 23 11 true (-2),
.cycle 0 19 true (-2),
.cycle 17 11 true (-1),
.last 17 (4,false),
.cycle 9 8 true (-2)
]),
.cycle 0 23 true (-2),
.cycle 16 11 true (1),
.cycle 18 11 true (2),
.cycle 0 38 true (-2),
.cycle 0 17 true (-2),
.split 16 (4,true) (byMove [
.cycle 33 11 true (1),
.cycle 1 16 true (-2),
.cycle 17 11 true (-1),
.cycle 18 11 true (0),
.last 17 (4,false),
.last 24 (4,false),
.cycle 0 17 true (-2),
.cycle 18 11 true (2),
.cycle 30 11 true (2),
.cycle 0 30 true (-2),
.last 17 (4,false),
.cycle 0 20 true (-2),
.last 19 (4,false),
.cycle 23 11 true (-2),
.cycle 0 19 true (-2),
.cycle 17 11 true (-1),
.last 17 (4,false),
.cycle 9 8 true (-2),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 5, 6, 7, 8, 4, 8, 1, 4, 4, 4, 8, 4, 4],[128, 256, 8, 0, 18014398509481984, 1, 524288, 1048576, 32768, 67109120, 18014398509481984, 65536, 2147483648, 4294967296, 134217728, 24770348898681216, 18014398509481984, 16777216, 8796093022208, 17592186044416, 549755813888, 4294967296, 18014398509481984, 16777216, 33554432, 67108864, 2251799813685248, 24770348898681216, 18014398509481984, 25051823875391872, 128, 256, 2251799813685248, 67108864, 18014398509481984, 18014398509481984, 33554432, 67108864, 134217728, 128, 18014398509481984, 16777216, 562949953421312, 1125899906842624, 134217728, 67108864, 18014398509481984, 24770348898681216, 33554432, 67108864, 134217728, 24770348898681216, 18014398509481984, 4503599644147712, 18014398509481984],[256, 16, 128, 1, 64, 256, 1048576, 65536, 32768, 4096, 262144, 32768, 4294967296, 268435456, 18014398509481984, 16777216, 1073741824, 1073741824, 17592186044416, 1099511627776, 24770348898681216, 68719476736, 4398046511104, 16777216, 67108864, 4503599627370496, 24770348898681216, 281474976710656, 16777216, 24770348898681216, 256, 4503599627370496, 128, 281474976710656, 64, 256, 67108864, 268435456, 33554432, 16777216, 16777216, 67108864, 1125899906842624, 268435456, 33554432, 16777216, 281474976710656, 67108864, 67108864, 268435456, 24770348898681216, 16777216, 16777216, 24770348898681216, 18014398509481984],36028246188359506⟩,
.last 34 (4,false),
.cycle 17 11 true (1),
.cycle 18 11 true (2),
.last 17 (4,false),
.last 26 (4,false)
]),
.cycle 8 8 true (-2),
.cycle 0 25 true (-2),
.cycle 24 11 true (0),
.cycle 10 6 true (-2),
.cycle 16 11 true (-1),
.split 16 (4,true) (byMove [
.far true 1 ⟨0,[0, 0],[45, 45, 45, 8, 64, 4, 64],[45, 16, 32, 45, 1, 32, 64],80⟩,
.cycle 18 11 true (0),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 11 6 true (-2),
.cycle 17 11 true (-1),
.last 18 (4,false),
.cycle 0 28 true (-2),
.cycle 17 11 true (1),
.last 19 (4,false),
.cycle 20 11 true (-1),
.cycle 14 3 false (1),
.cycle 24 11 true (0),
.cycle 18 11 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 0 29 true (-2),
.cycle 23 11 true (-2),
.cycle 15 2 true (0),
.cycle 0 25 true (-2),
.cycle 17 11 true (1),
.last 19 (4,false),
.cycle 0 31 true (-2)
]),
.cycle 0 29 true (-2),
.cycle 31 11 true (1),
.cycle 50 11 true (2),
.cycle 21 11 true (-2),
.cycle 12 23 true (-2),
.split 16 (4,true) (byMove [
.cycle 2 16 true (-2),
.last 18 (4,false),
.cycle 17 11 true (-2),
.last 36 (4,false),
.last 19 (4,false),
.cycle 21 11 true (-2),
.cycle 12 23 true (-2),
.cycle 18 11 true (2),
.cycle 0 35 true (-2),
.cycle 3 14 true (-2),
.last 17 (4,false),
.cycle 0 20 true (-2),
.cycle 23 11 true (-2),
.cycle 15 2 true (1),
.cycle 0 25 true (-2),
.cycle 17 11 true (1),
.last 19 (4,false),
.cycle 0 31 true (-2),
.cycle 12 29 true (-2),
.cycle 50 11 true (2),
.cycle 31 11 true (1),
.cycle 18 11 true (2),
.last 17 (4,false),
.cycle 0 44 true (-2)
]),
.cycle 0 31 true (-2)
])
theorem kid05_part993_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part993) = true := by rfl

def kid05_part994 : Audit := .cycle 15 1 false (-1)
theorem kid05_part994_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part994) = true := by rfl

def kid05_part996 : Audit := .split 17 (4,false) (byMove [
.cycle 11 7 false (1),
.last 26 (1,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 15 5 false (-1),
.last 18 (1,true),
.cycle 16 3 false (-2),
.proven (BB6.Agent11Raw39B1RCPumps.M339.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M339.never m hm),
.cycle 10 8 false (1),
.cycle 15 3 false (-1),
.last 19 (1,true),
.cycle 15 5 false (-1),
.cycle 15 7 false (-1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 13 6 false (1),
.last 18 (1,true),
.cycle 15 4 false (-1),
.cycle 5 13 false (3),
.proven (BB6.Agent11Raw39B1RCPumps.M340.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M340.never m hm),
.cycle 14 4 false (0)
])
theorem kid05_part996_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part996) = true := by rfl

def kid05_part997 : Audit := .split 23 (4,false) (byMove [
.cycle 28 7 false (0),
.cycle 11 13 true (-1),
.cycle 34 1 false (-2),
.cycle 12 15 true (-1),
.cycle 35 1 false (-3),
.last 30 (1,true),
.cycle 6 23 false (4),
.last 24 (1,true),
.last 47 (1,true),
.cycle 13 11 true (1),
.cycle 0 28 true (-1),
.cycle 24 11 false (2),
.last 25 (1,true),
.cycle 27 5 false (-1),
.cycle 24 13 false (3),
.cycle 31 1 false (-3),
.cycle 24 9 false (2),
.cycle 35 2 false (-3),
.cycle 41 6 false (-1),
.last 24 (1,true),
.cycle 0 34 true (-2),
.cycle 13 11 true (1),
.last 25 (1,true),
.cycle 37 4 false (-1)
])
theorem kid05_part997_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part997) = true := by rfl

def kid05_part998 : Audit := .cycle 12 1 false (0)
theorem kid05_part998_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part998) = true := by rfl

def kid05_part999 : Audit := .cycle 11 1 false (-1)
theorem kid05_part999_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part999) = true := by rfl

def kid05_part1000 : Audit := .split 11 (4,false) (byMove [
.cycle 31 7 false (-1),
.cycle 26 13 true (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 13 (1,true),
.last 17 (1,true),
.cycle 22 3 false (2),
.cycle 12 1 false (0),
.cycle 17 1 true (1),
.cycle 12 3 false (0),
.last 13 (1,true),
.cycle 11 5 false (-1),
.last 15 (1,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 34 true (-2),
.cycle 0 23 true (-2),
.cycle 25 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid05_part1000_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1000) = true := by rfl

def kid05_part1001 : Audit := .split 12 (4,false) (byMove [
.cycle 11 7 false (-1),
.last 17 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 6 25 false (4),
.last 13 (1,true),
.cycle 11 3 false (-1),
.last 15 (1,true),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 28 13 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 32 6 false (-2),
.last 13 (1,true),
.cycle 11 4 false (-1),
.last 15 (1,true),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part1001_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1001) = true := by rfl

def kid05_part1002 : Audit := .split 15 (4,false) (byMove [
.cycle 13 7 false (1),
.cycle 11 13 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.last 16 (1,true),
.cycle 14 3 false (0),
.cycle 11 11 true (-1),
.cycle 11 11 true (-1),
.cycle 13 3 false (1),
.last 17 (1,true),
.cycle 12 5 false (2),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 13 6 false (1),
.last 16 (1,true),
.cycle 12 4 false (2),
.cycle 11 11 true (-1),
.cycle 11 11 true (-1),
.cycle 13 4 false (1)
])
theorem kid05_part1002_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1002) = true := by rfl

def kid05_part1003 : Audit := .split 11 (1,true) (byMove [
.last 18 (4,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.last 21 (4,false),
.last 22 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.last 23 (4,false),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.last 15 (4,false)
])
theorem kid05_part1003_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1003) = true := by rfl

def kid05_part1004 : Audit := .split 13 (4,false) (byMove [
.cycle 12 7 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 0 17 true (-1),
.last 14 (1,true),
.cycle 11 3 false (1),
.last 16 (1,true),
.cycle 0 17 true (-1),
.cycle 12 3 false (0),
.last 15 (1,true),
.cycle 12 5 false (0),
.cycle 0 19 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 0 17 true (-1),
.last 14 (1,true),
.cycle 12 4 false (0),
.last 16 (1,true),
.cycle 0 17 true (-1),
.cycle 12 4 false (0)
])
theorem kid05_part1004_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1004) = true := by rfl

def kid05_part1005 : Audit := .split 21 (4,false) (byMove [
.cycle 19 7 false (3),
.cycle 11 13 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 17 5 false (4),
.last 22 (1,true),
.cycle 20 3 false (2),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.cycle 19 3 false (3),
.last 23 (1,true),
.cycle 18 5 false (4),
.cycle 16 7 false (4),
.cycle 22 1 false (0),
.cycle 21 1 false (1),
.cycle 20 2 false (2),
.cycle 19 6 false (3),
.last 22 (1,true),
.cycle 18 4 false (4),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.cycle 19 4 false (3)
])
theorem kid05_part1005_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1005) = true := by rfl

def kid05_part1006 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 15 13 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.last 24 (1,true),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 14 3 false (4),
.last 15 (1,true),
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
theorem kid05_part1006_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1006) = true := by rfl

def kid05_part1007 : Audit := .split 13 (4,false) (byMove [
.cycle 11 7 false (1),
.last 22 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 5 false (1),
.last 14 (1,true),
.cycle 12 3 false (0),
.cycle 14 11 true (-1),
.cycle 10 4 true (-1),
.cycle 11 3 false (1),
.last 15 (1,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 6 false (1),
.last 14 (1,true),
.cycle 11 4 false (1),
.cycle 5 9 false (3),
.cycle 8 7 false (2),
.cycle 11 4 false (1)
])
theorem kid05_part1007_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1007) = true := by rfl

def kid05_part1008 : Audit := .split 12 (1,true) (byMove [
.last 25 (4,false),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 20 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 6 7 false (3),
.last 24 (4,false),
.cycle 9 5 false (1),
.last 23 (4,false),
.last 19 (4,false),
.cycle 8 5 false (2),
.last 17 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 19 (4,false),
.last 31 (4,false),
.last 17 (4,false),
.last 23 (4,false),
.last 19 (4,false),
.last 17 (4,false)
])
theorem kid05_part1008_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1008) = true := by rfl

def kid05_part1009 : Audit := .split 15 (4,false) (byMove [
.cycle 13 7 false (-1),
.cycle 20 13 true (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 5 false (0),
.last 16 (1,true),
.cycle 14 3 false (-2),
.cycle 19 11 true (1),
.cycle 10 6 false (0),
.cycle 13 3 false (-1),
.last 17 (1,true),
.cycle 11 5 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 13 6 false (-1),
.last 16 (1,true),
.cycle 12 4 false (0),
.cycle 19 11 true (1),
.last 17 (1,true),
.cycle 13 4 false (-1)
])
theorem kid05_part1009_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1009) = true := by rfl

def kid05_part1010 : Audit := .split 17 (4,false) (byMove [
.cycle 15 7 false (1),
.cycle 12 13 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.last 18 (1,true),
.cycle 16 3 false (0),
.cycle 12 11 true (-1),
.cycle 12 13 true (-1),
.cycle 15 3 false (1),
.last 19 (1,true),
.cycle 14 5 false (2),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 15 6 false (1),
.last 18 (1,true),
.cycle 14 4 false (2),
.cycle 12 11 true (-1),
.cycle 16 4 false (0),
.cycle 15 4 false (1)
])
theorem kid05_part1010_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1010) = true := by rfl

def kid05_part1011 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1011_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1011) = true := by rfl

def kid05_part1012 : Audit := .split 11 (4,false) (byMove [
.cycle 11 7 false (0),
.last 20 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 5 false (1),
.last 12 (1,true),
.cycle 11 3 false (0),
.cycle 12 11 true (-1),
.cycle 10 2 true (-1),
.cycle 11 3 false (0),
.last 13 (1,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 6 false (1),
.last 12 (1,true),
.cycle 11 4 false (0),
.cycle 5 7 false (3),
.cycle 10 3 false (0),
.cycle 11 4 false (0)
])
theorem kid05_part1012_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1012) = true := by rfl

def kid05_part1013 : Audit := .split 12 (4,false) (byMove [
.cycle 11 7 false (-1),
.last 21 (1,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.last 13 (1,true),
.cycle 11 3 false (-1),
.cycle 0 23 true (-2),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.last 14 (1,true),
.cycle 11 5 false (-1),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 6 false (0),
.last 13 (1,true),
.cycle 11 4 false (-1),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part1013_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1013) = true := by rfl

def kid05_part1014 : Audit := .split 16 (4,false) (byMove [
.cycle 12 7 false (2),
.last 25 (1,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 14 5 false (0),
.last 17 (1,true),
.cycle 15 3 false (-1),
.cycle 17 11 true (-2),
.cycle 10 7 false (2),
.cycle 14 3 false (0),
.last 18 (1,true),
.cycle 14 5 false (0),
.cycle 14 7 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 11 6 false (2),
.last 17 (1,true),
.cycle 14 4 false (0),
.cycle 5 12 false (3),
.cycle 13 8 false (1),
.cycle 13 4 false (1)
])
theorem kid05_part1014_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1014) = true := by rfl

def kid05_part1015 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 22 (4,false),
.last 14 (4,false),
.cycle 0 16 true (0),
.last 18 (4,false),
.last 14 (4,false),
.last 21 (4,false),
.last 22 (4,false),
.last 25 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 8 4 true (0),
.last 16 (4,false),
.last 17 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 16 (4,false)
])
theorem kid05_part1015_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1015) = true := by rfl

def kid05_part1016 : Audit := .split 14 (4,false) (byMove [
.cycle 12 7 false (0),
.last 36 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 5 false (1),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 19 true (-2),
.cycle 10 5 false (1),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 6 false (0),
.last 15 (1,true),
.cycle 11 4 false (1),
.cycle 0 19 true (-2),
.cycle 12 6 false (0),
.cycle 12 4 false (0)
])
theorem kid05_part1016_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1016) = true := by rfl

def kid05_part1017 : Audit := .split 21 (4,false) (byMove [
.cycle 39 7 false (1),
.last 22 (1,true),
.cycle 26 1 false (-2),
.last 24 (1,true),
.cycle 29 1 false (-1),
.cycle 23 2 false (-1),
.cycle 6 16 true (0),
.last 22 (1,true),
.last 27 (1,true),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.cycle 5 20 true (0),
.last 28 (1,true),
.last 22 (1,true),
.cycle 16 13 false (4),
.cycle 28 1 false (-2),
.cycle 5 18 true (0),
.cycle 23 2 false (-1),
.cycle 25 6 false (1),
.last 22 (1,true),
.cycle 24 4 false (0),
.cycle 11 11 true (1),
.cycle 0 24 true (0),
.cycle 23 4 false (1)
])
theorem kid05_part1017_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1017) = true := by rfl

def kid05_part1018 : Audit := .split 13 (4,false) (byMove [
.cycle 2 13 true (0),
.last 14 (1,true),
.cycle 20 1 false (-2),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 17 2 false (-1),
.cycle 0 14 true (0),
.last 24 (1,true),
.cycle 11 18 true (1),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.cycle 8 8 true (0),
.last 22 (1,true),
.last 14 (1,true),
.cycle 16 7 false (0),
.cycle 5 29 true (0),
.cycle 11 3 true (1),
.cycle 17 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 15 11 true (3),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid05_part1018_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1018) = true := by rfl

def kid05_part1019 : Audit := .split 14 (4,false) (byMove [
.cycle 11 7 false (1),
.last 23 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 5 false (0),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 0 25 true (-2),
.cycle 10 5 false (1),
.cycle 12 3 false (0),
.last 16 (1,true),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 6 false (1),
.last 15 (1,true),
.cycle 12 4 false (0),
.cycle 5 10 false (3),
.cycle 11 6 false (1),
.cycle 11 4 false (1)
])
theorem kid05_part1019_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1019) = true := by rfl

def kid05_part995 : Audit := .split 10 (4,true) (byMove [(kid05_part996),(kid05_part997),(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019)])

theorem kid05_part995_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part995) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part996),(kid05_part997),(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part996_checked

  · exact kid05_part1002_checked

  · exact kid05_part1008_checked

  · exact kid05_part1014_checked

  · exact kid05_part997_checked

  · exact kid05_part1003_checked

  · exact kid05_part1009_checked

  · exact kid05_part1015_checked

  · exact kid05_part998_checked

  · exact kid05_part1004_checked

  · exact kid05_part1010_checked

  · exact kid05_part1016_checked

  · exact kid05_part999_checked

  · exact kid05_part1005_checked

  · exact kid05_part1011_checked

  · exact kid05_part1017_checked

  · exact kid05_part1000_checked

  · exact kid05_part1006_checked

  · exact kid05_part1012_checked

  · exact kid05_part1018_checked

  · exact kid05_part1001_checked

  · exact kid05_part1007_checked

  · exact kid05_part1013_checked

  · exact kid05_part1019_checked

def kid05_part1020 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1020_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1020) = true := by rfl

def kid05_part1021 : Audit := .cycle 2 9 true (1)
theorem kid05_part1021_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1021) = true := by rfl

def kid05_part1022 : Audit := .split 10 (1,true) (byMove [
.cycle 2 10 true (1),
.cycle 11 11 false (1),
.cycle 1 16 false (3),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 23 false (3),
.last 13 (4,false),
.cycle 1 13 false (3),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 1 16 false (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 1 12 true (1),
.cycle 16 3 false (0),
.last 13 (4,false),
.cycle 0 28 true (-3),
.cycle 24 1 false (0),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 1 12 true (1)
]),
.cycle 12 3 false (0),
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
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 32 (4,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1),
.cycle 14 5 false (0),
.cycle 11 6 false (1),
.cycle 12 8 false (0),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 13 (4,false),
.cycle 0 17 true (-1),
.cycle 16 1 false (0),
.last 13 (4,false),
.cycle 12 8 false (0),
.cycle 2 11 true (1),
.last 13 (4,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (1),
.cycle 16 3 false (0),
.last 13 (4,false),
.far true 1 ⟨0,[0, 0],[44, 44, 44, 8, 64, 44, 64],[44, 16, 32, 44, 4, 32, 64],80⟩,
.cycle 19 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 13 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 24 true (1),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.last 19 (4,true),
.last 13 (4,true),
.last 17 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid05_part1022_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1022) = true := by rfl

def kid05_part1023 : Audit := .cycle 12 3 false (0)
theorem kid05_part1023_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1023) = true := by rfl

def kid05_part1024 : Audit := .cycle 0 11 true (0)
theorem kid05_part1024_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1024) = true := by rfl

def kid05_part1026 : Audit := .cycle 2 10 true (1)
theorem kid05_part1026_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1026) = true := by rfl

def kid05_part1027 : Audit := .split 11 (1,true) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.last 24 (4,false),
.last 17 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 14 (4,false),
.cycle 24 1 false (0),
.cycle 0 16 true (-1),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid05_part1027_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1027) = true := by rfl

def kid05_part1028 : Audit := .split 17 (4,false) (byMove [
.cycle 11 13 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 0 19 false (3),
.cycle 20 1 false (-2),
.cycle 12 6 false (0),
.cycle 7 22 false (3),
.cycle 11 13 true (-2),
.cycle 11 13 false (1),
.cycle 11 11 false (1),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2),
.cycle 11 8 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 11 14 true (-2),
.cycle 20 1 false (-2),
.cycle 12 6 false (0),
.last 39 (1,true),
.cycle 29 10 false (-1),
.cycle 2 16 false (3),
.cycle 11 15 true (-2),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
])
theorem kid05_part1028_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1028) = true := by rfl

def kid05_part1029 : Audit := .cycle 0 12 true (0)
theorem kid05_part1029_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1029) = true := by rfl

def kid05_part1030 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 0 14 true (-1),
.cycle 11 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 13 2 true (-1),
.last 15 (1,true),
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
theorem kid05_part1030_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1030) = true := by rfl

def kid05_part1031 : Audit := .cycle 12 3 false (0)
theorem kid05_part1031_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1031) = true := by rfl

def kid05_part1032 : Audit := .cycle 0 11 true (0)
theorem kid05_part1032_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1032) = true := by rfl

def kid05_part1033 : Audit := .cycle 1 10 true (1)
theorem kid05_part1033_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1033) = true := by rfl

def kid05_part1034 : Audit := .cycle 0 23 true (0)
theorem kid05_part1034_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1034) = true := by rfl

def kid05_part1035 : Audit := .cycle 3 8 true (1)
theorem kid05_part1035_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1035) = true := by rfl

def kid05_part1036 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 17 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 26 14 true (4),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 13 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 0, 0, 1024, 128, 256, 8, 256, 4096, 1024, 4096],[256, 4096, 4096, 1, 16, 16, 256, 4096, 0, 1, 16, 16, 4096],7200⟩,
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
theorem kid05_part1036_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1036) = true := by rfl

def kid05_part1037 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 8 13 false (4),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 8 5 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 6 7 true (1),
.last 13 (1,true),
.cycle 8 18 true (-1),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.cycle 8 8 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part1037_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1037) = true := by rfl

def kid05_part1038 : Audit := .cycle 14 5 false (0)
theorem kid05_part1038_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1038) = true := by rfl

def kid05_part1039 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 44 true (-2),
.last 14 (4,false),
.cycle 0 16 true (0),
.last 19 (4,false),
.last 17 (4,false),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 16 7 false (0),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.cycle 12 6 false (0),
.last 14 (4,false),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 13 3 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 13 5 false (1)
])
theorem kid05_part1039_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1039) = true := by rfl

def kid05_part1040 : Audit := .split 17 (4,false) (byMove [
.last 22 (1,true),
.last 18 (1,true),
.cycle 15 3 false (-1),
.last 20 (1,true),
.last 22 (1,true),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.last 18 (1,true),
.cycle 0 23 true (-2),
.last 20 (1,true),
.last 22 (1,true),
.cycle 8 10 false (2),
.cycle 11 8 false (1),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 11 9 false (1),
.cycle 11 11 false (1),
.cycle 12 6 false (0),
.cycle 0 21 true (-2),
.last 18 (1,true),
.cycle 12 8 false (0),
.last 20 (1,true),
.cycle 10 8 false (2),
.cycle 12 8 false (0)
])
theorem kid05_part1040_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1040) = true := by rfl

def kid05_part1041 : Audit := .cycle 2 11 true (1)
theorem kid05_part1041_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1041) = true := by rfl

def kid05_part1042 : Audit := .split 13 (4,false) (byMove [
.cycle 11 9 false (1),
.last 24 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 14 (1,true),
.cycle 0 51 true (-2),
.cycle 14 13 true (-1),
.cycle 12 2 true (-1),
.cycle 11 5 false (1),
.last 15 (1,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.cycle 11 8 false (1),
.last 14 (1,true),
.cycle 11 6 false (1),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.cycle 11 6 false (1)
])
theorem kid05_part1042_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1042) = true := by rfl

def kid05_part1043 : Audit := .cycle 12 3 false (0)
theorem kid05_part1043_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1043) = true := by rfl

def kid05_part1044 : Audit := .cycle 0 11 true (0)
theorem kid05_part1044_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1044) = true := by rfl

def kid05_part1045 : Audit := .cycle 1 10 true (1)
theorem kid05_part1045_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1045) = true := by rfl

def kid05_part1046 : Audit := .cycle 2 9 true (1)
theorem kid05_part1046_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1046) = true := by rfl

def kid05_part1047 : Audit := .cycle 2 12 true (1)
theorem kid05_part1047_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1047) = true := by rfl

def kid05_part1048 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 10 7 false (3),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 0, 16, 64],[4, 64, 0, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 14 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 0, 4096, 1024, 128, 256, 8, 256, 0, 1024, 4096],[256, 4096, 0, 1, 1024, 1024, 256, 4096, 0, 1, 1024, 1024, 4096],4112⟩,
.last 12 (1,true),
.cycle 10 7 false (3),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid05_part1048_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1048) = true := by rfl

def kid05_part1049 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 14 5 false (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 14 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 9 14 true (1),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 16 5 false (2),
.last 13 (1,true),
.cycle 14 5 false (2),
.cycle 2 13 true (1),
.cycle 16 5 false (2),
.cycle 14 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part1049_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1049) = true := by rfl

def kid05_part1025 : Audit := .split 10 (4,true) (byMove [(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046),(kid05_part1047),(kid05_part1048),(kid05_part1049)])

theorem kid05_part1025_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1025) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046),(kid05_part1047),(kid05_part1048),(kid05_part1049)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1026_checked

  · exact kid05_part1032_checked

  · exact kid05_part1038_checked

  · exact kid05_part1044_checked

  · exact kid05_part1027_checked

  · exact kid05_part1033_checked

  · exact kid05_part1039_checked

  · exact kid05_part1045_checked

  · exact kid05_part1028_checked

  · exact kid05_part1034_checked

  · exact kid05_part1040_checked

  · exact kid05_part1046_checked

  · exact kid05_part1029_checked

  · exact kid05_part1035_checked

  · exact kid05_part1041_checked

  · exact kid05_part1047_checked

  · exact kid05_part1030_checked

  · exact kid05_part1036_checked

  · exact kid05_part1042_checked

  · exact kid05_part1048_checked

  · exact kid05_part1031_checked

  · exact kid05_part1037_checked

  · exact kid05_part1043_checked

  · exact kid05_part1049_checked

def kid05_part1050 : Audit := .cycle 11 3 false (1)
theorem kid05_part1050_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1050) = true := by rfl

def kid05_part930 : Audit := .split 9 (5,false) (byMove [(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995),(kid05_part1020),(kid05_part1021),(kid05_part1022),(kid05_part1023),(kid05_part1024),(kid05_part1025),(kid05_part1050)])

theorem kid05_part930_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (kid05_part930) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995),(kid05_part1020),(kid05_part1021),(kid05_part1022),(kid05_part1023),(kid05_part1024),(kid05_part1025),(kid05_part1050)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part931_checked

  · exact kid05_part961_checked

  · exact kid05_part991_checked

  · exact kid05_part1021_checked

  · exact kid05_part932_checked

  · exact kid05_part962_checked

  · exact kid05_part992_checked

  · exact kid05_part1022_checked

  · exact kid05_part933_checked

  · exact kid05_part963_checked

  · exact kid05_part993_checked

  · exact kid05_part1023_checked

  · exact kid05_part934_checked

  · exact kid05_part964_checked

  · exact kid05_part994_checked

  · exact kid05_part1024_checked

  · exact kid05_part935_checked

  · exact kid05_part965_checked

  · exact kid05_part995_checked

  · exact kid05_part1025_checked

  · exact kid05_part960_checked

  · exact kid05_part990_checked

  · exact kid05_part1020_checked

  · exact kid05_part1050_checked

def kid05_part1051 : Audit := .cycle 0 9 true (0)
theorem kid05_part1051_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,0⟩)) (kid05_part1051) = true := by rfl

def kid05_part1052 : Audit := .cycle 1 8 true (1)
theorem kid05_part1052_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,1⟩)) (kid05_part1052) = true := by rfl

def kid05_part1053 : Audit := .cycle 2 7 true (1)
theorem kid05_part1053_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,2⟩)) (kid05_part1053) = true := by rfl

def kid05_part1054 : Audit := .cycle 2 10 true (1)
theorem kid05_part1054_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,3⟩)) (kid05_part1054) = true := by rfl

def kid05_part1056 : Audit := .cycle 2 9 true (1)
theorem kid05_part1056_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1056) = true := by rfl

def kid05_part1057 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 11 11 false (1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.cycle 14 6 false (1),
.cycle 12 6 false (0),
.cycle 0 24 true (-2),
.cycle 24 1 false (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 15 3 false (1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 10 3 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
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
.split 19 (4,true) (byMove [
.cycle 0 37 true (-2),
.cycle 0 23 true (-2),
.cycle 11 17 false (2),
.cycle 18 19 false (2),
.cycle 1 20 false (3),
.last 20 (5,false),
.cycle 0 34 true (-2),
.cycle 0 25 true (-2),
.last 21 (5,false),
.cycle 0 21 true (-2),
.cycle 0 36 true (-2),
.cycle 0 27 true (-2),
.cycle 11 18 false (2),
.cycle 7 14 false (3),
.cycle 0 36 true (-2),
.cycle 11 15 false (2),
.cycle 0 38 true (-2),
.last 20 (5,false),
.cycle 2 19 true (-2),
.cycle 18 2 true (1),
.cycle 0 28 true (-2),
.far true 1 ⟨0,[0, 0],[18, 18, 26, 8, 2, 64, 64],[18, 16, 32, 18, 18, 18, 64],96⟩,
.cycle 18 4 true (1),
.cycle 18 4 true (1)
]),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 20 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.last 21 (4,true),
.cycle 12 6 false (0),
.last 19 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 2 11 true (1),
.last 14 (4,true),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 8 5 true (2),
.last 33 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid05_part1057_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1057) = true := by rfl

def kid05_part1059 : Audit := .cycle 0 23 false (3)
theorem kid05_part1059_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part1059) = true := by rfl

def kid05_part1060 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 11 false (0),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 11 false (2),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 16 11 false (3),
.cycle 13 11 false (1),
.cycle 11 2 true (0)
])
theorem kid05_part1060_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part1060) = true := by rfl

def kid05_part1061 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1061_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part1061) = true := by rfl

def kid05_part1062 : Audit := .cycle 0 13 true (0)
theorem kid05_part1062_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part1062) = true := by rfl

def kid05_part1063 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 26 1 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 26 1 false (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (-1),
.cycle 28 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 2 true (0)
])
theorem kid05_part1063_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part1063) = true := by rfl

def kid05_part1064 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1064_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part1064) = true := by rfl

def kid05_part1065 : Audit := .cycle 0 12 true (0)
theorem kid05_part1065_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part1065) = true := by rfl

def kid05_part1066 : Audit := .cycle 1 11 true (1)
theorem kid05_part1066_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part1066) = true := by rfl

def kid05_part1067 : Audit := .cycle 24 1 false (2)
theorem kid05_part1067_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part1067) = true := by rfl

def kid05_part1068 : Audit := .cycle 21 1 false (1)
theorem kid05_part1068_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part1068) = true := by rfl

def kid05_part1069 : Audit := .cycle 25 1 false (1)
theorem kid05_part1069_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part1069) = true := by rfl

def kid05_part1070 : Audit := .cycle 11 1 true (1)
theorem kid05_part1070_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part1070) = true := by rfl

def kid05_part1071 : Audit := .split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 0 21 false (3),
.last 20 (4,true),
.cycle 14 6 false (1),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 12 13 false (1),
.cycle 17 3 true (-2),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 12 14 true (-2),
.last 20 (4,true),
.last 21 (4,true),
.cycle 13 26 false (3),
.cycle 13 22 false (2),
.cycle 2 18 false (3),
.cycle 12 15 true (-2),
.cycle 13 8 false (1),
.cycle 13 12 false (1)
])
theorem kid05_part1071_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part1071) = true := by rfl

def kid05_part1072 : Audit := .split 12 (1,true) (byMove [
.cycle 18 6 false (0),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 6 false (-1),
.cycle 19 6 false (3),
.cycle 20 6 false (4),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 6 false (2),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 21 6 false (3),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 6 false (-1),
.cycle 2 12 true (0),
.cycle 1 13 true (0),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 6 false (1)
])
theorem kid05_part1072_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part1072) = true := by rfl

def kid05_part1073 : Audit := .split 17 (1,true) (byMove [
.cycle 0 31 true (-2),
.cycle 0 32 true (-2),
.cycle 0 22 true (-2),
.cycle 0 19 true (-2),
.last 18 (4,true),
.cycle 0 24 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 64, 16, 64],64⟩,
.cycle 0 31 true (-2),
.cycle 0 43 true (-2),
.cycle 0 29 true (-2),
.cycle 0 31 true (-2),
.cycle 0 21 true (-2),
.cycle 0 26 true (-2),
.cycle 0 39 false (3),
.cycle 12 6 true (-2),
.cycle 0 32 true (-2),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 44 true (-2),
.cycle 0 48 true (-2),
.cycle 2 16 true (-2),
.cycle 0 33 true (-2),
.cycle 0 26 true (-2),
.cycle 0 38 true (-2)
])
theorem kid05_part1073_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part1073) = true := by rfl

def kid05_part1074 : Audit := .cycle 24 1 false (0)
theorem kid05_part1074_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part1074) = true := by rfl

def kid05_part1075 : Audit := .split 12 (4,true) (byMove [
.cycle 25 1 false (-3),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 26 1 false (0),
.last 13 (1,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 16 1 false (2),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 21 1 false (-3),
.cycle 28 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 22 1 false (-2),
.cycle 22 1 false (-2)
])
theorem kid05_part1075_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part1075) = true := by rfl

def kid05_part1076 : Audit := .split 13 (4,true) (byMove [
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
.cycle 24 1 false (0),
.cycle 8 10 true (0),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 25 1 false (1),
.cycle 17 1 false (-1),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 0 31 true (0),
.cycle 19 1 false (-1),
.cycle 11 3 true (0)
])
theorem kid05_part1076_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1076) = true := by rfl

def kid05_part1077 : Audit := .cycle 0 12 true (0)
theorem kid05_part1077_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1077) = true := by rfl

def kid05_part1078 : Audit := .cycle 1 11 true (1)
theorem kid05_part1078_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1078) = true := by rfl

def kid05_part1079 : Audit := .cycle 2 10 true (1)
theorem kid05_part1079_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1079) = true := by rfl

def kid05_part1080 : Audit := .cycle 2 13 true (1)
theorem kid05_part1080_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1080) = true := by rfl

def kid05_part1081 : Audit := .cycle 15 3 false (1)
theorem kid05_part1081_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1081) = true := by rfl

def kid05_part1082 : Audit := .cycle 11 1 true (1)
theorem kid05_part1082_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1082) = true := by rfl

def kid05_part1058 : Audit := .split 11 (5,false) (byMove [(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073),(kid05_part1074),(kid05_part1075),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079),(kid05_part1080),(kid05_part1081),(kid05_part1082)])

theorem kid05_part1058_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1058) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,false) (some mv)) (byMove [(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073),(kid05_part1074),(kid05_part1075),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079),(kid05_part1080),(kid05_part1081),(kid05_part1082)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1059_checked

  · exact kid05_part1065_checked

  · exact kid05_part1071_checked

  · exact kid05_part1077_checked

  · exact kid05_part1060_checked

  · exact kid05_part1066_checked

  · exact kid05_part1072_checked

  · exact kid05_part1078_checked

  · exact kid05_part1061_checked

  · exact kid05_part1067_checked

  · exact kid05_part1073_checked

  · exact kid05_part1079_checked

  · exact kid05_part1062_checked

  · exact kid05_part1068_checked

  · exact kid05_part1074_checked

  · exact kid05_part1080_checked

  · exact kid05_part1063_checked

  · exact kid05_part1069_checked

  · exact kid05_part1075_checked

  · exact kid05_part1081_checked

  · exact kid05_part1064_checked

  · exact kid05_part1070_checked

  · exact kid05_part1076_checked

  · exact kid05_part1082_checked

def kid05_part1083 : Audit := .cycle 0 11 true (0)
theorem kid05_part1083_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1083) = true := by rfl

def kid05_part1084 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 24 1 false (0),
.cycle 14 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 15 3 false (1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 41 1 false (9),
.cycle 35 1 false (7),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 8 14 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 18 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 19 5 false (1),
.last 13 (5,false),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 20 (5,false),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 19 9 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 18 9 false (2),
.last 13 (5,false)
]),
.split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 17 5 false (1),
.cycle 17 5 false (2),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 13 4 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 28 1 false (2),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 15 2 true (0),
.cycle 0 13 true (0),
.cycle 12 2 true (1),
.cycle 14 2 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 13 true (2),
.cycle 3 9 true (1),
.cycle 9 4 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.last 19 (1,true),
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
])
theorem kid05_part1084_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1084) = true := by rfl

def kid05_part1085 : Audit := .cycle 8 2 true (2)
theorem kid05_part1085_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1085) = true := by rfl

def kid05_part1086 : Audit := .cycle 0 10 true (0)
theorem kid05_part1086_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1086) = true := by rfl

def kid05_part1087 : Audit := .cycle 1 9 true (1)
theorem kid05_part1087_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1087) = true := by rfl

def kid05_part1088 : Audit := .split 20 (5,false) (byMove [
.cycle 2 20 true (1),
.split 21 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 38 1 false (2),
.cycle 1 22 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 59 1 false (9),
.cycle 1 22 true (1),
.cycle 6 18 true (2),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 32 1 false (0),
.cycle 1 24 true (1),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 9 13 true (2),
.cycle 20 2 true (3)
]),
.cycle 45 1 false (1),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 38 1 false (2),
.cycle 39 1 false (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 59 1 false (9),
.cycle 41 1 false (3),
.last 23 (1,true),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 32 1 false (0),
.cycle 43 1 false (1),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 9 13 true (2),
.cycle 20 2 true (3)
]),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 4, 16, 64],[4, 64, 4, 1, 64, 16, 64],64⟩,
.cycle 20 1 true (4),
.cycle 6 15 true (2),
.split 21 (1,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 35 1 false (1),
.cycle 0 31 true (0),
.cycle 0 25 true (0),
.cycle 0 29 true (0),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 7 18 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 8 14 true (2),
.cycle 39 9 false (2),
.cycle 36 7 false (1),
.cycle 2 23 true (1),
.cycle 32 1 false (0),
.cycle 0 31 true (0),
.last 31 (4,true),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 8 14 true (2)
]),
.split 26 (1,true) (byMove [
.cycle 2 26 true (1),
.cycle 1 27 true (1),
.cycle 0 31 true (0),
.cycle 0 28 true (0),
.last 27 (4,true),
.cycle 8 19 true (1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 10 17 true (1),
.cycle 3 24 true (1),
.cycle 0 51 true (0),
.cycle 0 30 true (0),
.cycle 6 21 true (1),
.cycle 34 13 false (2),
.cycle 21 6 true (1),
.cycle 2 27 true (1),
.last 27 (4,true),
.last 28 (4,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 2 28 true (1),
.cycle 16 34 true (1),
.cycle 16 12 true (1)
]),
.cycle 2 21 true (1),
.split 21 (4,true) (byMove [
.cycle 7 17 true (2),
.cycle 0 25 true (0),
.cycle 35 1 false (1),
.cycle 0 31 true (0),
.cycle 0 25 true (0),
.cycle 27 3 false (-1),
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 31 3 false (1),
.cycle 0 23 true (0),
.cycle 41 3 false (4),
.cycle 8 14 true (2),
.last 23 (1,true),
.last 36 (1,true),
.cycle 2 23 true (1),
.cycle 32 1 false (0),
.cycle 29 3 false (0),
.cycle 27 3 false (-1),
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 9 14 true (2),
.cycle 8 14 true (2)
]),
.split 22 (4,true) (byMove [
.cycle 2 22 true (1),
.last 23 (1,true),
.cycle 29 1 false (-1),
.cycle 0 24 true (0),
.cycle 42 1 false (2),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 13 true (2),
.cycle 3 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 4, 16, 64],[4, 64, 4, 1, 16, 16, 64],64⟩,
.cycle 8 19 true (2),
.cycle 6 17 true (2),
.last 23 (1,true),
.cycle 29 1 false (-1),
.cycle 2 23 true (1),
.cycle 33 1 false (-1),
.cycle 21 2 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 2 24 true (1),
.cycle 9 14 true (2),
.cycle 20 3 true (3)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 9 12 true (2),
.cycle 20 1 true (4)
])
theorem kid05_part1088_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1088) = true := by rfl

def kid05_part1089 : Audit := .cycle 3 7 true (1)
theorem kid05_part1089_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1089) = true := by rfl

def kid05_part1090 : Audit := .cycle 9 1 true (3)
theorem kid05_part1090_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1090) = true := by rfl

def kid05_part1091 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (4,true) (byMove [
.cycle 2 22 true (1),
.last 23 (1,true),
.cycle 8 26 true (2),
.cycle 0 24 true (0),
.cycle 9 15 true (2),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 8 24 true (2),
.cycle 3 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 32, 4, 64],[4, 64, 40, 1, 16, 16, 64],64⟩,
.cycle 10 13 true (2),
.cycle 6 17 true (2),
.last 23 (1,true),
.cycle 0 27 true (0),
.cycle 2 23 true (1),
.cycle 20 4 true (4),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 2 24 true (1),
.cycle 9 14 true (2),
.cycle 8 25 true (2)
]),
.cycle 8 11 true (2),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3),
.cycle 6 7 true (2),
.last 20 (4,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 14 (4,true),
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
.cycle 8 4 true (2),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 19 1 false (-1),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 8 19 true (2),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 32, 1, 16, 16, 64],64⟩,
.cycle 8 6 true (2),
.cycle 8 10 true (2),
.last 14 (1,true),
.cycle 19 1 false (-1),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.cycle 12 2 true (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 9 6 true (2),
.cycle 8 6 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part1091_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1091) = true := by rfl

def kid05_part1092 : Audit := .cycle 6 4 true (2)
theorem kid05_part1092_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1092) = true := by rfl

def kid05_part1093 : Audit := .split 10 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.cycle 11 6 false (1),
.split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 7 false (1),
.cycle 8 5 true (1),
.cycle 14 6 false (1),
.cycle 12 6 false (0),
.cycle 13 8 true (-2),
.cycle 0 16 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 16 9 false (2),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 3 false (1),
.last 28 (4,true)
]),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 8 false (1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 7 8 true (2),
.cycle 12 1 true (2),
.cycle 0 31 true (0),
.cycle 20 7 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 8 false (1),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 19 7 false (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,false),
.cycle 35 1 false (7),
.cycle 7 7 true (2),
.last 12 (5,false),
.cycle 7 9 true (2),
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
.cycle 8 3 true (2),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.cycle 11 6 false (1),
.split 11 (5,false) (byMove [
.last 33 (4,true),
.last 20 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 6 6 true (1),
.cycle 10 2 true (1),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.last 21 (4,true),
.cycle 12 6 false (0),
.last 19 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 13 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 13 8 false (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,false),
.cycle 3 9 true (1),
.cycle 7 7 true (2),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 13 8 false (1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 8 3 true (2)
])
theorem kid05_part1093_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1093) = true := by rfl

def kid05_part1095 : Audit := .cycle 0 42 true (-1)
theorem kid05_part1095_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part1095) = true := by rfl

def kid05_part1096 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 20 true (-2),
.cycle 13 11 false (0),
.cycle 18 11 false (2),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 21 true (0),
.cycle 13 11 false (2),
.cycle 15 11 false (0),
.cycle 14 11 false (0),
.cycle 20 11 false (2),
.cycle 13 1 false (-1),
.cycle 17 11 false (2),
.cycle 1 26 false (3),
.cycle 21 11 false (1),
.cycle 0 16 true (0),
.cycle 13 11 false (2),
.cycle 0 18 true (0),
.cycle 13 11 false (1),
.cycle 11 2 true (0)
])
theorem kid05_part1096_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part1096) = true := by rfl

def kid05_part1097 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1097_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part1097) = true := by rfl

def kid05_part1098 : Audit := .cycle 23 1 false (-1)
theorem kid05_part1098_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part1098) = true := by rfl

def kid05_part1099 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 13 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 20 true (-2),
.cycle 0 17 false (3),
.cycle 13 13 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 17 (1,true),
.cycle 13 13 false (3),
.last 14 (1,true),
.cycle 14 13 false (0),
.cycle 13 13 false (3),
.cycle 13 1 false (-1),
.cycle 22 13 false (2),
.last 18 (1,true),
.cycle 18 13 false (2),
.cycle 0 16 true (0),
.cycle 18 13 false (2),
.cycle 0 18 true (0),
.cycle 13 13 false (1),
.cycle 11 2 true (0)
])
theorem kid05_part1099_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part1099) = true := by rfl

def kid05_part1100 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part1100) = true := by rfl

def kid05_part1101 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 29 true (0),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 6 8 true (1),
.cycle 19 9 false (1),
.cycle 10 4 true (1),
.cycle 2 14 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 22 (4,true),
.cycle 0 15 true (0)
])
theorem kid05_part1101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part1101) = true := by rfl

def kid05_part1102 : Audit := .cycle 7 6 true (1)
theorem kid05_part1102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part1102) = true := by rfl

def kid05_part1103 : Audit := .cycle 0 14 true (0)
theorem kid05_part1103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part1103) = true := by rfl

def kid05_part1104 : Audit := .cycle 21 1 false (1)
theorem kid05_part1104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part1104) = true := by rfl

def kid05_part1105 : Audit := .cycle 2 14 true (1)
theorem kid05_part1105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part1105) = true := by rfl

def kid05_part1106 : Audit := .cycle 8 5 true (1)
theorem kid05_part1106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part1106) = true := by rfl

def kid05_part1107 : Audit := .split 19 (1,true) (byMove [
.cycle 12 13 false (1),
.cycle 12 14 false (1),
.cycle 16 4 false (0),
.cycle 13 13 false (1),
.last 20 (4,true),
.cycle 14 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 64, 16, 64],64⟩,
.cycle 7 14 false (3),
.cycle 0 54 true (-2),
.cycle 12 11 false (1),
.cycle 0 26 true (-2),
.last 42 (4,true),
.cycle 12 8 false (1),
.cycle 13 9 false (1),
.cycle 16 4 false (0),
.cycle 0 44 true (-2),
.last 20 (4,true),
.last 21 (4,true),
.cycle 43 22 false (3),
.cycle 13 14 false (1),
.cycle 2 22 true (-2),
.cycle 4 16 false (3),
.cycle 13 8 false (1),
.cycle 13 12 false (1)
])
theorem kid05_part1107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part1107) = true := by rfl

def kid05_part1108 : Audit := .split 12 (1,true) (byMove [
.cycle 18 6 false (0),
.cycle 34 6 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 18 (4,true),
.cycle 13 6 false (-1),
.cycle 0 16 true (0),
.cycle 14 6 false (3),
.cycle 13 6 false (1),
.cycle 20 6 false (4),
.last 13 (4,true),
.cycle 13 6 false (2),
.cycle 16 6 false (0),
.cycle 13 6 false (0),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.cycle 17 6 false (1),
.cycle 13 6 false (-1),
.cycle 0 16 true (0),
.cycle 21 6 false (1),
.cycle 13 6 false (1),
.cycle 12 29 true (0),
.last 13 (4,true),
.cycle 15 6 false (1)
])
theorem kid05_part1108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part1108) = true := by rfl

def kid05_part1109 : Audit := .split 17 (1,true) (byMove [
.cycle 0 36 true (-2),
.cycle 12 16 true (-2),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.last 18 (4,true),
.cycle 12 8 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 1, 15, 1, 64, 16, 64],64⟩,
.cycle 7 12 true (-2),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.cycle 0 39 true (-2),
.cycle 0 39 true (-2),
.cycle 12 10 true (-2),
.cycle 12 11 false (1),
.cycle 12 6 true (-2),
.cycle 0 22 true (-2),
.last 18 (4,true),
.last 19 (4,true),
.cycle 35 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[4, 2, 15, 1, 64, 16, 64],64⟩,
.cycle 0 20 true (-2),
.cycle 4 14 true (-2),
.last 28 (4,true),
.last 29 (4,true)
])
theorem kid05_part1109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part1109) = true := by rfl

def kid05_part1110 : Audit := .cycle 0 16 true (0)
theorem kid05_part1110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part1110) = true := by rfl

def kid05_part1111 : Audit := .split 12 (4,true) (byMove [
.proven (BB6.Agent11Raw39B1RCPumps.M356.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M356.never m hm),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (1,true),
.last 21 (1,true),
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 0 52 true (-2),
.last 15 (1,true),
.cycle 0 34 true (0),
.cycle 0 40 true (-2),
.last 14 (1,true),
.proven (BB6.Agent11Raw39B1RCPumps.M357.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M357.never m hm),
.cycle 0 18 true (-1),
.cycle 13 1 false (-1),
.last 29 (1,true),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 257, 1, 256, 8192, 16384, 8, 256, 1, 256, 524288, 1048576, 32768, 257, 4352, 1048577, 524288, 1048576, 2097152, 20763017, 20763017, 20763017, 16777216],[256, 16777216, 8, 1, 1, 1024, 16384, 16777216, 1, 1, 0, 65536, 1048576, 16777216, 2101632, 4096, 20763017, 4194304, 1048576, 16777216, 20763017, 262144, 20763017, 4194304, 16777216],33501248⟩,
.cycle 0 16 true (0),
.last 13 (1,true),
.last 25 (1,true),
.last 15 (1,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 1, 4, 4, 4, 4],[128, 256, 8, 1327513993, 1, 256, 8192, 16384, 8, 67109120, 1, 65536, 128, 256, 2097152, 256, 256, 1024, 33554432, 67108864, 134217728, 1, 16777216, 1, 33554432, 67108864, 134217728, 1327513993, 1327513993, 1595949449, 1073741824],[256, 1073741824, 264, 1, 1024, 1024, 16384, 1073741824, 1, 1, 65536, 65536, 256, 1073741824, 256, 262144, 1024, 1024, 67108864, 1073741824, 1, 16777216, 268435456, 268435456, 67108864, 1073741824, 1327513993, 16777216, 268435456, 268435456, 1073741824],2136845166⟩,
.far false 5 ⟨0,[0, 1, 0, 2, 3, 1, 4, 4, 4, 4],[128, 256, 8, 1327513993, 1, 256, 8192, 16384, 8, 67109120, 1, 65536, 128, 256, 2097152, 256, 256, 1024, 33554432, 67108864, 134217728, 1, 16777216, 1, 33554432, 67108864, 134217728, 1327513993, 1327513993, 1595949449, 1073741824],[256, 1073741824, 264, 1, 2048, 1024, 16384, 1073741824, 1, 1, 131072, 65536, 256, 1073741824, 256, 262144, 2048, 1024, 67108864, 1073741824, 1, 16777216, 536870912, 268435456, 67108864, 1073741824, 1327513993, 16777216, 536870912, 268435456, 1073741824],2136845166⟩
])
theorem kid05_part1111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part1111) = true := by rfl

def kid05_part1112 : Audit := .split 13 (4,true) (byMove [
.cycle 24 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 22 true (-2),
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 7 8 true (0),
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 5, 5, 16, 64],[4, 64, 5, 1, 16, 16, 64],64⟩,
.cycle 8 16 true (0),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.cycle 23 1 false (-1),
.cycle 12 2 true (0),
.last 15 (1,true),
.cycle 25 1 false (-1),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 19 1 false (-1),
.cycle 29 1 false (-1)
])
theorem kid05_part1112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1112) = true := by rfl

def kid05_part1113 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 14 15 false (2),
.cycle 17 7 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 29 true (0),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 18 11 false (2),
.cycle 14 10 false (2),
.cycle 17 7 false (1),
.cycle 2 14 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 28 (4,true),
.cycle 0 15 true (0)
])
theorem kid05_part1113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1113) = true := by rfl

def kid05_part1114 : Audit := .cycle 16 9 false (2)
theorem kid05_part1114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1114) = true := by rfl

def kid05_part1115 : Audit := .cycle 0 14 true (0)
theorem kid05_part1115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1115) = true := by rfl

def kid05_part1116 : Audit := .cycle 4 8 true (1)
theorem kid05_part1116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1116) = true := by rfl

def kid05_part1117 : Audit := .cycle 15 3 false (1)
theorem kid05_part1117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1117) = true := by rfl

def kid05_part1118 : Audit := .split 28 (4,true) (byMove [
.cycle 0 60 true (-1),
.last 29 (1,true),
.cycle 18 11 false (2),
.last 31 (1,true),
.cycle 0 57 false (4),
.cycle 16 13 false (3),
.cycle 59 25 true (1),
.last 29 (1,true),
.cycle 60 1 true (4),
.cycle 0 56 true (-1),
.cycle 0 34 true (-1),
.cycle 31 1 true (5),
.cycle 15 15 false (3),
.last 29 (1,true),
.cycle 18 11 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 53, 32, 64],[4, 64, 53, 1, 53, 16, 64],64⟩,
.cycle 21 15 false (2),
.cycle 27 2 true (1),
.cycle 13 21 false (4),
.last 29 (1,true),
.cycle 13 17 false (4),
.cycle 0 56 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 53, 32, 64],[4, 64, 53, 1, 16, 16, 64],64⟩,
.cycle 31 1 true (5)
])
theorem kid05_part1118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1118) = true := by rfl

def kid05_part1094 : Audit := .split 11 (5,false) (byMove [(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1107),(kid05_part1108),(kid05_part1109),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118)])

theorem kid05_part1094_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1094) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (5,false) (some mv)) (byMove [(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1107),(kid05_part1108),(kid05_part1109),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1095_checked

  · exact kid05_part1101_checked

  · exact kid05_part1107_checked

  · exact kid05_part1113_checked

  · exact kid05_part1096_checked

  · exact kid05_part1102_checked

  · exact kid05_part1108_checked

  · exact kid05_part1114_checked

  · exact kid05_part1097_checked

  · exact kid05_part1103_checked

  · exact kid05_part1109_checked

  · exact kid05_part1115_checked

  · exact kid05_part1098_checked

  · exact kid05_part1104_checked

  · exact kid05_part1110_checked

  · exact kid05_part1116_checked

  · exact kid05_part1099_checked

  · exact kid05_part1105_checked

  · exact kid05_part1111_checked

  · exact kid05_part1117_checked

  · exact kid05_part1100_checked

  · exact kid05_part1106_checked

  · exact kid05_part1112_checked

  · exact kid05_part1118_checked

def kid05_part1119 : Audit := .cycle 2 10 true (1)
theorem kid05_part1119_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1119) = true := by rfl

def kid05_part1121 : Audit := .cycle 0 20 true (0)
theorem kid05_part1121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1121) = true := by rfl

def kid05_part1122 : Audit := .cycle 0 14 true (0)
theorem kid05_part1122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1122) = true := by rfl

def kid05_part1123 : Audit := .cycle 21 1 false (1)
theorem kid05_part1123_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1123) = true := by rfl

def kid05_part1124 : Audit := .cycle 0 16 true (0)
theorem kid05_part1124_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1124) = true := by rfl

def kid05_part1125 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1125_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1125) = true := by rfl

def kid05_part1126 : Audit := .split 11 (5,false) (byMove [
.cycle 0 42 true (-1),
.last 12 (1,true),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 8 5 true (1),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 14 1 false (-2),
.cycle 17 1 false (-1),
.last 13 (1,true),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 3 false (1),
.cycle 15 13 false (3)
])
theorem kid05_part1126_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1126) = true := by rfl

def kid05_part1127 : Audit := .cycle 2 10 true (1)
theorem kid05_part1127_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1127) = true := by rfl

def kid05_part1128 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (5,false),
.cycle 35 1 false (7),
.cycle 32 1 false (8),
.last 12 (5,false),
.cycle 6 8 true (2),
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
])
theorem kid05_part1128_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1128) = true := by rfl

def kid05_part1129 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.cycle 19 1 false (1),
.cycle 12 1 true (2),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
])
theorem kid05_part1129_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1129) = true := by rfl

def kid05_part1130 : Audit := .cycle 0 12 true (0)
theorem kid05_part1130_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1130) = true := by rfl

def kid05_part1131 : Audit := .cycle 21 1 false (5)
theorem kid05_part1131_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1131) = true := by rfl

def kid05_part1132 : Audit := .cycle 8 3 true (2)
theorem kid05_part1132_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1132) = true := by rfl

def kid05_part1133 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.last 20 (5,false),
.cycle 0 17 true (0),
.cycle 18 3 false (0),
.cycle 18 5 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 16, 64, 64],[1, 17, 32, 1, 1, 1, 64],96⟩,
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 20 (5,false),
.cycle 5 8 true (1),
.cycle 18 3 false (0),
.cycle 19 9 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.cycle 18 13 false (2),
.cycle 15 19 false (3)
])
theorem kid05_part1133_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1133) = true := by rfl

def kid05_part1134 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.last 18 (5,false),
.cycle 19 5 false (3),
.cycle 17 5 false (1),
.cycle 23 5 false (4),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 17 (5,false),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.cycle 15 2 true (0),
.cycle 18 7 true (1)
])
theorem kid05_part1134_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1134) = true := by rfl

def kid05_part1135 : Audit := .cycle 2 12 true (1)
theorem kid05_part1135_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1135) = true := by rfl

def kid05_part1136 : Audit := .cycle 18 1 false (0)
theorem kid05_part1136_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1136) = true := by rfl

def kid05_part1137 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1137_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1137) = true := by rfl

def kid05_part1138 : Audit := .split 11 (5,false) (byMove [
.cycle 31 2 true (2),
.last 12 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 10 2 true (1),
.cycle 12 2 true (2),
.last 19 (1,true),
.last 12 (1,true),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 16 2 true (1),
.last 12 (1,true),
.cycle 15 2 true (0),
.cycle 2 12 true (1),
.cycle 12 2 true (1),
.cycle 12 2 true (2)
])
theorem kid05_part1138_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1138) = true := by rfl

def kid05_part1139 : Audit := .cycle 2 10 true (1)
theorem kid05_part1139_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1139) = true := by rfl

def kid05_part1140 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (5,false),
.cycle 3 9 true (1),
.cycle 1 16 true (1),
.last 12 (5,false),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid05_part1140_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1140) = true := by rfl

def kid05_part1141 : Audit := .cycle 7 4 true (2)
theorem kid05_part1141_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1141) = true := by rfl

def kid05_part1142 : Audit := .cycle 0 12 true (0)
theorem kid05_part1142_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1142) = true := by rfl

def kid05_part1143 : Audit := .cycle 9 3 true (2)
theorem kid05_part1143_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1143) = true := by rfl

def kid05_part1144 : Audit := .cycle 8 3 true (2)
theorem kid05_part1144_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1144) = true := by rfl

def kid05_part1120 : Audit := .split 10 (4,true) (byMove [(kid05_part1121),(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130),(kid05_part1131),(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144)])

theorem kid05_part1120_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1120) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1121),(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130),(kid05_part1131),(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1121_checked

  · exact kid05_part1127_checked

  · exact kid05_part1133_checked

  · exact kid05_part1139_checked

  · exact kid05_part1122_checked

  · exact kid05_part1128_checked

  · exact kid05_part1134_checked

  · exact kid05_part1140_checked

  · exact kid05_part1123_checked

  · exact kid05_part1129_checked

  · exact kid05_part1135_checked

  · exact kid05_part1141_checked

  · exact kid05_part1124_checked

  · exact kid05_part1130_checked

  · exact kid05_part1136_checked

  · exact kid05_part1142_checked

  · exact kid05_part1125_checked

  · exact kid05_part1131_checked

  · exact kid05_part1137_checked

  · exact kid05_part1143_checked

  · exact kid05_part1126_checked

  · exact kid05_part1132_checked

  · exact kid05_part1138_checked

  · exact kid05_part1144_checked

def kid05_part1146 : Audit := .cycle 2 11 true (1)
theorem kid05_part1146_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1146) = true := by rfl

def kid05_part1147 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (7),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 21 9 false (1),
.cycle 20 7 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
])
theorem kid05_part1147_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1147) = true := by rfl

def kid05_part1148 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (3),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 33 1 false (1),
.cycle 13 1 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 28 1 false (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 19 5 false (1),
.cycle 13 1 true (1)
])
theorem kid05_part1148_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1148) = true := by rfl

def kid05_part1149 : Audit := .cycle 0 13 true (0)
theorem kid05_part1149_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1149) = true := by rfl

def kid05_part1150 : Audit := .split 18 (5,false) (byMove [
.cycle 15 11 false (1),
.last 41 (1,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 13 14 true (-2),
.last 19 (1,true),
.cycle 22 1 false (0),
.cycle 0 20 true (-2),
.cycle 16 3 false (0),
.cycle 13 7 false (1),
.last 20 (1,true),
.cycle 13 9 false (1),
.cycle 13 16 true (-3),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 2 18 false (3),
.last 19 (1,true),
.cycle 13 8 false (1),
.cycle 9 24 false (3),
.cycle 15 4 false (1),
.cycle 15 8 false (1)
])
theorem kid05_part1150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1150) = true := by rfl

def kid05_part1151 : Audit := .cycle 8 4 true (2)
theorem kid05_part1151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1151) = true := by rfl

def kid05_part1152 : Audit := .cycle 0 12 true (0)
theorem kid05_part1152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1152) = true := by rfl

def kid05_part1153 : Audit := .cycle 1 11 true (1)
theorem kid05_part1153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1153) = true := by rfl

def kid05_part1154 : Audit := .split 24 (5,false) (byMove [
.cycle 2 24 true (1),
.last 25 (1,true),
.cycle 53 1 false (1),
.cycle 0 26 true (0),
.cycle 43 1 false (3),
.cycle 8 17 true (2),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 12 13 true (2),
.cycle 3 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 4, 16, 64],[4, 64, 4, 1, 4, 16, 64],64⟩,
.cycle 24 1 true (4),
.cycle 6 19 true (2),
.last 25 (1,true),
.last 30 (1,true),
.cycle 2 25 true (1),
.cycle 32 2 false (0),
.cycle 10 15 true (2),
.cycle 0 25 true (0),
.cycle 1 24 true (1),
.cycle 2 23 true (1),
.cycle 2 26 true (1),
.cycle 9 16 true (2),
.cycle 24 1 true (4)
])
theorem kid05_part1154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1154) = true := by rfl

def kid05_part1155 : Audit := .cycle 3 9 true (1)
theorem kid05_part1155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1155) = true := by rfl

def kid05_part1156 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 19 1 false (-1),
.last 16 (1,true),
.cycle 23 2 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 2 13 true (1),
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 24, 4, 64],[4, 64, 24, 1, 16, 16, 64],64⟩,
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.cycle 8 6 true (2),
.last 24 (1,true),
.last 14 (1,true),
.last 21 (1,true),
.cycle 5 9 true (1),
.cycle 41 2 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.cycle 8 6 true (2)
])
theorem kid05_part1156_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1156) = true := by rfl

def kid05_part1157 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 15 true (2),
.cycle 8 15 true (2),
.cycle 11 4 true (3),
.cycle 12 1 true (4),
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
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part1157_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1157) = true := by rfl

def kid05_part1158 : Audit := .cycle 6 6 true (2)
theorem kid05_part1158_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1158) = true := by rfl

def kid05_part1159 : Audit := .split 12 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 18 true (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 21 9 false (1),
.cycle 20 7 false (0),
.cycle 2 14 true (1),
.cycle 22 1 false (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part1159_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1159) = true := by rfl

def kid05_part1160 : Audit := .split 13 (5,false) (byMove [
.cycle 0 48 true (-1),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 29 1 false (-1),
.cycle 30 2 false (0),
.cycle 19 1 false (-1),
.last 15 (1,true),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 2 18 true (1),
.cycle 8 7 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 19 (1,true),
.cycle 0 18 true (0),
.cycle 0 20 true (-1),
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 19 5 false (1),
.cycle 22 15 false (3)
])
theorem kid05_part1160_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1160) = true := by rfl

def kid05_part1161 : Audit := .cycle 2 12 true (1)
theorem kid05_part1161_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1161) = true := by rfl

def kid05_part1162 : Audit := .split 18 (5,false) (byMove [
.cycle 15 11 false (1),
.last 31 (1,true),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 13 9 false (1),
.last 19 (1,true),
.cycle 35 18 true (0),
.cycle 13 10 true (-2),
.cycle 16 3 false (0),
.cycle 14 5 false (1),
.last 20 (1,true),
.cycle 13 9 false (1),
.cycle 13 11 false (1),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 15 10 false (1),
.last 19 (1,true),
.cycle 13 8 false (1),
.cycle 5 14 false (3),
.cycle 15 4 false (1),
.cycle 15 6 false (1)
])
theorem kid05_part1162_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1162) = true := by rfl

def kid05_part1163 : Audit := .cycle 10 2 true (2)
theorem kid05_part1163_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1163) = true := by rfl

def kid05_part1164 : Audit := .cycle 0 12 true (0)
theorem kid05_part1164_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1164) = true := by rfl

def kid05_part1165 : Audit := .cycle 1 11 true (1)
theorem kid05_part1165_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1165) = true := by rfl

def kid05_part1166 : Audit := .cycle 2 10 true (1)
theorem kid05_part1166_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1166) = true := by rfl

def kid05_part1167 : Audit := .cycle 2 13 true (1)
theorem kid05_part1167_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1167) = true := by rfl

def kid05_part1168 : Audit := .cycle 9 3 true (2)
theorem kid05_part1168_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1168) = true := by rfl

def kid05_part1169 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (2),
.cycle 3 10 true (1),
.cycle 11 4 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 10 true (2),
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
theorem kid05_part1169_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1169) = true := by rfl

def kid05_part1145 : Audit := .split 11 (4,true) (byMove [(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152),(kid05_part1153),(kid05_part1154),(kid05_part1155),(kid05_part1156),(kid05_part1157),(kid05_part1158),(kid05_part1159),(kid05_part1160),(kid05_part1161),(kid05_part1162),(kid05_part1163),(kid05_part1164),(kid05_part1165),(kid05_part1166),(kid05_part1167),(kid05_part1168),(kid05_part1169)])

theorem kid05_part1145_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1145) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some mv)) (byMove [(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152),(kid05_part1153),(kid05_part1154),(kid05_part1155),(kid05_part1156),(kid05_part1157),(kid05_part1158),(kid05_part1159),(kid05_part1160),(kid05_part1161),(kid05_part1162),(kid05_part1163),(kid05_part1164),(kid05_part1165),(kid05_part1166),(kid05_part1167),(kid05_part1168),(kid05_part1169)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1146_checked

  · exact kid05_part1152_checked

  · exact kid05_part1158_checked

  · exact kid05_part1164_checked

  · exact kid05_part1147_checked

  · exact kid05_part1153_checked

  · exact kid05_part1159_checked

  · exact kid05_part1165_checked

  · exact kid05_part1148_checked

  · exact kid05_part1154_checked

  · exact kid05_part1160_checked

  · exact kid05_part1166_checked

  · exact kid05_part1149_checked

  · exact kid05_part1155_checked

  · exact kid05_part1161_checked

  · exact kid05_part1167_checked

  · exact kid05_part1150_checked

  · exact kid05_part1156_checked

  · exact kid05_part1162_checked

  · exact kid05_part1168_checked

  · exact kid05_part1151_checked

  · exact kid05_part1157_checked

  · exact kid05_part1163_checked

  · exact kid05_part1169_checked

def kid05_part1170 : Audit := .cycle 0 10 true (0)
theorem kid05_part1170_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1170) = true := by rfl

def kid05_part1171 : Audit := .cycle 1 9 true (1)
theorem kid05_part1171_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1171) = true := by rfl

def kid05_part1172 : Audit := .cycle 2 8 true (1)
theorem kid05_part1172_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1172) = true := by rfl

def kid05_part1173 : Audit := .cycle 2 11 true (1)
theorem kid05_part1173_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1173) = true := by rfl

def kid05_part1174 : Audit := .cycle 9 1 true (3)
theorem kid05_part1174_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1174) = true := by rfl

def kid05_part1175 : Audit := .split 10 (5,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 13 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.last 30 (4,true),
.cycle 20 7 true (1),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 16 3 false (0),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 13 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 9 4 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 20 7 true (1),
.cycle 2 12 true (1),
.cycle 16 5 false (2),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 8 12 true (2),
.cycle 3 8 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.far false 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 1, 0, 1],[128, 256, 8, 1073742848, 2048, 8388608, 524288, 1048576, 32768, 256, 8388608, 1073741825, 128, 256, 8, 8388608, 2048, 2048, 128, 256, 134217728, 256, 2048, 1024, 128, 256, 8, 8388608, 2048, 8388608, 1073741824],[256, 32768, 1073742849, 1, 1073741824, 1024, 1048576, 8388608, 8388608, 4096, 1073741824, 4194304, 256, 134217728, 1073741952, 1, 1073741824, 1024, 256, 1024, 2048, 16777216, 1073741824, 1024, 256, 32768, 8388608, 1, 1073741824, 1024, 1073741824],1413695516⟩,
.cycle 16 1 false (0),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 24 11 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 18 (4,true),
.last 59 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 3 false (0),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 23 13 false (3),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 12 (1,true),
.cycle 34 12 true (4),
.cycle 5 7 true (1),
.cycle 16 5 false (2),
.cycle 11 2 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2)
]),
.split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 19 5 false (1),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 14 true (2),
.cycle 3 10 true (1),
.cycle 9 4 true (3),
.cycle 8 9 true (2),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 8 true (2),
.cycle 2 13 true (1),
.cycle 18 5 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part1175_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1175) = true := by rfl

def kid05_part1055 : Audit := .split 9 (4,false) (byMove [(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1119),(kid05_part1120),(kid05_part1145),(kid05_part1170),(kid05_part1171),(kid05_part1172),(kid05_part1173),(kid05_part1174),(kid05_part1175)])

theorem kid05_part1055_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (kid05_part1055) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1119),(kid05_part1120),(kid05_part1145),(kid05_part1170),(kid05_part1171),(kid05_part1172),(kid05_part1173),(kid05_part1174),(kid05_part1175)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1056_checked

  · exact kid05_part1086_checked

  · exact kid05_part1092_checked

  · exact kid05_part1170_checked

  · exact kid05_part1057_checked

  · exact kid05_part1087_checked

  · exact kid05_part1093_checked

  · exact kid05_part1171_checked

  · exact kid05_part1058_checked

  · exact kid05_part1088_checked

  · exact kid05_part1094_checked

  · exact kid05_part1172_checked

  · exact kid05_part1083_checked

  · exact kid05_part1089_checked

  · exact kid05_part1119_checked

  · exact kid05_part1173_checked

  · exact kid05_part1084_checked

  · exact kid05_part1090_checked

  · exact kid05_part1120_checked

  · exact kid05_part1174_checked

  · exact kid05_part1085_checked

  · exact kid05_part1091_checked

  · exact kid05_part1145_checked

  · exact kid05_part1175_checked

def kid05_part1177 : Audit := .cycle 2 9 true (1)
theorem kid05_part1177_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part1177) = true := by rfl

def kid05_part1178 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.cycle 12 11 false (0),
.cycle 26 1 false (-2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 12 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.last 33 (4,true),
.cycle 24 1 false (0),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.last 14 (4,true)
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
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 65 1 false (7),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 10 3 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
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
.last 19 (4,true),
.cycle 26 1 false (-2),
.last 15 (4,true),
.last 12 (4,true),
.cycle 12 12 false (1),
.cycle 2 11 true (1),
.cycle 10 2 true (1),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 28 13 true (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 2 11 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 15 (4,true)
]),
.cycle 18 4 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.cycle 10 2 true (2),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 13 13 false (1),
.cycle 2 12 true (1),
.last 12 (4,true),
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
theorem kid05_part1178_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part1178) = true := by rfl

def kid05_part1179 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1179_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part1179) = true := by rfl

def kid05_part1180 : Audit := .cycle 0 11 true (0)
theorem kid05_part1180_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part1180) = true := by rfl

def kid05_part1182 : Audit := .cycle 0 11 true (0)
theorem kid05_part1182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1182) = true := by rfl

def kid05_part1183 : Audit := .cycle 1 10 true (1)
theorem kid05_part1183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1183) = true := by rfl

def kid05_part1184 : Audit := .cycle 21 1 false (1)
theorem kid05_part1184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1184) = true := by rfl

def kid05_part1185 : Audit := .cycle 23 1 false (1)
theorem kid05_part1185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1185) = true := by rfl

def kid05_part1186 : Audit := .split 11 (4,false) (byMove [
.cycle 0 23 false (3),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 27 false (3),
.cycle 24 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (1),
.cycle 14 3 false (0)
])
theorem kid05_part1186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1186) = true := by rfl

def kid05_part1187 : Audit := .split 14 (4,false) (byMove [
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
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 18 false (2),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 11 14 true (-2),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid05_part1187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1187) = true := by rfl

def kid05_part1188 : Audit := .cycle 0 11 true (0)
theorem kid05_part1188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1188) = true := by rfl

def kid05_part1189 : Audit := .cycle 1 10 true (1)
theorem kid05_part1189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1189) = true := by rfl

def kid05_part1190 : Audit := .cycle 35 1 false (7)
theorem kid05_part1190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1190) = true := by rfl

def kid05_part1191 : Audit := .cycle 20 1 false (2)
theorem kid05_part1191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1191) = true := by rfl

def kid05_part1192 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 17 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (3),
.cycle 35 1 false (7),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.cycle 21 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid05_part1192_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1192) = true := by rfl

def kid05_part1193 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 26 1 false (2),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
])
theorem kid05_part1193_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1193) = true := by rfl

def kid05_part1194 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (1),
.last 21 (4,false),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 18 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 21 (4,false),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 19 11 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 13 (4,false),
.cycle 18 9 false (2)
])
theorem kid05_part1194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1194) = true := by rfl

def kid05_part1195 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 23 5 false (3),
.cycle 24 5 false (4),
.last 19 (4,false),
.cycle 0 18 true (0),
.cycle 17 5 false (1),
.cycle 17 5 false (2),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 25 5 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (1),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 13 4 true (0)
])
theorem kid05_part1195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1195) = true := by rfl

def kid05_part1196 : Audit := .cycle 0 13 true (0)
theorem kid05_part1196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1196) = true := by rfl

def kid05_part1197 : Audit := .cycle 18 1 false (0)
theorem kid05_part1197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1197) = true := by rfl

def kid05_part1198 : Audit := .split 11 (4,false) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 129 13 true (3),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 32, 0, 64],[4, 64, 0, 1, 32, 32, 64],64⟩
])
theorem kid05_part1198_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1198) = true := by rfl

def kid05_part1199 : Audit := .split 14 (4,false) (byMove [
.last 20 (1,true),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 18 (1,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 16 (1,true),
.cycle 17 4 true (-2),
.last 18 (1,true),
.cycle 11 9 false (1),
.cycle 16 4 true (-1),
.cycle 11 4 false (1)
])
theorem kid05_part1199_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1199) = true := by rfl

def kid05_part1200 : Audit := .cycle 0 11 true (0)
theorem kid05_part1200_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1200) = true := by rfl

def kid05_part1201 : Audit := .cycle 1 10 true (1)
theorem kid05_part1201_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1201) = true := by rfl

def kid05_part1202 : Audit := .cycle 2 9 true (1)
theorem kid05_part1202_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1202) = true := by rfl

def kid05_part1203 : Audit := .cycle 2 12 true (1)
theorem kid05_part1203_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1203) = true := by rfl

def kid05_part1204 : Audit := .split 11 (4,false) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 1 false (-2),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 13 17 false (1),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid05_part1204_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1204) = true := by rfl

def kid05_part1205 : Audit := .cycle 9 2 true (2)
theorem kid05_part1205_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1205) = true := by rfl

def kid05_part1181 : Audit := .split 10 (4,true) (byMove [(kid05_part1182),(kid05_part1183),(kid05_part1184),(kid05_part1185),(kid05_part1186),(kid05_part1187),(kid05_part1188),(kid05_part1189),(kid05_part1190),(kid05_part1191),(kid05_part1192),(kid05_part1193),(kid05_part1194),(kid05_part1195),(kid05_part1196),(kid05_part1197),(kid05_part1198),(kid05_part1199),(kid05_part1200),(kid05_part1201),(kid05_part1202),(kid05_part1203),(kid05_part1204),(kid05_part1205)])

theorem kid05_part1181_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part1181) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1182),(kid05_part1183),(kid05_part1184),(kid05_part1185),(kid05_part1186),(kid05_part1187),(kid05_part1188),(kid05_part1189),(kid05_part1190),(kid05_part1191),(kid05_part1192),(kid05_part1193),(kid05_part1194),(kid05_part1195),(kid05_part1196),(kid05_part1197),(kid05_part1198),(kid05_part1199),(kid05_part1200),(kid05_part1201),(kid05_part1202),(kid05_part1203),(kid05_part1204),(kid05_part1205)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1182_checked

  · exact kid05_part1188_checked

  · exact kid05_part1194_checked

  · exact kid05_part1200_checked

  · exact kid05_part1183_checked

  · exact kid05_part1189_checked

  · exact kid05_part1195_checked

  · exact kid05_part1201_checked

  · exact kid05_part1184_checked

  · exact kid05_part1190_checked

  · exact kid05_part1196_checked

  · exact kid05_part1202_checked

  · exact kid05_part1185_checked

  · exact kid05_part1191_checked

  · exact kid05_part1197_checked

  · exact kid05_part1203_checked

  · exact kid05_part1186_checked

  · exact kid05_part1192_checked

  · exact kid05_part1198_checked

  · exact kid05_part1204_checked

  · exact kid05_part1187_checked

  · exact kid05_part1193_checked

  · exact kid05_part1199_checked

  · exact kid05_part1205_checked

def kid05_part1206 : Audit := .cycle 8 2 true (2)
theorem kid05_part1206_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part1206) = true := by rfl

def kid05_part1207 : Audit := .cycle 0 10 true (0)
theorem kid05_part1207_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part1207) = true := by rfl

def kid05_part1208 : Audit := .cycle 1 9 true (1)
theorem kid05_part1208_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part1208) = true := by rfl

def kid05_part1209 : Audit := .cycle 9 11 true (2)
theorem kid05_part1209_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part1209) = true := by rfl

def kid05_part1210 : Audit := .cycle 3 7 true (1)
theorem kid05_part1210_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part1210) = true := by rfl

def kid05_part1211 : Audit := .split 10 (4,false) (byMove [
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
.cycle 31 1 false (3),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.last 14 (1,true),
.last 20 (1,true),
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
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 20, 32, 64],64⟩,
.cycle 2 21 true (1),
.last 22 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 4, 32, 64],64⟩,
.cycle 0 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 16, 32, 64],64⟩,
.cycle 8 14 true (2),
.last 23 (1,true),
.cycle 7 21 true (2),
.cycle 2 23 true (1),
.cycle 4 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 20, 32, 64],64⟩,
.cycle 20 2 true (4),
.cycle 2 21 true (1),
.last 22 (1,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.cycle 8 14 true (2)
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
.cycle 21 13 true (3),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 8, 16, 64],[4, 64, 24, 1, 16, 32, 64],64⟩,
.cycle 8 26 true (2),
.last 21 (1,true),
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
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 3 10 true (1),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 6 7 true (2),
.last 19 (4,true),
.last 16 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
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
.split 12 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 21 1 false (1),
.cycle 2 13 true (1),
.cycle 26 1 false (6),
.cycle 8 6 true (2),
.last 14 (1,true),
.last 30 (1,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 13 3 true (3),
.cycle 8 6 true (2)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 36, 16, 64],[4, 64, 52, 1, 4, 32, 64],64⟩,
.cycle 11 9 true (2),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 8 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part1211_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part1211) = true := by rfl

def kid05_part1212 : Audit := .cycle 9 1 true (3)
theorem kid05_part1212_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part1212) = true := by rfl

def kid05_part1213 : Audit := .cycle 6 4 true (2)
theorem kid05_part1213_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part1213) = true := by rfl

def kid05_part1214 : Audit := .split 10 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 16 true (0),
.split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.cycle 12 11 false (0),
.cycle 21 1 false (-3),
.last 19 (4,true),
.last 12 (4,true),
.cycle 12 7 false (1),
.last 14 (4,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.last 18 (4,true),
.last 20 (4,true),
.cycle 12 6 false (0),
.last 24 (4,true),
.cycle 0 16 true (0),
.last 12 (4,true),
.last 16 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 11 6 false (1),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 47 1 false (9),
.cycle 35 1 false (7),
.last 12 (4,false),
.cycle 7 7 true (2),
.last 14 (4,false),
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
.cycle 8 3 true (2),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 32 (4,true),
.last 19 (4,true),
.cycle 21 1 false (-3),
.last 15 (4,true),
.last 12 (4,true),
.cycle 12 7 false (1),
.cycle 6 6 true (1),
.cycle 10 2 true (1),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 12 6 false (0),
.cycle 15 8 true (-4),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.last 13 (4,true),
.last 16 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 16 (4,true)
]),
.cycle 11 6 false (1),
.cycle 2 10 true (1),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 13 (4,false),
.cycle 13 8 false (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 7 7 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 8 3 true (2)
])
theorem kid05_part1214_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part1214) = true := by rfl

def kid05_part1215 : Audit := .split 17 (1,true) (byMove [
.cycle 0 36 true (-2),
.cycle 11 16 true (-2),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.split 18 (4,true) (byMove [
.cycle 0 19 false (3),
.cycle 11 16 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.cycle 0 22 true (-2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 0 28 true (-2),
.cycle 16 3 false (1),
.cycle 11 11 false (1),
.cycle 0 43 true (-2),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 0 44 true (-2),
.far true 1 ⟨0,[0, 0],[44, 44, 8, 8, 64, 4, 64],[44, 16, 32, 12, 44, 32, 64],80⟩,
.cycle 0 22 true (-2),
.cycle 0 36 true (-2),
.cycle 0 24 true (-2),
.last 19 (4,false),
.cycle 11 8 true (-2)
]),
.cycle 11 8 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 1, 15, 1, 64, 32, 64],80⟩,
.cycle 7 12 true (-2),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.split 18 (4,false) (byMove [
.last 36 (4,true),
.cycle 0 22 true (-2),
.last 33 (4,true),
.cycle 0 24 true (-2),
.last 20 (4,true),
.cycle 11 8 true (-2),
.cycle 0 35 true (-2),
.cycle 19 16 true (3),
.cycle 0 23 true (-2),
.cycle 0 20 true (-2),
.last 19 (4,true),
.cycle 0 31 true (-2),
.last 21 (4,true),
.last 32 (4,true),
.cycle 0 39 true (-2),
.last 31 (4,true),
.last 20 (4,true),
.last 26 (4,true),
.cycle 0 42 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073741840, 128, 1, 8192, 16384, 8, 256, 8192, 16, 33554432, 67108864, 2097152, 256, 33554432, 1073741824, 8192, 16384, 8, 16, 8192, 1, 33554432, 67108864, 134217728, 1595949465, 33554432, 1595949465, 1073741824],[256, 16, 128, 1, 1073741824, 2048, 16384, 16, 16, 1, 1073741824, 131072, 67108864, 4194304, 1073741824, 262144, 1073741824, 536870912, 16384, 16, 1073741824, 1, 1073741824, 131072, 67108864, 268435456, 1595949465, 16777216, 1073741824, 536870912, 1073741824],2136454990⟩,
.cycle 7 12 true (-2),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719546624, 512, 1, 524288, 1048576, 32768, 256, 2097152, 69632, 128, 256, 8, 69632, 512, 1, 2147483648, 4294967296, 134217728, 256, 8589934592, 68719476992, 2147483648, 4294967296, 8589934592, 69632, 8589934592, 1073741824, 2147483648, 4294967296, 8589934592, 102140842881, 8589934592, 102140842881, 68719476736],[256, 16, 128, 1, 68719476736, 2048, 1048576, 65536, 69632, 4096, 68719476736, 8388608, 256, 16, 640, 1, 68719476736, 2048, 4294967296, 268435456, 68719476992, 16777216, 68719476736, 34359738368, 4294967296, 17179869184, 68719509504, 1073741824, 68719476736, 34359738368, 4294967296, 17179869184, 102140842881, 1073741824, 68719476736, 34359738368, 68719476736],137301344332⟩,
.last 19 (4,true),
.proven (BB6.Agent11Raw39B1RCPumps.M381.table) (fun m hm => BB6.Agent11Raw39B1RCPumps.M381.never m hm)
]),
.cycle 0 39 true (-2),
.cycle 11 10 true (-2),
.cycle 11 11 false (1),
.cycle 12 6 true (-2),
.cycle 0 22 true (-2),
.split 18 (4,true) (byMove [
.cycle 11 15 false (1),
.cycle 0 28 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 13 6 true (-2),
.cycle 0 22 true (-2),
.last 20 (4,false),
.cycle 0 49 true (-2),
.cycle 0 24 true (-2),
.last 20 (4,false),
.cycle 19 13 true (-1),
.cycle 16 3 false (1),
.cycle 11 11 false (1),
.cycle 0 24 true (-2),
.cycle 19 1 false (-1),
.last 19 (4,false),
.cycle 11 14 true (-2),
.cycle 0 22 true (-2),
.cycle 17 2 true (0),
.cycle 11 10 true (-2),
.far true 1 ⟨0,[0, 0],[44, 44, 8, 8, 64, 4, 64],[44, 16, 32, 12, 44, 32, 64],80⟩,
.last 20 (4,false),
.far true 1 ⟨0,[0, 0],[44, 44, 8, 8, 64, 4, 64],[44, 16, 32, 12, 32, 32, 64],80⟩
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 47, 64, 47, 64],[4, 47, 47, 1, 64, 32, 64],80⟩,
.cycle 35 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[4, 2, 15, 1, 64, 32, 64],80⟩,
.cycle 0 20 true (-2),
.cycle 4 14 true (-2),
.split 18 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 17 2 true (1),
.cycle 11 10 true (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 0, 2, 4, 4],[128, 256, 8, 1073807360, 1073741960, 1, 8192, 16384, 8, 256, 128, 65536, 33554432, 67108864, 2097152, 256, 128, 1073741824, 8192, 16384, 8, 65536, 8, 1, 33554432, 67108864, 134217728, 1596023177, 1596023177, 1596023177, 1073741824],[256, 1024, 128, 1, 1073741824, 2048, 16384, 65536, 65536, 1, 1073741824, 131072, 67108864, 268435456, 1073741824, 262144, 1073741824, 536870912, 16384, 65536, 1073741824, 1, 1073741824, 131072, 67108864, 268435456, 1596023177, 16777216, 1073741824, 536870912, 1073741824],2136388446⟩,
.last 19 (4,true),
.last 30 (4,true),
.last 58 (4,true),
.cycle 19 16 true (3),
.last 30 (4,true),
.cycle 0 20 true (-2),
.last 19 (4,true),
.last 32 (4,true),
.last 32 (4,true),
.last 20 (4,true),
.last 28 (4,true),
.cycle 5 14 true (-2),
.last 19 (4,true),
.last 38 (4,true),
.last 42 (4,true),
.last 50 (4,true),
.last 34 (4,true),
.last 46 (4,true),
.last 19 (4,true),
.last 36 (4,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 47, 64, 47, 64],[4, 32, 47, 1, 64, 32, 64],80⟩
])
theorem kid05_part1215_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part1215) = true := by rfl

def kid05_part1216 : Audit := .cycle 2 10 true (1)
theorem kid05_part1216_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part1216) = true := by rfl

def kid05_part1218 : Audit := .cycle 0 20 true (0)
theorem kid05_part1218_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1218) = true := by rfl

def kid05_part1219 : Audit := .cycle 0 14 true (0)
theorem kid05_part1219_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1219) = true := by rfl

def kid05_part1220 : Audit := .cycle 21 1 false (1)
theorem kid05_part1220_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1220) = true := by rfl

def kid05_part1221 : Audit := .cycle 0 16 true (0)
theorem kid05_part1221_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1221) = true := by rfl

def kid05_part1222 : Audit := .split 11 (4,false) (byMove [
.cycle 0 42 true (-1),
.last 12 (1,true),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.last 13 (1,true),
.cycle 7 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.last 19 (1,true),
.last 12 (1,true),
.last 21 (1,true),
.cycle 0 16 true (0),
.cycle 13 1 false (-1),
.cycle 17 2 false (-1),
.last 13 (1,true),
.cycle 1 19 false (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 14 3 false (0)
])
theorem kid05_part1222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1222) = true := by rfl

def kid05_part1223 : Audit := .split 14 (4,false) (byMove [
.cycle 11 11 false (1),
.last 19 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 19 (1,true),
.last 15 (1,true),
.cycle 13 3 false (-1),
.last 17 (1,true),
.cycle 12 3 false (0),
.cycle 11 5 false (1),
.last 16 (1,true),
.cycle 11 7 false (1),
.last 21 (1,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 19 (1,true),
.last 15 (1,true),
.cycle 11 6 false (1),
.last 17 (1,true),
.cycle 11 6 false (1),
.cycle 11 8 false (1)
])
theorem kid05_part1223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1223) = true := by rfl

def kid05_part1224 : Audit := .cycle 2 10 true (1)
theorem kid05_part1224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1224) = true := by rfl

def kid05_part1225 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,false),
.cycle 35 1 false (7),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 8 true (2),
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
theorem kid05_part1225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1225) = true := by rfl

def kid05_part1226 : Audit := .split 13 (4,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 18 1 false (-2),
.last 16 (1,true),
.cycle 0 17 true (0),
.cycle 18 2 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 47 1 false (7),
.cycle 8 6 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 20 15 true (0),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.cycle 26 2 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 19 7 false (1),
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.cycle 18 9 false (2)
])
theorem kid05_part1226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1226) = true := by rfl

def kid05_part1227 : Audit := .cycle 0 12 true (0)
theorem kid05_part1227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1227) = true := by rfl

def kid05_part1228 : Audit := .split 12 (4,false) (byMove [
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
.cycle 8 7 true (2),
.last 14 (1,true),
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
theorem kid05_part1228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1228) = true := by rfl

def kid05_part1229 : Audit := .cycle 8 3 true (2)
theorem kid05_part1229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1229) = true := by rfl

def kid05_part1230 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 13 13 false (1),
.last 21 (4,false),
.cycle 0 17 true (0),
.cycle 18 3 false (0),
.cycle 18 5 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 19 5 false (1),
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 13 8 false (1),
.last 21 (4,false),
.cycle 5 8 true (1),
.cycle 18 3 false (0),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 64, 16, 64],[1, 32, 32, 1, 1, 1, 64],112⟩,
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 18 11 false (2),
.cycle 0 14 true (0),
.cycle 18 13 false (2),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 64, 16, 64],[1, 1, 32, 1, 1, 1, 64],112⟩
])
theorem kid05_part1230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1230) = true := by rfl

def kid05_part1231 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (2),
.cycle 7 19 false (3),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 18 5 false (2),
.cycle 26 5 false (6),
.last 19 (4,false),
.cycle 19 5 false (3),
.cycle 17 5 false (1),
.cycle 18 5 true (2),
.cycle 20 5 false (0),
.cycle 17 5 false (0),
.cycle 20 5 false (2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.last 18 (4,false),
.cycle 12 6 true (0),
.cycle 1 19 true (0),
.cycle 17 5 false (1),
.cycle 5 12 true (0),
.cycle 15 2 true (0),
.cycle 18 5 true (2)
])
theorem kid05_part1231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1231) = true := by rfl

def kid05_part1232 : Audit := .cycle 2 12 true (1)
theorem kid05_part1232_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1232) = true := by rfl

def kid05_part1233 : Audit := .cycle 18 1 false (0)
theorem kid05_part1233_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1233) = true := by rfl

def kid05_part1234 : Audit := .split 11 (4,false) (byMove [
.cycle 49 8 false (1),
.last 12 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 6 6 true (1),
.last 12 (1,true),
.cycle 15 3 false (0),
.cycle 2 12 true (1),
.cycle 10 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩,
.last 19 (1,true),
.last 12 (1,true),
.cycle 18 8 true (0),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 2 false (-1),
.cycle 17 7 false (1),
.last 12 (1,true),
.cycle 16 5 false (0),
.cycle 2 12 true (1),
.cycle 13 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 36, 32, 32, 64],[4, 64, 32, 1, 32, 32, 64],64⟩
])
theorem kid05_part1234_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1234) = true := by rfl

def kid05_part1235 : Audit := .split 14 (4,false) (byMove [
.cycle 25 5 true (1),
.last 25 (1,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.last 15 (1,true),
.cycle 13 3 false (-1),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 17 5 true (1),
.last 16 (1,true),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 23 5 true (1),
.last 15 (1,true),
.cycle 11 6 false (1),
.cycle 5 10 false (3),
.cycle 19 5 true (1),
.cycle 17 5 true (1)
])
theorem kid05_part1235_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1235) = true := by rfl

def kid05_part1236 : Audit := .cycle 2 10 true (1)
theorem kid05_part1236_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1236) = true := by rfl

def kid05_part1237 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.cycle 19 7 false (1),
.last 18 (4,false),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid05_part1237_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1237) = true := by rfl

def kid05_part1238 : Audit := .cycle 7 4 true (2)
theorem kid05_part1238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1238) = true := by rfl

def kid05_part1239 : Audit := .cycle 0 12 true (0)
theorem kid05_part1239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1239) = true := by rfl

def kid05_part1240 : Audit := .split 12 (4,false) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 13 true (2),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 7 true (2),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 10 7 true (2),
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
theorem kid05_part1240_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1240) = true := by rfl

def kid05_part1241 : Audit := .cycle 8 3 true (2)
theorem kid05_part1241_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1241) = true := by rfl

def kid05_part1217 : Audit := .split 10 (4,true) (byMove [(kid05_part1218),(kid05_part1219),(kid05_part1220),(kid05_part1221),(kid05_part1222),(kid05_part1223),(kid05_part1224),(kid05_part1225),(kid05_part1226),(kid05_part1227),(kid05_part1228),(kid05_part1229),(kid05_part1230),(kid05_part1231),(kid05_part1232),(kid05_part1233),(kid05_part1234),(kid05_part1235),(kid05_part1236),(kid05_part1237),(kid05_part1238),(kid05_part1239),(kid05_part1240),(kid05_part1241)])

theorem kid05_part1217_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part1217) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1218),(kid05_part1219),(kid05_part1220),(kid05_part1221),(kid05_part1222),(kid05_part1223),(kid05_part1224),(kid05_part1225),(kid05_part1226),(kid05_part1227),(kid05_part1228),(kid05_part1229),(kid05_part1230),(kid05_part1231),(kid05_part1232),(kid05_part1233),(kid05_part1234),(kid05_part1235),(kid05_part1236),(kid05_part1237),(kid05_part1238),(kid05_part1239),(kid05_part1240),(kid05_part1241)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1218_checked

  · exact kid05_part1224_checked

  · exact kid05_part1230_checked

  · exact kid05_part1236_checked

  · exact kid05_part1219_checked

  · exact kid05_part1225_checked

  · exact kid05_part1231_checked

  · exact kid05_part1237_checked

  · exact kid05_part1220_checked

  · exact kid05_part1226_checked

  · exact kid05_part1232_checked

  · exact kid05_part1238_checked

  · exact kid05_part1221_checked

  · exact kid05_part1227_checked

  · exact kid05_part1233_checked

  · exact kid05_part1239_checked

  · exact kid05_part1222_checked

  · exact kid05_part1228_checked

  · exact kid05_part1234_checked

  · exact kid05_part1240_checked

  · exact kid05_part1223_checked

  · exact kid05_part1229_checked

  · exact kid05_part1235_checked

  · exact kid05_part1241_checked

def kid05_part1242 : Audit := .cycle 8 3 true (2)
theorem kid05_part1242_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1242) = true := by rfl

def kid05_part1243 : Audit := .cycle 0 10 true (0)
theorem kid05_part1243_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1243) = true := by rfl

def kid05_part1244 : Audit := .cycle 1 9 true (1)
theorem kid05_part1244_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1244) = true := by rfl

def kid05_part1245 : Audit := .cycle 2 8 true (1)
theorem kid05_part1245_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1245) = true := by rfl

def kid05_part1246 : Audit := .cycle 2 11 true (1)
theorem kid05_part1246_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1246) = true := by rfl

def kid05_part1247 : Audit := .split 10 (4,false) (byMove [
.cycle 2 10 true (1),
.split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.last 17 (4,true),
.cycle 15 8 true (-2),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 7 4 true (2),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 15 1 false (-1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 11 10 true (2),
.cycle 3 9 true (1),
.cycle 19 1 false (1),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.last 23 (1,true),
.cycle 2 12 true (1),
.cycle 15 1 false (-1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 20, 1, 16, 32, 64],64⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 17 4 true (4),
.cycle 2 21 true (1),
.cycle 9 22 true (3),
.cycle 8 14 true (2),
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
.split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 22 (4,true),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.last 12 (4,true),
.last 14 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.last 16 (4,true),
.last 17 (4,true),
.last 26 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.split 14 (4,true) (byMove [
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 17 3 false (1),
.cycle 8 7 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.cycle 0 18 true (0),
.cycle 8 16 true (2),
.cycle 6 9 true (2),
.last 15 (1,true),
.cycle 11 4 true (2),
.cycle 2 15 true (1),
.cycle 17 3 false (1),
.cycle 8 8 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 10 5 true (2),
.cycle 9 6 true (2)
]),
.cycle 2 11 true (1),
.split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 8 7 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.cycle 8 4 true (2),
.cycle 6 11 true (2),
.last 12 (1,true),
.cycle 23 4 true (0),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.cycle 8 6 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 8 4 true (2)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part1247_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1247) = true := by rfl

def kid05_part1248 : Audit := .cycle 9 1 true (3)
theorem kid05_part1248_checked : zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1248) = true := by rfl

def kid05_part1176 : Audit := .split 9 (5,false) (byMove [(kid05_part1177),(kid05_part1178),(kid05_part1179),(kid05_part1180),(kid05_part1181),(kid05_part1206),(kid05_part1207),(kid05_part1208),(kid05_part1209),(kid05_part1210),(kid05_part1211),(kid05_part1212),(kid05_part1213),(kid05_part1214),(kid05_part1215),(kid05_part1216),(kid05_part1217),(kid05_part1242),(kid05_part1243),(kid05_part1244),(kid05_part1245),(kid05_part1246),(kid05_part1247),(kid05_part1248)])

theorem kid05_part1176_checked : zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (kid05_part1176) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part1177),(kid05_part1178),(kid05_part1179),(kid05_part1180),(kid05_part1181),(kid05_part1206),(kid05_part1207),(kid05_part1208),(kid05_part1209),(kid05_part1210),(kid05_part1211),(kid05_part1212),(kid05_part1213),(kid05_part1214),(kid05_part1215),(kid05_part1216),(kid05_part1217),(kid05_part1242),(kid05_part1243),(kid05_part1244),(kid05_part1245),(kid05_part1246),(kid05_part1247),(kid05_part1248)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1177_checked

  · exact kid05_part1207_checked

  · exact kid05_part1213_checked

  · exact kid05_part1243_checked

  · exact kid05_part1178_checked

  · exact kid05_part1208_checked

  · exact kid05_part1214_checked

  · exact kid05_part1244_checked

  · exact kid05_part1179_checked

  · exact kid05_part1209_checked

  · exact kid05_part1215_checked

  · exact kid05_part1245_checked

  · exact kid05_part1180_checked

  · exact kid05_part1210_checked

  · exact kid05_part1216_checked

  · exact kid05_part1246_checked

  · exact kid05_part1181_checked

  · exact kid05_part1211_checked

  · exact kid05_part1217_checked

  · exact kid05_part1247_checked

  · exact kid05_part1206_checked

  · exact kid05_part1212_checked

  · exact kid05_part1242_checked

  · exact kid05_part1248_checked

def kid05 : Audit := .split 8 (5,true) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part5),(kid05_part174),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part250),(kid05_part251),(kid05_part348),(kid05_part445),(kid05_part542),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part930),(kid05_part1051),(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1176)])

theorem check05 : zipCheck 1882 (child ⟨false,false,5⟩) (kid05) = true := by

  change (zipQueryOK 1882 (child ⟨false,false,5⟩) 8 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (child ⟨false,false,5⟩) (5,true) (some mv)) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part5),(kid05_part174),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part250),(kid05_part251),(kid05_part348),(kid05_part445),(kid05_part542),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part930),(kid05_part1051),(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1176)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1_checked

  · exact kid05_part247_checked

  · exact kid05_part445_checked

  · exact kid05_part1051_checked

  · exact kid05_part2_checked

  · exact kid05_part248_checked

  · exact kid05_part542_checked

  · exact kid05_part1052_checked

  · exact kid05_part3_checked

  · exact kid05_part249_checked

  · exact kid05_part663_checked

  · exact kid05_part1053_checked

  · exact kid05_part4_checked

  · exact kid05_part250_checked

  · exact kid05_part664_checked

  · exact kid05_part1054_checked

  · exact kid05_part5_checked

  · exact kid05_part251_checked

  · exact kid05_part665_checked

  · exact kid05_part1055_checked

  · exact kid05_part174_checked

  · exact kid05_part348_checked

  · exact kid05_part930_checked

  · exact kid05_part1176_checked

end BB6.Agent11Raw39B1RC
