import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid10_part1 : Audit := .cycle 0 9 true (0)
theorem kid10_part1_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid10_part1) = true := by rfl

def kid10_part2 : Audit := .cycle 1 8 true (1)
theorem kid10_part2_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid10_part2) = true := by rfl

def kid10_part3 : Audit := .cycle 2 7 true (1)
theorem kid10_part3_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid10_part3) = true := by rfl

def kid10_part4 : Audit := .cycle 2 10 true (1)
theorem kid10_part4_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid10_part4) = true := by rfl

def kid10_part6 : Audit := .cycle 0 11 true (0)
theorem kid10_part6_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part6) = true := by rfl

def kid10_part7 : Audit := .cycle 1 10 true (1)
theorem kid10_part7_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part7) = true := by rfl

def kid10_part8 : Audit := .cycle 21 1 false (1)
theorem kid10_part8_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part8) = true := by rfl

def kid10_part9 : Audit := .cycle 23 1 false (1)
theorem kid10_part9_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part9) = true := by rfl

def kid10_part10 : Audit := .cycle 13 1 false (-1)
theorem kid10_part10_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part10) = true := by rfl

def kid10_part11 : Audit := .split 11 (5,false) (byMove [
.cycle 0 23 false (4),
.split 12 (1,true) (byMove [
.cycle 0 13 false (4),
.cycle 13 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (1),
.cycle 0 13 true (0),
.cycle 13 11 false (4),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 11 false (3),
.cycle 15 11 false (1),
.cycle 14 11 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (3),
.cycle 16 11 false (4),
.cycle 13 11 false (1),
.cycle 11 2 true (0)
]),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 18 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (1),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.split 19 (1,true) (byMove [
.cycle 12 13 false (2),
.cycle 12 14 false (2),
.cycle 21 1 false (-1),
.cycle 0 21 false (4),
.cycle 16 4 false (0),
.last 20 (5,true),
.cycle 6 26 false (4),
.cycle 12 13 true (-2),
.cycle 10 17 false (2),
.cycle 12 11 false (2),
.cycle 14 6 false (2),
.cycle 17 3 true (-2),
.cycle 12 8 false (2),
.cycle 10 13 false (2),
.cycle 16 5 false (0),
.cycle 12 14 true (-2),
.cycle 16 4 false (0),
.last 20 (5,true),
.last 37 (5,true),
.last 36 (5,true),
.cycle 2 18 false (4),
.cycle 12 15 true (-2),
.last 22 (5,true),
.last 26 (5,true)
]),
.split 12 (1,true) (byMove [
.last 19 (5,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 6 false (0),
.cycle 19 6 false (4),
.cycle 20 6 false (5),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 10 7 false (2),
.cycle 10 5 false (2),
.cycle 21 6 false (4),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (2),
.cycle 2 12 true (0),
.cycle 1 13 true (0),
.cycle 13 6 false (2),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 0 17 true (-1),
.cycle 24 1 false (0),
.cycle 14 1 false (-2),
.split 12 (5,true) (byMove [
.cycle 0 20 false (4),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 23 1 false (1),
.last 13 (1,true),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 25 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 2 12 true (0),
.last 13 (1,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.cycle 11 3 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 23 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 23 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.last 16 (1,true),
.cycle 18 3 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 22 3 false (2),
.cycle 25 3 false (3),
.cycle 15 3 false (1),
.cycle 11 4 true (0)
]),
.cycle 11 1 true (1)
])
theorem kid10_part11_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part11) = true := by rfl

def kid10_part12 : Audit := .cycle 0 11 true (0)
theorem kid10_part12_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part12) = true := by rfl

def kid10_part13 : Audit := .cycle 1 10 true (1)
theorem kid10_part13_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part13) = true := by rfl

def kid10_part14 : Audit := .cycle 27 1 false (3)
theorem kid10_part14_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part14) = true := by rfl

def kid10_part15 : Audit := .cycle 10 7 true (0)
theorem kid10_part15_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part15) = true := by rfl

def kid10_part16 : Audit := .cycle 15 1 false (1)
theorem kid10_part16_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part16) = true := by rfl

def kid10_part17 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 25 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 25 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 20 1 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 1 false (2),
.cycle 27 1 false (3),
.cycle 17 1 false (1),
.cycle 13 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 22 (5,true) (byMove [
.cycle 0 40 true (0),
.cycle 0 26 true (0),
.cycle 10 29 true (0),
.cycle 0 34 true (0),
.cycle 28 1 false (4),
.cycle 0 26 true (0),
.cycle 0 52 true (0),
.last 23 (1,true),
.cycle 32 1 false (4),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 60, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 60, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 24 (1,true),
.cycle 10 15 true (0),
.cycle 0 58 true (0),
.cycle 10 25 true (0),
.cycle 41 1 false (9),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 60, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 22 true (0),
.last 23 (1,true),
.cycle 10 31 true (0),
.cycle 0 24 true (0),
.cycle 9 43 true (0),
.cycle 10 22 true (0)
]),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (3),
.cycle 10 18 true (0),
.cycle 0 21 true (0),
.last 44 (1,true),
.cycle 40 1 false (4),
.cycle 12 9 true (0),
.cycle 27 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 60, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 22 (1,true),
.cycle 7 15 true (0),
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 10 33 true (0),
.cycle 5 41 true (0),
.cycle 10 32 true (0),
.cycle 3 42 true (0)
]),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 11 3 true (2),
.cycle 6 8 true (2),
.cycle 10 7 true (1),
.cycle 10 5 true (2),
.cycle 2 14 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 9 5 true (2),
.cycle 6 9 true (2)
]),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.split 14 (5,true) (byMove [
.cycle 0 20 true (-1),
.cycle 10 23 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.last 15 (1,true),
.cycle 19 1 false (5),
.cycle 21 1 false (3),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.last 16 (1,true),
.cycle 10 11 true (-1),
.cycle 10 9 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.last 15 (1,true),
.cycle 10 27 true (0),
.cycle 5 10 true (0),
.cycle 9 14 true (0),
.cycle 16 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid10_part17_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part17) = true := by rfl

def kid10_part18 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (2),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.split 13 (5,true) (byMove [
.cycle 0 27 false (4),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.last 14 (5,false),
.cycle 19 3 false (0),
.last 15 (5,false),
.cycle 0 21 true (-1),
.cycle 28 1 false (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 19 5 false (1),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 18 5 false (2),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 19 5 false (1),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.cycle 10 10 true (1),
.cycle 20 7 false (2),
.cycle 13 1 true (3),
.cycle 11 3 true (1),
.cycle 20 13 false (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 19 5 false (1),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 9 5 true (1),
.cycle 13 1 true (3)
]),
.cycle 18 7 false (2),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 13 true (1),
.cycle 10 6 true (0),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.last 15 (5,false),
.cycle 10 6 true (0),
.last 15 (5,false),
.cycle 20 15 true (-1),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 12 2 true (1),
.cycle 19 7 false (2),
.cycle 0 15 true (0),
.cycle 19 9 false (2),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 18 9 false (2),
.split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.cycle 12 2 true (2),
.cycle 19 7 false (2),
.cycle 0 15 true (0),
.cycle 19 9 false (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (1),
.cycle 3 11 true (1),
.cycle 19 11 false (3),
.cycle 13 1 true (3),
.cycle 19 13 false (3),
.last 15 (5,true),
.cycle 10 5 true (1),
.cycle 2 14 true (1),
.cycle 10 7 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 19 15 false (3),
.cycle 13 1 true (3)
])
])
theorem kid10_part18_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part18) = true := by rfl

def kid10_part19 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (3),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.split 17 (5,false) (byMove [
.cycle 0 22 true (-2),
.cycle 10 15 false (3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 18 5 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 19 (5,true),
.last 20 (5,true),
.cycle 18 5 false (0),
.last 22 (5,true),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 11 7 false (3),
.cycle 0 20 true (-1),
.cycle 21 5 false (2),
.cycle 18 5 false (0),
.last 19 (5,true)
]),
.cycle 23 5 false (4),
.cycle 24 5 false (5),
.cycle 18 1 false (2),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 24 5 false (3),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 24 5 false (5),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.last 18 (5,false),
.last 20 (5,false),
.cycle 18 5 false (2),
.cycle 0 20 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 23 5 false (4),
.cycle 26 5 false (5),
.cycle 18 5 false (2),
.last 18 (5,false)
]),
.cycle 10 11 false (3),
.cycle 10 9 false (3),
.cycle 25 5 false (4),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.split 17 (5,false) (byMove [
.last 28 (5,true),
.cycle 7 30 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 19 5 false (2),
.cycle 16 2 true (-1),
.cycle 19 5 false (2),
.cycle 25 5 false (4),
.cycle 10 11 false (3),
.last 18 (5,true),
.last 20 (5,true),
.last 30 (5,true),
.cycle 21 5 false (2),
.cycle 18 1 false (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 12 7 false (3),
.last 19 (5,true),
.cycle 10 9 false (3),
.cycle 7 23 false (4),
.cycle 15 3 false (1),
.last 18 (5,true)
]),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.split 17 (5,true) (byMove [
.cycle 24 5 false (3),
.last 19 (5,false),
.cycle 19 1 false (1),
.cycle 0 19 true (0),
.cycle 18 5 false (1),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 7 22 true (0),
.cycle 10 15 true (0),
.cycle 22 5 false (3),
.cycle 18 5 false (2),
.last 18 (5,false),
.cycle 19 5 false (2),
.cycle 16 2 true (0),
.cycle 19 5 false (2),
.cycle 25 5 false (4),
.cycle 10 11 false (3),
.last 19 (5,false),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 7 24 true (0),
.cycle 14 4 true (0),
.last 18 (5,false)
])
])
theorem kid10_part19_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part19) = true := by rfl

def kid10_part20 : Audit := .cycle 0 13 true (0)
theorem kid10_part20_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part20) = true := by rfl

def kid10_part21 : Audit := .cycle 18 1 false (0)
theorem kid10_part21_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part21) = true := by rfl

def kid10_part22 : Audit := .cycle 13 1 false (-1)
theorem kid10_part22_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part22) = true := by rfl

def kid10_part24 : Audit := .cycle 0 15 true (0)
theorem kid10_part24_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part24) = true := by rfl

def kid10_part25 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 34 (5,true),
.cycle 0 15 true (0),
.cycle 0 22 true (-1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 0 17 true (0),
.last 30 (5,true),
.last 28 (5,true),
.cycle 0 23 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 19 (5,true),
.cycle 0 15 true (0),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 0 24 true (-1),
.last 23 (5,true),
.cycle 11 2 true (0)
])
theorem kid10_part25_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part25) = true := by rfl

def kid10_part26 : Audit := .cycle 13 1 false (1)
theorem kid10_part26_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part26) = true := by rfl

def kid10_part27 : Audit := .split 14 (1,true) (byMove [
.cycle 26 1 false (0),
.cycle 27 1 false (-1),
.cycle 16 1 false (2),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.cycle 10 12 true (0),
.cycle 24 1 false (0),
.cycle 19 1 false (-1),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 10 8 true (0),
.cycle 18 1 false (0),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 0 33 true (0),
.last 17 (5,true),
.cycle 0 17 true (0)
])
theorem kid10_part27_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part27) = true := by rfl

def kid10_part28 : Audit := .cycle 14 1 false (-2)
theorem kid10_part28_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part28) = true := by rfl

def kid10_part29 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 18 1 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part29_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part29) = true := by rfl

def kid10_part30 : Audit := .cycle 2 11 true (1)
theorem kid10_part30_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part30) = true := by rfl

def kid10_part31 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 1 13 true (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.cycle 1 13 true (1)
])
theorem kid10_part31_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part31) = true := by rfl

def kid10_part32 : Audit := .cycle 19 1 false (1)
theorem kid10_part32_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part32) = true := by rfl

def kid10_part33 : Audit := .cycle 0 13 true (0)
theorem kid10_part33_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part33) = true := by rfl

def kid10_part34 : Audit := .cycle 10 2 true (1)
theorem kid10_part34_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part34) = true := by rfl

def kid10_part35 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 13 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 13 1 true (3),
.last 14 (1,true),
.cycle 10 11 false (3),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (1),
.cycle 13 1 true (3)
])
theorem kid10_part35_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part35) = true := by rfl

def kid10_part36 : Audit := .cycle 10 4 true (0)
theorem kid10_part36_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part36) = true := by rfl

def kid10_part37 : Audit := .split 12 (1,true) (byMove [
.cycle 10 25 true (-1),
.cycle 10 19 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 12 false (2),
.cycle 10 11 false (3),
.cycle 10 18 true (0),
.cycle 10 8 true (0),
.cycle 10 17 true (0),
.cycle 10 7 false (2),
.last 13 (5,true),
.cycle 10 7 false (2),
.cycle 10 5 false (2),
.cycle 10 13 false (3),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (2),
.last 18 (5,true),
.cycle 1 14 true (0),
.cycle 10 4 true (0),
.cycle 10 17 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part37_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part37) = true := by rfl

def kid10_part38 : Audit := .cycle 16 13 true (-1)
theorem kid10_part38_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part38) = true := by rfl

def kid10_part39 : Audit := .cycle 19 1 false (-1)
theorem kid10_part39_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part39) = true := by rfl

def kid10_part40 : Audit := .cycle 14 1 false (-2)
theorem kid10_part40_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part40) = true := by rfl

def kid10_part41 : Audit := .split 12 (5,true) (byMove [
.cycle 10 37 true (-2),
.cycle 10 25 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 13 (1,true),
.cycle 15 1 false (1),
.cycle 24 1 false (2),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 2 18 true (0),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 5 22 true (0),
.cycle 12 2 true (0),
.cycle 13 3 true (1)
])
theorem kid10_part41_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part41) = true := by rfl

def kid10_part42 : Audit := .cycle 2 11 true (1)
theorem kid10_part42_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part42) = true := by rfl

def kid10_part43 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (2),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.last 16 (5,true),
.cycle 1 13 true (1),
.last 18 (5,true),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 15 (5,true),
.cycle 1 13 true (1)
])
theorem kid10_part43_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part43) = true := by rfl

def kid10_part44 : Audit := .split 16 (5,true) (byMove [
.cycle 12 7 false (3),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 23 5 false (4),
.last 17 (1,true),
.cycle 18 1 false (2),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.cycle 24 5 false (5),
.last 18 (1,true),
.cycle 10 9 false (3),
.cycle 25 5 false (4),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 9 false (3),
.cycle 2 16 true (0),
.last 17 (1,true),
.cycle 17 5 false (2),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 2 17 true (0)
])
theorem kid10_part44_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part44) = true := by rfl

def kid10_part45 : Audit := .cycle 0 13 true (0)
theorem kid10_part45_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part45) = true := by rfl

def kid10_part46 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 18 1 false (-2),
.cycle 14 6 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.cycle 9 7 true (1),
.cycle 10 6 true (0),
.last 14 (1,true),
.cycle 20 15 true (-1),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 14 3 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 17 7 false (2),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.cycle 12 5 true (1)
])
theorem kid10_part46_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part46) = true := by rfl

def kid10_part47 : Audit := .split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 17 5 false (2),
.cycle 13 1 true (3),
.last 20 (1,true),
.last 13 (1,true),
.cycle 10 4 true (1),
.cycle 2 13 true (1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 14 2 true (1),
.cycle 13 1 true (3)
])
theorem kid10_part47_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part47) = true := by rfl

def kid10_part23 : Audit := .split 11 (5,false) (byMove [(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44),(kid10_part45),(kid10_part46),(kid10_part47)])

theorem kid10_part23_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part23) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44),(kid10_part45),(kid10_part46),(kid10_part47)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part24_checked

  · exact kid10_part30_checked

  · exact kid10_part36_checked

  · exact kid10_part42_checked

  · exact kid10_part25_checked

  · exact kid10_part31_checked

  · exact kid10_part37_checked

  · exact kid10_part43_checked

  · exact kid10_part26_checked

  · exact kid10_part32_checked

  · exact kid10_part38_checked

  · exact kid10_part44_checked

  · exact kid10_part27_checked

  · exact kid10_part33_checked

  · exact kid10_part39_checked

  · exact kid10_part45_checked

  · exact kid10_part28_checked

  · exact kid10_part34_checked

  · exact kid10_part40_checked

  · exact kid10_part46_checked

  · exact kid10_part29_checked

  · exact kid10_part35_checked

  · exact kid10_part41_checked

  · exact kid10_part47_checked

def kid10_part48 : Audit := .cycle 0 11 true (0)
theorem kid10_part48_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part48) = true := by rfl

def kid10_part49 : Audit := .cycle 1 10 true (1)
theorem kid10_part49_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part49) = true := by rfl

def kid10_part50 : Audit := .cycle 2 9 true (1)
theorem kid10_part50_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part50) = true := by rfl

def kid10_part51 : Audit := .cycle 2 12 true (1)
theorem kid10_part51_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part51) = true := by rfl

def kid10_part52 : Audit := .cycle 9 2 true (2)
theorem kid10_part52_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part52) = true := by rfl

def kid10_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 2 11 true (1),
.split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 1 13 true (1),
.cycle 21 9 false (2),
.cycle 10 13 false (3),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
]),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 20 true (0),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.split 12 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 13 8 false (1),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 10 7 true (1),
.cycle 10 5 true (1),
.cycle 2 14 true (1),
.cycle 10 7 true (0),
.cycle 17 1 false (-1),
.last 19 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true)
]),
.cycle 10 3 true (2),
.cycle 2 12 true (1),
.split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 32, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 10 5 true (2),
.cycle 2 14 true (1),
.cycle 12 2 true (2),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 9 5 true (2),
.cycle 11 3 true (2)
]),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.cycle 0 18 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 22 1 false (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 23 1 false (5),
.last 14 (1,true),
.cycle 10 5 true (1),
.cycle 2 14 true (1),
.cycle 10 7 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid10_part53_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part53) = true := by rfl

def kid10_part5 : Audit := .split 10 (4,true) (byMove [(kid10_part6),(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part48),(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53)])

theorem kid10_part5_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid10_part5) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part6),(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part48),(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part6_checked

  · exact kid10_part12_checked

  · exact kid10_part18_checked

  · exact kid10_part48_checked

  · exact kid10_part7_checked

  · exact kid10_part13_checked

  · exact kid10_part19_checked

  · exact kid10_part49_checked

  · exact kid10_part8_checked

  · exact kid10_part14_checked

  · exact kid10_part20_checked

  · exact kid10_part50_checked

  · exact kid10_part9_checked

  · exact kid10_part15_checked

  · exact kid10_part21_checked

  · exact kid10_part51_checked

  · exact kid10_part10_checked

  · exact kid10_part16_checked

  · exact kid10_part22_checked

  · exact kid10_part52_checked

  · exact kid10_part11_checked

  · exact kid10_part17_checked

  · exact kid10_part23_checked

  · exact kid10_part53_checked

def kid10_part55 : Audit := .cycle 2 9 true (1)
theorem kid10_part55_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part55) = true := by rfl

def kid10_part57 : Audit := .cycle 0 11 true (0)
theorem kid10_part57_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part57) = true := by rfl

def kid10_part58 : Audit := .cycle 1 10 true (1)
theorem kid10_part58_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part58) = true := by rfl

def kid10_part59 : Audit := .cycle 21 1 false (1)
theorem kid10_part59_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part59) = true := by rfl

def kid10_part60 : Audit := .cycle 23 1 false (1)
theorem kid10_part60_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part60) = true := by rfl

def kid10_part61 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 13 12 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 12 false (0),
.cycle 13 12 false (1),
.cycle 0 13 true (0),
.cycle 13 12 false (4),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 12 false (2),
.cycle 13 12 false (3),
.last 15 (4,true),
.cycle 14 12 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 22 (4,true),
.cycle 0 17 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 12 false (3),
.cycle 16 12 false (4),
.cycle 11 2 true (0),
.cycle 13 12 false (1)
])
theorem kid10_part61_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part61) = true := by rfl

def kid10_part62 : Audit := .cycle 11 11 false (1)
theorem kid10_part62_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part62) = true := by rfl

def kid10_part63 : Audit := .cycle 0 11 true (0)
theorem kid10_part63_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part63) = true := by rfl

def kid10_part64 : Audit := .cycle 1 10 true (1)
theorem kid10_part64_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part64) = true := by rfl

def kid10_part65 : Audit := .split 19 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 0 25 true (0),
.last 21 (5,true),
.cycle 23 1 false (3),
.cycle 0 44 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 2, 64],[8, 8, 10, 8, 8, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 2, 64],[8, 8, 10, 8, 8, 64, 64],64⟩,
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 2, 64],[8, 8, 10, 8, 10, 64, 64],64⟩,
.last 20 (5,true),
.cycle 1 24 true (0),
.cycle 21 13 true (2),
.cycle 0 50 true (0),
.cycle 33 1 false (5),
.last 21 (5,true),
.cycle 35 1 false (7),
.cycle 2 19 true (0),
.cycle 1 28 true (0),
.cycle 7 13 true (0),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid10_part65_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part65) = true := by rfl

def kid10_part66 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 30 1 false (4),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 0 39 true (0),
.cycle 19 21 true (1),
.cycle 11 7 true (0),
.cycle 1 19 true (0),
.last 37 (5,true),
.cycle 3 17 true (0),
.cycle 31 1 false (3),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 7 28 true (0),
.cycle 0 59 true (0),
.last 19 (5,true),
.cycle 9 9 true (0)
])
theorem kid10_part66_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part66) = true := by rfl

def kid10_part67 : Audit := .cycle 1 12 true (1)
theorem kid10_part67_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part67) = true := by rfl

def kid10_part68 : Audit := .cycle 1 11 true (1)
theorem kid10_part68_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part68) = true := by rfl

def kid10_part69 : Audit := .cycle 17 7 false (2)
theorem kid10_part69_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part69) = true := by rfl

def kid10_part70 : Audit := .split 19 (4,true) (byMove [
.cycle 31 11 false (3),
.cycle 1 19 false (4),
.cycle 25 5 false (2),
.cycle 28 5 false (3),
.last 21 (5,true),
.cycle 20 5 false (0),
.cycle 0 20 true (-1),
.cycle 7 29 false (5),
.cycle 7 36 true (-1),
.cycle 18 7 true (-1),
.cycle 1 21 false (4),
.cycle 7 25 false (4),
.cycle 15 7 false (1),
.cycle 11 9 false (3),
.cycle 0 22 true (-1),
.cycle 23 5 false (2),
.last 21 (5,true),
.cycle 20 5 false (0),
.cycle 2 40 true (-1),
.cycle 1 19 true (-1),
.cycle 7 23 false (4),
.cycle 7 31 false (5),
.last 21 (5,true),
.cycle 9 11 false (3)
])
theorem kid10_part70_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part70) = true := by rfl

def kid10_part71 : Audit := .cycle 0 13 true (0)
theorem kid10_part71_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part71) = true := by rfl

def kid10_part72 : Audit := .cycle 18 1 false (0)
theorem kid10_part72_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part72) = true := by rfl

def kid10_part73 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 34 (4,true),
.last 33 (4,true),
.last 15 (4,true),
.last 27 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 22 (4,true),
.cycle 0 17 true (0),
.last 15 (4,true),
.last 27 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 22 (4,true),
.last 19 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.last 29 (4,true),
.cycle 11 2 true (0),
.last 24 (4,true)
])
theorem kid10_part73_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part73) = true := by rfl

def kid10_part74 : Audit := .split 19 (5,true) (byMove [
.cycle 0 37 true (-2),
.cycle 0 23 true (-2),
.last 27 (4,true),
.cycle 18 19 false (3),
.last 55 (4,true),
.last 28 (4,true),
.cycle 0 34 true (-2),
.cycle 0 25 true (-2),
.cycle 0 37 true (-2),
.cycle 0 21 true (-2),
.last 20 (4,true),
.cycle 0 36 true (-2),
.last 28 (4,true),
.last 22 (4,true),
.cycle 0 36 true (-2),
.last 25 (4,true),
.last 30 (4,true),
.cycle 0 38 true (-2),
.cycle 2 19 true (-2),
.cycle 18 2 true (1),
.cycle 0 28 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 65536, 32768, 128, 256, 32768, 256, 256, 128, 128, 256, 8, 65536, 256, 32768, 262144],[256, 1, 16, 1, 262144, 512, 256, 4096, 65536, 4096, 262144, 512, 256, 4096, 16, 1, 262144, 512, 262144],278540⟩,
.last 20 (4,true),
.cycle 18 4 true (1)
])
theorem kid10_part74_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part74) = true := by rfl

def kid10_part75 : Audit := .cycle 0 11 true (0)
theorem kid10_part75_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part75) = true := by rfl

def kid10_part76 : Audit := .cycle 1 10 true (1)
theorem kid10_part76_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part76) = true := by rfl

def kid10_part77 : Audit := .cycle 2 9 true (1)
theorem kid10_part77_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part77) = true := by rfl

def kid10_part78 : Audit := .cycle 2 12 true (1)
theorem kid10_part78_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part78) = true := by rfl

def kid10_part79 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 14 false (1),
.cycle 13 13 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 1 14 true (1),
.cycle 1 13 true (1),
.cycle 21 11 false (2),
.last 21 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 24 (4,true),
.cycle 0 46 true (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
])
theorem kid10_part79_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part79) = true := by rfl

def kid10_part80 : Audit := .cycle 9 2 true (2)
theorem kid10_part80_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part80) = true := by rfl

def kid10_part56 : Audit := .split 10 (1,true) (byMove [(kid10_part57),(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78),(kid10_part79),(kid10_part80)])

theorem kid10_part56_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part56) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part57),(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78),(kid10_part79),(kid10_part80)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part57_checked

  · exact kid10_part63_checked

  · exact kid10_part69_checked

  · exact kid10_part75_checked

  · exact kid10_part58_checked

  · exact kid10_part64_checked

  · exact kid10_part70_checked

  · exact kid10_part76_checked

  · exact kid10_part59_checked

  · exact kid10_part65_checked

  · exact kid10_part71_checked

  · exact kid10_part77_checked

  · exact kid10_part60_checked

  · exact kid10_part66_checked

  · exact kid10_part72_checked

  · exact kid10_part78_checked

  · exact kid10_part61_checked

  · exact kid10_part67_checked

  · exact kid10_part73_checked

  · exact kid10_part79_checked

  · exact kid10_part62_checked

  · exact kid10_part68_checked

  · exact kid10_part74_checked

  · exact kid10_part80_checked

def kid10_part81 : Audit := .cycle 25 1 false (1)
theorem kid10_part81_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part81) = true := by rfl

def kid10_part82 : Audit := .cycle 0 11 true (0)
theorem kid10_part82_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part82) = true := by rfl

def kid10_part83 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 23 2 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 14 (1,true),
.cycle 18 2 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 2 false (0),
.cycle 25 2 false (1),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
]),
.cycle 13 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 27 1 false (3),
.cycle 10 7 true (0),
.split 14 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 25 2 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 25 2 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 2 false (1),
.cycle 15 2 false (1),
.last 16 (1,true),
.cycle 20 2 false (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 2 false (2),
.cycle 27 2 false (3),
.cycle 13 2 true (0),
.cycle 17 2 false (1)
]),
.cycle 15 2 false (1),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (2),
.cycle 20 2 false (0),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 18 5 false (2),
.last 15 (5,true),
.cycle 18 7 false (2),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 13 true (1),
.cycle 10 6 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 18 9 false (2)
]),
.split 16 (1,true) (byMove [
.cycle 11 7 false (3),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 23 5 false (4),
.cycle 24 5 false (5),
.cycle 18 2 false (2),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.last 17 (5,true),
.cycle 10 11 false (3),
.cycle 10 9 false (3),
.cycle 25 5 false (4),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.last 17 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 18 2 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 14 (1,true),
.cycle 18 2 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 19 2 false (-1),
.cycle 0 15 true (0),
.cycle 20 2 false (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
]),
.cycle 13 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 22 true (0),
.cycle 10 9 true (0),
.cycle 17 2 false (1),
.cycle 19 2 false (1),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid10_part83_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part83) = true := by rfl

def kid10_part84 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 23 1 false (3),
.cycle 0 44 true (0),
.last 20 (1,true),
.cycle 27 1 false (3),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.cycle 40 1 false (4),
.last 21 (1,true),
.cycle 21 13 true (2),
.cycle 0 50 true (0),
.cycle 33 1 false (5),
.cycle 35 1 false (7),
.cycle 35 1 false (7),
.cycle 2 19 true (0),
.last 20 (1,true),
.cycle 7 13 true (0),
.cycle 0 21 true (0),
.cycle 10 22 true (0),
.cycle 9 20 true (0)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 30 1 false (4),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.last 37 (1,true),
.cycle 33 1 false (3),
.cycle 11 7 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.last 19 (1,true),
.cycle 31 1 false (3),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 7 28 true (0),
.cycle 0 59 true (0),
.cycle 10 9 true (0),
.cycle 9 9 true (0)
]),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 13 false (2),
.cycle 21 1 false (-1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 18 5 false (2),
.cycle 19 5 false (1),
.cycle 18 7 false (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 19 9 false (2),
.cycle 18 9 false (2)
]),
.split 16 (1,true) (byMove [
.cycle 11 7 false (3),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 23 5 false (4),
.cycle 24 5 false (5),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 17 5 false (2),
.last 21 (4,true),
.last 19 (4,true),
.cycle 25 5 false (4),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 2 16 true (0),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 15 2 true (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.cycle 9 2 true (2)
])
theorem kid10_part84_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part84) = true := by rfl

def kid10_part85 : Audit := .cycle 0 10 true (0)
theorem kid10_part85_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part85) = true := by rfl

def kid10_part86 : Audit := .cycle 1 9 true (1)
theorem kid10_part86_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part86) = true := by rfl

def kid10_part87 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 34 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 37 1 false (3),
.cycle 53 1 false (9),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 28 1 false (0),
.cycle 0 24 true (0),
.cycle 41 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 18 2 true (3),
.cycle 9 11 true (2)
]),
.cycle 9 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 256, 4096, 4, 4096],[256, 4096, 16, 1, 4, 4096, 256, 4096, 16, 1, 4, 4096, 4096],5120⟩,
.cycle 11 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 256, 4096, 4, 4096],[256, 4096, 16, 1, 16, 4096, 256, 4096, 16, 1, 16, 4096, 4096],5120⟩,
.split 29 (5,true) (byMove [
.cycle 7 25 true (2),
.cycle 0 33 true (0),
.cycle 10 29 true (2),
.cycle 0 39 true (0),
.cycle 8 33 true (2),
.cycle 0 33 true (0),
.cycle 2 29 true (1),
.last 30 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 12, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 31 (1,true),
.cycle 16 15 true (3),
.cycle 2 31 true (1),
.cycle 12 25 true (2),
.cycle 2 33 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 12, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 29 true (1),
.last 30 (1,true),
.cycle 7 23 true (2),
.cycle 0 31 true (0),
.cycle 41 2 true (11),
.cycle 9 22 true (2)
]),
.split 19 (1,true) (byMove [
.cycle 2 19 true (1),
.cycle 1 21 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 6 15 true (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.last 32 (5,true),
.cycle 6 14 true (2),
.cycle 34 7 false (2),
.cycle 16 4 true (4),
.cycle 2 20 true (1),
.cycle 15 6 true (3),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.last 21 (5,true),
.cycle 9 11 true (2)
]),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 34 1 false (2),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.cycle 0 24 true (0),
.cycle 55 1 false (9),
.last 21 (1,true),
.cycle 0 26 true (0),
.last 23 (1,true),
.cycle 28 1 false (0),
.last 25 (1,true),
.cycle 0 26 true (0),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (3),
.cycle 0 42 true (0)
]),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 256, 4096, 4, 4096],[256, 4096, 16, 1, 16, 4096, 256, 4096, 16, 1, 4096, 4096, 4096],5120⟩,
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 39 1 false (1),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 22 true (2),
.cycle 11 9 true (2),
.cycle 8 26 true (2),
.cycle 31 13 true (7),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 27 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 4, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 18 2 true (5),
.cycle 9 11 true (2)
]),
.cycle 9 9 true (2)
])
theorem kid10_part87_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part87) = true := by rfl

def kid10_part88 : Audit := .cycle 3 7 true (1)
theorem kid10_part88_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part88) = true := by rfl

def kid10_part89 : Audit := .cycle 8 2 true (3)
theorem kid10_part89_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part89) = true := by rfl

def kid10_part90 : Audit := .cycle 9 1 true (3)
theorem kid10_part90_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part90) = true := by rfl

def kid10_part91 : Audit := .cycle 6 4 true (2)
theorem kid10_part91_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part91) = true := by rfl

def kid10_part93 : Audit := .cycle 0 20 true (0)
theorem kid10_part93_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part93) = true := by rfl

def kid10_part94 : Audit := .cycle 0 14 true (0)
theorem kid10_part94_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part94) = true := by rfl

def kid10_part95 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 12 37 true (0),
.cycle 7 24 true (0),
.cycle 12 7 true (0),
.cycle 34 1 false (0),
.cycle 7 13 true (0),
.cycle 25 1 false (1),
.cycle 32 1 false (0),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 7 28 true (0),
.cycle 0 59 true (0),
.last 19 (5,true),
.cycle 9 9 true (0)
])
theorem kid10_part95_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part95) = true := by rfl

def kid10_part96 : Audit := .cycle 0 16 true (0)
theorem kid10_part96_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part96) = true := by rfl

def kid10_part97 : Audit := .split 12 (5,true) (byMove [
.last 21 (4,true),
.cycle 19 7 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 7 false (-1),
.cycle 13 7 false (0),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 7 false (1),
.cycle 13 7 false (2),
.last 15 (4,true),
.cycle 13 7 false (1),
.last 21 (4,true),
.cycle 13 1 false (-1),
.cycle 13 7 false (-1),
.last 16 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.cycle 13 7 false (1)
])
theorem kid10_part97_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part97) = true := by rfl

def kid10_part98 : Audit := .cycle 11 6 false (1)
theorem kid10_part98_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part98) = true := by rfl

def kid10_part99 : Audit := .cycle 2 10 true (1)
theorem kid10_part99_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part99) = true := by rfl

def kid10_part100 : Audit := .cycle 1 11 true (1)
theorem kid10_part100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part100) = true := by rfl

def kid10_part101 : Audit := .cycle 7 8 true (2)
theorem kid10_part101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part101) = true := by rfl

def kid10_part102 : Audit := .cycle 0 12 true (0)
theorem kid10_part102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part102) = true := by rfl

def kid10_part103 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 12 8 false (2),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far true 1 ⟨0,[0, 0],[10, 10, 10, 8, 32, 2, 64],[10, 10, 10, 10, 10, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 7 8 true (2),
.cycle 7 7 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 12 8 false (2),
.cycle 18 7 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part103) = true := by rfl

def kid10_part104 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 12 8 false (2),
.cycle 19 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 7 8 true (2),
.cycle 7 7 true (2),
.cycle 7 9 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 12 8 false (2),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part104) = true := by rfl

def kid10_part105 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.last 17 (5,true),
.cycle 17 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 22 true (1),
.cycle 13 7 true (1),
.cycle 12 10 true (1),
.cycle 7 11 true (1),
.cycle 12 10 true (1),
.cycle 12 8 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 17 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.last 17 (5,true),
.cycle 9 7 true (1)
])
theorem kid10_part105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part105) = true := by rfl

def kid10_part106 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 16 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 20 true (1),
.cycle 12 7 true (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 7 9 true (1),
.cycle 16 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 16 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 9 5 true (1)
])
theorem kid10_part106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part106) = true := by rfl

def kid10_part107 : Audit := .cycle 2 12 true (1)
theorem kid10_part107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part107) = true := by rfl

def kid10_part108 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 11 31 true (0),
.cycle 7 22 true (0),
.cycle 11 7 true (0),
.cycle 29 1 false (1),
.cycle 7 11 true (0),
.cycle 5 32 true (0),
.cycle 27 1 false (1),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 7 24 true (0),
.cycle 0 53 true (0),
.last 17 (5,true),
.cycle 9 7 true (0)
])
theorem kid10_part108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part108) = true := by rfl

def kid10_part109 : Audit := .split 12 (5,true) (byMove [
.last 34 (4,true),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 7 false (-1),
.cycle 13 7 false (0),
.last 15 (4,true),
.last 15 (4,true),
.cycle 21 7 false (6),
.cycle 13 1 false (1),
.cycle 13 7 false (1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 13 7 false (1),
.last 17 (4,true),
.cycle 13 1 false (-1),
.cycle 13 7 false (-1),
.last 16 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.last 32 (4,true),
.last 17 (4,true),
.cycle 11 2 true (0),
.cycle 13 7 false (1)
])
theorem kid10_part109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part109) = true := by rfl

def kid10_part110 : Audit := .split 16 (4,true) (byMove [
.last 27 (5,true),
.cycle 0 32 true (-2),
.cycle 29 20 true (0),
.cycle 0 36 true (-2),
.last 18 (5,true),
.cycle 11 6 false (1),
.cycle 0 20 true (-2),
.cycle 22 19 true (0),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 1],[8388608, 128, 2097152, 512, 32, 128, 1073741824, 8388608, 1082130432, 2097152, 131072, 524288, 1082261504, 1082269824, 1084400256, 32768, 131072, 8192, 1073741824, 1082130560, 1082130560, 512, 536870912, 128, 1082130432, 1082130432, 2097152, 512, 131072, 128, 1073741824],[128, 2048, 128, 128, 512, 1073741824, 8388608, 8388608, 1084227712, 1082130560, 8388608, 1073741824, 1082269824, 131072, 1084400256, 1082269824, 1084400256, 1073741824, 1082130560, 2048, 128, 128, 1082131072, 1073741824, 1082130432, 2048, 128, 1073741824, 1082130560, 1073741824, 1073741824],1394572608⟩,
.cycle 0 28 true (-2),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 1],[8388608, 128, 2097152, 512, 32, 128, 1073741824, 8388608, 1082130432, 2097152, 131072, 524288, 1082261504, 1082269824, 1084400256, 32768, 131072, 8192, 1073741824, 1073741824, 1082130560, 512, 536870912, 128, 1073741824, 1082130432, 2097152, 512, 131072, 128, 1073741824],[128, 2048, 128, 128, 128, 1073741824, 8388608, 8388608, 8388608, 1082130560, 8388608, 1073741824, 1082269824, 131072, 1082269824, 1082269824, 1082269824, 1073741824, 1073741824, 2048, 128, 128, 128, 1073741824, 1082130432, 2048, 128, 1073741824, 128, 1073741824, 1073741824],1394572608⟩,
.last 17 (5,true),
.last 19 (5,true),
.last 31 (5,true),
.cycle 0 24 true (-2),
.cycle 25 16 true (0),
.last 18 (5,true),
.cycle 11 6 false (1),
.last 33 (5,true),
.last 18 (5,true),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 1],[8388608, 128, 2097152, 512, 32, 128, 1073741824, 8388608, 1082130432, 2097152, 131072, 524288, 1082261504, 1082269824, 1084400256, 32768, 131072, 8192, 1073741824, 1082130432, 1082130560, 512, 536870912, 128, 1073741824, 1082130432, 2097152, 512, 131072, 128, 1073741824],[128, 2048, 128, 128, 128, 1073741824, 8388608, 8388608, 1082130560, 1082130560, 8388608, 1073741824, 1082269824, 131072, 1082269824, 1082269824, 1082269824, 1073741824, 1082130432, 2048, 128, 128, 1082130432, 1073741824, 1082130432, 2048, 128, 1073741824, 1082130432, 1073741824, 1073741824],1394572608⟩,
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 65536, 524288, 1048576, 32768, 67109120, 68719476736, 69632, 128, 256, 134217728, 268500992, 128, 17179869184, 33554432, 67108864, 8589934592, 256, 68719476736, 68719476736, 33554432, 67108864, 134217728, 486609664, 68753031296, 69004759040, 33554432, 67108864, 134217728, 65536, 68719476736, 268435456, 68719476736],[256, 512, 16, 1, 512, 68719476736, 1048576, 68719476736, 65536, 4096, 2097152, 68719476736, 256, 768, 268435456, 16777216, 512, 68719476736, 67108864, 68719476736, 17179869184, 1073741824, 134217728, 68719476736, 67108864, 68920804096, 268435456, 16777216, 134217728, 68719476736, 67108864, 68719476736, 268435456, 16777216, 134217728, 68719476736, 68719476736],128847898434⟩,
.last 21 (5,true),
.last 17 (5,true)
])
theorem kid10_part110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part110) = true := by rfl

def kid10_part111 : Audit := .cycle 2 10 true (1)
theorem kid10_part111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part111) = true := by rfl

def kid10_part112 : Audit := .cycle 1 11 true (1)
theorem kid10_part112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part112) = true := by rfl

def kid10_part113 : Audit := .cycle 7 4 true (2)
theorem kid10_part113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part113) = true := by rfl

def kid10_part114 : Audit := .cycle 0 12 true (0)
theorem kid10_part114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part114) = true := by rfl

def kid10_part115 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 21 9 false (2),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 26 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 7 7 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part115) = true := by rfl

def kid10_part116 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 9 4 true (2),
.cycle 21 9 false (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 8 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 7 7 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 20 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part116) = true := by rfl

def kid10_part92 : Audit := .split 10 (1,true) (byMove [(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116)])

theorem kid10_part92_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part92) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part93_checked

  · exact kid10_part99_checked

  · exact kid10_part105_checked

  · exact kid10_part111_checked

  · exact kid10_part94_checked

  · exact kid10_part100_checked

  · exact kid10_part106_checked

  · exact kid10_part112_checked

  · exact kid10_part95_checked

  · exact kid10_part101_checked

  · exact kid10_part107_checked

  · exact kid10_part113_checked

  · exact kid10_part96_checked

  · exact kid10_part102_checked

  · exact kid10_part108_checked

  · exact kid10_part114_checked

  · exact kid10_part97_checked

  · exact kid10_part103_checked

  · exact kid10_part109_checked

  · exact kid10_part115_checked

  · exact kid10_part98_checked

  · exact kid10_part104_checked

  · exact kid10_part110_checked

  · exact kid10_part116_checked

def kid10_part117 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 0 20 true (-2),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 42 true (0),
.cycle 0 21 true (0),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 23 3 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.cycle 20 7 false (2),
.cycle 10 4 true (2),
.cycle 2 14 true (1),
.cycle 14 6 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 9 5 true (2)
]),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.split 21 (1,true) (byMove [
.last 31 (5,true),
.cycle 12 18 true (-2),
.last 35 (5,true),
.last 31 (5,true),
.cycle 15 7 false (1),
.last 22 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 128, 1, 524288, 1048576, 32768, 256, 68719476736, 4096, 128, 256, 8, 65536, 128, 1, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 65536, 68719476736, 1073741824, 2147483648, 4294967296, 8589934592, 91268055040, 79456894976, 91268055040, 68719476736],[256, 1, 16, 1, 4096, 68719476736, 1048576, 4096, 65536, 4096, 68719476992, 68719476736, 256, 1, 16, 1, 68719476736, 68719476736, 4294967296, 16777216, 268435456, 16777216, 68719542272, 68719476736, 4294967296, 1073741824, 17179869184, 1073741824, 68719476736, 68719476736, 4294967296, 1073741824, 17179869184, 1073741824, 91268055040, 68719476736, 68719476736],137301345356⟩,
.cycle 7 16 true (-2),
.cycle 0 24 true (-2),
.last 29 (5,true),
.cycle 12 10 true (-2),
.cycle 0 45 true (-2),
.cycle 12 12 true (-2),
.last 27 (5,true),
.cycle 14 8 true (-2),
.cycle 0 26 true (-2),
.cycle 15 7 false (1),
.last 22 (5,true),
.last 41 (5,true),
.last 29 (5,true),
.cycle 0 24 true (-2),
.cycle 4 18 true (-2),
.last 23 (5,true),
.last 26 (5,true)
]),
.cycle 2 14 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.cycle 0 24 true (-2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 24 22 true (4),
.cycle 3 46 true (0),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.last 25 (1,true),
.cycle 2 16 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 2 true (3),
.cycle 9 5 true (2)
]),
.cycle 9 3 true (2)
])
theorem kid10_part117_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part117) = true := by rfl

def kid10_part118 : Audit := .cycle 2 10 true (1)
theorem kid10_part118_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part118) = true := by rfl

def kid10_part120 : Audit := .cycle 0 20 true (0)
theorem kid10_part120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part120) = true := by rfl

def kid10_part121 : Audit := .cycle 0 14 true (0)
theorem kid10_part121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part121) = true := by rfl

def kid10_part122 : Audit := .cycle 28 1 false (2)
theorem kid10_part122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part122) = true := by rfl

def kid10_part123 : Audit := .cycle 0 16 true (0)
theorem kid10_part123_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part123) = true := by rfl

def kid10_part124 : Audit := .split 12 (5,true) (byMove [
.cycle 47 2 false (-1),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 20 2 false (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 14 (1,true),
.cycle 18 2 false (-2),
.cycle 22 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 21 2 false (-1),
.cycle 0 16 true (0),
.cycle 31 2 false (1),
.cycle 0 18 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid10_part124_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part124) = true := by rfl

def kid10_part125 : Audit := .cycle 13 2 false (-1)
theorem kid10_part125_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part125) = true := by rfl

def kid10_part126 : Audit := .cycle 2 10 true (1)
theorem kid10_part126_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part126) = true := by rfl

def kid10_part127 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 39 true (0),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (5,true),
.cycle 10 9 true (0),
.cycle 18 2 false (2),
.last 16 (5,true),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 33 true (0),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part127_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part127) = true := by rfl

def kid10_part128 : Audit := .cycle 18 2 false (2)
theorem kid10_part128_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part128) = true := by rfl

def kid10_part129 : Audit := .cycle 0 12 true (0)
theorem kid10_part129_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part129) = true := by rfl

def kid10_part130 : Audit := .cycle 18 2 false (2)
theorem kid10_part130_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part130) = true := by rfl

def kid10_part131 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 33 (1,true),
.cycle 10 9 true (0),
.cycle 18 2 false (2),
.cycle 17 2 false (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part131_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part131) = true := by rfl

def kid10_part132 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 10 25 false (2),
.cycle 20 2 false (0),
.cycle 0 17 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 17 (5,true),
.cycle 0 14 true (0),
.cycle 13 8 true (1),
.last 13 (5,true),
.cycle 13 10 true (1),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 5 8 true (1),
.cycle 10 6 true (0),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 2 20 true (1),
.cycle 0 14 true (0),
.last 25 (5,true),
.last 13 (5,true)
])
theorem kid10_part132_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part132) = true := by rfl

def kid10_part133 : Audit := .split 19 (1,true) (byMove [
.cycle 11 32 true (0),
.cycle 10 18 true (-1),
.cycle 21 2 false (1),
.cycle 0 27 true (0),
.cycle 35 2 false (-3),
.last 20 (5,true),
.cycle 6 14 true (1),
.cycle 1 21 true (1),
.cycle 7 16 true (1),
.cycle 2 20 true (1),
.cycle 10 10 true (1),
.last 20 (5,true),
.cycle 10 12 true (0),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 16, 64],[2, 2, 18, 2, 2, 64, 64],64⟩,
.cycle 10 14 true (0),
.cycle 30 1 false (0),
.cycle 38 2 false (-2),
.last 20 (5,true),
.cycle 15 6 true (1),
.cycle 1 21 true (1),
.cycle 12 8 true (1),
.cycle 2 20 true (1),
.cycle 18 2 true (1),
.last 20 (5,true)
])
theorem kid10_part133_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part133) = true := by rfl

def kid10_part134 : Audit := .cycle 2 12 true (1)
theorem kid10_part134_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part134) = true := by rfl

def kid10_part135 : Audit := .cycle 23 1 false (1)
theorem kid10_part135_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part135) = true := by rfl

def kid10_part136 : Audit := .split 12 (5,true) (byMove [
.last 46 (1,true),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 23 2 false (1),
.cycle 25 2 false (3),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.last 14 (1,true),
.cycle 18 2 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 14 (1,true),
.cycle 25 2 false (-1),
.last 32 (1,true),
.cycle 27 2 false (1),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid10_part136_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part136) = true := by rfl

def kid10_part137 : Audit := .cycle 13 2 false (-1)
theorem kid10_part137_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part137) = true := by rfl

def kid10_part138 : Audit := .cycle 2 10 true (1)
theorem kid10_part138_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part138) = true := by rfl

def kid10_part139 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 19 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part139_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part139) = true := by rfl

def kid10_part140 : Audit := .cycle 7 4 true (2)
theorem kid10_part140_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part140) = true := by rfl

def kid10_part141 : Audit := .cycle 0 12 true (0)
theorem kid10_part141_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part141) = true := by rfl

def kid10_part142 : Audit := .split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 19 2 false (-1),
.cycle 21 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 22 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 27 2 false (1),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 0 20 true (0),
.cycle 2 14 true (1),
.cycle 10 4 true (2),
.cycle 25 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 2 true (3),
.cycle 9 5 true (2)
])
theorem kid10_part142_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part142) = true := by rfl

def kid10_part143 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 9 4 true (2),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 23 2 false (1),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 9 5 true (2),
.cycle 2 12 true (1),
.cycle 10 2 true (2),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part143_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part143) = true := by rfl

def kid10_part119 : Audit := .split 10 (4,true) (byMove [(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132),(kid10_part133),(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140),(kid10_part141),(kid10_part142),(kid10_part143)])

theorem kid10_part119_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part119) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132),(kid10_part133),(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140),(kid10_part141),(kid10_part142),(kid10_part143)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part120_checked

  · exact kid10_part126_checked

  · exact kid10_part132_checked

  · exact kid10_part138_checked

  · exact kid10_part121_checked

  · exact kid10_part127_checked

  · exact kid10_part133_checked

  · exact kid10_part139_checked

  · exact kid10_part122_checked

  · exact kid10_part128_checked

  · exact kid10_part134_checked

  · exact kid10_part140_checked

  · exact kid10_part123_checked

  · exact kid10_part129_checked

  · exact kid10_part135_checked

  · exact kid10_part141_checked

  · exact kid10_part124_checked

  · exact kid10_part130_checked

  · exact kid10_part136_checked

  · exact kid10_part142_checked

  · exact kid10_part125_checked

  · exact kid10_part131_checked

  · exact kid10_part137_checked

  · exact kid10_part143_checked

def kid10_part145 : Audit := .cycle 0 20 true (0)
theorem kid10_part145_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part145) = true := by rfl

def kid10_part146 : Audit := .cycle 0 14 true (0)
theorem kid10_part146_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part146) = true := by rfl

def kid10_part147 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.last 37 (1,true),
.cycle 34 1 false (2),
.cycle 12 7 true (0),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.last 19 (1,true),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 7 28 true (0),
.cycle 0 59 true (0),
.cycle 30 1 false (2),
.cycle 9 9 true (0)
])
theorem kid10_part147_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part147) = true := by rfl

def kid10_part148 : Audit := .cycle 0 16 true (0)
theorem kid10_part148_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part148) = true := by rfl

def kid10_part149 : Audit := .cycle 14 1 false (-2)
theorem kid10_part149_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part149) = true := by rfl

def kid10_part150 : Audit := .cycle 13 1 false (-1)
theorem kid10_part150_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part150) = true := by rfl

def kid10_part151 : Audit := .cycle 2 10 true (1)
theorem kid10_part151_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part151) = true := by rfl

def kid10_part152 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 18 (4,true),
.cycle 32 1 false (8),
.cycle 6 8 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 13 true (1),
.cycle 9 3 true (2)
])
theorem kid10_part152_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part152) = true := by rfl

def kid10_part153 : Audit := .split 18 (4,true) (byMove [
.cycle 0 32 true (0),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 31 1 false (5),
.last 19 (1,true),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (5),
.last 20 (1,true),
.cycle 41 1 false (3),
.cycle 33 1 false (5),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 2 18 true (0),
.last 19 (1,true),
.cycle 25 1 false (3),
.cycle 0 20 true (0),
.cycle 17 22 true (1),
.cycle 9 19 true (0)
])
theorem kid10_part153_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part153) = true := by rfl

def kid10_part154 : Audit := .cycle 0 12 true (0)
theorem kid10_part154_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part154) = true := by rfl

def kid10_part155 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 51 1 false (9),
.cycle 0 21 true (0),
.cycle 21 1 false (3),
.cycle 22 1 false (4),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 45 1 false (3),
.cycle 9 3 true (2)
])
theorem kid10_part155_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part155) = true := by rfl

def kid10_part156 : Audit := .cycle 21 1 false (5)
theorem kid10_part156_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part156) = true := by rfl

def kid10_part157 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.last 35 (4,true),
.cycle 21 1 false (-1),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 20 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.last 19 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true)
])
theorem kid10_part157_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part157) = true := by rfl

def kid10_part158 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 16 (1,true),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 0, 4, 2, 3],[0, 0, 2097152, 512, 32, 2048, 1073741824, 524288, 1073741824, 2097152, 131072, 8388608, 1073741824, 1073750016, 1208000512, 32768, 131072, 131072, 1073741824, 0, 0, 134217728, 32, 536870912, 1073741824, 524288, 0, 2097152, 131072, 8388608, 1073741824],[0, 1073741824, 2048, 1073741824, 134217728, 128, 524288, 1073741824, 2097152, 0, 8388608, 524288, 1073750016, 1073741824, 1208131584, 1073750016, 1076011008, 8192, 0, 1073741824, 536870912, 0, 134217728, 33554432, 524288, 1073741824, 2097152, 0, 8388608, 524288, 1073741824],1090810176⟩,
.cycle 12 7 true (1),
.last 18 (1,true),
.last 18 (1,true),
.last 15 (1,true),
.last 19 (1,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (1,true),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 21 (1,true),
.cycle 9 5 true (1)
])
theorem kid10_part158_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part158) = true := by rfl

def kid10_part159 : Audit := .cycle 2 12 true (1)
theorem kid10_part159_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part159) = true := by rfl

def kid10_part160 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 33 (1,true),
.cycle 31 1 false (1),
.cycle 11 7 true (0),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.last 17 (1,true),
.cycle 27 1 false (1),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 7 24 true (0),
.cycle 0 53 true (0),
.cycle 25 1 false (1),
.cycle 9 7 true (0)
])
theorem kid10_part160_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part160) = true := by rfl

def kid10_part161 : Audit := .cycle 14 1 false (-2)
theorem kid10_part161_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part161) = true := by rfl

def kid10_part162 : Audit := .cycle 13 1 false (-1)
theorem kid10_part162_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part162) = true := by rfl

def kid10_part163 : Audit := .cycle 2 10 true (1)
theorem kid10_part163_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part163) = true := by rfl

def kid10_part164 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 1 16 true (1),
.cycle 6 6 true (2),
.last 15 (4,true),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 1 13 true (1),
.cycle 9 3 true (2)
])
theorem kid10_part164_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part164) = true := by rfl

def kid10_part165 : Audit := .cycle 7 4 true (2)
theorem kid10_part165_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part165) = true := by rfl

def kid10_part166 : Audit := .cycle 0 12 true (0)
theorem kid10_part166_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part166) = true := by rfl

def kid10_part167 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 20 1 false (0),
.cycle 0 13 true (0),
.cycle 13 2 true (0),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 20, 64],[4, 64, 16, 1, 4, 16, 64],64⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 16 2 true (4),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 13 2 true (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 12 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part167_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part167) = true := by rfl

def kid10_part168 : Audit := .cycle 9 3 true (2)
theorem kid10_part168_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part168) = true := by rfl

def kid10_part144 : Audit := .split 10 (5,true) (byMove [(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165),(kid10_part166),(kid10_part167),(kid10_part168)])

theorem kid10_part144_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part144) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165),(kid10_part166),(kid10_part167),(kid10_part168)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part145_checked

  · exact kid10_part151_checked

  · exact kid10_part157_checked

  · exact kid10_part163_checked

  · exact kid10_part146_checked

  · exact kid10_part152_checked

  · exact kid10_part158_checked

  · exact kid10_part164_checked

  · exact kid10_part147_checked

  · exact kid10_part153_checked

  · exact kid10_part159_checked

  · exact kid10_part165_checked

  · exact kid10_part148_checked

  · exact kid10_part154_checked

  · exact kid10_part160_checked

  · exact kid10_part166_checked

  · exact kid10_part149_checked

  · exact kid10_part155_checked

  · exact kid10_part161_checked

  · exact kid10_part167_checked

  · exact kid10_part150_checked

  · exact kid10_part156_checked

  · exact kid10_part162_checked

  · exact kid10_part168_checked

def kid10_part169 : Audit := .cycle 0 10 true (0)
theorem kid10_part169_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part169) = true := by rfl

def kid10_part170 : Audit := .cycle 1 9 true (1)
theorem kid10_part170_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part170) = true := by rfl

def kid10_part171 : Audit := .cycle 2 8 true (1)
theorem kid10_part171_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part171) = true := by rfl

def kid10_part172 : Audit := .cycle 2 11 true (1)
theorem kid10_part172_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part172) = true := by rfl

def kid10_part174 : Audit := .cycle 2 11 true (1)
theorem kid10_part174_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part174) = true := by rfl

def kid10_part175 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 16 false (2),
.cycle 13 15 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.cycle 21 9 false (2),
.last 23 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 22 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 14 true (1),
.cycle 9 4 true (2)
])
theorem kid10_part175_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part175) = true := by rfl

def kid10_part176 : Audit := .cycle 33 1 false (1)
theorem kid10_part176_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part176) = true := by rfl

def kid10_part177 : Audit := .cycle 0 13 true (0)
theorem kid10_part177_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part177) = true := by rfl

def kid10_part178 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 13 4 false (1),
.cycle 17 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 12 7 true (0),
.cycle 17 4 false (1),
.cycle 21 4 false (2),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 4 false (1),
.cycle 19 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 15 4 false (1),
.cycle 9 4 true (2)
])
theorem kid10_part178_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part178) = true := by rfl

def kid10_part179 : Audit := .cycle 16 3 false (0)
theorem kid10_part179_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part179) = true := by rfl

def kid10_part180 : Audit := .cycle 0 12 true (0)
theorem kid10_part180_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part180) = true := by rfl

def kid10_part181 : Audit := .cycle 1 11 true (1)
theorem kid10_part181_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part181) = true := by rfl

def kid10_part182 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 35 1 false (3),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 16, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 13 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 16, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 10 22 true (2),
.cycle 9 11 true (2)
])
theorem kid10_part182_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part182) = true := by rfl

def kid10_part183 : Audit := .cycle 3 9 true (1)
theorem kid10_part183_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part183) = true := by rfl

def kid10_part184 : Audit := .cycle 8 4 true (3)
theorem kid10_part184_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part184) = true := by rfl

def kid10_part185 : Audit := .cycle 9 3 true (3)
theorem kid10_part185_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part185) = true := by rfl

def kid10_part186 : Audit := .cycle 6 6 true (2)
theorem kid10_part186_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part186) = true := by rfl

def kid10_part187 : Audit := .split 12 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 13 11 false (1),
.cycle 13 10 false (2),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 12 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 7 8 true (2),
.last 17 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 17 (4,true),
.cycle 13 11 false (1),
.last 14 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (2)
])
theorem kid10_part187_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part187) = true := by rfl

def kid10_part188 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.cycle 0 26 true (-2),
.cycle 0 19 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 46 true (0),
.cycle 0 23 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.last 27 (1,true),
.cycle 2 18 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 0 18 true (0),
.cycle 9 5 true (2)
])
theorem kid10_part188_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part188) = true := by rfl

def kid10_part189 : Audit := .cycle 2 12 true (1)
theorem kid10_part189_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part189) = true := by rfl

def kid10_part190 : Audit := .split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 0 18 true (0),
.cycle 13 4 false (1),
.cycle 17 4 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 24 4 false (2),
.cycle 0 14 true (0),
.cycle 24 4 false (2),
.cycle 19 4 false (1),
.last 14 (1,true),
.last 23 (1,true),
.cycle 2 14 true (1),
.cycle 27 1 false (1),
.cycle 13 4 false (1),
.cycle 19 4 false (-1),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part190_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part190) = true := by rfl

def kid10_part191 : Audit := .split 14 (4,true) (byMove [
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 20 7 false (0),
.last 17 (1,true),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 14 24 true (2),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 0, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 15 5 true (2),
.last 19 (1,true),
.last 15 (1,true),
.cycle 2 18 true (1),
.cycle 5 10 true (1),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 47 24 true (1),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 0, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 16 5 false (2)
])
theorem kid10_part191_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part191) = true := by rfl

def kid10_part192 : Audit := .cycle 0 12 true (0)
theorem kid10_part192_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part192) = true := by rfl

def kid10_part193 : Audit := .cycle 1 11 true (1)
theorem kid10_part193_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part193) = true := by rfl

def kid10_part194 : Audit := .cycle 2 10 true (1)
theorem kid10_part194_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part194) = true := by rfl

def kid10_part195 : Audit := .cycle 2 13 true (1)
theorem kid10_part195_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part195) = true := by rfl

def kid10_part196 : Audit := .cycle 10 2 true (3)
theorem kid10_part196_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part196) = true := by rfl

def kid10_part197 : Audit := .cycle 9 3 true (3)
theorem kid10_part197_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part197) = true := by rfl

def kid10_part173 : Audit := .split 11 (5,true) (byMove [(kid10_part174),(kid10_part175),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181),(kid10_part182),(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part189),(kid10_part190),(kid10_part191),(kid10_part192),(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197)])

theorem kid10_part173_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part173) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some mv)) (byMove [(kid10_part174),(kid10_part175),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181),(kid10_part182),(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part189),(kid10_part190),(kid10_part191),(kid10_part192),(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part174_checked

  · exact kid10_part180_checked

  · exact kid10_part186_checked

  · exact kid10_part192_checked

  · exact kid10_part175_checked

  · exact kid10_part181_checked

  · exact kid10_part187_checked

  · exact kid10_part193_checked

  · exact kid10_part176_checked

  · exact kid10_part182_checked

  · exact kid10_part188_checked

  · exact kid10_part194_checked

  · exact kid10_part177_checked

  · exact kid10_part183_checked

  · exact kid10_part189_checked

  · exact kid10_part195_checked

  · exact kid10_part178_checked

  · exact kid10_part184_checked

  · exact kid10_part190_checked

  · exact kid10_part196_checked

  · exact kid10_part179_checked

  · exact kid10_part185_checked

  · exact kid10_part191_checked

  · exact kid10_part197_checked

def kid10_part198 : Audit := .cycle 9 1 true (3)
theorem kid10_part198_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part198) = true := by rfl

def kid10_part54 : Audit := .split 9 (5,false) (byMove [(kid10_part55),(kid10_part56),(kid10_part81),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part144),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part198)])

theorem kid10_part54_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid10_part54) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part55),(kid10_part56),(kid10_part81),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part144),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part198)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part55_checked

  · exact kid10_part85_checked

  · exact kid10_part91_checked

  · exact kid10_part169_checked

  · exact kid10_part56_checked

  · exact kid10_part86_checked

  · exact kid10_part92_checked

  · exact kid10_part170_checked

  · exact kid10_part81_checked

  · exact kid10_part87_checked

  · exact kid10_part117_checked

  · exact kid10_part171_checked

  · exact kid10_part82_checked

  · exact kid10_part88_checked

  · exact kid10_part118_checked

  · exact kid10_part172_checked

  · exact kid10_part83_checked

  · exact kid10_part89_checked

  · exact kid10_part119_checked

  · exact kid10_part173_checked

  · exact kid10_part84_checked

  · exact kid10_part90_checked

  · exact kid10_part144_checked

  · exact kid10_part198_checked

def kid10_part199 : Audit := .cycle 0 9 true (0)
theorem kid10_part199_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid10_part199) = true := by rfl

def kid10_part200 : Audit := .cycle 1 8 true (1)
theorem kid10_part200_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid10_part200) = true := by rfl

def kid10_part202 : Audit := .cycle 7 13 true (2)
theorem kid10_part202_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part202) = true := by rfl

def kid10_part203 : Audit := .cycle 0 21 true (0)
theorem kid10_part203_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part203) = true := by rfl

def kid10_part204 : Audit := .cycle 2 23 true (1)
theorem kid10_part204_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part204) = true := by rfl

def kid10_part205 : Audit := .cycle 0 23 true (0)
theorem kid10_part205_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part205) = true := by rfl

def kid10_part206 : Audit := .cycle 0 21 true (0)
theorem kid10_part206_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part206) = true := by rfl

def kid10_part208 : Audit := .cycle 2 27 true (1)
theorem kid10_part208_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part208) = true := by rfl

def kid10_part209 : Audit := .split 19 (1,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 63 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 0 31 true (0),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 23 true (0),
.cycle 1 31 true (1),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 7 17 true (2),
.cycle 28 1 false (0),
.cycle 0 25 true (0),
.last 47 (5,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part209_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part209) = true := by rfl

def kid10_part210 : Audit := .cycle 0 23 true (0)
theorem kid10_part210_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part210) = true := by rfl

def kid10_part211 : Audit := .cycle 7 15 true (2)
theorem kid10_part211_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part211) = true := by rfl

def kid10_part212 : Audit := .cycle 35 1 false (1)
theorem kid10_part212_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part212) = true := by rfl

def kid10_part213 : Audit := .split 19 (5,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 89 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 23 true (0),
.cycle 25 1 false (1),
.last 21 (1,true),
.cycle 0 25 true (0),
.cycle 7 17 true (2),
.cycle 28 1 false (0),
.cycle 0 25 true (0),
.cycle 23 1 false (-1),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part213_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part213) = true := by rfl

def kid10_part214 : Audit := .split 20 (1,true) (byMove [
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 4, 8, 8, 32, 64, 64],64⟩,
.cycle 0 22 true (0),
.cycle 0 23 true (0),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 30 true (0),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 6 15 true (2),
.cycle 0 26 true (0),
.cycle 0 24 true (0),
.cycle 2 21 true (1),
.cycle 17 4 true (4),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 0 31 true (0),
.cycle 0 22 true (0)
])
theorem kid10_part214_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part214) = true := by rfl

def kid10_part215 : Audit := .cycle 7 13 true (2)
theorem kid10_part215_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part215) = true := by rfl

def kid10_part216 : Audit := .cycle 0 21 true (0)
theorem kid10_part216_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part216) = true := by rfl

def kid10_part217 : Audit := .cycle 3 23 true (1)
theorem kid10_part217_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part217) = true := by rfl

def kid10_part218 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 256, 4, 16, 4096],[256, 4096, 16, 1, 4, 4096, 256, 4096, 16, 1, 4096, 4096, 4096],4096⟩
theorem kid10_part218_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part218) = true := by rfl

def kid10_part219 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 29 1 true (5),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 21 1 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 4, 32, 64],[4, 64, 16, 1, 40, 4, 64],64⟩,
.cycle 10 11 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 32, 64],[4, 64, 16, 1, 36, 16, 64],64⟩,
.cycle 21 1 true (7),
.last 22 (1,true),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 27 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 32, 64],[4, 64, 16, 1, 36, 16, 64],64⟩,
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 30 1 true (8),
.cycle 21 1 true (7)
])
theorem kid10_part219_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part219) = true := by rfl

def kid10_part220 : Audit := .split 43 (1,true) (byMove [
.cycle 6 47 true (2),
.cycle 19 31 true (3),
.cycle 0 48 true (0),
.cycle 7 40 true (2),
.cycle 6 63 true (2),
.last 44 (5,true),
.cycle 0 46 true (0),
.cycle 7 38 true (2),
.cycle 0 46 true (0),
.cycle 6 45 true (2),
.cycle 21 23 true (3),
.last 47 (5,true),
.cycle 19 25 true (3),
.cycle 0 54 true (0),
.cycle 6 75 true (2),
.cycle 0 48 true (0),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 3, 2, 2],[0, 0, 512, 512, 512, 64, 131072, 0, 0, 512, 131584, 64, 8388608, 1099300864, 1233519104, 134217728, 1099300864, 16777216, 1099300864, 1099300864, 1101430784, 2097152, 1235649024, 262144, 131072, 0, 131072, 32768, 131584, 4096, 1073741824],[0, 1024, 512, 0, 32, 1073741824, 0, 1024, 16777280, 0, 131072, 1073741824, 1099300864, 268435456, 16777728, 16777216, 8388608, 1073741824, 1099300864, 4194304, 1235649024, 1099300864, 8388608, 1073741824, 0, 65536, 262144, 1099300864, 131072, 1073741824, 1073741824],1625124864⟩,
.last 44 (5,true),
.cycle 0 46 true (0),
.cycle 7 38 true (2),
.cycle 0 46 true (0),
.cycle 4 40 true (1),
.cycle 6 70 true (2),
.cycle 6 43 true (2)
])
theorem kid10_part220_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part220) = true := by rfl

def kid10_part221 : Audit := .split 19 (1,true) (byMove [
.cycle 21 25 true (3),
.cycle 1 25 true (1),
.cycle 31 1 false (1),
.cycle 45 1 false (1),
.cycle 7 21 true (2),
.cycle 57 27 true (5),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.cycle 7 51 true (0),
.cycle 3 20 true (1),
.cycle 0 27 true (0),
.last 20 (5,true),
.cycle 33 7 false (2),
.cycle 30 5 false (1),
.cycle 0 25 true (0),
.cycle 28 1 false (0),
.cycle 0 29 true (0),
.last 26 (5,true),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.cycle 20 23 true (3),
.cycle 2 24 true (1),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part221_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part221) = true := by rfl

def kid10_part222 : Audit := .cycle 7 19 true (2)
theorem kid10_part222_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part222) = true := by rfl

def kid10_part223 : Audit := .cycle 0 23 true (0)
theorem kid10_part223_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part223) = true := by rfl

def kid10_part224 : Audit := .cycle 69 1 false (11)
theorem kid10_part224_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part224) = true := by rfl

def kid10_part225 : Audit := .split 19 (5,true) (byMove [
.cycle 22 31 true (3),
.last 24 (1,true),
.cycle 31 1 false (1),
.cycle 45 1 false (1),
.last 24 (1,true),
.cycle 23 1 false (-1),
.cycle 0 23 true (0),
.last 20 (1,true),
.cycle 44 1 false (4),
.last 22 (1,true),
.cycle 26 1 false (0),
.cycle 33 1 false (7),
.last 21 (1,true),
.last 30 (1,true),
.cycle 0 25 true (0),
.cycle 28 1 false (0),
.cycle 30 1 false (0),
.cycle 23 1 false (-1),
.cycle 0 23 true (0),
.last 20 (1,true),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 3, 2, 2],[0, 0, 512, 512, 512, 2048, 1073741824, 0, 0, 512, 133632, 2048, 1073741824, 1073741824, 1207960064, 134217728, 1082130432, 536870912, 1073741824, 1073741824, 1075871744, 2097152, 1218478592, 8388608, 1073741824, 0, 1073741824, 32768, 133632, 131072, 1073741824],[0, 1073741824, 512, 0, 32, 0, 0, 1073741824, 536872960, 0, 131072, 0, 1073741824, 1073741824, 536873472, 1073741824, 8388608, 1073741824, 1073741824, 1073741824, 1218478592, 1073741824, 8388608, 1073741824, 0, 1073741824, 8388608, 1073741824, 131072, 0, 1073741824],1163751488⟩,
.last 22 (1,true),
.cycle 0 25 true (0),
.cycle 23 3 true (5)
])
theorem kid10_part225_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part225) = true := by rfl

def kid10_part226 : Audit := .split 20 (1,true) (byMove [
.cycle 2 20 true (1),
.cycle 1 23 true (1),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 30 true (0),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 0 22 true (0),
.cycle 6 15 true (2),
.cycle 39 9 false (3),
.cycle 0 24 true (0),
.cycle 2 21 true (1),
.last 22 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 0 31 true (0),
.cycle 0 22 true (0)
])
theorem kid10_part226_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part226) = true := by rfl

def kid10_part227 : Audit := .cycle 7 13 true (2)
theorem kid10_part227_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part227) = true := by rfl

def kid10_part228 : Audit := .cycle 0 21 true (0)
theorem kid10_part228_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part228) = true := by rfl

def kid10_part229 : Audit := .cycle 4 15 true (1)
theorem kid10_part229_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part229) = true := by rfl

def kid10_part230 : Audit := .cycle 34 10 true (8)
theorem kid10_part230_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part230) = true := by rfl

def kid10_part231 : Audit := .split 20 (5,true) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 24 1 true (2),
.cycle 24 1 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 29 1 true (7),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 21 1 true (7),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 23 1 true (5),
.cycle 2 21 true (1),
.cycle 88 1 true (8),
.cycle 29 3 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 30 1 true (8),
.cycle 21 1 true (7)
])
theorem kid10_part231_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part231) = true := by rfl

def kid10_part207 : Audit := .split 18 (5,false) (byMove [(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231)])

theorem kid10_part207_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part207) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part208_checked

  · exact kid10_part214_checked

  · exact kid10_part220_checked

  · exact kid10_part226_checked

  · exact kid10_part209_checked

  · exact kid10_part215_checked

  · exact kid10_part221_checked

  · exact kid10_part227_checked

  · exact kid10_part210_checked

  · exact kid10_part216_checked

  · exact kid10_part222_checked

  · exact kid10_part228_checked

  · exact kid10_part211_checked

  · exact kid10_part217_checked

  · exact kid10_part223_checked

  · exact kid10_part229_checked

  · exact kid10_part212_checked

  · exact kid10_part218_checked

  · exact kid10_part224_checked

  · exact kid10_part230_checked

  · exact kid10_part213_checked

  · exact kid10_part219_checked

  · exact kid10_part225_checked

  · exact kid10_part231_checked

def kid10_part232 : Audit := .cycle 2 17 true (1)
theorem kid10_part232_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part232) = true := by rfl

def kid10_part233 : Audit := .split 18 (1,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 26 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 1 26 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 22, 4, 16, 128, 256, 8, 256, 4, 16, 4096],[256, 4, 16, 1, 2, 4096, 256, 4096, 16, 1, 2, 4096, 4096],4096⟩,
.cycle 19 1 true (5),
.last 22 (5,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 22, 4, 16, 128, 256, 32768, 256, 16384, 98590, 128, 256, 8, 65536, 4, 16, 262144],[256, 4, 16, 1, 2, 262144, 256, 262144, 65536, 4096, 8192, 262144, 256, 98590, 16, 1, 2, 262144, 262144],262144⟩,
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.cycle 19 1 true (5)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[4, 4, 16, 1, 2, 64, 64],96⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[4, 16, 16, 1, 2, 64, 64],96⟩,
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 1 26 true (1),
.last 32 (5,true),
.last 23 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (5,true),
.last 30 (5,true),
.last 34 (5,true),
.cycle 19 1 true (7),
.cycle 18 3 true (6),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.last 36 (5,true),
.last 23 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.cycle 19 1 true (7)
]),
.cycle 6 15 true (2),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 1 24 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[4, 16, 16, 1, 2, 64, 64],96⟩,
.split 19 (5,false) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 1 26 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.last 21 (5,true),
.cycle 2 19 true (1),
.cycle 18 2 true (5),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 4, 4, 128, 256, 8, 256, 4, 4, 4096],[256, 16, 16, 1, 2, 4096, 256, 4096, 16, 1, 2, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 20 (5,true),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 2 19 true (1),
.last 21 (5,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 20 (5,true)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 1 27 true (1),
.split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.cycle 18 2 true (6),
.last 34 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 27 true (1),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 17 3 true (5),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.cycle 19 1 true (7)
])
])
theorem kid10_part233_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part233) = true := by rfl

def kid10_part234 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 64, 16, 1, 4, 64, 64],96⟩
theorem kid10_part234_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part234) = true := by rfl

def kid10_part235 : Audit := .cycle 0 19 true (0)
theorem kid10_part235_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part235) = true := by rfl

def kid10_part236 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 64, 16, 1, 16, 64, 64],96⟩
theorem kid10_part236_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part236) = true := by rfl

def kid10_part238 : Audit := .cycle 0 19 true (0)
theorem kid10_part238_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part238) = true := by rfl

def kid10_part239 : Audit := .cycle 1 18 true (1)
theorem kid10_part239_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part239) = true := by rfl

def kid10_part240 : Audit := .split 27 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 19 9 true (3),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 54 1 false (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 11 29 true (2),
.cycle 10 18 true (2),
.cycle 11 40 true (2),
.cycle 27 1 true (7),
.last 29 (1,true),
.cycle 7 22 true (2),
.cycle 0 30 true (0),
.cycle 21 7 true (3),
.cycle 11 42 true (2),
.cycle 81 1 false (5),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 2 29 true (1),
.cycle 19 10 true (3),
.cycle 27 1 true (7)
])
theorem kid10_part240_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part240) = true := by rfl

def kid10_part241 : Audit := .cycle 3 16 true (1)
theorem kid10_part241_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part241) = true := by rfl

def kid10_part242 : Audit := .cycle 8 11 true (2)
theorem kid10_part242_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part242) = true := by rfl

def kid10_part243 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 8 22 true (2),
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 10 18 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 52, 4, 16, 128, 256, 8, 256, 4, 16, 4096],[256, 4096, 16, 1, 32, 4, 256, 4096, 16, 1, 32, 60, 4096],4096⟩,
.cycle 19 1 true (5),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 52, 4, 16, 128, 256, 32768, 256, 16384, 60, 128, 256, 8, 65536, 4, 16, 262144],[256, 262144, 16, 1, 32, 4, 256, 262144, 65536, 4096, 131072, 60, 256, 262144, 16, 1, 32, 60, 262144],262144⟩,
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 19 10 true (5),
.cycle 19 1 true (5)
])
theorem kid10_part243_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part243) = true := by rfl

def kid10_part244 : Audit := .cycle 0 19 true (0)
theorem kid10_part244_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part244) = true := by rfl

def kid10_part245 : Audit := .cycle 1 18 true (1)
theorem kid10_part245_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part245) = true := by rfl

def kid10_part246 : Audit := .far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 67109120, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 8388608, 256, 1073741824, 128, 256, 32768, 256, 16384, 1073741824, 1073741824],[256, 1073741824, 16, 1, 32, 4, 256, 1073741824, 65536, 4096, 131072, 16384, 67108864, 1073741824, 4194304, 262144, 8388608, 1048576, 256, 1073741824, 1024, 64, 2048, 256, 256, 1073741824, 65536, 4096, 131072, 16384, 1073741824],1889684512⟩
theorem kid10_part246_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part246) = true := by rfl

def kid10_part247 : Audit := .cycle 10 9 true (2)
theorem kid10_part247_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part247) = true := by rfl

def kid10_part248 : Audit := .far true 5 ⟨0,[0, 1, 2, 3, 4, 1, 4, 1, 4, 4],[0, 0, 2097152, 512, 512, 1073741824, 1073741824, 0, 1073741824, 2097152, 512, 1073741824, 0, 1073741824, 512, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1210056704, 134217728, 1210057216, 1073741824, 1073741824],[0, 1073741824, 2097152, 0, 1073741824, 2097152, 0, 1073741824, 1073741824, 1073741824, 512, 1073741824, 1073741824, 1073741824, 2097152, 1073741824, 1073741824, 2097152, 1073741824, 1073741824, 2097152, 0, 1073741824, 2097152, 1073741824, 1073741824, 1210057216, 1073741824, 1210057216, 1210057216, 1073741824],2011113824⟩
theorem kid10_part248_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part248) = true := by rfl

def kid10_part249 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 29 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 19 1 true (7),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 48, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 45 1 false (9),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part249_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part249) = true := by rfl

def kid10_part250 : Audit := .split 20 (1,true) (byMove [
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 67109120, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 8388608, 256, 1073741824, 128, 256, 32768, 256, 16384, 1073741824, 1073741824],[256, 0, 16, 1, 32, 68174084, 256, 68174084, 65536, 4096, 131072, 68239620, 67108864, 65536, 4194304, 262144, 8388608, 68174084, 256, 8388608, 1024, 64, 2048, 256, 256, 256, 65536, 4096, 131072, 65536, 1073741824],1889684512⟩,
.cycle 0 22 true (0),
.last 22 (5,false),
.cycle 6 19 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 6 15 true (2),
.last 25 (5,false),
.last 23 (5,false),
.cycle 2 21 true (1),
.cycle 17 4 true (5),
.cycle 15 10 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 30 (5,false),
.last 21 (5,false)
])
theorem kid10_part250_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part250) = true := by rfl

def kid10_part251 : Audit := .cycle 7 13 true (2)
theorem kid10_part251_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part251) = true := by rfl

def kid10_part252 : Audit := .cycle 0 21 true (0)
theorem kid10_part252_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part252) = true := by rfl

def kid10_part253 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 19 9 true (3),
.cycle 3 23 true (1),
.cycle 8 18 true (2),
.cycle 47 1 false (1),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 12 25 true (2),
.cycle 10 16 true (2),
.cycle 12 34 true (2),
.cycle 25 1 true (7),
.last 27 (1,true),
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.cycle 19 7 true (3),
.cycle 12 36 true (2),
.cycle 68 1 false (4),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 2 27 true (1),
.cycle 19 10 true (3),
.cycle 25 1 true (7)
])
theorem kid10_part253_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part253) = true := by rfl

def kid10_part254 : Audit := .far true 5 ⟨0,[0, 1, 2, 3, 4, 1, 4, 1, 4, 4],[0, 0, 2097152, 512, 512, 1073741824, 1073741824, 0, 1073741824, 2097152, 512, 1073741824, 0, 1073741824, 512, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1210056704, 134217728, 1210057216, 1073741824, 1073741824],[0, 1073741824, 2097152, 0, 1073741824, 1024, 0, 1073741824, 1073741824, 1073741824, 512, 4194304, 1073741824, 1073741824, 2097152, 1073741824, 1073741824, 1024, 1073741824, 1073741824, 2097152, 0, 1073741824, 1024, 1073741824, 1073741824, 1210057216, 1073741824, 1210057216, 268435456, 1073741824],2011113824⟩
theorem kid10_part254_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part254) = true := by rfl

def kid10_part255 : Audit := .split 19 (5,false) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 21 9 true (3),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 25 1 false (-1),
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 18 2 true (5),
.last 21 (1,true),
.cycle 7 18 true (2),
.cycle 2 21 true (1),
.cycle 20 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 48, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 25 1 false (-1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 20 10 true (6),
.cycle 31 3 false (1)
])
theorem kid10_part255_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part255) = true := by rfl

def kid10_part256 : Audit := .cycle 0 19 true (0)
theorem kid10_part256_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part256) = true := by rfl

def kid10_part257 : Audit := .cycle 1 18 true (1)
theorem kid10_part257_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part257) = true := by rfl

def kid10_part258 : Audit := .cycle 2 17 true (1)
theorem kid10_part258_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part258) = true := by rfl

def kid10_part259 : Audit := .cycle 2 20 true (1)
theorem kid10_part259_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part259) = true := by rfl

def kid10_part260 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 20 9 true (6),
.cycle 3 26 true (1),
.cycle 8 21 true (2),
.cycle 18 13 true (6),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 9 33 true (2),
.cycle 10 19 true (2),
.cycle 17 25 true (5),
.cycle 28 1 true (10),
.last 30 (1,true),
.cycle 7 23 true (2),
.cycle 0 31 true (0),
.cycle 22 7 true (6),
.cycle 17 27 true (5),
.cycle 17 21 true (5),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 2 30 true (1),
.cycle 19 10 true (6),
.cycle 28 1 true (10)
])
theorem kid10_part260_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part260) = true := by rfl

def kid10_part261 : Audit := .split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 30 true (2),
.cycle 0 21 true (0),
.cycle 8 40 true (2),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 18 22 true (6),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.last 20 (1,true),
.cycle 0 25 true (0),
.cycle 2 20 true (1),
.cycle 17 3 true (5),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part261_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part261) = true := by rfl

def kid10_part237 : Audit := .split 18 (5,true) (byMove [(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245),(kid10_part246),(kid10_part247),(kid10_part248),(kid10_part249),(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254),(kid10_part255),(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part259),(kid10_part260),(kid10_part261)])

theorem kid10_part237_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part237) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245),(kid10_part246),(kid10_part247),(kid10_part248),(kid10_part249),(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254),(kid10_part255),(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part259),(kid10_part260),(kid10_part261)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part238_checked

  · exact kid10_part244_checked

  · exact kid10_part250_checked

  · exact kid10_part256_checked

  · exact kid10_part239_checked

  · exact kid10_part245_checked

  · exact kid10_part251_checked

  · exact kid10_part257_checked

  · exact kid10_part240_checked

  · exact kid10_part246_checked

  · exact kid10_part252_checked

  · exact kid10_part258_checked

  · exact kid10_part241_checked

  · exact kid10_part247_checked

  · exact kid10_part253_checked

  · exact kid10_part259_checked

  · exact kid10_part242_checked

  · exact kid10_part248_checked

  · exact kid10_part254_checked

  · exact kid10_part260_checked

  · exact kid10_part243_checked

  · exact kid10_part249_checked

  · exact kid10_part255_checked

  · exact kid10_part261_checked

def kid10_part262 : Audit := .split 19 (1,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 71 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 20, 16, 1, 20, 64, 64],96⟩,
.cycle 0 24 true (0),
.cycle 6 77 true (2),
.split 20 (5,true) (byMove [
.cycle 2 31 true (1),
.last 22 (5,false),
.cycle 0 25 true (0),
.cycle 7 17 true (2),
.cycle 43 1 false (1),
.last 22 (5,false),
.cycle 0 24 true (0),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 1, 8, 64],96⟩,
.last 21 (5,false),
.cycle 6 77 true (2),
.last 22 (5,false),
.cycle 7 23 true (2),
.cycle 0 25 true (0),
.cycle 83 1 false (11),
.last 22 (5,false),
.cycle 0 24 true (0),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.cycle 38 12 true (8),
.last 21 (5,false)
]),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 34 10 true (8),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 32 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (2),
.last 30 (5,false),
.last 38 (5,false),
.last 21 (5,false),
.last 23 (5,false),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 42 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 32 (5,false),
.last 21 (5,false)
]),
.cycle 6 19 true (2),
.cycle 34 7 false (2),
.cycle 16 4 true (4),
.cycle 5 15 true (1),
.cycle 15 6 true (3),
.split 20 (5,true) (byMove [
.cycle 2 23 true (1),
.last 22 (5,false),
.cycle 49 1 false (3),
.cycle 39 1 false (1),
.cycle 2 33 true (1),
.last 22 (5,false),
.cycle 6 15 true (2),
.last 22 (5,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 1, 8, 64],96⟩,
.cycle 2 21 true (1),
.cycle 17 4 true (4),
.last 23 (5,false),
.cycle 15 6 true (3),
.last 22 (5,false),
.cycle 5 35 true (1),
.cycle 5 23 true (1),
.cycle 21 6 true (1),
.last 22 (5,false),
.cycle 6 15 true (2),
.cycle 19 2 true (4),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 6 23 true (2),
.last 23 (5,false)
]),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 6 15 true (2),
.split 20 (5,true) (byMove [
.cycle 2 20 true (1),
.last 22 (5,false),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 6 16 true (2),
.last 24 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 6 15 true (2),
.cycle 19 2 true (5),
.last 25 (5,false),
.cycle 2 21 true (1),
.last 27 (5,false),
.last 24 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 32 (5,false),
.last 21 (5,false)
])
])
theorem kid10_part262_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part262) = true := by rfl

def kid10_part263 : Audit := .cycle 7 15 true (2)
theorem kid10_part263_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part263) = true := by rfl

def kid10_part264 : Audit := .cycle 2 19 true (1)
theorem kid10_part264_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part264) = true := by rfl

def kid10_part265 : Audit := .cycle 4 19 true (1)
theorem kid10_part265_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part265) = true := by rfl

def kid10_part266 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 64, 64],[4, 64, 16, 1, 16, 64, 64],96⟩
theorem kid10_part266_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part266) = true := by rfl

def kid10_part268 : Audit := .cycle 2 21 true (1)
theorem kid10_part268_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part268) = true := by rfl

def kid10_part269 : Audit := .split 19 (1,true) (byMove [
.cycle 2 23 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 59 1 false (1),
.cycle 34 1 false (2),
.cycle 0 35 true (0),
.cycle 2 21 true (1),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 30 1 false (2),
.cycle 0 27 true (0),
.cycle 2 23 true (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 2 29 true (1),
.cycle 28 1 false (0),
.cycle 0 29 true (0),
.last 26 (5,true),
.cycle 2 21 true (1),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 4 23 true (1),
.cycle 0 27 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part269_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part269) = true := by rfl

def kid10_part270 : Audit := .cycle 41 1 false (3)
theorem kid10_part270_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part270) = true := by rfl

def kid10_part271 : Audit := .split 21 (1,true) (byMove [
.cycle 0 25 true (0),
.cycle 1 35 true (1),
.cycle 49 1 false (3),
.cycle 0 26 true (0),
.cycle 53 1 false (1),
.last 22 (5,true),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 0 46 true (0),
.cycle 0 23 true (0),
.cycle 8 19 true (2),
.last 22 (5,true),
.cycle 6 23 true (2),
.cycle 16 8 true (3),
.cycle 39 1 false (1),
.cycle 5 17 true (1),
.cycle 67 1 false (3),
.last 22 (5,true),
.cycle 2 21 true (1),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid10_part271_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part271) = true := by rfl

def kid10_part272 : Audit := .split 25 (1,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 43 true (1),
.cycle 76 1 false (12),
.cycle 0 30 true (0),
.cycle 0 38 true (0),
.last 26 (5,true),
.cycle 2 25 true (1),
.cycle 1 26 true (1),
.cycle 0 52 true (0),
.cycle 0 27 true (0),
.cycle 8 27 true (1),
.last 26 (5,true),
.cycle 6 31 true (1),
.cycle 16 12 true (1),
.cycle 2 31 true (1),
.cycle 5 21 true (1),
.cycle 5 25 true (1),
.last 26 (5,true),
.cycle 2 25 true (1),
.cycle 1 26 true (1),
.cycle 2 48 true (1),
.cycle 0 27 true (0),
.last 27 (5,true),
.last 26 (5,true)
])
theorem kid10_part272_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part272) = true := by rfl

def kid10_part273 : Audit := .split 19 (5,true) (byMove [
.cycle 2 23 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 59 1 false (1),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.last 21 (1,true),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 30 1 false (2),
.cycle 31 1 false (3),
.cycle 25 1 false (1),
.last 21 (1,true),
.last 52 (1,true),
.last 23 (1,true),
.cycle 28 1 false (0),
.cycle 35 1 false (3),
.cycle 23 1 false (-1),
.last 21 (1,true),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 4 23 true (1),
.cycle 0 29 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part273_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part273) = true := by rfl

def kid10_part274 : Audit := .cycle 6 13 true (2)
theorem kid10_part274_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part274) = true := by rfl

def kid10_part275 : Audit := .split 19 (1,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 8, 8, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 8, 8, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.last 20 (5,true),
.cycle 6 23 true (2),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 4 23 true (1),
.far true 1 ⟨0,[0, 0],[40, 8, 8, 8, 8, 8, 64],[8, 16, 8, 8, 32, 64, 64],64⟩,
.cycle 18 2 true (4),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part275_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part275) = true := by rfl

def kid10_part276 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 4, 128, 256, 8, 256, 4, 4, 4096],[256, 4096, 16, 1, 16, 4096, 256, 4096, 16, 1, 4096, 4096, 4096],4096⟩
theorem kid10_part276_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part276) = true := by rfl

def kid10_part277 : Audit := .cycle 2 19 true (1)
theorem kid10_part277_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part277) = true := by rfl

def kid10_part278 : Audit := .cycle 17 2 true (4)
theorem kid10_part278_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part278) = true := by rfl

def kid10_part279 : Audit := .split 19 (5,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 23 1 true (5),
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 32, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 32, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 21 1 true (7),
.last 21 (1,true),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 4 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 32, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 18 2 true (4),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 19 2 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part279_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part279) = true := by rfl

def kid10_part280 : Audit := .cycle 15 4 true (3)
theorem kid10_part280_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part280) = true := by rfl

def kid10_part281 : Audit := .split 19 (1,true) (byMove [
.cycle 5 23 true (1),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.cycle 62 1 false (2),
.cycle 5 17 true (1),
.last 34 (5,true),
.cycle 6 19 true (2),
.cycle 1 22 true (1),
.cycle 16 8 true (3),
.cycle 5 15 true (1),
.cycle 34 7 false (2),
.last 20 (5,true),
.cycle 33 7 false (2),
.cycle 30 5 false (1),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 38 9 false (0),
.last 26 (5,true),
.cycle 6 19 true (2),
.cycle 1 22 true (1),
.cycle 16 4 true (3),
.cycle 5 15 true (1),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part281_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part281) = true := by rfl

def kid10_part282 : Audit := .cycle 5 27 true (1)
theorem kid10_part282_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part282) = true := by rfl

def kid10_part283 : Audit := .cycle 5 19 true (1)
theorem kid10_part283_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part283) = true := by rfl

def kid10_part284 : Audit := .cycle 19 4 true (1)
theorem kid10_part284_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part284) = true := by rfl

def kid10_part285 : Audit := .split 19 (5,true) (byMove [
.cycle 5 23 true (1),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.cycle 32 1 false (0),
.cycle 5 17 true (1),
.cycle 23 1 false (-1),
.cycle 6 19 true (2),
.last 20 (1,true),
.cycle 29 1 false (1),
.cycle 5 15 true (1),
.cycle 26 1 false (0),
.cycle 38 1 false (8),
.last 21 (1,true),
.last 30 (1,true),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 30 1 false (0),
.cycle 23 1 false (-1),
.cycle 6 19 true (2),
.last 20 (1,true),
.cycle 16 4 true (3),
.cycle 5 15 true (1),
.cycle 19 2 true (3),
.cycle 21 3 true (5)
])
theorem kid10_part285_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part285) = true := by rfl

def kid10_part286 : Audit := .cycle 6 13 true (2)
theorem kid10_part286_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part286) = true := by rfl

def kid10_part287 : Audit := .split 19 (1,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 71 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 4, 8, 8, 32, 64, 64],64⟩,
.cycle 0 24 true (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 34 10 true (8),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.last 20 (5,true),
.cycle 6 19 true (2),
.cycle 34 7 false (2),
.cycle 16 4 true (4),
.cycle 5 15 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part287_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part287) = true := by rfl

def kid10_part288 : Audit := .cycle 7 15 true (2)
theorem kid10_part288_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part288) = true := by rfl

def kid10_part289 : Audit := .cycle 2 19 true (1)
theorem kid10_part289_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part289) = true := by rfl

def kid10_part290 : Audit := .split 20 (5,true) (byMove [
.cycle 2 23 true (1),
.last 21 (1,true),
.cycle 49 1 false (3),
.last 23 (1,true),
.last 29 (1,true),
.cycle 2 25 true (1),
.cycle 6 15 true (2),
.last 21 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 2 21 true (1),
.cycle 17 4 true (4),
.cycle 21 14 true (5),
.cycle 15 6 true (3),
.last 21 (1,true),
.cycle 5 35 true (1),
.cycle 5 23 true (1),
.cycle 21 6 true (1),
.cycle 28 3 false (0),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 19 2 true (4),
.cycle 21 14 true (5)
])
theorem kid10_part290_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part290) = true := by rfl

def kid10_part291 : Audit := .split 19 (5,true) (byMove [
.cycle 0 23 true (0),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 32, 64],[4, 64, 16, 1, 20, 20, 64],64⟩,
.last 22 (1,true),
.last 26 (1,true),
.cycle 31 1 true (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 34 10 true (8),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.cycle 21 1 true (7),
.cycle 6 19 true (2),
.last 20 (1,true),
.cycle 16 4 true (4),
.cycle 5 15 true (1),
.cycle 37 3 false (1),
.cycle 27 3 false (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 19 2 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part291_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part291) = true := by rfl

def kid10_part267 : Audit := .split 18 (5,false) (byMove [(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291)])

theorem kid10_part267_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part267) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part268_checked

  · exact kid10_part274_checked

  · exact kid10_part280_checked

  · exact kid10_part286_checked

  · exact kid10_part269_checked

  · exact kid10_part275_checked

  · exact kid10_part281_checked

  · exact kid10_part287_checked

  · exact kid10_part270_checked

  · exact kid10_part276_checked

  · exact kid10_part282_checked

  · exact kid10_part288_checked

  · exact kid10_part271_checked

  · exact kid10_part277_checked

  · exact kid10_part283_checked

  · exact kid10_part289_checked

  · exact kid10_part272_checked

  · exact kid10_part278_checked

  · exact kid10_part284_checked

  · exact kid10_part290_checked

  · exact kid10_part273_checked

  · exact kid10_part279_checked

  · exact kid10_part285_checked

  · exact kid10_part291_checked

def kid10_part292 : Audit := .cycle 2 17 true (1)
theorem kid10_part292_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part292) = true := by rfl

def kid10_part293 : Audit := .split 18 (1,true) (byMove [
.cycle 2 18 true (1),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[4, 22, 16, 1, 2, 64, 64],96⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 1 26 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 8, 8, 64],96⟩,
.last 20 (5,false),
.cycle 6 17 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far true 1 ⟨0,[0, 0],[24, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 24, 16, 64],96⟩,
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.last 20 (5,false)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 26 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 1 26 true (1),
.last 32 (5,true),
.cycle 19 1 true (7),
.cycle 18 3 true (6),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 34 (5,true),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.cycle 19 1 true (7)
]),
.cycle 6 13 true (2),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 17 2 true (5),
.split 19 (5,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 1 26 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 2 19 true (1),
.last 21 (5,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 8, 8, 64],96⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 21 (5,false),
.cycle 15 8 true (3),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.last 20 (5,false),
.cycle 2 19 true (1),
.cycle 18 2 true (5),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 21 (5,false)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 1 27 true (1),
.split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.cycle 18 2 true (6),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 27 true (1),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 17 3 true (5),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 1 28 true (1),
.cycle 19 1 true (7)
])
])
theorem kid10_part293_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part293) = true := by rfl

def kid10_part294 : Audit := .cycle 7 11 true (2)
theorem kid10_part294_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part294) = true := by rfl

def kid10_part295 : Audit := .cycle 0 19 true (0)
theorem kid10_part295_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part295) = true := by rfl

def kid10_part296 : Audit := .cycle 18 9 true (6)
theorem kid10_part296_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part296) = true := by rfl

def kid10_part298 : Audit := .cycle 2 18 true (1)
theorem kid10_part298_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part298) = true := by rfl

def kid10_part299 : Audit := .split 19 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.last 29 (5,false),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.last 27 (5,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 67109120, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 536870912, 256, 1073741824, 128, 256, 32768, 256, 16384, 1073741824, 1073741824],[256, 16, 16, 1, 2048, 32768, 256, 65536, 65536, 4096, 2048, 1097732, 67108864, 4194304, 4194304, 262144, 536870912, 32768, 256, 1024, 1024, 64, 2048, 32768, 256, 65536, 65536, 4096, 2048, 256, 1073741824],1889684512⟩,
.last 20 (5,false),
.cycle 6 16 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 67109120, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 536870912, 256, 1073741824, 128, 256, 32768, 256, 16384, 1073741824, 1073741824],[256, 16, 16, 1, 2048, 32768, 256, 1680982796, 65536, 4096, 2048, 1680982796, 67108864, 4194304, 4194304, 262144, 536870912, 32768, 256, 1024, 1024, 64, 2048, 32768, 256, 256, 65536, 4096, 2048, 256, 1073741824],1889684512⟩,
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.last 29 (5,false),
.last 20 (5,false)
])
theorem kid10_part299_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part299) = true := by rfl

def kid10_part300 : Audit := .far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 67109120, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 536870912, 256, 1073741824, 128, 256, 32768, 256, 16384, 1073741824, 1073741824],[256, 1073741824, 16, 1, 2048, 0, 256, 1073741824, 65536, 4096, 2048, 68174084, 67108864, 1073741824, 4194304, 262144, 536870912, 65536, 256, 1073741824, 1024, 64, 2048, 536870912, 256, 1073741824, 65536, 4096, 2048, 256, 1073741824],1889684512⟩
theorem kid10_part300_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part300) = true := by rfl

def kid10_part301 : Audit := .cycle 0 20 true (0)
theorem kid10_part301_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part301) = true := by rfl

def kid10_part302 : Audit := .split 20 (5,false) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 4, 61, 64],[4, 64, 16, 1, 32, 61, 64],64⟩,
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 19 11 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 19 9 true (5),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 19 3 true (5),
.cycle 2 21 true (1),
.cycle 17 4 true (5),
.cycle 0 25 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 19 10 true (5),
.cycle 20 1 true (6)
])
theorem kid10_part302_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part302) = true := by rfl

def kid10_part303 : Audit := .split 20 (5,false) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 40 1 false (4),
.cycle 0 22 true (0),
.cycle 20 2 true (3),
.cycle 25 1 false (-1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 20 9 true (3),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 20 1 true (4),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 20 3 true (3),
.cycle 2 21 true (1),
.cycle 49 1 false (3),
.cycle 25 1 false (-1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 20 10 true (4),
.cycle 20 1 true (4)
])
theorem kid10_part303_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part303) = true := by rfl

def kid10_part304 : Audit := .cycle 0 19 true (0)
theorem kid10_part304_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part304) = true := by rfl

def kid10_part305 : Audit := .cycle 1 18 true (1)
theorem kid10_part305_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part305) = true := by rfl

def kid10_part306 : Audit := .split 27 (5,false) (byMove [
.cycle 2 27 true (1),
.last 28 (1,true),
.cycle 28 13 true (6),
.cycle 0 29 true (0),
.cycle 26 2 true (8),
.cycle 9 20 true (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 19 9 true (5),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 27 1 true (9),
.cycle 6 22 true (2),
.last 28 (1,true),
.cycle 25 3 true (7),
.cycle 2 28 true (1),
.cycle 17 11 true (5),
.cycle 16 46 true (4),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 2 29 true (1),
.cycle 19 10 true (5),
.cycle 27 1 true (9)
])
theorem kid10_part306_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part306) = true := by rfl

def kid10_part307 : Audit := .cycle 3 16 true (1)
theorem kid10_part307_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part307) = true := by rfl

def kid10_part308 : Audit := .cycle 8 11 true (2)
theorem kid10_part308_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part308) = true := by rfl

def kid10_part309 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 28 2 true (8),
.cycle 31 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 19 1 true (7),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 48, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 54 1 false (10),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part309_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part309) = true := by rfl

def kid10_part310 : Audit := .cycle 6 13 true (2)
theorem kid10_part310_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part310) = true := by rfl

def kid10_part311 : Audit := .split 19 (1,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.last 27 (5,false),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.far true 5 ⟨0,[0, 1, 2, 3, 4, 1, 4, 1, 4, 4],[0, 0, 2097152, 512, 512, 1073741824, 1073741824, 0, 1073741824, 2097152, 512, 1073741824, 0, 1073741824, 512, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1073741824, 512, 1073741824, 1073741824, 1073741824, 1073741824, 1210056704, 134217728, 1210057216, 1073741824, 1073741824],[0, 512, 2097152, 0, 1073741824, 128, 0, 512, 1073741824, 1073741824, 512, 524288, 1073741824, 1073741824, 2097152, 1073741824, 1073741824, 128, 1073741824, 1073741824, 2097152, 0, 1073741824, 128, 1073741824, 1210057216, 1210057216, 1073741824, 1210057216, 33554432, 1073741824],2011113824⟩,
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 7 15 true (2),
.last 25 (5,false),
.last 23 (5,false),
.cycle 2 21 true (1),
.last 25 (5,false),
.last 23 (5,false),
.last 20 (5,false),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 18 2 true (5)
])
theorem kid10_part311_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part311) = true := by rfl

def kid10_part312 : Audit := .split 21 (5,false) (byMove [
.cycle 2 21 true (1),
.last 22 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 4, 53, 64],[4, 64, 16, 1, 32, 33, 64],64⟩,
.cycle 0 23 true (0),
.cycle 20 2 true (6),
.cycle 0 25 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 19 9 true (5),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.cycle 21 1 true (7),
.cycle 6 16 true (2),
.last 22 (1,true),
.cycle 19 3 true (5),
.cycle 2 22 true (1),
.cycle 17 5 true (5),
.cycle 2 24 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 19 10 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part312_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part312) = true := by rfl

def kid10_part313 : Audit := .cycle 2 19 true (1)
theorem kid10_part313_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part313) = true := by rfl

def kid10_part314 : Audit := .cycle 17 2 true (5)
theorem kid10_part314_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part314) = true := by rfl

def kid10_part315 : Audit := .split 20 (5,false) (byMove [
.cycle 2 23 true (1),
.last 21 (1,true),
.cycle 53 1 false (3),
.last 23 (1,true),
.cycle 20 2 true (3),
.cycle 25 1 false (-1),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 21 9 true (5),
.cycle 2 21 true (1),
.cycle 17 4 true (4),
.cycle 19 2 true (4),
.cycle 15 6 true (3),
.last 21 (1,true),
.cycle 29 3 true (5),
.cycle 2 26 true (1),
.cycle 21 6 true (1),
.cycle 25 1 false (-1),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 2 22 true (1),
.cycle 2 21 true (1),
.cycle 34 5 false (2),
.cycle 29 3 false (1)
])
theorem kid10_part315_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part315) = true := by rfl

def kid10_part316 : Audit := .cycle 0 19 true (0)
theorem kid10_part316_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part316) = true := by rfl

def kid10_part317 : Audit := .cycle 1 18 true (1)
theorem kid10_part317_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part317) = true := by rfl

def kid10_part318 : Audit := .cycle 2 17 true (1)
theorem kid10_part318_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part318) = true := by rfl

def kid10_part319 : Audit := .cycle 2 20 true (1)
theorem kid10_part319_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part319) = true := by rfl

def kid10_part320 : Audit := .split 28 (5,false) (byMove [
.cycle 2 28 true (1),
.last 29 (1,true),
.cycle 7 37 true (2),
.cycle 0 30 true (0),
.cycle 27 2 true (9),
.cycle 18 11 true (6),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 20 9 true (6),
.cycle 3 26 true (1),
.cycle 8 21 true (2),
.cycle 28 1 true (10),
.cycle 6 23 true (2),
.last 29 (1,true),
.cycle 26 3 true (8),
.cycle 2 29 true (1),
.cycle 17 12 true (5),
.cycle 27 3 true (9),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 2 30 true (1),
.cycle 19 10 true (6),
.cycle 28 1 true (10)
])
theorem kid10_part320_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part320) = true := by rfl

def kid10_part321 : Audit := .split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 19 2 true (6),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 19 9 true (6),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.last 20 (1,true),
.cycle 19 3 true (6),
.cycle 2 20 true (1),
.cycle 17 3 true (5),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part321_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part321) = true := by rfl

def kid10_part297 : Audit := .split 18 (5,true) (byMove [(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320),(kid10_part321)])

theorem kid10_part297_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part297) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320),(kid10_part321)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part298_checked

  · exact kid10_part304_checked

  · exact kid10_part310_checked

  · exact kid10_part316_checked

  · exact kid10_part299_checked

  · exact kid10_part305_checked

  · exact kid10_part311_checked

  · exact kid10_part317_checked

  · exact kid10_part300_checked

  · exact kid10_part306_checked

  · exact kid10_part312_checked

  · exact kid10_part318_checked

  · exact kid10_part301_checked

  · exact kid10_part307_checked

  · exact kid10_part313_checked

  · exact kid10_part319_checked

  · exact kid10_part302_checked

  · exact kid10_part308_checked

  · exact kid10_part314_checked

  · exact kid10_part320_checked

  · exact kid10_part303_checked

  · exact kid10_part309_checked

  · exact kid10_part315_checked

  · exact kid10_part321_checked

def kid10_part201 : Audit := .split 17 (4,true) (byMove [(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295),(kid10_part296),(kid10_part297)])

theorem kid10_part201_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid10_part201) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295),(kid10_part296),(kid10_part297)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part202_checked

  · exact kid10_part232_checked

  · exact kid10_part262_checked

  · exact kid10_part292_checked

  · exact kid10_part203_checked

  · exact kid10_part233_checked

  · exact kid10_part263_checked

  · exact kid10_part293_checked

  · exact kid10_part204_checked

  · exact kid10_part234_checked

  · exact kid10_part264_checked

  · exact kid10_part294_checked

  · exact kid10_part205_checked

  · exact kid10_part235_checked

  · exact kid10_part265_checked

  · exact kid10_part295_checked

  · exact kid10_part206_checked

  · exact kid10_part236_checked

  · exact kid10_part266_checked

  · exact kid10_part296_checked

  · exact kid10_part207_checked

  · exact kid10_part237_checked

  · exact kid10_part267_checked

  · exact kid10_part297_checked

def kid10_part323 : Audit := .cycle 0 16 true (0)
theorem kid10_part323_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part323) = true := by rfl

def kid10_part324 : Audit := .cycle 1 15 true (1)
theorem kid10_part324_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part324) = true := by rfl

def kid10_part325 : Audit := .cycle 2 14 true (1)
theorem kid10_part325_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part325) = true := by rfl

def kid10_part326 : Audit := .cycle 2 17 true (1)
theorem kid10_part326_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part326) = true := by rfl

def kid10_part327 : Audit := .cycle 3 14 true (1)
theorem kid10_part327_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part327) = true := by rfl

def kid10_part328 : Audit := .split 16 (5,false) (byMove [
.cycle 2 16 true (1),
.split 17 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (3)
]),
.cycle 31 1 false (3),
.cycle 0 18 true (0),
.cycle 37 1 false (1),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 23 1 false (1),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 21 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.cycle 8 9 true (2),
.cycle 16 1 true (4),
.cycle 6 11 true (2),
.split 17 (1,true) (byMove [
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 29 1 false (1),
.cycle 0 23 true (0),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.cycle 49 1 false (9),
.cycle 0 19 true (0),
.cycle 7 14 true (2),
.last 18 (5,true),
.cycle 31 7 false (2),
.cycle 28 5 false (1),
.cycle 2 19 true (1),
.cycle 26 1 false (0),
.cycle 2 19 true (1),
.last 24 (5,true),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true)
]),
.cycle 0 22 true (0),
.cycle 2 17 true (1),
.split 22 (1,true) (byMove [
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.cycle 43 1 false (3),
.cycle 0 24 true (0),
.cycle 0 27 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 9 15 true (1),
.cycle 3 20 true (1),
.cycle 8 15 true (1),
.cycle 0 26 true (0),
.cycle 6 17 true (1),
.cycle 28 11 false (2),
.cycle 0 28 true (0),
.cycle 2 23 true (1),
.cycle 17 6 true (1),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 2 24 true (1),
.cycle 3 21 true (1),
.last 25 (5,true)
]),
.split 17 (5,true) (byMove [
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 49 1 false (9),
.cycle 0 19 true (0),
.cycle 24 1 false (0),
.cycle 30 1 false (6),
.last 19 (1,true),
.last 28 (1,true),
.cycle 2 19 true (1),
.cycle 26 1 false (0),
.cycle 2 19 true (1),
.cycle 21 1 false (-1),
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 3 18 true (1),
.cycle 16 3 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (4)
])
theorem kid10_part328_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part328) = true := by rfl

def kid10_part329 : Audit := .cycle 0 16 true (0)
theorem kid10_part329_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part329) = true := by rfl

def kid10_part330 : Audit := .cycle 1 15 true (1)
theorem kid10_part330_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part330) = true := by rfl

def kid10_part331 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 64, 64],[4, 64, 16, 1, 4, 64, 64],96⟩
theorem kid10_part331_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part331) = true := by rfl

def kid10_part332 : Audit := .cycle 9 7 true (2)
theorem kid10_part332_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part332) = true := by rfl

def kid10_part333 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 64, 64],[4, 64, 16, 1, 16, 64, 64],96⟩
theorem kid10_part333_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part333) = true := by rfl

def kid10_part334 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.cycle 8 9 true (2),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (1),
.cycle 37 1 false (1),
.cycle 33 1 false (1),
.cycle 23 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 54 1 false (4),
.cycle 19 9 true (0),
.cycle 39 1 false (3),
.cycle 25 1 false (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 30 1 false (0),
.cycle 0 22 true (0),
.cycle 23 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 3 18 true (1),
.cycle 18 2 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.split 27 (5,true) (byMove [
.cycle 7 23 true (2),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 8 29 true (2),
.cycle 0 31 true (0),
.cycle 2 27 true (1),
.last 28 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 29 (1,true),
.cycle 14 15 true (3),
.cycle 2 29 true (1),
.cycle 10 25 true (2),
.cycle 2 29 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 27 true (1),
.last 28 (1,true),
.cycle 7 21 true (2),
.cycle 0 29 true (0),
.cycle 3 38 true (1),
.cycle 9 22 true (2)
]),
.split 25 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 9 18 true (2),
.cycle 3 23 true (1),
.cycle 8 18 true (2),
.cycle 9 18 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 8, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 17 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 8, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 27 (1,true),
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 2 27 true (1),
.cycle 3 24 true (1),
.cycle 3 24 true (1)
]),
.split 27 (5,true) (byMove [
.cycle 7 23 true (2),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 8 29 true (2),
.cycle 0 31 true (0),
.cycle 2 27 true (1),
.last 28 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 16, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 29 (1,true),
.cycle 14 15 true (3),
.cycle 2 29 true (1),
.cycle 10 25 true (2),
.cycle 2 29 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 8, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 2 27 true (1),
.last 28 (1,true),
.cycle 7 21 true (2),
.cycle 0 29 true (0),
.cycle 3 38 true (1),
.cycle 8 22 true (2)
]),
.cycle 16 1 true (6),
.split 18 (1,true) (byMove [
.cycle 2 18 true (1),
.cycle 1 19 true (1),
.last 29 (5,true),
.cycle 0 20 true (0),
.cycle 15 4 true (5),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 16 3 true (5),
.cycle 6 13 true (2),
.cycle 14 7 true (4),
.cycle 14 5 true (4),
.cycle 2 19 true (1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.cycle 6 14 true (2)
]),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 10 7 true (2),
.cycle 0 19 true (0),
.split 19 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 5 17 true (1),
.cycle 60 1 false (4),
.last 108 (1,true),
.cycle 60 1 false (4),
.cycle 23 1 false (-1),
.cycle 13 7 true (3),
.last 20 (1,true),
.cycle 81 1 false (13),
.cycle 5 15 true (1),
.cycle 38 1 false (8),
.cycle 38 1 false (8),
.last 21 (1,true),
.cycle 14 11 true (2),
.cycle 12 9 true (2),
.cycle 51 1 false (3),
.cycle 12 9 true (2),
.cycle 23 1 false (-1),
.cycle 13 7 true (3),
.last 20 (1,true),
.cycle 2 21 true (1),
.cycle 5 15 true (1),
.cycle 3 26 true (1),
.cycle 21 3 true (5)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (6)
])
theorem kid10_part334_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part334) = true := by rfl

def kid10_part335 : Audit := .split 17 (1,true) (byMove [
.cycle 2 17 true (1),
.cycle 1 19 true (1),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 6 13 true (2),
.split 18 (5,true) (byMove [
.cycle 2 18 true (1),
.last 20 (5,false),
.cycle 35 1 false (3),
.cycle 0 20 true (0),
.cycle 45 1 false (1),
.last 20 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.last 19 (5,false),
.cycle 6 13 true (2),
.last 20 (5,false),
.cycle 0 26 true (0),
.cycle 2 19 true (1),
.cycle 0 30 true (0),
.last 20 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.last 19 (5,false)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.split 18 (5,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (5,true),
.cycle 9 10 true (2),
.last 30 (5,true),
.cycle 18 1 true (6),
.cycle 16 3 true (4),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 0 21 true (0),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.cycle 18 1 true (6)
]),
.cycle 6 12 true (2),
.cycle 32 7 false (2),
.cycle 14 4 true (4),
.cycle 2 18 true (1),
.cycle 13 6 true (3),
.split 18 (5,true) (byMove [
.cycle 0 22 true (0),
.last 20 (5,false),
.cycle 0 22 true (0),
.cycle 37 1 false (1),
.cycle 38 1 false (0),
.last 20 (5,false),
.cycle 2 18 true (1),
.last 20 (5,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 64, 64],[8, 32, 8, 8, 1, 8, 64],96⟩,
.cycle 0 20 true (0),
.cycle 15 4 true (4),
.last 20 (5,false),
.cycle 13 6 true (3),
.last 20 (5,false),
.cycle 5 20 true (1),
.cycle 5 14 true (1),
.cycle 12 12 true (1),
.last 20 (5,false),
.cycle 2 18 true (1),
.cycle 17 2 true (4),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 6 14 true (2),
.last 20 (5,false)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.split 18 (5,false) (byMove [
.cycle 2 18 true (1),
.cycle 17 2 true (5),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 6 14 true (2),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 18 1 true (6),
.cycle 6 13 true (2),
.last 20 (5,true),
.cycle 14 5 true (4),
.cycle 2 19 true (1),
.cycle 13 7 true (3),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.cycle 18 1 true (6)
])
])
theorem kid10_part335_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part335) = true := by rfl

def kid10_part336 : Audit := .cycle 7 10 true (2)
theorem kid10_part336_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part336) = true := by rfl

def kid10_part337 : Audit := .cycle 0 18 true (0)
theorem kid10_part337_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part337) = true := by rfl

def kid10_part338 : Audit := .cycle 4 12 true (1)
theorem kid10_part338_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part338) = true := by rfl

def kid10_part339 : Audit := .cycle 0 18 true (0)
theorem kid10_part339_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part339) = true := by rfl

def kid10_part341 : Audit := .cycle 0 20 true (0)
theorem kid10_part341_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part341) = true := by rfl

def kid10_part342 : Audit := .split 17 (1,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 0 28 true (0),
.cycle 0 20 true (0),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 0 20 true (0),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.cycle 0 28 true (0),
.cycle 26 1 false (0),
.cycle 2 26 true (1),
.last 24 (5,true),
.cycle 0 20 true (0),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (3)
])
theorem kid10_part342_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part342) = true := by rfl

def kid10_part343 : Audit := .cycle 0 20 true (0)
theorem kid10_part343_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part343) = true := by rfl

def kid10_part344 : Audit := .split 19 (1,true) (byMove [
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 55 1 false (9),
.cycle 0 21 true (0),
.cycle 0 29 true (0),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 12 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 2 22 true (1),
.cycle 6 14 true (2),
.cycle 14 8 true (3),
.cycle 37 1 false (1),
.cycle 2 20 true (1),
.cycle 65 1 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 3 18 true (1),
.cycle 0 22 true (0)
])
theorem kid10_part344_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part344) = true := by rfl

def kid10_part345 : Audit := .cycle 30 1 false (0)
theorem kid10_part345_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part345) = true := by rfl

def kid10_part346 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 0 20 true (0),
.cycle 23 1 false (1),
.last 19 (1,true),
.cycle 0 22 true (0),
.last 21 (1,true),
.cycle 26 1 false (0),
.last 21 (1,true),
.cycle 21 1 false (-1),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (3)
])
theorem kid10_part346_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part346) = true := by rfl

def kid10_part347 : Audit := .cycle 2 16 true (1)
theorem kid10_part347_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part347) = true := by rfl

def kid10_part348 : Audit := .split 17 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 8, 8, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 9 9 true (2),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 8, 8, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 1 18 true (1)
])
theorem kid10_part348_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part348) = true := by rfl

def kid10_part349 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 256, 8, 4, 4096],[256, 4096, 16, 1, 16, 4096, 256, 4096, 16, 1, 4096, 4096, 4096],4096⟩
theorem kid10_part349_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part349) = true := by rfl

def kid10_part350 : Audit := .cycle 0 18 true (0)
theorem kid10_part350_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part350) = true := by rfl

def kid10_part351 : Audit := .cycle 15 2 true (4)
theorem kid10_part351_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part351) = true := by rfl

def kid10_part352 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 32, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 9 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 32, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 18 1 true (6),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (6)
])
theorem kid10_part352_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part352) = true := by rfl

def kid10_part353 : Audit := .cycle 13 4 true (3)
theorem kid10_part353_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part353) = true := by rfl

def kid10_part354 : Audit := .split 17 (1,true) (byMove [
.cycle 2 26 true (1),
.cycle 2 20 true (1),
.cycle 29 1 false (1),
.cycle 53 1 false (1),
.cycle 29 1 false (1),
.cycle 2 22 true (1),
.cycle 6 12 true (2),
.cycle 1 19 true (1),
.cycle 14 8 true (3),
.cycle 2 18 true (1),
.cycle 32 7 false (2),
.last 18 (5,true),
.cycle 31 7 false (2),
.cycle 28 5 false (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.last 24 (5,true),
.cycle 6 12 true (2),
.cycle 1 19 true (1),
.cycle 14 4 true (3),
.cycle 2 18 true (1),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid10_part354_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part354) = true := by rfl

def kid10_part355 : Audit := .cycle 5 16 true (1)
theorem kid10_part355_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part355) = true := by rfl

def kid10_part356 : Audit := .cycle 5 12 true (1)
theorem kid10_part356_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part356) = true := by rfl

def kid10_part357 : Audit := .cycle 12 8 true (1)
theorem kid10_part357_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part357) = true := by rfl

def kid10_part358 : Audit := .split 17 (5,true) (byMove [
.cycle 2 26 true (1),
.cycle 2 20 true (1),
.cycle 29 1 false (1),
.cycle 53 1 false (1),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 6 12 true (2),
.last 18 (1,true),
.cycle 27 1 false (1),
.cycle 2 18 true (1),
.cycle 24 1 false (0),
.cycle 33 1 false (7),
.last 19 (1,true),
.last 28 (1,true),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.cycle 21 1 false (-1),
.cycle 6 12 true (2),
.last 18 (1,true),
.cycle 14 4 true (3),
.cycle 2 18 true (1),
.cycle 17 2 true (3),
.cycle 18 3 true (4)
])
theorem kid10_part358_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part358) = true := by rfl

def kid10_part359 : Audit := .cycle 2 16 true (1)
theorem kid10_part359_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part359) = true := by rfl

def kid10_part360 : Audit := .split 17 (1,true) (byMove [
.cycle 2 17 true (1),
.cycle 1 19 true (1),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 1 18 true (1),
.cycle 6 12 true (2),
.cycle 32 7 false (2),
.cycle 14 4 true (4),
.cycle 2 18 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 1 18 true (1)
])
theorem kid10_part360_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part360) = true := by rfl

def kid10_part361 : Audit := .cycle 7 10 true (2)
theorem kid10_part361_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part361) = true := by rfl

def kid10_part362 : Audit := .cycle 0 18 true (0)
theorem kid10_part362_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part362) = true := by rfl

def kid10_part363 : Audit := .split 18 (5,true) (byMove [
.cycle 0 22 true (0),
.last 19 (1,true),
.cycle 0 22 true (0),
.last 21 (1,true),
.cycle 38 1 false (0),
.cycle 10 12 true (2),
.cycle 2 18 true (1),
.last 19 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 8, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 0 20 true (0),
.cycle 15 4 true (4),
.cycle 3 19 true (1),
.cycle 13 6 true (3),
.last 19 (1,true),
.cycle 5 20 true (1),
.cycle 5 14 true (1),
.cycle 12 12 true (1),
.cycle 26 3 false (0),
.cycle 2 18 true (1),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 17 2 true (4),
.cycle 3 19 true (1)
])
theorem kid10_part363_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part363) = true := by rfl

def kid10_part364 : Audit := .split 17 (5,true) (byMove [
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 33 1 false (1),
.cycle 20 1 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 18 1 true (6),
.cycle 6 12 true (2),
.last 18 (1,true),
.cycle 14 4 true (4),
.cycle 2 18 true (1),
.cycle 5 16 true (1),
.cycle 25 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (6)
])
theorem kid10_part364_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part364) = true := by rfl

def kid10_part340 : Audit := .split 16 (5,false) (byMove [(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345),(kid10_part346),(kid10_part347),(kid10_part348),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360),(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364)])

theorem kid10_part340_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part340) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) 16 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345),(kid10_part346),(kid10_part347),(kid10_part348),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360),(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part341_checked

  · exact kid10_part347_checked

  · exact kid10_part353_checked

  · exact kid10_part359_checked

  · exact kid10_part342_checked

  · exact kid10_part348_checked

  · exact kid10_part354_checked

  · exact kid10_part360_checked

  · exact kid10_part343_checked

  · exact kid10_part349_checked

  · exact kid10_part355_checked

  · exact kid10_part361_checked

  · exact kid10_part344_checked

  · exact kid10_part350_checked

  · exact kid10_part356_checked

  · exact kid10_part362_checked

  · exact kid10_part345_checked

  · exact kid10_part351_checked

  · exact kid10_part357_checked

  · exact kid10_part363_checked

  · exact kid10_part346_checked

  · exact kid10_part352_checked

  · exact kid10_part358_checked

  · exact kid10_part364_checked

def kid10_part365 : Audit := .cycle 0 16 true (0)
theorem kid10_part365_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part365) = true := by rfl

def kid10_part366 : Audit := .cycle 1 15 true (1)
theorem kid10_part366_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part366) = true := by rfl

def kid10_part367 : Audit := .cycle 2 14 true (1)
theorem kid10_part367_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part367) = true := by rfl

def kid10_part368 : Audit := .cycle 2 17 true (1)
theorem kid10_part368_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part368) = true := by rfl

def kid10_part369 : Audit := .cycle 3 14 true (1)
theorem kid10_part369_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part369) = true := by rfl

def kid10_part370 : Audit := .split 16 (5,false) (byMove [
.cycle 2 16 true (1),
.split 17 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 1 20 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (5,true),
.cycle 9 9 true (2),
.last 27 (5,true),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.last 26 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (5)
]),
.split 27 (5,true) (byMove [
.cycle 2 27 true (1),
.last 28 (1,true),
.cycle 17 11 true (3),
.cycle 0 29 true (0),
.cycle 15 13 true (3),
.cycle 47 1 false (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 9 20 true (2),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 2 27 true (1),
.cycle 6 22 true (2),
.last 28 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 8, 61, 64],[4, 64, 16, 1, 32, 33, 64],64⟩,
.cycle 2 28 true (1),
.cycle 26 2 true (6),
.cycle 2 32 true (1),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 2 29 true (1),
.cycle 3 26 true (1),
.cycle 7 22 true (2)
]),
.cycle 0 18 true (0),
.cycle 15 2 true (5),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 20 true (2),
.cycle 9 9 true (2),
.cycle 8 20 true (2),
.cycle 27 1 false (1),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (5)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 9 9 true (2),
.cycle 3 14 true (1),
.cycle 8 9 true (2),
.cycle 16 1 true (6),
.cycle 6 11 true (2),
.split 17 (1,true) (byMove [
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.cycle 0 23 true (0),
.cycle 10 9 true (2),
.last 27 (5,true),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.last 29 (5,true),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.last 18 (5,true),
.cycle 13 7 true (3),
.cycle 14 5 true (4),
.cycle 2 19 true (1),
.cycle 11 7 true (2),
.cycle 2 19 true (1),
.last 24 (5,true),
.cycle 2 17 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.last 18 (5,true)
]),
.cycle 14 3 true (4),
.cycle 2 17 true (1),
.split 18 (5,true) (byMove [
.cycle 2 18 true (1),
.last 19 (1,true),
.cycle 17 11 true (3),
.cycle 0 20 true (0),
.cycle 15 4 true (5),
.cycle 0 27 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 0 22 true (0),
.cycle 6 13 true (2),
.last 19 (1,true),
.cycle 14 5 true (4),
.cycle 2 19 true (1),
.cycle 17 2 true (5),
.cycle 17 12 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 17 true (1),
.cycle 16 3 true (5)
]),
.split 17 (5,true) (byMove [
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.cycle 0 23 true (0),
.cycle 10 9 true (2),
.cycle 23 1 false (-1),
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 9 33 true (2),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.cycle 45 1 false (9),
.last 19 (1,true),
.cycle 14 5 true (4),
.cycle 2 19 true (1),
.cycle 11 7 true (2),
.cycle 2 19 true (1),
.cycle 23 1 false (-1),
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.cycle 16 3 true (5)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (6)
])
theorem kid10_part370_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part370) = true := by rfl

def kid10_part322 : Audit := .split 15 (4,true) (byMove [(kid10_part323),(kid10_part324),(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339),(kid10_part340),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369),(kid10_part370)])

theorem kid10_part322_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid10_part322) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) 15 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some mv)) (byMove [(kid10_part323),(kid10_part324),(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339),(kid10_part340),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369),(kid10_part370)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part323_checked

  · exact kid10_part329_checked

  · exact kid10_part335_checked

  · exact kid10_part365_checked

  · exact kid10_part324_checked

  · exact kid10_part330_checked

  · exact kid10_part336_checked

  · exact kid10_part366_checked

  · exact kid10_part325_checked

  · exact kid10_part331_checked

  · exact kid10_part337_checked

  · exact kid10_part367_checked

  · exact kid10_part326_checked

  · exact kid10_part332_checked

  · exact kid10_part338_checked

  · exact kid10_part368_checked

  · exact kid10_part327_checked

  · exact kid10_part333_checked

  · exact kid10_part339_checked

  · exact kid10_part369_checked

  · exact kid10_part328_checked

  · exact kid10_part334_checked

  · exact kid10_part340_checked

  · exact kid10_part370_checked

def kid10_part371 : Audit := .cycle 8 1 true (4)
theorem kid10_part371_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid10_part371) = true := by rfl

def kid10_part373 : Audit := .cycle 0 10 true (0)
theorem kid10_part373_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part373) = true := by rfl

def kid10_part374 : Audit := .cycle 1 9 true (1)
theorem kid10_part374_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part374) = true := by rfl

def kid10_part375 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 2 18 true (1),
.cycle 37 1 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 16, 64, 64],64⟩,
.cycle 9 9 true (2),
.split 19 (1,true) (byMove [
.cycle 2 19 true (1),
.cycle 1 21 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 6 15 true (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 2 19 true (1),
.cycle 6 14 true (2),
.cycle 34 7 false (2),
.cycle 16 4 true (4),
.cycle 2 20 true (1),
.cycle 15 6 true (3),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 2 20 true (1),
.cycle 7 14 true (2)
]),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 2 20 true (1),
.cycle 41 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 9 11 true (2),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.cycle 42 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 2 20 true (1),
.cycle 7 30 true (2)
]),
.split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 41 1 false (3),
.cycle 38 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 42 1 false (4),
.cycle 53 1 false (9),
.cycle 43 1 false (3),
.cycle 43 1 false (7),
.last 23 (1,true),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 34 1 false (2),
.cycle 20 2 true (4),
.cycle 38 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 2 23 true (1),
.cycle 2 22 true (1),
.cycle 42 38 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 2 18 true (1),
.split 31 (5,true) (byMove [
.cycle 2 31 true (1),
.last 32 (1,true),
.cycle 19 13 true (3),
.cycle 0 33 true (0),
.cycle 17 15 true (3),
.cycle 55 1 false (3),
.cycle 0 32 true (0),
.cycle 1 31 true (1),
.cycle 10 22 true (2),
.cycle 3 29 true (1),
.cycle 8 24 true (2),
.cycle 2 31 true (1),
.cycle 6 26 true (2),
.last 32 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 53, 32, 53, 64],[4, 64, 16, 1, 32, 33, 64],64⟩,
.cycle 2 32 true (1),
.cycle 30 2 true (6),
.cycle 56 1 false (2),
.cycle 0 32 true (0),
.cycle 1 31 true (1),
.cycle 2 30 true (1),
.cycle 2 33 true (1),
.cycle 2 32 true (1),
.cycle 7 26 true (2)
])
])
theorem kid10_part375_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part375) = true := by rfl

def kid10_part376 : Audit := .cycle 3 7 true (1)
theorem kid10_part376_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part376) = true := by rfl

def kid10_part377 : Audit := .cycle 8 2 true (4)
theorem kid10_part377_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part377) = true := by rfl

def kid10_part378 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 21 (4,true) (byMove [
.cycle 0 38 true (0),
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 0 27 true (0),
.cycle 27 1 false (3),
.cycle 25 1 false (3),
.cycle 0 48 true (0),
.last 22 (1,true),
.cycle 31 1 false (3),
.cycle 0 23 true (0),
.cycle 31 1 false (3),
.cycle 44 1 false (4),
.last 23 (1,true),
.cycle 23 15 true (2),
.cycle 0 54 true (0),
.cycle 37 1 false (5),
.cycle 33 1 false (3),
.cycle 39 1 false (7),
.cycle 2 21 true (0),
.last 22 (1,true),
.cycle 7 15 true (0),
.cycle 0 23 true (0),
.cycle 10 26 true (0),
.cycle 11 20 true (0)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (3),
.cycle 34 1 false (4),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.last 41 (1,true),
.cycle 37 1 false (3),
.cycle 13 7 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.last 21 (1,true),
.cycle 37 1 false (3),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 12 9 true (0),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 7 32 true (0),
.cycle 0 65 true (0),
.cycle 10 11 true (0),
.cycle 11 9 true (0)
]),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.split 14 (1,true) (byMove [
.cycle 2 14 true (1),
.cycle 15 15 false (3),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 22 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 3 12 true (1),
.cycle 22 7 false (3),
.cycle 22 5 false (2),
.cycle 22 9 false (3),
.last 19 (4,true),
.last 16 (4,true),
.cycle 2 15 true (1),
.last 15 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 23 13 false (3),
.cycle 22 11 false (3)
]),
.split 20 (1,true) (byMove [
.cycle 13 9 false (4),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 27 7 false (5),
.cycle 28 7 false (6),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 21 7 false (3),
.last 25 (4,true),
.last 23 (4,true),
.cycle 29 7 false (5),
.cycle 21 1 false (-1),
.last 25 (4,true),
.cycle 21 1 false (-1),
.cycle 2 20 true (0),
.cycle 1 21 true (0),
.cycle 21 7 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 2 true (0)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part378_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part378) = true := by rfl

def kid10_part379 : Audit := .cycle 0 10 true (0)
theorem kid10_part379_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part379) = true := by rfl

def kid10_part380 : Audit := .cycle 1 9 true (1)
theorem kid10_part380_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part380) = true := by rfl

def kid10_part381 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 2 22 true (1),
.cycle 2 32 true (1),
.cycle 2 24 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 256, 32, 4, 4096],[256, 4096, 16, 1, 4, 4096, 256, 4096, 16, 1, 60, 4096, 4096],4096⟩,
.cycle 2 22 true (1),
.cycle 6 14 true (2),
.split 20 (1,true) (byMove [
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 1 37 true (1),
.last 27 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[4, 4, 16, 1, 2, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[4, 4, 16, 1, 2, 64, 64],64⟩,
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 21 (5,true),
.cycle 1 25 true (1),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 33 true (1),
.last 22 (5,true),
.cycle 1 23 true (1),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 21 (5,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 2 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 64, 16, 1, 16, 64, 64],64⟩,
.split 20 (5,true) (byMove [
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.cycle 9 29 true (2),
.cycle 3 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 0 24 true (0),
.cycle 2 20 true (1),
.last 21 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 22 (1,true),
.cycle 9 15 true (2),
.cycle 2 22 true (1),
.cycle 9 25 true (2),
.cycle 20 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 22 12 true (6),
.cycle 9 22 true (2)
]),
.split 21 (1,true) (byMove [
.cycle 2 24 true (1),
.last 32 (5,true),
.last 24 (5,true),
.cycle 0 29 true (0),
.last 26 (5,true),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.cycle 22 10 true (6),
.cycle 2 22 true (1),
.cycle 8 20 true (2),
.last 22 (5,true),
.cycle 6 26 true (2),
.cycle 36 7 false (2),
.cycle 18 4 true (4),
.cycle 2 28 true (1),
.cycle 17 6 true (3),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.cycle 2 24 true (1),
.cycle 2 22 true (1),
.cycle 6 36 true (2),
.last 22 (5,true)
]),
.cycle 7 20 true (2),
.cycle 5 16 true (1),
.cycle 4 26 true (1),
.split 21 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 2 24 true (1),
.cycle 2 38 true (1),
.cycle 2 26 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 256, 32, 4, 4096],[256, 4096, 16, 1, 4, 4, 256, 4096, 16, 1, 20, 40, 4096],4096⟩,
.cycle 2 24 true (1),
.cycle 6 16 true (2),
.last 22 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 2 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 23 (1,true),
.cycle 7 26 true (2),
.cycle 5 18 true (1),
.cycle 4 32 true (1),
.cycle 20 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 4, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 6 16 true (2),
.last 22 (1,true),
.cycle 2 24 true (1),
.cycle 2 22 true (1),
.cycle 19 4 true (4),
.cycle 23 11 true (7)
]),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 4, 128, 256, 8, 256, 32, 4, 4096],[256, 4096, 16, 1, 16, 4096, 256, 4096, 16, 1, 4096, 4096, 4096],4096⟩,
.cycle 6 14 true (2),
.split 20 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 29 true (1),
.last 23 (5,true),
.cycle 0 25 true (0),
.cycle 7 16 true (2),
.last 21 (5,true),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.cycle 1 37 true (1),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 21 (5,true),
.cycle 1 23 true (1),
.cycle 1 29 true (1),
.cycle 1 25 true (1),
.cycle 5 16 true (1),
.cycle 19 2 true (5),
.last 21 (5,true),
.cycle 2 20 true (1),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.last 21 (5,true)
]),
.cycle 2 20 true (1),
.cycle 2 20 true (1),
.cycle 20 12 true (6),
.split 20 (5,true) (byMove [
.cycle 0 24 true (0),
.last 21 (1,true),
.cycle 12 41 true (2),
.last 23 (1,true),
.cycle 40 9 true (10),
.cycle 33 9 true (4),
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 36 9 true (10),
.cycle 0 22 true (0),
.cycle 21 9 true (7),
.cycle 9 13 true (2),
.cycle 21 9 true (5),
.last 21 (1,true),
.cycle 24 9 true (6),
.cycle 5 16 true (1),
.cycle 19 2 true (5),
.cycle 28 9 true (6),
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 21 9 true (7),
.cycle 22 9 true (7)
])
])
theorem kid10_part381_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part381) = true := by rfl

def kid10_part382 : Audit := .split 17 (4,true) (byMove [
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 2 23 true (1),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 3 23 true (1),
.cycle 2 17 true (1),
.split 18 (1,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 26 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 1 26 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[4, 4, 16, 1, 2, 64, 64],64⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[4, 16, 16, 1, 2, 64, 64],64⟩,
.last 30 (5,true),
.cycle 6 15 true (2),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 1 24 true (1),
.last 20 (5,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 1 27 true (1),
.cycle 3 17 true (1)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 0 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 64, 16, 1, 16, 64, 64],64⟩,
.split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 9 18 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 8, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 8, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 9 16 true (2),
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 9 19 true (2),
.cycle 3 17 true (1)
]),
.split 19 (1,true) (byMove [
.cycle 0 23 true (0),
.last 30 (5,true),
.last 22 (5,true),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 34 10 true (8),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.last 20 (5,true),
.cycle 6 19 true (2),
.cycle 34 7 false (2),
.cycle 16 4 true (4),
.cycle 5 15 true (1),
.cycle 15 6 true (3),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 6 15 true (2),
.last 20 (5,true)
]),
.cycle 7 15 true (2),
.cycle 2 19 true (1),
.cycle 4 19 true (1),
.split 19 (5,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 21 (1,true),
.cycle 7 19 true (2),
.cycle 2 21 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (4),
.cycle 2 21 true (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 17 4 true (4),
.cycle 3 19 true (1)
]),
.cycle 2 19 true (1),
.cycle 2 17 true (1),
.split 18 (1,true) (byMove [
.cycle 2 18 true (1),
.cycle 1 19 true (1),
.last 34 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 26 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 1 26 true (1),
.cycle 6 13 true (2),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 17 2 true (5),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 1 27 true (1),
.cycle 3 17 true (1)
]),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 18 9 true (6),
.split 18 (5,true) (byMove [
.cycle 2 18 true (1),
.last 19 (1,true),
.cycle 10 26 true (2),
.cycle 0 20 true (0),
.cycle 3 18 true (1),
.cycle 3 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 3 25 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 3 25 true (1),
.cycle 6 13 true (2),
.last 19 (1,true),
.cycle 3 19 true (1),
.cycle 2 19 true (1),
.cycle 17 2 true (5),
.cycle 2 21 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 3 26 true (1),
.cycle 3 17 true (1)
])
])
theorem kid10_part382_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part382) = true := by rfl

def kid10_part383 : Audit := .cycle 8 2 true (4)
theorem kid10_part383_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part383) = true := by rfl

def kid10_part384 : Audit := .cycle 9 1 true (5)
theorem kid10_part384_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part384) = true := by rfl

def kid10_part386 : Audit := .cycle 2 11 true (1)
theorem kid10_part386_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part386) = true := by rfl

def kid10_part387 : Audit := .cycle 1 12 true (1)
theorem kid10_part387_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part387) = true := by rfl

def kid10_part388 : Audit := .cycle 7 5 true (3)
theorem kid10_part388_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part388) = true := by rfl

def kid10_part389 : Audit := .cycle 0 13 true (0)
theorem kid10_part389_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part389) = true := by rfl

def kid10_part390 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 24 5 false (0),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 24, 64],[4, 24, 16, 1, 4, 64, 64],64⟩,
.cycle 12 7 true (2),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 6 10 true (2),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 12 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 5 true (4),
.cycle 6 8 true (2)
])
theorem kid10_part390_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part390) = true := by rfl

def kid10_part391 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 18 (4,true),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 6 10 true (2),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 12 2 true (3),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 8 5 true (4),
.cycle 6 8 true (2)
])
theorem kid10_part391_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part391) = true := by rfl

def kid10_part392 : Audit := .cycle 0 12 true (0)
theorem kid10_part392_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part392) = true := by rfl

def kid10_part393 : Audit := .cycle 1 11 true (1)
theorem kid10_part393_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part393) = true := by rfl

def kid10_part394 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 8 12 true (4),
.cycle 6 15 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 22 true (3),
.cycle 13 7 true (4),
.cycle 8 12 true (4),
.cycle 9 11 true (4),
.cycle 10 10 true (4),
.cycle 7 14 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 17 4 true (5),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 8 12 true (4),
.cycle 6 15 true (2)
])
theorem kid10_part394_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part394) = true := by rfl

def kid10_part395 : Audit := .cycle 3 9 true (1)
theorem kid10_part395_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part395) = true := by rfl

def kid10_part396 : Audit := .cycle 8 4 true (4)
theorem kid10_part396_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part396) = true := by rfl

def kid10_part397 : Audit := .cycle 9 3 true (4)
theorem kid10_part397_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part397) = true := by rfl

def kid10_part398 : Audit := .cycle 6 6 true (2)
theorem kid10_part398_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part398) = true := by rfl

def kid10_part399 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 30 9 false (2),
.cycle 6 11 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 18 true (3),
.cycle 14 7 true (3),
.cycle 8 8 true (3),
.cycle 9 7 true (3),
.cycle 26 7 false (2),
.cycle 7 10 true (3),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 14 4 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 6 11 true (2)
])
theorem kid10_part399_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part399) = true := by rfl

def kid10_part400 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 20 true (1),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 6 14 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 21, 64],[4, 5, 16, 1, 4, 64, 64],64⟩,
.cycle 0 23 true (0),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 4 16 true (1),
.last 15 (5,true),
.cycle 17 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 8 6 true (4),
.cycle 6 9 true (2)
])
theorem kid10_part400_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part400) = true := by rfl

def kid10_part401 : Audit := .cycle 2 12 true (1)
theorem kid10_part401_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part401) = true := by rfl

def kid10_part402 : Audit := .split 12 (4,true) (byMove [
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 2 18 true (1),
.cycle 0 18 true (0),
.cycle 24 5 false (0),
.last 17 (5,true),
.cycle 2 12 true (1),
.last 15 (5,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true),
.cycle 12 6 true (2),
.cycle 7 10 true (3),
.cycle 2 14 true (1),
.cycle 4 14 true (1),
.last 14 (5,true),
.cycle 12 4 true (2),
.cycle 2 12 true (1),
.cycle 11 2 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true)
])
theorem kid10_part402_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part402) = true := by rfl

def kid10_part403 : Audit := .split 12 (5,true) (byMove [
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 18 true (0),
.last 18 (4,true),
.cycle 40 4 false (0),
.cycle 2 12 true (1),
.last 22 (4,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 5 true (4),
.last 18 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 17 (4,true),
.cycle 12 2 true (3),
.last 16 (4,true),
.cycle 2 12 true (1),
.cycle 11 2 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 6 9 true (2)
])
theorem kid10_part403_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part403) = true := by rfl

def kid10_part404 : Audit := .cycle 0 12 true (0)
theorem kid10_part404_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part404) = true := by rfl

def kid10_part405 : Audit := .cycle 1 11 true (1)
theorem kid10_part405_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part405) = true := by rfl

def kid10_part406 : Audit := .cycle 2 10 true (1)
theorem kid10_part406_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part406) = true := by rfl

def kid10_part407 : Audit := .cycle 2 13 true (1)
theorem kid10_part407_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part407) = true := by rfl

def kid10_part408 : Audit := .cycle 8 4 true (4)
theorem kid10_part408_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part408) = true := by rfl

def kid10_part409 : Audit := .cycle 6 7 true (2)
theorem kid10_part409_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part409) = true := by rfl

def kid10_part385 : Audit := .split 11 (1,true) (byMove [(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398),(kid10_part399),(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409)])

theorem kid10_part385_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part385) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398),(kid10_part399),(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part386_checked

  · exact kid10_part392_checked

  · exact kid10_part398_checked

  · exact kid10_part404_checked

  · exact kid10_part387_checked

  · exact kid10_part393_checked

  · exact kid10_part399_checked

  · exact kid10_part405_checked

  · exact kid10_part388_checked

  · exact kid10_part394_checked

  · exact kid10_part400_checked

  · exact kid10_part406_checked

  · exact kid10_part389_checked

  · exact kid10_part395_checked

  · exact kid10_part401_checked

  · exact kid10_part407_checked

  · exact kid10_part390_checked

  · exact kid10_part396_checked

  · exact kid10_part402_checked

  · exact kid10_part408_checked

  · exact kid10_part391_checked

  · exact kid10_part397_checked

  · exact kid10_part403_checked

  · exact kid10_part409_checked

def kid10_part410 : Audit := .cycle 7 4 true (3)
theorem kid10_part410_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part410) = true := by rfl

def kid10_part411 : Audit := .cycle 0 12 true (0)
theorem kid10_part411_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part411) = true := by rfl

def kid10_part412 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 4 14 true (1),
.cycle 2 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 10 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 64, 64],64⟩,
.cycle 9 7 true (2),
.split 17 (1,true) (byMove [
.cycle 2 17 true (1),
.cycle 1 19 true (1),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 6 13 true (2),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 4 15 true (1),
.cycle 6 12 true (2),
.cycle 32 7 false (2),
.cycle 14 4 true (4),
.cycle 2 18 true (1),
.cycle 13 6 true (3),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 4 16 true (1),
.cycle 2 19 true (1)
]),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 4 16 true (1),
.cycle 2 19 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 9 9 true (2),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 5 14 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 4 16 true (1),
.cycle 2 19 true (1)
]),
.cycle 5 12 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 4 14 true (1),
.cycle 2 17 true (1)
])
theorem kid10_part412_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part412) = true := by rfl

def kid10_part414 : Audit := .cycle 0 12 true (0)
theorem kid10_part414_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part414) = true := by rfl

def kid10_part415 : Audit := .cycle 1 11 true (1)
theorem kid10_part415_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part415) = true := by rfl

def kid10_part416 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 2 22 true (1),
.cycle 47 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 4, 52, 64],64⟩,
.cycle 13 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 16, 52, 64],64⟩,
.cycle 9 11 true (2),
.last 21 (1,true),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 2 20 true (1),
.cycle 38 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 2 22 true (1),
.cycle 21 15 true (3)
])
theorem kid10_part416_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part416) = true := by rfl

def kid10_part417 : Audit := .cycle 3 9 true (1)
theorem kid10_part417_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part417) = true := by rfl

def kid10_part418 : Audit := .cycle 8 4 true (4)
theorem kid10_part418_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part418) = true := by rfl

def kid10_part419 : Audit := .split 16 (4,true) (byMove [
.cycle 0 32 true (0),
.cycle 0 20 true (0),
.cycle 40 1 false (2),
.cycle 0 22 true (0),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 2 16 true (1),
.last 17 (1,true),
.cycle 35 3 false (3),
.cycle 0 18 true (0),
.cycle 35 3 false (3),
.cycle 23 3 false (1),
.last 18 (1,true),
.last 31 (1,true),
.cycle 2 18 true (1),
.cycle 35 1 false (1),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 2 16 true (1),
.last 17 (1,true),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 12 7 true (2),
.cycle 22 3 false (0)
])
theorem kid10_part419_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part419) = true := by rfl

def kid10_part420 : Audit := .cycle 0 12 true (0)
theorem kid10_part420_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part420) = true := by rfl

def kid10_part421 : Audit := .cycle 1 11 true (1)
theorem kid10_part421_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part421) = true := by rfl

def kid10_part422 : Audit := .split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 2 24 true (1),
.cycle 2 34 true (1),
.cycle 2 26 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 256, 32, 21, 4096],[256, 4096, 16, 1, 4, 4, 256, 4096, 16, 1, 60, 4, 4096],4096⟩,
.last 30 (1,true),
.cycle 6 16 true (2),
.last 22 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 2 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.last 23 (1,true),
.cycle 7 22 true (2),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 129 1 false (15),
.cycle 6 16 true (2),
.last 22 (1,true),
.cycle 2 22 true (1),
.cycle 2 22 true (1),
.cycle 22 14 true (6),
.cycle 40 11 true (10)
])
theorem kid10_part422_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part422) = true := by rfl

def kid10_part423 : Audit := .split 19 (4,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 37 1 false (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 24, 64],[4, 64, 16, 1, 4, 8, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 24, 64],[4, 64, 16, 1, 16, 8, 64],64⟩,
.cycle 11 9 true (2),
.last 21 (1,true),
.cycle 7 17 true (2),
.cycle 2 21 true (1),
.cycle 4 21 true (1),
.cycle 0 23 true (0),
.cycle 5 29 true (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.cycle 3 18 true (1)
])
theorem kid10_part423_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part423) = true := by rfl

def kid10_part424 : Audit := .cycle 8 4 true (4)
theorem kid10_part424_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part424) = true := by rfl

def kid10_part425 : Audit := .cycle 9 3 true (4)
theorem kid10_part425_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part425) = true := by rfl

def kid10_part426 : Audit := .split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 6 12 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.last 17 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.last 20 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 8 6 true (4),
.last 15 (4,true)
])
theorem kid10_part426_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part426) = true := by rfl

def kid10_part427 : Audit := .cycle 7 6 true (3)
theorem kid10_part427_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part427) = true := by rfl

def kid10_part428 : Audit := .cycle 0 14 true (0)
theorem kid10_part428_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part428) = true := by rfl

def kid10_part429 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 4 18 true (1),
.cycle 40 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 20, 64],64⟩,
.cycle 12 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 20, 64],64⟩,
.cycle 9 9 true (2),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 4 16 true (1),
.cycle 33 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 4 18 true (1),
.cycle 2 21 true (1)
])
theorem kid10_part429_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part429) = true := by rfl

def kid10_part430 : Audit := .cycle 10 2 true (4)
theorem kid10_part430_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part430) = true := by rfl

def kid10_part431 : Audit := .split 16 (4,true) (byMove [
.cycle 5 30 true (1),
.cycle 5 14 true (1),
.cycle 54 1 false (4),
.cycle 45 1 false (1),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 0 20 true (0),
.last 17 (1,true),
.cycle 49 3 false (9),
.cycle 5 12 true (1),
.cycle 49 3 false (9),
.cycle 23 3 false (1),
.last 18 (1,true),
.last 37 (1,true),
.cycle 0 24 true (0),
.cycle 45 1 false (3),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 0 20 true (0),
.last 17 (1,true),
.cycle 7 12 true (2),
.cycle 5 12 true (1),
.cycle 17 8 true (3),
.cycle 22 3 false (0)
])
theorem kid10_part431_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part431) = true := by rfl

def kid10_part432 : Audit := .cycle 0 12 true (0)
theorem kid10_part432_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part432) = true := by rfl

def kid10_part433 : Audit := .cycle 1 11 true (1)
theorem kid10_part433_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part433) = true := by rfl

def kid10_part434 : Audit := .cycle 2 10 true (1)
theorem kid10_part434_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part434) = true := by rfl

def kid10_part435 : Audit := .cycle 2 13 true (1)
theorem kid10_part435_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part435) = true := by rfl

def kid10_part436 : Audit := .cycle 8 4 true (4)
theorem kid10_part436_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part436) = true := by rfl

def kid10_part437 : Audit := .split 13 (4,true) (byMove [
.cycle 7 9 true (3),
.cycle 0 17 true (0),
.cycle 2 27 true (1),
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 32, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 21 5 false (1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5),
.last 15 (1,true),
.cycle 7 11 true (3),
.cycle 2 15 true (1),
.cycle 4 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 32, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 16 5 true (4),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5)
])
theorem kid10_part437_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part437) = true := by rfl

def kid10_part413 : Audit := .split 11 (5,true) (byMove [(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418),(kid10_part419),(kid10_part420),(kid10_part421),(kid10_part422),(kid10_part423),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437)])

theorem kid10_part413_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part413) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418),(kid10_part419),(kid10_part420),(kid10_part421),(kid10_part422),(kid10_part423),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part414_checked

  · exact kid10_part420_checked

  · exact kid10_part426_checked

  · exact kid10_part432_checked

  · exact kid10_part415_checked

  · exact kid10_part421_checked

  · exact kid10_part427_checked

  · exact kid10_part433_checked

  · exact kid10_part416_checked

  · exact kid10_part422_checked

  · exact kid10_part428_checked

  · exact kid10_part434_checked

  · exact kid10_part417_checked

  · exact kid10_part423_checked

  · exact kid10_part429_checked

  · exact kid10_part435_checked

  · exact kid10_part418_checked

  · exact kid10_part424_checked

  · exact kid10_part430_checked

  · exact kid10_part436_checked

  · exact kid10_part419_checked

  · exact kid10_part425_checked

  · exact kid10_part431_checked

  · exact kid10_part437_checked

def kid10_part439 : Audit := .split 16 (4,true) (byMove [
.cycle 5 22 true (1),
.cycle 0 20 true (0),
.cycle 2 22 true (1),
.cycle 0 22 true (0),
.cycle 5 18 true (1),
.last 23 (1,true),
.cycle 2 16 true (1),
.last 17 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 21, 64],[4, 64, 16, 1, 4, 12, 64],64⟩,
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 21, 64],[4, 64, 16, 1, 16, 12, 64],64⟩,
.cycle 0 18 true (0),
.last 18 (1,true),
.cycle 5 24 true (1),
.cycle 2 18 true (1),
.cycle 4 18 true (1),
.cycle 5 24 true (1),
.cycle 5 16 true (1),
.cycle 2 16 true (1),
.last 17 (1,true),
.cycle 7 10 true (1),
.cycle 0 18 true (0),
.cycle 2 24 true (1),
.cycle 2 17 true (1)
])
theorem kid10_part439_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part439) = true := by rfl

def kid10_part440 : Audit := .cycle 5 10 true (1)
theorem kid10_part440_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part440) = true := by rfl

def kid10_part441 : Audit := .split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 49 true (0),
.cycle 46 1 false (4),
.cycle 0 91 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 38 true (0),
.last 20 (1,true),
.cycle 46 1 false (2),
.cycle 0 48 true (0),
.cycle 31 1 false (1),
.cycle 43 1 false (3),
.last 21 (1,true),
.cycle 14 24 true (0),
.cycle 0 44 true (0),
.cycle 40 1 false (4),
.cycle 52 1 false (4),
.cycle 23 1 false (1),
.cycle 0 42 true (0),
.last 20 (1,true),
.cycle 7 36 true (0),
.cycle 5 36 true (0),
.cycle 14 34 true (0),
.cycle 42 1 false (2)
])
theorem kid10_part441_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part441) = true := by rfl

def kid10_part442 : Audit := .cycle 56 1 false (4)
theorem kid10_part442_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part442) = true := by rfl

def kid10_part443 : Audit := .cycle 18 1 false (0)
theorem kid10_part443_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part443) = true := by rfl

def kid10_part444 : Audit := .cycle 15 1 false (-1)
theorem kid10_part444_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part444) = true := by rfl

def kid10_part445 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 14 true (2),
.cycle 2 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 1, 64],64⟩,
.cycle 13 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 1, 64],64⟩,
.cycle 9 7 true (2),
.last 17 (1,true),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 18 true (0),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 14 true (2),
.cycle 2 17 true (1)
])
theorem kid10_part445_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part445) = true := by rfl

def kid10_part446 : Audit := .split 13 (1,true) (byMove [
.last 17 (4,true),
.cycle 2 16 true (1),
.last 21 (4,true),
.last 28 (4,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 44 1 false (12),
.last 18 (4,true),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 19 (4,true),
.cycle 1 21 true (1),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid10_part446_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part446) = true := by rfl

def kid10_part447 : Audit := .split 14 (4,true) (byMove [
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 52 1 false (6),
.cycle 48 1 false (6),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 33 1 false (9),
.cycle 0 16 true (0),
.cycle 33 1 false (9),
.cycle 71 1 false (13),
.last 16 (1,true),
.cycle 7 12 true (2),
.cycle 2 16 true (1),
.cycle 43 1 false (5),
.cycle 41 1 false (9),
.cycle 21 1 false (1),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 15 6 true (5),
.cycle 12 40 true (2)
])
theorem kid10_part447_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part447) = true := by rfl

def kid10_part448 : Audit := .cycle 5 8 true (1)
theorem kid10_part448_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part448) = true := by rfl

def kid10_part449 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 2 16 true (1),
.cycle 49 1 false (5),
.cycle 44 1 false (4),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 71 1 false (13),
.cycle 2 14 true (1),
.cycle 33 1 false (9),
.cycle 30 1 false (8),
.last 15 (1,true),
.cycle 7 14 true (2),
.cycle 5 10 true (1),
.cycle 40 1 false (4),
.cycle 53 1 false (9),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 14 6 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part449_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part449) = true := by rfl

def kid10_part450 : Audit := .cycle 29 1 false (7)
theorem kid10_part450_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part450) = true := by rfl

def kid10_part451 : Audit := .split 14 (1,true) (byMove [
.cycle 5 12 true (1),
.last 36 (4,true),
.cycle 73 1 false (7),
.cycle 0 25 true (0),
.last 15 (4,true),
.cycle 32 3 false (0),
.last 17 (4,true),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 29 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 18 (4,true)
])
theorem kid10_part451_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part451) = true := by rfl

def kid10_part452 : Audit := .split 15 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 2 18 true (1),
.cycle 2 28 true (1),
.cycle 2 20 true (1),
.last 20 (1,true),
.last 18 (1,true),
.cycle 6 10 true (1),
.last 16 (1,true),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 0, 4, 2, 3],[0, 0, 2097152, 512, 8388608, 2048, 1073741824, 524288, 1073741824, 2097152, 524288, 8388608, 1073741824, 1107828736, 1242079232, 32768, 1644830720, 131072, 1073741824, 0, 0, 134217728, 0, 536870912, 1073741824, 524288, 0, 2097152, 524288, 8388608, 1073741824],[0, 1073741824, 536870912, 1073741824, 134217728, 128, 524288, 1073741824, 2097152, 0, 8388608, 524288, 1107828736, 1073741824, 1250598912, 1107828736, 1646960640, 8192, 0, 1073741824, 536870912, 0, 134217728, 33554432, 524288, 1073741824, 2097152, 0, 8388608, 524288, 1073741824],1090875712⟩,
.cycle 2 16 true (1),
.last 26 (1,true),
.cycle 9 11 true (1),
.last 17 (1,true),
.last 29 (1,true),
.cycle 5 12 true (1),
.cycle 4 22 true (1),
.last 35 (1,true),
.last 18 (1,true),
.last 23 (1,true),
.last 16 (1,true),
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.last 22 (1,true),
.last 17 (1,true)
])
theorem kid10_part452_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part452) = true := by rfl

def kid10_part453 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 5 18 true (1),
.cycle 2 21 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 5, 64],64⟩,
.cycle 14 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 17, 64],64⟩,
.cycle 9 9 true (1),
.last 19 (1,true),
.cycle 16 18 true (3),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 22 true (0),
.cycle 5 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 5 18 true (1),
.cycle 2 21 true (1)
])
theorem kid10_part453_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part453) = true := by rfl

def kid10_part454 : Audit := .split 17 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 45 true (0),
.cycle 43 1 false (3),
.cycle 0 85 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 0 34 true (0),
.last 18 (1,true),
.cycle 43 1 false (1),
.cycle 0 44 true (0),
.cycle 28 1 false (0),
.cycle 36 1 false (2),
.last 19 (1,true),
.cycle 19 14 true (3),
.cycle 0 40 true (0),
.cycle 37 1 false (3),
.cycle 43 1 false (3),
.cycle 20 1 false (0),
.cycle 2 28 true (0),
.last 18 (1,true),
.cycle 7 32 true (0),
.cycle 5 32 true (0),
.cycle 18 18 true (4),
.cycle 34 7 true (4)
])
theorem kid10_part454_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part454) = true := by rfl

def kid10_part455 : Audit := .cycle 12 2 true (1)
theorem kid10_part455_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part455) = true := by rfl

def kid10_part456 : Audit := .cycle 15 1 false (-1)
theorem kid10_part456_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part456) = true := by rfl

def kid10_part457 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 14 true (2),
.cycle 2 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 1, 64],64⟩,
.cycle 13 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 16, 1, 64],64⟩,
.cycle 9 7 true (2),
.last 17 (1,true),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 18 true (0),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 14 true (2),
.cycle 2 17 true (1)
])
theorem kid10_part457_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part457) = true := by rfl

def kid10_part458 : Audit := .split 13 (1,true) (byMove [
.cycle 2 16 true (1),
.last 22 (4,true),
.cycle 1 38 true (0),
.cycle 0 21 true (0),
.last 14 (4,true),
.last 17 (4,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 1 20 true (1),
.last 16 (4,true),
.last 17 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid10_part458_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part458) = true := by rfl

def kid10_part459 : Audit := .split 14 (4,true) (byMove [
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.cycle 0 20 true (0),
.cycle 10 6 true (2),
.cycle 2 18 true (1),
.cycle 2 14 true (1),
.last 15 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 2 14 true (1),
.last 16 (1,true),
.cycle 7 12 true (2),
.cycle 2 16 true (1),
.cycle 4 16 true (1),
.cycle 7 10 true (2),
.cycle 11 4 true (2),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 15 6 true (5),
.cycle 2 14 true (1)
])
theorem kid10_part459_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part459) = true := by rfl

def kid10_part460 : Audit := .cycle 5 8 true (1)
theorem kid10_part460_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part460) = true := by rfl

def kid10_part461 : Audit := .split 13 (4,true) (byMove [
.cycle 2 16 true (1),
.last 14 (1,true),
.cycle 34 8 true (4),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 18 8 true (4),
.cycle 6 8 true (2),
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 16, 64],64⟩,
.cycle 2 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 16 6 true (4),
.last 18 (1,true),
.last 14 (1,true),
.cycle 5 12 true (1),
.cycle 4 14 true (1),
.cycle 12 4 true (1),
.cycle 12 2 true (2),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 14 6 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part461_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part461) = true := by rfl

def kid10_part462 : Audit := .cycle 14 3 true (4)
theorem kid10_part462_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part462) = true := by rfl

def kid10_part438 : Audit := .split 12 (5,true) (byMove [(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450),(kid10_part451),(kid10_part452),(kid10_part453),(kid10_part454),(kid10_part455),(kid10_part456),(kid10_part457),(kid10_part458),(kid10_part459),(kid10_part460),(kid10_part461),(kid10_part462)])

theorem kid10_part438_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part438) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450),(kid10_part451),(kid10_part452),(kid10_part453),(kid10_part454),(kid10_part455),(kid10_part456),(kid10_part457),(kid10_part458),(kid10_part459),(kid10_part460),(kid10_part461),(kid10_part462)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part439_checked

  · exact kid10_part445_checked

  · exact kid10_part451_checked

  · exact kid10_part457_checked

  · exact kid10_part440_checked

  · exact kid10_part446_checked

  · exact kid10_part452_checked

  · exact kid10_part458_checked

  · exact kid10_part441_checked

  · exact kid10_part447_checked

  · exact kid10_part453_checked

  · exact kid10_part459_checked

  · exact kid10_part442_checked

  · exact kid10_part448_checked

  · exact kid10_part454_checked

  · exact kid10_part460_checked

  · exact kid10_part443_checked

  · exact kid10_part449_checked

  · exact kid10_part455_checked

  · exact kid10_part461_checked

  · exact kid10_part444_checked

  · exact kid10_part450_checked

  · exact kid10_part456_checked

  · exact kid10_part462_checked

def kid10_part463 : Audit := .cycle 0 10 true (0)
theorem kid10_part463_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part463) = true := by rfl

def kid10_part464 : Audit := .cycle 1 9 true (1)
theorem kid10_part464_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part464) = true := by rfl

def kid10_part465 : Audit := .cycle 2 8 true (1)
theorem kid10_part465_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part465) = true := by rfl

def kid10_part466 : Audit := .cycle 2 11 true (1)
theorem kid10_part466_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part466) = true := by rfl

def kid10_part467 : Audit := .cycle 8 2 true (4)
theorem kid10_part467_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part467) = true := by rfl

def kid10_part468 : Audit := .cycle 9 1 true (5)
theorem kid10_part468_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part468) = true := by rfl

def kid10_part372 : Audit := .split 9 (5,false) (byMove [(kid10_part373),(kid10_part374),(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part410),(kid10_part411),(kid10_part412),(kid10_part413),(kid10_part438),(kid10_part463),(kid10_part464),(kid10_part465),(kid10_part466),(kid10_part467),(kid10_part468)])

theorem kid10_part372_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid10_part372) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part373),(kid10_part374),(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part410),(kid10_part411),(kid10_part412),(kid10_part413),(kid10_part438),(kid10_part463),(kid10_part464),(kid10_part465),(kid10_part466),(kid10_part467),(kid10_part468)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part373_checked

  · exact kid10_part379_checked

  · exact kid10_part385_checked

  · exact kid10_part463_checked

  · exact kid10_part374_checked

  · exact kid10_part380_checked

  · exact kid10_part410_checked

  · exact kid10_part464_checked

  · exact kid10_part375_checked

  · exact kid10_part381_checked

  · exact kid10_part411_checked

  · exact kid10_part465_checked

  · exact kid10_part376_checked

  · exact kid10_part382_checked

  · exact kid10_part412_checked

  · exact kid10_part466_checked

  · exact kid10_part377_checked

  · exact kid10_part383_checked

  · exact kid10_part413_checked

  · exact kid10_part467_checked

  · exact kid10_part378_checked

  · exact kid10_part384_checked

  · exact kid10_part438_checked

  · exact kid10_part468_checked

def kid10_part470 : Audit := .cycle 2 10 true (1)
theorem kid10_part470_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part470) = true := by rfl

def kid10_part471 : Audit := .cycle 1 12 true (1)
theorem kid10_part471_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part471) = true := by rfl

def kid10_part472 : Audit := .cycle 7 4 true (3)
theorem kid10_part472_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part472) = true := by rfl

def kid10_part473 : Audit := .cycle 0 12 true (0)
theorem kid10_part473_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part473) = true := by rfl

def kid10_part474 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 14 16 false (2),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 20 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 25 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 17 (5,false),
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
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 28, 64, 64],[4, 28, 16, 1, 4, 64, 64],96⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.last 29 (5,true),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 27 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 15 11 false (2),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 12 4 true (0),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.last 20 (5,false),
.cycle 0 18 true (0),
.last 25 (5,false),
.last 13 (5,false),
.cycle 2 12 true (1),
.last 24 (5,false),
.last 18 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.cycle 2 14 true (1),
.last 18 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.cycle 2 12 true (1),
.last 15 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 6 7 true (2),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 25 6 false (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 9 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 25 6 false (1),
.cycle 11 3 true (3),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
])
theorem kid10_part474_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part474) = true := by rfl

def kid10_part476 : Audit := .cycle 2 11 true (1)
theorem kid10_part476_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part476) = true := by rfl

def kid10_part477 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (4),
.cycle 14 13 false (1),
.cycle 33 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 27 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 14 17 false (2),
.cycle 13 1 true (1),
.cycle 14 16 false (2),
.cycle 14 8 false (0),
.last 15 (4,true),
.cycle 28 1 false (0),
.last 14 (4,true),
.cycle 0 18 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 28 9 false (2),
.cycle 13 1 true (1)
])
theorem kid10_part477_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part477) = true := by rfl

def kid10_part478 : Audit := .cycle 33 1 false (1)
theorem kid10_part478_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part478) = true := by rfl

def kid10_part479 : Audit := .cycle 0 13 true (0)
theorem kid10_part479_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part479) = true := by rfl

def kid10_part480 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.cycle 21 4 false (-1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (3),
.cycle 12 7 true (0),
.cycle 25 4 false (1),
.last 13 (5,false),
.cycle 17 4 false (0),
.last 21 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 4 true (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
])
theorem kid10_part480_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part480) = true := by rfl

def kid10_part481 : Audit := .split 13 (5,false) (byMove [
.cycle 0 27 false (4),
.cycle 15 13 false (1),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 18 5 false (0),
.cycle 13 1 true (1),
.cycle 20 4 false (0),
.cycle 15 8 false (0),
.last 15 (4,true),
.cycle 28 1 false (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 21 9 false (1),
.cycle 13 1 true (1)
])
theorem kid10_part481_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part481) = true := by rfl

def kid10_part482 : Audit := .cycle 0 12 true (0)
theorem kid10_part482_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part482) = true := by rfl

def kid10_part483 : Audit := .cycle 1 11 true (1)
theorem kid10_part483_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part483) = true := by rfl

def kid10_part484 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 64, 64],[8, 32, 8, 8, 8, 8, 64],96⟩,
.cycle 13 7 true (2),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 64, 64],[8, 32, 8, 8, 8, 8, 64],96⟩,
.last 20 (5,false),
.cycle 9 11 true (2),
.cycle 7 14 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 17 4 true (3),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.last 20 (5,false)
])
theorem kid10_part484_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part484) = true := by rfl

def kid10_part485 : Audit := .cycle 3 9 true (1)
theorem kid10_part485_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part485) = true := by rfl

def kid10_part486 : Audit := .cycle 8 4 true (3)
theorem kid10_part486_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part486) = true := by rfl

def kid10_part487 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (4,true),
.cycle 28 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
theorem kid10_part487_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part487) = true := by rfl

def kid10_part488 : Audit := .cycle 6 6 true (2)
theorem kid10_part488_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part488) = true := by rfl

def kid10_part489 : Audit := .split 13 (5,false) (byMove [
.last 21 (4,true),
.last 36 (4,true),
.cycle 28 1 false (-2),
.cycle 32 1 false (-2),
.last 14 (4,true),
.cycle 22 1 false (-2),
.cycle 23 11 false (1),
.cycle 7 8 true (1),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 14 12 false (2),
.cycle 7 10 true (1),
.cycle 15 11 false (2),
.cycle 14 8 false (0),
.last 15 (4,true),
.cycle 0 18 true (0),
.last 14 (4,true),
.last 17 (4,true),
.cycle 22 5 false (1),
.cycle 20 16 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 17 (4,true),
.cycle 16 12 false (2)
])
theorem kid10_part489_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part489) = true := by rfl

def kid10_part490 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.cycle 0 26 true (-2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 46 true (0),
.cycle 0 23 true (0),
.cycle 0 20 true (0),
.last 14 (5,false),
.cycle 0 19 true (0),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.cycle 38 4 true (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.last 14 (5,false)
])
theorem kid10_part490_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part490) = true := by rfl

def kid10_part491 : Audit := .cycle 2 12 true (1)
theorem kid10_part491_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part491) = true := by rfl

def kid10_part492 : Audit := .split 12 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 0 18 true (0),
.cycle 21 4 false (-1),
.last 13 (5,false),
.cycle 2 12 true (1),
.last 14 (5,false),
.cycle 24 4 false (2),
.cycle 0 14 true (0),
.cycle 24 4 false (2),
.cycle 19 4 false (1),
.cycle 17 4 false (0),
.cycle 23 4 false (1),
.cycle 2 14 true (1),
.cycle 27 1 false (1),
.cycle 12 4 true (0),
.last 13 (5,false),
.cycle 2 12 true (1),
.cycle 1 18 true (0),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 6 9 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part492_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part492) = true := by rfl

def kid10_part493 : Audit := .split 13 (5,false) (byMove [
.last 33 (4,true),
.cycle 33 16 true (1),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.cycle 7 10 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 16 (4,true),
.last 26 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 26 (4,true),
.cycle 16 3 false (0),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid10_part493_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part493) = true := by rfl

def kid10_part494 : Audit := .cycle 0 12 true (0)
theorem kid10_part494_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part494) = true := by rfl

def kid10_part495 : Audit := .cycle 1 11 true (1)
theorem kid10_part495_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part495) = true := by rfl

def kid10_part496 : Audit := .cycle 2 10 true (1)
theorem kid10_part496_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part496) = true := by rfl

def kid10_part497 : Audit := .cycle 2 13 true (1)
theorem kid10_part497_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part497) = true := by rfl

def kid10_part498 : Audit := .cycle 6 7 true (2)
theorem kid10_part498_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part498) = true := by rfl

def kid10_part499 : Audit := .split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 17 17 false (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 17 12 false (1),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
theorem kid10_part499_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part499) = true := by rfl

def kid10_part475 : Audit := .split 11 (5,true) (byMove [(kid10_part476),(kid10_part477),(kid10_part478),(kid10_part479),(kid10_part480),(kid10_part481),(kid10_part482),(kid10_part483),(kid10_part484),(kid10_part485),(kid10_part486),(kid10_part487),(kid10_part488),(kid10_part489),(kid10_part490),(kid10_part491),(kid10_part492),(kid10_part493),(kid10_part494),(kid10_part495),(kid10_part496),(kid10_part497),(kid10_part498),(kid10_part499)])

theorem kid10_part475_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part475) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part476),(kid10_part477),(kid10_part478),(kid10_part479),(kid10_part480),(kid10_part481),(kid10_part482),(kid10_part483),(kid10_part484),(kid10_part485),(kid10_part486),(kid10_part487),(kid10_part488),(kid10_part489),(kid10_part490),(kid10_part491),(kid10_part492),(kid10_part493),(kid10_part494),(kid10_part495),(kid10_part496),(kid10_part497),(kid10_part498),(kid10_part499)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part476_checked

  · exact kid10_part482_checked

  · exact kid10_part488_checked

  · exact kid10_part494_checked

  · exact kid10_part477_checked

  · exact kid10_part483_checked

  · exact kid10_part489_checked

  · exact kid10_part495_checked

  · exact kid10_part478_checked

  · exact kid10_part484_checked

  · exact kid10_part490_checked

  · exact kid10_part496_checked

  · exact kid10_part479_checked

  · exact kid10_part485_checked

  · exact kid10_part491_checked

  · exact kid10_part497_checked

  · exact kid10_part480_checked

  · exact kid10_part486_checked

  · exact kid10_part492_checked

  · exact kid10_part498_checked

  · exact kid10_part481_checked

  · exact kid10_part487_checked

  · exact kid10_part493_checked

  · exact kid10_part499_checked

def kid10_part500 : Audit := .cycle 0 11 true (0)
theorem kid10_part500_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part500) = true := by rfl

def kid10_part501 : Audit := .cycle 1 10 true (1)
theorem kid10_part501_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part501) = true := by rfl

def kid10_part502 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 6 14 true (2),
.split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.cycle 45 1 false (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 22 14 false (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 8 12 true (3),
.cycle 19 1 true (5),
.cycle 6 14 true (2),
.cycle 7 14 true (3),
.cycle 0 25 true (0),
.cycle 2 20 true (1),
.last 162 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.cycle 19 1 true (5)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 7 21 true (3),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 8 12 true (3),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 30 (5,true),
.last 28 (5,true),
.cycle 8 12 true (3),
.cycle 19 1 true (7),
.cycle 9 11 true (3),
.cycle 7 14 true (3),
.cycle 0 22 true (0),
.cycle 13 7 true (3),
.cycle 7 16 true (3),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.cycle 19 1 true (7)
]),
.cycle 9 10 true (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 16 4 true (4),
.split 19 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 7 17 true (3),
.cycle 9 12 true (3),
.cycle 31 18 true (1),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 7 25 true (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.last 20 (5,true),
.cycle 16 4 true (4),
.cycle 17 8 true (4),
.cycle 5 19 true (1),
.cycle 5 15 true (1),
.cycle 22 13 false (2),
.last 20 (5,true),
.cycle 2 19 true (1),
.cycle 10 10 true (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 6 14 true (2),
.split 19 (5,false) (byMove [
.cycle 2 19 true (1),
.last 30 (5,true),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 18 2 true (6),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 8 12 true (3),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.cycle 7 14 true (3),
.cycle 17 3 true (5),
.cycle 2 20 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.cycle 19 1 true (7)
])
])
theorem kid10_part502_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part502) = true := by rfl

def kid10_part503 : Audit := .cycle 3 8 true (1)
theorem kid10_part503_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part503) = true := by rfl

def kid10_part504 : Audit := .cycle 8 3 true (3)
theorem kid10_part504_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part504) = true := by rfl

def kid10_part505 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.cycle 33 1 false (1),
.cycle 41 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 21 1 false (1),
.cycle 6 8 true (2),
.cycle 7 10 true (2),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 12 2 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 20 (4,true) (byMove [
.cycle 7 16 true (3),
.cycle 0 24 true (0),
.cycle 2 26 true (1),
.cycle 0 26 true (0),
.last 27 (5,true),
.cycle 0 24 true (0),
.cycle 2 20 true (1),
.last 35 (5,true),
.cycle 7 14 true (3),
.cycle 0 22 true (0),
.cycle 8 14 true (3),
.last 21 (5,true),
.last 23 (5,true),
.cycle 7 18 true (3),
.cycle 2 22 true (1),
.cycle 4 22 true (1),
.cycle 18 4 true (4),
.cycle 7 18 true (3),
.cycle 2 20 true (1),
.cycle 10 11 true (3),
.cycle 7 14 true (3),
.cycle 0 22 true (0),
.cycle 6 17 true (2),
.last 21 (5,true)
]),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 6 14 true (2),
.cycle 3 17 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 7 21 true (3),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.last 28 (5,true),
.cycle 9 10 true (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 16 4 true (4),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 6 14 true (2),
.cycle 3 17 true (1)
]),
.cycle 8 4 true (3),
.cycle 11 1 true (5),
.cycle 9 3 true (3),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 11 true (2),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 18 true (3),
.cycle 13 7 true (3),
.cycle 8 8 true (3),
.last 20 (5,true),
.cycle 9 7 true (3),
.cycle 7 10 true (3),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 12 4 true (3),
.last 18 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 11 true (2),
.last 18 (5,true)
]),
.split 13 (5,true) (byMove [
.cycle 2 16 true (1),
.last 24 (4,true),
.last 25 (4,true),
.cycle 2 19 true (1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 40 1 false (8),
.last 16 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 6 7 true (2),
.cycle 11 1 true (5)
])
theorem kid10_part505_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part505) = true := by rfl

def kid10_part506 : Audit := .cycle 6 5 true (2)
theorem kid10_part506_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part506) = true := by rfl

def kid10_part507 : Audit := .split 15 (4,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 29, 64, 64],[4, 29, 16, 1, 12, 64, 64],96⟩,
.cycle 0 19 true (0),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.cycle 22 11 false (2),
.split 16 (5,false) (byMove [
.cycle 2 25 true (1),
.cycle 17 12 false (1),
.cycle 21 9 false (1),
.cycle 0 38 true (0),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 24 true (0),
.cycle 7 11 true (1),
.cycle 0 19 true (0),
.cycle 3 21 true (1),
.cycle 20 9 false (2),
.last 18 (5,true),
.cycle 22 11 false (2),
.cycle 18 5 false (1),
.cycle 0 29 true (-1),
.cycle 0 21 true (0),
.last 18 (5,true),
.last 17 (5,true),
.cycle 19 9 false (3),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 1, 2, 64],[2, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 1024, 128, 256, 8, 256, 16, 1024, 4096],[256, 16, 16, 1, 16, 4096, 256, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.last 18 (5,true)
]),
.cycle 2 15 true (1),
.cycle 7 11 true (1),
.cycle 14 17 true (2),
.cycle 0 17 true (0),
.cycle 16 7 true (3),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.last 25 (5,false),
.cycle 3 14 true (1),
.cycle 20 9 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.last 36 (5,false),
.cycle 14 9 true (1),
.last 24 (5,false),
.last 17 (5,false),
.last 23 (5,false),
.cycle 7 11 true (1),
.cycle 0 19 true (0),
.last 23 (5,false),
.cycle 20 9 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.cycle 6 12 true (1),
.last 17 (5,false)
]),
.cycle 18 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.cycle 2 17 true (1),
.cycle 4 17 true (1),
.cycle 14 4 true (1),
.split 16 (5,false) (byMove [
.cycle 2 19 true (1),
.cycle 17 12 false (1),
.cycle 21 9 false (1),
.cycle 11 8 true (1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 6 11 true (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 1, 2, 64],[2, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 17 9 true (3),
.cycle 2 17 true (1),
.cycle 15 2 true (2),
.last 17 (5,true),
.cycle 14 4 true (1),
.cycle 18 5 false (1),
.cycle 26 25 true (0),
.cycle 5 17 true (1),
.last 18 (5,true),
.last 17 (5,true),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 1, 2, 64],[2, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 18 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 1, 2, 64],[2, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 2 17 true (1),
.last 18 (5,true),
.last 17 (5,true)
]),
.cycle 2 15 true (1),
.cycle 1 20 true (1),
.cycle 7 9 true (1),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.split 16 (5,true) (byMove [
.cycle 2 16 true (1),
.cycle 23 13 false (3),
.last 25 (5,false),
.cycle 0 18 true (0),
.last 18 (5,false),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.last 25 (5,false),
.cycle 3 14 true (1),
.cycle 8 9 true (1),
.last 17 (5,false),
.cycle 6 11 true (1),
.last 21 (5,false),
.last 19 (5,false),
.cycle 2 17 true (1),
.cycle 15 2 true (3),
.last 18 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 31 (5,false),
.last 17 (5,false)
])
])
theorem kid10_part507_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part507) = true := by rfl

def kid10_part508 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.cycle 0 17 true (0),
.cycle 41 1 false (1),
.cycle 0 15 true (0),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (3),
.cycle 6 8 true (2),
.cycle 2 16 true (1),
.cycle 0 19 true (0),
.cycle 2 14 true (1),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 13 1 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 21, 64, 64],[4, 5, 16, 1, 4, 64, 64],96⟩,
.cycle 11 7 true (2),
.cycle 8 5 true (3),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (5,true),
.last 22 (5,true),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 9 5 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 11 7 true (2),
.last 19 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
]),
.cycle 9 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 11 4 true (2),
.split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 25 true (0),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 0 17 true (0),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.last 14 (5,true),
.cycle 11 4 true (2),
.cycle 5 11 true (1),
.cycle 5 13 true (1),
.cycle 5 9 true (1),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 10 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.cycle 0 17 true (0),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 2 16 true (1),
.cycle 11 3 true (3),
.cycle 2 14 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
])
])
theorem kid10_part508_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part508) = true := by rfl

def kid10_part509 : Audit := .cycle 2 11 true (1)
theorem kid10_part509_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part509) = true := by rfl

def kid10_part510 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 24 true (0),
.cycle 47 1 false (3),
.cycle 29 1 false (1),
.cycle 20 4 false (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.last 21 (5,false),
.cycle 25 1 false (1),
.last 23 (5,false),
.last 25 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 20 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.last 25 (5,false),
.last 18 (5,false),
.cycle 22 1 false (0),
.last 17 (5,false),
.last 13 (5,false),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 17 (5,false),
.last 13 (5,false)
]),
.cycle 2 11 true (1),
.cycle 1 16 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 0, 1],[0, 0, 2097152, 512, 64, 1073741824, 512, 0, 1073741824, 2097152, 262144, 1073741824, 1210089984, 1210089984, 1210089984, 32768, 4096, 1073741824, 134217728, 1073741824, 0, 134217728, 16777216, 1073741824, 1073741824, 0, 0, 512, 64, 1073741824, 1073741824],[0, 1024, 512, 1073741824, 1073741824, 134217728, 0, 4194304, 1073741824, 0, 512, 2097152, 1210089984, 65536, 1210089984, 1210089984, 1210089984, 1210089984, 1073741824, 268435456, 2097152, 0, 134217728, 1073741824, 0, 1024, 512, 1073741824, 1073741824, 134217728, 1073741824],1640724768⟩,
.last 20 (5,false),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 9 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 17 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
]),
.cycle 9 6 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.cycle 12 4 true (0),
.split 12 (5,true) (byMove [
.last 17 (5,false),
.cycle 2 15 true (1),
.last 20 (5,false),
.last 37 (5,false),
.last 25 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 24 (5,false),
.last 15 (5,false),
.cycle 2 13 true (1),
.last 14 (5,false),
.last 15 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.cycle 5 9 true (1),
.last 18 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 11 2 true (2),
.last 15 (5,false)
]),
.cycle 2 11 true (1),
.cycle 10 2 true (3),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 6 8 true (2),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 21 (5,false),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 14 6 true (0),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
])
])
theorem kid10_part510_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part510) = true := by rfl

def kid10_part512 : Audit := .cycle 0 15 true (0)
theorem kid10_part512_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part512) = true := by rfl

def kid10_part513 : Audit := .split 13 (5,false) (byMove [
.cycle 0 23 true (0),
.cycle 0 31 true (-2),
.cycle 0 25 true (-1),
.cycle 0 27 true (0),
.last 14 (4,true),
.last 22 (4,true),
.cycle 0 17 true (0),
.cycle 12 2 true (1),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.last 14 (4,true),
.last 22 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 0 21 true (-1),
.cycle 0 17 true (0),
.cycle 0 35 true (-2),
.last 75 (4,true),
.cycle 0 21 true (0),
.last 14 (4,true),
.cycle 0 38 true (-1)
])
theorem kid10_part513_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part513) = true := by rfl

def kid10_part514 : Audit := .split 23 (4,true) (byMove [
.cycle 47 1 false (1),
.cycle 0 27 true (0),
.cycle 47 1 false (3),
.cycle 0 29 true (0),
.cycle 37 1 false (1),
.last 24 (5,false),
.cycle 0 52 true (0),
.last 25 (5,false),
.cycle 18 13 true (0),
.cycle 0 25 true (0),
.cycle 18 13 true (0),
.last 33 (5,false),
.cycle 33 1 false (1),
.cycle 49 1 false (1),
.cycle 0 58 true (0),
.cycle 43 1 false (3),
.cycle 21 4 true (1),
.last 24 (5,false),
.cycle 2 23 true (0),
.cycle 1 32 true (0),
.cycle 7 17 true (0),
.cycle 0 25 true (0),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 1, 64, 64],[12, 32, 12, 8, 12, 4, 64],96⟩,
.last 37 (5,false)
])
theorem kid10_part514_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part514) = true := by rfl

def kid10_part515 : Audit := .cycle 29 1 false (1)
theorem kid10_part515_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part515) = true := by rfl

def kid10_part516 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 37 1 false (3),
.cycle 21 4 false (-1),
.last 13 (5,false),
.cycle 21 4 false (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.cycle 25 4 false (1),
.last 13 (5,false),
.cycle 17 4 false (0),
.last 21 (5,false),
.cycle 25 4 false (2),
.cycle 22 1 false (0),
.cycle 12 4 true (0),
.last 13 (5,false),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 6 12 true (2),
.last 13 (5,false)
])
theorem kid10_part516_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part516) = true := by rfl

def kid10_part517 : Audit := .split 13 (5,false) (byMove [
.last 35 (4,true),
.cycle 0 23 true (-2),
.cycle 21 1 false (-1),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 28 true (0),
.cycle 0 17 true (0),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 18 5 false (0),
.cycle 17 1 true (3),
.cycle 20 4 false (0),
.last 18 (4,true),
.last 15 (4,true),
.last 22 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 43 (4,true),
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 21 9 false (1),
.cycle 21 1 true (-1)
])
theorem kid10_part517_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part517) = true := by rfl

def kid10_part518 : Audit := .cycle 2 11 true (1)
theorem kid10_part518_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part518) = true := by rfl

def kid10_part519 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 0 37 true (-2),
.last 27 (4,true),
.cycle 37 1 false (1),
.last 14 (4,true),
.cycle 7 9 true (2),
.cycle 2 13 true (1),
.cycle 12 2 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 16 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 2 13 true (1),
.cycle 10 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 14 true (1)
])
theorem kid10_part519_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part519) = true := by rfl

def kid10_part520 : Audit := .cycle 7 5 true (3)
theorem kid10_part520_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part520) = true := by rfl

def kid10_part521 : Audit := .cycle 0 13 true (0)
theorem kid10_part521_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part521) = true := by rfl

def kid10_part522 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 64, 64],[8, 32, 8, 8, 8, 8, 64],96⟩,
.cycle 12 7 true (2),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 9 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 12 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
])
theorem kid10_part522_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part522) = true := by rfl

def kid10_part523 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 21 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 9 5 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 11 7 true (3),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part523_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part523) = true := by rfl

def kid10_part524 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 6 10 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 1, 64, 64],[1, 32, 9, 1, 9, 1, 64],96⟩,
.cycle 12 7 true (2),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 1, 64, 64],[1, 32, 1, 1, 1, 1, 64],96⟩,
.last 15 (5,false),
.cycle 9 6 true (2),
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 12 4 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 6 10 true (2),
.last 15 (5,false)
])
theorem kid10_part524_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part524) = true := by rfl

def kid10_part525 : Audit := .split 13 (5,false) (byMove [
.last 28 (4,true),
.last 24 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.last 14 (4,true),
.cycle 22 1 false (-2),
.last 16 (4,true),
.cycle 12 2 true (1),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 22 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 19 (4,true)
])
theorem kid10_part525_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part525) = true := by rfl

def kid10_part526 : Audit := .split 13 (4,true) (byMove [
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.cycle 42 1 false (4),
.cycle 25 1 false (1),
.cycle 0 56 true (-2),
.last 14 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.cycle 2 20 true (1),
.cycle 0 15 true (0),
.cycle 2 20 true (1),
.cycle 0 17 true (0),
.cycle 5 13 true (1),
.cycle 7 11 true (2),
.cycle 2 15 true (1),
.cycle 35 1 false (3),
.cycle 26 4 true (0),
.last 14 (5,false),
.cycle 2 13 true (1),
.cycle 2 17 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 6 10 true (2),
.last 17 (5,false)
])
theorem kid10_part526_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part526) = true := by rfl

def kid10_part527 : Audit := .cycle 5 7 true (1)
theorem kid10_part527_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part527) = true := by rfl

def kid10_part528 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 2 15 true (1),
.cycle 39 1 false (3),
.cycle 0 52 true (0),
.cycle 21 4 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 14 (5,false),
.cycle 49 1 false (9),
.cycle 2 13 true (1),
.cycle 49 4 false (7),
.cycle 19 4 false (1),
.cycle 17 4 false (0),
.cycle 54 4 false (0),
.cycle 5 9 true (1),
.cycle 32 1 false (2),
.cycle 12 4 true (0),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 12 6 true (0),
.cycle 2 13 true (1),
.cycle 2 13 true (1),
.cycle 6 10 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part528_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part528) = true := by rfl

def kid10_part529 : Audit := .split 13 (5,false) (byMove [
.last 28 (4,true),
.last 28 (4,true),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.cycle 13 2 true (1),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 16 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.cycle 16 3 false (0),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid10_part529_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part529) = true := by rfl

def kid10_part530 : Audit := .cycle 2 11 true (1)
theorem kid10_part530_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part530) = true := by rfl

def kid10_part531 : Audit := .cycle 10 2 true (3)
theorem kid10_part531_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part531) = true := by rfl

def kid10_part532 : Audit := .cycle 7 5 true (3)
theorem kid10_part532_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part532) = true := by rfl

def kid10_part533 : Audit := .cycle 0 13 true (0)
theorem kid10_part533_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part533) = true := by rfl

def kid10_part534 : Audit := .split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.last 17 (5,false),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 23 6 false (1),
.cycle 6 9 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 23 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.cycle 14 4 true (0),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.last 13 (5,false)
])
theorem kid10_part534_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part534) = true := by rfl

def kid10_part535 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 5 true (3),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part535_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part535) = true := by rfl

def kid10_part511 : Audit := .split 11 (5,true) (byMove [(kid10_part512),(kid10_part513),(kid10_part514),(kid10_part515),(kid10_part516),(kid10_part517),(kid10_part518),(kid10_part519),(kid10_part520),(kid10_part521),(kid10_part522),(kid10_part523),(kid10_part524),(kid10_part525),(kid10_part526),(kid10_part527),(kid10_part528),(kid10_part529),(kid10_part530),(kid10_part531),(kid10_part532),(kid10_part533),(kid10_part534),(kid10_part535)])

theorem kid10_part511_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part511) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part512),(kid10_part513),(kid10_part514),(kid10_part515),(kid10_part516),(kid10_part517),(kid10_part518),(kid10_part519),(kid10_part520),(kid10_part521),(kid10_part522),(kid10_part523),(kid10_part524),(kid10_part525),(kid10_part526),(kid10_part527),(kid10_part528),(kid10_part529),(kid10_part530),(kid10_part531),(kid10_part532),(kid10_part533),(kid10_part534),(kid10_part535)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part512_checked

  · exact kid10_part518_checked

  · exact kid10_part524_checked

  · exact kid10_part530_checked

  · exact kid10_part513_checked

  · exact kid10_part519_checked

  · exact kid10_part525_checked

  · exact kid10_part531_checked

  · exact kid10_part514_checked

  · exact kid10_part520_checked

  · exact kid10_part526_checked

  · exact kid10_part532_checked

  · exact kid10_part515_checked

  · exact kid10_part521_checked

  · exact kid10_part527_checked

  · exact kid10_part533_checked

  · exact kid10_part516_checked

  · exact kid10_part522_checked

  · exact kid10_part528_checked

  · exact kid10_part534_checked

  · exact kid10_part517_checked

  · exact kid10_part523_checked

  · exact kid10_part529_checked

  · exact kid10_part535_checked

def kid10_part536 : Audit := .cycle 0 11 true (0)
theorem kid10_part536_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part536) = true := by rfl

def kid10_part537 : Audit := .cycle 1 10 true (1)
theorem kid10_part537_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part537) = true := by rfl

def kid10_part538 : Audit := .cycle 2 9 true (1)
theorem kid10_part538_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part538) = true := by rfl

def kid10_part539 : Audit := .cycle 2 12 true (1)
theorem kid10_part539_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part539) = true := by rfl

def kid10_part540 : Audit := .cycle 6 6 true (2)
theorem kid10_part540_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part540) = true := by rfl

def kid10_part542 : Audit := .cycle 2 11 true (1)
theorem kid10_part542_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part542) = true := by rfl

def kid10_part543 : Audit := .cycle 10 2 true (4)
theorem kid10_part543_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part543) = true := by rfl

def kid10_part544 : Audit := .cycle 7 5 true (3)
theorem kid10_part544_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part544) = true := by rfl

def kid10_part545 : Audit := .cycle 0 13 true (0)
theorem kid10_part545_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part545) = true := by rfl

def kid10_part546 : Audit := .split 12 (4,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 18 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 23 6 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 23 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 6 9 true (2),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 2 13 true (1),
.cycle 14 4 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 11 2 true (4)
])
theorem kid10_part546_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part546) = true := by rfl

def kid10_part547 : Audit := .split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 18 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 23 1 false (1),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 8 true (2),
.cycle 11 2 true (4)
])
theorem kid10_part547_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part547) = true := by rfl

def kid10_part548 : Audit := .cycle 0 12 true (0)
theorem kid10_part548_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part548) = true := by rfl

def kid10_part549 : Audit := .cycle 1 11 true (1)
theorem kid10_part549_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part549) = true := by rfl

def kid10_part550 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.cycle 11 9 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 7 22 true (3),
.cycle 13 7 true (4),
.cycle 8 12 true (3),
.last 31 (5,true),
.cycle 9 11 true (3),
.cycle 7 14 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 17 4 true (5),
.cycle 7 14 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 6 15 true (2),
.cycle 11 9 true (4)
])
theorem kid10_part550_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part550) = true := by rfl

def kid10_part551 : Audit := .cycle 3 9 true (1)
theorem kid10_part551_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part551) = true := by rfl

def kid10_part552 : Audit := .cycle 8 4 true (3)
theorem kid10_part552_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part552) = true := by rfl

def kid10_part553 : Audit := .cycle 11 1 true (5)
theorem kid10_part553_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part553) = true := by rfl

def kid10_part554 : Audit := .cycle 6 6 true (2)
theorem kid10_part554_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part554) = true := by rfl

def kid10_part555 : Audit := .split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.cycle 10 4 true (4),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 19 12 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 7 9 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 11 3 true (4)
])
theorem kid10_part555_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part555) = true := by rfl

def kid10_part556 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 0 23 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 16 true (3),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 9 5 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 12 4 true (3),
.cycle 5 26 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 6 9 true (2),
.cycle 11 3 true (4)
])
theorem kid10_part556_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part556) = true := by rfl

def kid10_part557 : Audit := .cycle 2 12 true (1)
theorem kid10_part557_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part557) = true := by rfl

def kid10_part558 : Audit := .split 12 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 5 16 true (1),
.last 17 (5,true),
.cycle 9 5 true (3),
.cycle 23 6 false (1),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.last 13 (5,true),
.cycle 9 7 true (3),
.last 14 (5,true),
.cycle 2 16 true (1),
.cycle 5 8 true (1),
.cycle 14 4 true (0),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 6 9 true (2),
.last 13 (5,true)
])
theorem kid10_part558_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part558) = true := by rfl

def kid10_part559 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 5 16 true (1),
.cycle 7 11 true (3),
.cycle 9 5 true (3),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 49 1 false (9),
.last 15 (4,true),
.cycle 12 2 true (3),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (4)
])
theorem kid10_part559_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part559) = true := by rfl

def kid10_part560 : Audit := .cycle 0 12 true (0)
theorem kid10_part560_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part560) = true := by rfl

def kid10_part561 : Audit := .cycle 1 11 true (1)
theorem kid10_part561_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part561) = true := by rfl

def kid10_part562 : Audit := .cycle 2 10 true (1)
theorem kid10_part562_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part562) = true := by rfl

def kid10_part563 : Audit := .cycle 2 13 true (1)
theorem kid10_part563_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part563) = true := by rfl

def kid10_part564 : Audit := .cycle 6 7 true (2)
theorem kid10_part564_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part564) = true := by rfl

def kid10_part565 : Audit := .cycle 11 1 true (5)
theorem kid10_part565_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part565) = true := by rfl

def kid10_part541 : Audit := .split 11 (5,false) (byMove [(kid10_part542),(kid10_part543),(kid10_part544),(kid10_part545),(kid10_part546),(kid10_part547),(kid10_part548),(kid10_part549),(kid10_part550),(kid10_part551),(kid10_part552),(kid10_part553),(kid10_part554),(kid10_part555),(kid10_part556),(kid10_part557),(kid10_part558),(kid10_part559),(kid10_part560),(kid10_part561),(kid10_part562),(kid10_part563),(kid10_part564),(kid10_part565)])

theorem kid10_part541_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part541) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part542),(kid10_part543),(kid10_part544),(kid10_part545),(kid10_part546),(kid10_part547),(kid10_part548),(kid10_part549),(kid10_part550),(kid10_part551),(kid10_part552),(kid10_part553),(kid10_part554),(kid10_part555),(kid10_part556),(kid10_part557),(kid10_part558),(kid10_part559),(kid10_part560),(kid10_part561),(kid10_part562),(kid10_part563),(kid10_part564),(kid10_part565)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part542_checked

  · exact kid10_part548_checked

  · exact kid10_part554_checked

  · exact kid10_part560_checked

  · exact kid10_part543_checked

  · exact kid10_part549_checked

  · exact kid10_part555_checked

  · exact kid10_part561_checked

  · exact kid10_part544_checked

  · exact kid10_part550_checked

  · exact kid10_part556_checked

  · exact kid10_part562_checked

  · exact kid10_part545_checked

  · exact kid10_part551_checked

  · exact kid10_part557_checked

  · exact kid10_part563_checked

  · exact kid10_part546_checked

  · exact kid10_part552_checked

  · exact kid10_part558_checked

  · exact kid10_part564_checked

  · exact kid10_part547_checked

  · exact kid10_part553_checked

  · exact kid10_part559_checked

  · exact kid10_part565_checked

def kid10_part469 : Audit := .split 10 (1,true) (byMove [(kid10_part470),(kid10_part471),(kid10_part472),(kid10_part473),(kid10_part474),(kid10_part475),(kid10_part500),(kid10_part501),(kid10_part502),(kid10_part503),(kid10_part504),(kid10_part505),(kid10_part506),(kid10_part507),(kid10_part508),(kid10_part509),(kid10_part510),(kid10_part511),(kid10_part536),(kid10_part537),(kid10_part538),(kid10_part539),(kid10_part540),(kid10_part541)])

theorem kid10_part469_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid10_part469) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid10_part470),(kid10_part471),(kid10_part472),(kid10_part473),(kid10_part474),(kid10_part475),(kid10_part500),(kid10_part501),(kid10_part502),(kid10_part503),(kid10_part504),(kid10_part505),(kid10_part506),(kid10_part507),(kid10_part508),(kid10_part509),(kid10_part510),(kid10_part511),(kid10_part536),(kid10_part537),(kid10_part538),(kid10_part539),(kid10_part540),(kid10_part541)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part470_checked

  · exact kid10_part500_checked

  · exact kid10_part506_checked

  · exact kid10_part536_checked

  · exact kid10_part471_checked

  · exact kid10_part501_checked

  · exact kid10_part507_checked

  · exact kid10_part537_checked

  · exact kid10_part472_checked

  · exact kid10_part502_checked

  · exact kid10_part508_checked

  · exact kid10_part538_checked

  · exact kid10_part473_checked

  · exact kid10_part503_checked

  · exact kid10_part509_checked

  · exact kid10_part539_checked

  · exact kid10_part474_checked

  · exact kid10_part504_checked

  · exact kid10_part510_checked

  · exact kid10_part540_checked

  · exact kid10_part475_checked

  · exact kid10_part505_checked

  · exact kid10_part511_checked

  · exact kid10_part541_checked

def kid10_part566 : Audit := .cycle 7 3 true (3)
theorem kid10_part566_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid10_part566) = true := by rfl

def kid10_part567 : Audit := .cycle 0 11 true (0)
theorem kid10_part567_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid10_part567) = true := by rfl

def kid10_part568 : Audit := .cycle 4 5 true (1)
theorem kid10_part568_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid10_part568) = true := by rfl

def kid10_part570 : Audit := .cycle 0 15 true (0)
theorem kid10_part570_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part570) = true := by rfl

def kid10_part571 : Audit := .cycle 2 13 true (1)
theorem kid10_part571_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part571) = true := by rfl

def kid10_part572 : Audit := .cycle 35 1 false (3)
theorem kid10_part572_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part572) = true := by rfl

def kid10_part573 : Audit := .cycle 0 48 true (0)
theorem kid10_part573_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part573) = true := by rfl

def kid10_part574 : Audit := .cycle 13 1 false (-1)
theorem kid10_part574_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part574) = true := by rfl

def kid10_part576 : Audit := .cycle 30 15 true (1)
theorem kid10_part576_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part576) = true := by rfl

def kid10_part577 : Audit := .split 12 (1,true) (byMove [
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 3, 1],[128, 256, 8, 16, 16, 2097160, 8192, 16384, 8, 256, 16, 2097152, 8192, 16384, 2097152, 256, 16777216, 16, 128, 256, 2097152, 16, 16777216, 2097160, 16777216],[256, 16384, 16, 1, 16, 16777216, 16384, 8, 16, 1, 16777216, 16777216, 16384, 2097152, 4194304, 262144, 16777216, 16777216, 256, 16384, 4194304, 262144, 16, 16777216, 16777216],21037056⟩,
.cycle 10 21 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 22 false (2),
.cycle 0 19 true (0),
.cycle 0 40 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 33 true (0),
.cycle 10 18 false (2),
.cycle 10 16 false (2),
.last 53 (5,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 23 (5,true),
.cycle 0 19 true (0),
.cycle 0 40 true (0),
.cycle 13 29 true (0),
.cycle 0 44 true (0),
.cycle 10 13 false (2),
.cycle 11 2 true (0)
])
theorem kid10_part577_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part577) = true := by rfl

def kid10_part578 : Audit := .cycle 13 1 false (1)
theorem kid10_part578_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part578) = true := by rfl

def kid10_part579 : Audit := .cycle 0 19 true (0)
theorem kid10_part579_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part579) = true := by rfl

def kid10_part580 : Audit := .cycle 14 1 false (-2)
theorem kid10_part580_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part580) = true := by rfl

def kid10_part581 : Audit := .split 12 (5,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 65792, 65792, 98560, 128, 256, 32768, 256, 65793, 98304, 128, 256, 8, 65536, 65792, 65792, 262144],[256, 262144, 16, 1, 98560, 256, 256, 262144, 65536, 4096, 98304, 32768, 256, 262144, 16, 1, 65792, 256, 262144],262144⟩,
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 19 true (0),
.cycle 40 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 18 1 false (-2),
.cycle 23 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 49 true (0),
.cycle 40 1 false (2),
.cycle 44 1 false (2),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part581_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part581) = true := by rfl

def kid10_part582 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 24 true (0),
.cycle 23 1 false (1),
.cycle 0 18 true (0),
.last 22 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 0 25 true (0),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 14 (5,true),
.cycle 0 18 true (0),
.cycle 0 26 true (0),
.cycle 0 22 true (0),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid10_part582_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part582) = true := by rfl

def kid10_part583 : Audit := .cycle 1 15 true (1)
theorem kid10_part583_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part583) = true := by rfl

def kid10_part584 : Audit := .cycle 2 13 true (1)
theorem kid10_part584_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part584) = true := by rfl

def kid10_part585 : Audit := .cycle 35 1 false (3)
theorem kid10_part585_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part585) = true := by rfl

def kid10_part586 : Audit := .cycle 16 1 false (0)
theorem kid10_part586_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part586) = true := by rfl

def kid10_part587 : Audit := .split 13 (5,true) (byMove [
.cycle 2 24 true (1),
.cycle 0 17 true (0),
.cycle 33 1 true (3),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 1 true (3),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 30 1 false (6),
.cycle 0 15 true (0),
.cycle 15 1 true (3),
.cycle 15 1 true (5),
.last 15 (1,true),
.cycle 17 1 true (3),
.cycle 2 15 true (1),
.cycle 29 1 true (3),
.cycle 20 1 false (0),
.cycle 12 2 true (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 15 5 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part587_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part587) = true := by rfl

def kid10_part588 : Audit := .split 19 (1,true) (byMove [
.cycle 10 17 false (2),
.cycle 12 14 false (2),
.cycle 21 1 false (-1),
.last 31 (5,true),
.cycle 16 4 false (0),
.last 20 (5,true),
.cycle 6 26 false (4),
.cycle 6 18 false (4),
.cycle 26 15 true (0),
.cycle 10 15 false (2),
.cycle 14 6 false (2),
.last 23 (5,true),
.cycle 12 8 false (2),
.cycle 10 13 false (2),
.cycle 16 5 false (0),
.cycle 28 17 true (0),
.cycle 16 4 false (0),
.last 20 (5,true),
.last 31 (5,true),
.last 29 (5,true),
.cycle 26 15 true (0),
.cycle 6 20 false (4),
.last 22 (5,true),
.last 30 (5,true)
])
theorem kid10_part588_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part588) = true := by rfl

def kid10_part589 : Audit := .split 12 (1,true) (byMove [
.last 19 (5,true),
.cycle 0 32 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 6 false (0),
.last 64 (5,true),
.cycle 26 6 false (7),
.cycle 14 1 false (2),
.cycle 0 17 true (0),
.cycle 13 6 false (1),
.last 13 (5,true),
.cycle 10 7 false (2),
.cycle 10 5 false (2),
.last 70 (5,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (2),
.cycle 2 41 true (0),
.cycle 1 19 true (0),
.cycle 13 6 false (2),
.cycle 0 17 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part589_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part589) = true := by rfl

def kid10_part590 : Audit := .cycle 0 30 true (-1)
theorem kid10_part590_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part590) = true := by rfl

def kid10_part591 : Audit := .cycle 0 48 true (0)
theorem kid10_part591_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part591) = true := by rfl

def kid10_part592 : Audit := .cycle 14 1 false (-2)
theorem kid10_part592_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part592) = true := by rfl

def kid10_part593 : Audit := .split 12 (5,true) (byMove [
.cycle 22 47 true (-1),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 48 true (0),
.last 13 (1,true),
.cycle 14 1 false (2),
.last 15 (1,true),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 0 56 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 48 true (0),
.last 13 (1,true),
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 17 3 true (3)
])
theorem kid10_part593_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part593) = true := by rfl

def kid10_part594 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 14 15 false (2),
.last 18 (5,true),
.cycle 0 18 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 19 (5,true),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 14 (5,true),
.cycle 0 18 true (0),
.cycle 10 9 false (3),
.cycle 0 22 true (0),
.cycle 5 9 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid10_part594_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part594) = true := by rfl

def kid10_part595 : Audit := .cycle 1 15 true (1)
theorem kid10_part595_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part595) = true := by rfl

def kid10_part596 : Audit := .cycle 2 13 true (1)
theorem kid10_part596_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part596) = true := by rfl

def kid10_part597 : Audit := .cycle 2 19 true (1)
theorem kid10_part597_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part597) = true := by rfl

def kid10_part598 : Audit := .split 14 (5,true) (byMove [
.cycle 0 58 true (-1),
.cycle 10 12 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.last 16 (1,true),
.cycle 32 3 false (4),
.cycle 20 3 false (4),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 24 3 false (5),
.last 16 (1,true),
.cycle 18 3 false (0),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.last 16 (1,true),
.cycle 19 13 true (1),
.cycle 0 40 true (0),
.cycle 38 3 false (4),
.cycle 15 3 false (1),
.cycle 19 7 true (2)
])
theorem kid10_part598_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part598) = true := by rfl

def kid10_part599 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 20 1 false (0),
.last 16 (1,true),
.cycle 28 1 true (-2),
.cycle 28 1 true (-2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 5 16 true (1),
.cycle 0 15 true (0),
.cycle 15 1 true (3),
.cycle 15 1 true (5),
.cycle 17 1 true (3),
.last 14 (1,true),
.cycle 21 1 true (3),
.cycle 5 9 true (1),
.cycle 22 1 false (-2),
.cycle 15 3 false (1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 2 20 true (1),
.cycle 0 15 true (0),
.cycle 17 13 false (3),
.cycle 15 1 true (5)
])
theorem kid10_part599_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part599) = true := by rfl

def kid10_part575 : Audit := .split 11 (5,false) (byMove [(kid10_part576),(kid10_part577),(kid10_part578),(kid10_part579),(kid10_part580),(kid10_part581),(kid10_part582),(kid10_part583),(kid10_part584),(kid10_part585),(kid10_part586),(kid10_part587),(kid10_part588),(kid10_part589),(kid10_part590),(kid10_part591),(kid10_part592),(kid10_part593),(kid10_part594),(kid10_part595),(kid10_part596),(kid10_part597),(kid10_part598),(kid10_part599)])

theorem kid10_part575_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part575) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part576),(kid10_part577),(kid10_part578),(kid10_part579),(kid10_part580),(kid10_part581),(kid10_part582),(kid10_part583),(kid10_part584),(kid10_part585),(kid10_part586),(kid10_part587),(kid10_part588),(kid10_part589),(kid10_part590),(kid10_part591),(kid10_part592),(kid10_part593),(kid10_part594),(kid10_part595),(kid10_part596),(kid10_part597),(kid10_part598),(kid10_part599)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part576_checked

  · exact kid10_part582_checked

  · exact kid10_part588_checked

  · exact kid10_part594_checked

  · exact kid10_part577_checked

  · exact kid10_part583_checked

  · exact kid10_part589_checked

  · exact kid10_part595_checked

  · exact kid10_part578_checked

  · exact kid10_part584_checked

  · exact kid10_part590_checked

  · exact kid10_part596_checked

  · exact kid10_part579_checked

  · exact kid10_part585_checked

  · exact kid10_part591_checked

  · exact kid10_part597_checked

  · exact kid10_part580_checked

  · exact kid10_part586_checked

  · exact kid10_part592_checked

  · exact kid10_part598_checked

  · exact kid10_part581_checked

  · exact kid10_part587_checked

  · exact kid10_part593_checked

  · exact kid10_part599_checked

def kid10_part600 : Audit := .cycle 6 5 true (2)
theorem kid10_part600_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part600) = true := by rfl

def kid10_part601 : Audit := .split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 10 48 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 0 45 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 10 48 true (0),
.cycle 19 1 false (1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 20 7 false (0),
.last 17 (5,true),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.last 15 (5,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 14 (5,true)
]),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 24 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 10 30 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (9),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.last 13 (5,false),
.last 15 (5,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 10 40 true (0),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 10 48 true (0),
.cycle 19 22 true (1),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.last 13 (5,true),
.last 15 (5,true),
.cycle 1 20 true (1),
.cycle 5 9 true (1),
.cycle 10 40 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.last 13 (5,true)
]),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 14 (5,false),
.cycle 22 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid10_part601_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part601) = true := by rfl

def kid10_part602 : Audit := .cycle 41 1 false (9)
theorem kid10_part602_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part602) = true := by rfl

def kid10_part603 : Audit := .cycle 2 11 true (1)
theorem kid10_part603_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part603) = true := by rfl

def kid10_part604 : Audit := .cycle 24 1 false (6)
theorem kid10_part604_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part604) = true := by rfl

def kid10_part606 : Audit := .cycle 7 7 true (2)
theorem kid10_part606_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part606) = true := by rfl

def kid10_part607 : Audit := .cycle 0 15 true (0)
theorem kid10_part607_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part607) = true := by rfl

def kid10_part608 : Audit := .split 29 (5,false) (byMove [
.cycle 0 30 true (0),
.cycle 10 39 true (0),
.cycle 21 9 true (1),
.cycle 40 1 false (4),
.cycle 35 1 false (3),
.cycle 34 1 false (2),
.cycle 0 30 true (0),
.cycle 10 59 true (0),
.cycle 10 29 true (0),
.cycle 13 18 true (0),
.cycle 37 1 false (3),
.cycle 29 1 true (5),
.last 31 (1,true),
.cycle 7 24 true (0),
.cycle 0 32 true (0),
.cycle 23 7 true (1),
.cycle 35 1 false (3),
.cycle 34 1 false (2),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 10 48 true (0),
.cycle 10 61 true (0),
.cycle 13 22 true (0),
.cycle 29 1 true (5)
])
theorem kid10_part608_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part608) = true := by rfl

def kid10_part609 : Audit := .cycle 21 1 false (1)
theorem kid10_part609_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part609) = true := by rfl

def kid10_part610 : Audit := .cycle 16 1 false (0)
theorem kid10_part610_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part610) = true := by rfl

def kid10_part611 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 21 true (1),
.cycle 25 1 false (1),
.cycle 34 1 false (2),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 19 1 false (1),
.cycle 15 1 true (3),
.last 14 (1,true),
.last 20 (1,true),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.cycle 17 1 true (1)
])
theorem kid10_part611_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part611) = true := by rfl

def kid10_part612 : Audit := .cycle 2 11 true (1)
theorem kid10_part612_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part612) = true := by rfl

def kid10_part613 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 58 true (0),
.last 20 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (9),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.last 13 (5,false),
.cycle 6 9 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 10 50 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 13 (5,false)
])
theorem kid10_part613_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part613) = true := by rfl

def kid10_part614 : Audit := .cycle 24 1 false (6)
theorem kid10_part614_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part614) = true := by rfl

def kid10_part615 : Audit := .cycle 0 13 true (0)
theorem kid10_part615_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part615) = true := by rfl

def kid10_part616 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 33 1 false (5),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 48, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 41 1 false (9),
.cycle 28 1 false (8),
.cycle 13 1 true (5),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 32 1 false (8),
.cycle 13 1 true (5)
])
theorem kid10_part616_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part616) = true := by rfl

def kid10_part617 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 43 1 false (5),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 8, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 28 1 false (8),
.cycle 13 1 true (5),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part617_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part617) = true := by rfl

def kid10_part618 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.last 23 (5,false),
.cycle 23 1 false (1),
.cycle 0 18 true (0),
.last 15 (5,false),
.cycle 23 3 false (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 24 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.last 21 (5,false),
.cycle 5 9 true (1),
.cycle 10 4 true (2),
.cycle 10 10 true (0),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 15 (5,false),
.cycle 6 9 true (2)
])
theorem kid10_part618_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part618) = true := by rfl

def kid10_part619 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 9 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.last 32 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 15 true (2),
.cycle 7 19 true (2),
.cycle 10 14 true (2),
.cycle 15 1 true (5),
.last 17 (1,true),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 13 7 true (2),
.cycle 7 18 true (2),
.cycle 10 11 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 7 13 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part619_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part619) = true := by rfl

def kid10_part620 : Audit := .cycle 2 13 true (1)
theorem kid10_part620_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part620) = true := by rfl

def kid10_part621 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 true (0),
.cycle 10 33 true (0),
.cycle 19 9 true (1),
.cycle 35 1 false (3),
.cycle 30 1 false (2),
.cycle 29 1 false (1),
.cycle 0 26 true (0),
.cycle 10 49 true (0),
.cycle 10 25 true (0),
.cycle 12 16 true (0),
.cycle 32 1 false (2),
.cycle 25 1 true (5),
.last 27 (1,true),
.cycle 7 20 true (0),
.cycle 0 28 true (0),
.cycle 19 7 true (1),
.cycle 30 1 false (2),
.cycle 29 1 false (1),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 10 40 true (0),
.cycle 10 51 true (0),
.cycle 12 18 true (0),
.cycle 25 1 true (5)
])
theorem kid10_part621_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part621) = true := by rfl

def kid10_part622 : Audit := .cycle 16 1 false (0)
theorem kid10_part622_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part622) = true := by rfl

def kid10_part623 : Audit := .split 12 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 2 15 true (1),
.cycle 23 9 true (1),
.cycle 48 1 false (2),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 48, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 13 true (1),
.cycle 44 1 false (8),
.cycle 11 2 true (2),
.last 14 (1,true),
.cycle 7 16 true (1),
.cycle 5 9 true (1),
.cycle 20 7 true (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 2 14 true (1),
.cycle 2 13 true (1),
.cycle 13 6 true (3),
.cycle 17 3 false (1)
])
theorem kid10_part623_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part623) = true := by rfl

def kid10_part624 : Audit := .cycle 2 11 true (1)
theorem kid10_part624_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part624) = true := by rfl

def kid10_part625 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 17 (5,false),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 13 (5,false)
])
theorem kid10_part625_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part625) = true := by rfl

def kid10_part626 : Audit := .cycle 7 5 true (2)
theorem kid10_part626_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part626) = true := by rfl

def kid10_part627 : Audit := .cycle 0 13 true (0)
theorem kid10_part627_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part627) = true := by rfl

def kid10_part628 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 14 3 true (3),
.cycle 15 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 22 3 true (6),
.cycle 29 3 true (7),
.cycle 19 3 true (5),
.cycle 13 1 true (5),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 9 5 true (2),
.cycle 16 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 14 3 true (5),
.cycle 13 1 true (5)
])
theorem kid10_part628_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part628) = true := by rfl

def kid10_part629 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 84 1 false (4),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 22 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 0 19 true (0),
.cycle 2 14 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part629_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part629) = true := by rfl

def kid10_part605 : Audit := .split 11 (5,true) (byMove [(kid10_part606),(kid10_part607),(kid10_part608),(kid10_part609),(kid10_part610),(kid10_part611),(kid10_part612),(kid10_part613),(kid10_part614),(kid10_part615),(kid10_part616),(kid10_part617),(kid10_part618),(kid10_part619),(kid10_part620),(kid10_part621),(kid10_part622),(kid10_part623),(kid10_part624),(kid10_part625),(kid10_part626),(kid10_part627),(kid10_part628),(kid10_part629)])

theorem kid10_part605_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part605) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part606),(kid10_part607),(kid10_part608),(kid10_part609),(kid10_part610),(kid10_part611),(kid10_part612),(kid10_part613),(kid10_part614),(kid10_part615),(kid10_part616),(kid10_part617),(kid10_part618),(kid10_part619),(kid10_part620),(kid10_part621),(kid10_part622),(kid10_part623),(kid10_part624),(kid10_part625),(kid10_part626),(kid10_part627),(kid10_part628),(kid10_part629)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part606_checked

  · exact kid10_part612_checked

  · exact kid10_part618_checked

  · exact kid10_part624_checked

  · exact kid10_part607_checked

  · exact kid10_part613_checked

  · exact kid10_part619_checked

  · exact kid10_part625_checked

  · exact kid10_part608_checked

  · exact kid10_part614_checked

  · exact kid10_part620_checked

  · exact kid10_part626_checked

  · exact kid10_part609_checked

  · exact kid10_part615_checked

  · exact kid10_part621_checked

  · exact kid10_part627_checked

  · exact kid10_part610_checked

  · exact kid10_part616_checked

  · exact kid10_part622_checked

  · exact kid10_part628_checked

  · exact kid10_part611_checked

  · exact kid10_part617_checked

  · exact kid10_part623_checked

  · exact kid10_part629_checked

def kid10_part630 : Audit := .split 12 (1,true) (byMove [
.cycle 2 15 true (1),
.cycle 10 25 false (2),
.cycle 20 1 false (0),
.cycle 0 20 true (0),
.cycle 18 3 false (0),
.split 13 (5,true) (byMove [
.cycle 36 17 true (1),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 0 23 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (0),
.last 14 (5,false),
.cycle 19 3 false (0),
.last 15 (5,false),
.cycle 0 40 true (-1),
.cycle 0 56 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 15 true (1),
.cycle 2 23 true (1),
.cycle 10 8 true (0),
.last 14 (5,false)
]),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.cycle 13 10 true (3),
.cycle 2 13 true (1),
.cycle 13 11 true (2),
.split 13 (5,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 17 true (0),
.last 23 (5,false),
.cycle 0 19 true (0),
.last 21 (5,false),
.last 14 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.last 30 (5,false),
.cycle 0 15 true (0),
.last 17 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 2 15 true (1),
.last 21 (5,false),
.cycle 10 8 true (0),
.last 14 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 6 9 true (1),
.last 15 (5,false)
]),
.cycle 13 15 true (1),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 19 true (1),
.cycle 10 6 true (0),
.split 13 (5,true) (byMove [
.cycle 16 23 true (1),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 2 19 true (1),
.last 15 (5,false),
.cycle 60 1 false (6),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.last 17 (5,false),
.cycle 10 6 true (0),
.last 15 (5,false),
.cycle 28 23 true (0),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 2 19 true (1),
.cycle 12 2 true (1),
.cycle 14 15 true (2),
.cycle 5 9 true (1),
.cycle 14 19 true (1),
.last 17 (5,false)
]),
.cycle 2 22 true (1),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 13 7 true (2),
.split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 15 (5,false),
.cycle 10 10 true (0),
.last 17 (5,false),
.cycle 10 12 true (0),
.last 17 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.cycle 10 11 true (1),
.cycle 0 15 true (0),
.last 17 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.cycle 12 2 true (2),
.last 23 (5,false),
.cycle 5 9 true (1),
.last 27 (5,false),
.last 17 (5,false),
.cycle 2 13 true (1),
.last 15 (5,false),
.cycle 2 22 true (1),
.cycle 0 15 true (0),
.last 33 (5,false),
.last 15 (5,false)
])
])
theorem kid10_part630_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part630) = true := by rfl

def kid10_part631 : Audit := .split 22 (1,true) (byMove [
.cycle 5 20 true (1),
.cycle 10 172 false (7),
.cycle 54 1 false (0),
.cycle 0 33 true (0),
.cycle 25 1 false (-1),
.split 23 (5,true) (byMove [
.cycle 10 21 true (0),
.last 25 (5,false),
.cycle 25 1 false (1),
.cycle 11 15 true (0),
.cycle 43 1 false (-3),
.last 25 (5,false),
.cycle 0 33 true (0),
.cycle 11 13 true (1),
.cycle 5 20 true (1),
.cycle 10 19 true (0),
.cycle 54 1 false (0),
.last 24 (5,false),
.cycle 56 3 false (0),
.last 25 (5,false),
.cycle 0 94 true (-2),
.cycle 10 51 true (0),
.last 34 (5,false),
.last 25 (5,false),
.cycle 0 33 true (0),
.cycle 11 13 true (1),
.cycle 5 20 true (1),
.cycle 12 15 true (1),
.last 27 (5,false),
.last 24 (5,false)
]),
.cycle 15 9 true (2),
.cycle 1 25 true (1),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 10 13 true (1),
.split 23 (5,true) (byMove [
.cycle 14 11 true (2),
.cycle 2 26 true (1),
.cycle 12 17 true (1),
.cycle 2 28 true (1),
.cycle 28 1 false (0),
.last 24 (5,false),
.cycle 6 18 true (1),
.cycle 1 25 true (1),
.cycle 7 20 true (1),
.cycle 2 24 true (1),
.cycle 13 11 true (2),
.last 26 (5,false),
.last 32 (5,false),
.cycle 11 13 true (1),
.cycle 5 20 true (1),
.cycle 12 15 true (1),
.cycle 28 1 false (0),
.last 24 (5,false),
.cycle 18 7 true (2),
.cycle 1 25 true (1),
.cycle 15 9 true (2),
.cycle 2 24 true (1),
.cycle 13 18 true (2),
.last 26 (5,false)
]),
.cycle 10 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 64, 64],[4, 16, 16, 1, 16, 64, 64],96⟩,
.cycle 10 17 true (1),
.cycle 12 13 true (1),
.cycle 25 1 false (-1),
.split 23 (5,true) (byMove [
.last 36 (5,false),
.last 25 (5,false),
.cycle 25 1 false (1),
.cycle 28 1 false (0),
.last 85 (5,false),
.last 25 (5,false),
.cycle 12 13 true (1),
.last 25 (5,false),
.cycle 10 15 true (1),
.last 34 (5,false),
.cycle 10 17 true (1),
.last 28 (5,false),
.cycle 10 19 true (0),
.last 25 (5,false),
.cycle 10 21 true (0),
.cycle 10 17 true (0),
.cycle 50 1 false (-2),
.last 25 (5,false),
.cycle 12 13 true (1),
.cycle 22 2 true (1),
.cycle 10 15 true (1),
.last 34 (5,false),
.last 29 (5,false),
.last 28 (5,false)
]),
.cycle 15 9 true (2),
.cycle 1 25 true (1),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 21 2 true (2),
.split 23 (5,true) (byMove [
.cycle 2 26 true (1),
.last 25 (5,false),
.cycle 31 1 false (1),
.cycle 0 29 true (0),
.cycle 24 22 false (2),
.last 27 (5,false),
.cycle 6 18 true (1),
.cycle 1 25 true (1),
.cycle 7 20 true (1),
.cycle 2 24 true (1),
.cycle 13 11 true (2),
.last 26 (5,false),
.cycle 12 13 true (2),
.cycle 22 2 true (2),
.cycle 10 15 true (1),
.cycle 15 11 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 64, 64],[4, 32, 16, 1, 16, 16, 64],96⟩,
.last 27 (5,false),
.cycle 18 7 true (2),
.cycle 1 25 true (1),
.cycle 15 9 true (2),
.cycle 2 24 true (1),
.cycle 24 7 true (3),
.last 26 (5,false)
])
])
theorem kid10_part631_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part631) = true := by rfl

def kid10_part632 : Audit := .cycle 5 7 true (1)
theorem kid10_part632_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part632) = true := by rfl

def kid10_part633 : Audit := .cycle 28 1 false (2)
theorem kid10_part633_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part633) = true := by rfl

def kid10_part634 : Audit := .cycle 13 1 false (-1)
theorem kid10_part634_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part634) = true := by rfl

def kid10_part636 : Audit := .cycle 14 19 true (1)
theorem kid10_part636_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part636) = true := by rfl

def kid10_part637 : Audit := .split 12 (1,true) (byMove [
.cycle 14 9 true (0),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 33 false (4),
.cycle 6 9 true (0),
.cycle 24 9 true (1),
.cycle 13 9 true (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 9 true (0),
.cycle 6 25 false (4),
.cycle 7 21 false (4),
.cycle 18 9 true (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 19 (5,true),
.last 20 (5,true),
.last 28 (5,true),
.cycle 13 9 true (1),
.cycle 28 9 true (1),
.cycle 35 9 true (0),
.cycle 11 2 true (0)
])
theorem kid10_part637_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part637) = true := by rfl

def kid10_part638 : Audit := .cycle 13 1 false (1)
theorem kid10_part638_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part638) = true := by rfl

def kid10_part639 : Audit := .split 14 (1,true) (byMove [
.cycle 38 1 false (0),
.cycle 53 1 false (1),
.cycle 16 1 false (2),
.cycle 0 22 true (0),
.cycle 17 1 false (-1),
.last 15 (5,true),
.cycle 6 9 true (0),
.cycle 76 1 false (2),
.cycle 0 23 true (0),
.cycle 36 1 false (0),
.cycle 29 1 false (1),
.last 15 (5,true),
.cycle 35 1 false (1),
.cycle 10 8 true (0),
.cycle 18 1 false (0),
.cycle 35 1 false (3),
.cycle 17 1 false (-1),
.last 15 (5,true),
.last 20 (5,true),
.cycle 1 16 true (0),
.cycle 2 19 true (0),
.cycle 20 11 true (2),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid10_part639_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part639) = true := by rfl

def kid10_part640 : Audit := .cycle 14 1 false (-2)
theorem kid10_part640_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part640) = true := by rfl

def kid10_part641 : Audit := .split 12 (5,true) (byMove [
.cycle 35 1 false (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 28 1 false (2),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 18 1 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 14 (1,true),
.last 29 (1,true),
.cycle 10 19 true (0),
.cycle 34 1 false (2),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part641_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part641) = true := by rfl

def kid10_part642 : Audit := .cycle 2 15 true (1)
theorem kid10_part642_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part642) = true := by rfl

def kid10_part643 : Audit := .split 12 (1,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 17 1 false (-1),
.cycle 1 19 true (1),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.cycle 57 1 false (9),
.cycle 2 13 true (1),
.cycle 42 1 false (6),
.last 13 (5,true),
.last 34 (5,true),
.last 28 (5,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.last 18 (5,true),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part643_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part643) = true := by rfl

def kid10_part644 : Audit := .cycle 42 1 false (6)
theorem kid10_part644_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part644) = true := by rfl

def kid10_part645 : Audit := .cycle 5 7 true (1)
theorem kid10_part645_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part645) = true := by rfl

def kid10_part646 : Audit := .cycle 10 2 true (1)
theorem kid10_part646_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part646) = true := by rfl

def kid10_part647 : Audit := .split 12 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 43 1 false (3),
.cycle 0 56 true (0),
.cycle 17 1 false (-1),
.cycle 19 1 true (3),
.cycle 6 7 true (1),
.last 13 (1,true),
.cycle 57 1 false (9),
.cycle 2 13 true (1),
.cycle 42 1 false (6),
.cycle 15 1 true (5),
.last 14 (1,true),
.last 29 (1,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 24 true (0),
.last 13 (1,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 12 2 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part647_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part647) = true := by rfl

def kid10_part648 : Audit := .cycle 10 4 true (0)
theorem kid10_part648_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part648) = true := by rfl

def kid10_part649 : Audit := .split 12 (1,true) (byMove [
.cycle 10 39 true (-1),
.cycle 10 27 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 12 false (2),
.cycle 10 21 true (0),
.cycle 10 20 true (0),
.cycle 10 8 true (0),
.cycle 10 23 true (0),
.cycle 10 7 false (2),
.last 13 (5,true),
.cycle 10 7 false (2),
.cycle 10 5 false (2),
.cycle 10 27 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 6 false (2),
.last 28 (5,true),
.cycle 1 16 true (0),
.cycle 10 4 true (0),
.cycle 10 23 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part649_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part649) = true := by rfl

def kid10_part650 : Audit := .cycle 22 17 true (0)
theorem kid10_part650_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part650) = true := by rfl

def kid10_part651 : Audit := .cycle 29 1 false (1)
theorem kid10_part651_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part651) = true := by rfl

def kid10_part652 : Audit := .cycle 14 1 false (-2)
theorem kid10_part652_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part652) = true := by rfl

def kid10_part653 : Audit := .split 12 (5,true) (byMove [
.cycle 10 51 true (-1),
.cycle 10 33 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 28 1 false (2),
.last 13 (1,true),
.cycle 15 1 false (1),
.cycle 30 1 false (4),
.cycle 14 1 false (0),
.cycle 17 1 false (5),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 34 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 11 true (1),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 5 34 true (0),
.cycle 12 2 true (0),
.cycle 15 3 true (3)
])
theorem kid10_part653_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part653) = true := by rfl

def kid10_part654 : Audit := .cycle 2 15 true (1)
theorem kid10_part654_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part654) = true := by rfl

def kid10_part655 : Audit := .split 12 (1,true) (byMove [
.cycle 2 15 true (1),
.cycle 10 25 false (2),
.cycle 20 1 false (0),
.cycle 0 20 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.cycle 13 10 true (3),
.cycle 2 13 true (1),
.last 22 (5,true),
.last 13 (5,true),
.last 28 (5,true),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 19 true (1),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part655_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part655) = true := by rfl

def kid10_part656 : Audit := .split 22 (5,true) (byMove [
.cycle 5 20 true (1),
.last 23 (1,true),
.cycle 54 1 false (0),
.last 25 (1,true),
.cycle 25 1 false (-1),
.cycle 10 172 false (7),
.cycle 15 9 true (2),
.last 23 (1,true),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 10 13 true (1),
.cycle 2 25 true (1),
.cycle 10 15 true (1),
.last 23 (1,true),
.cycle 10 17 true (1),
.cycle 12 13 true (1),
.cycle 25 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 4, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 15 9 true (2),
.last 23 (1,true),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 21 2 true (2),
.cycle 2 25 true (1)
])
theorem kid10_part656_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part656) = true := by rfl

def kid10_part657 : Audit := .cycle 5 7 true (1)
theorem kid10_part657_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part657) = true := by rfl

def kid10_part658 : Audit := .split 13 (5,true) (byMove [
.cycle 16 23 true (1),
.last 14 (1,true),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 18 1 false (-2),
.cycle 14 6 false (0),
.cycle 2 19 true (1),
.last 14 (1,true),
.cycle 60 1 false (6),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.cycle 14 8 true (2),
.cycle 10 6 true (0),
.last 14 (1,true),
.cycle 28 23 true (0),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.cycle 14 3 false (0),
.cycle 2 19 true (1),
.last 14 (1,true),
.cycle 12 15 true (1),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.cycle 14 6 true (2)
])
theorem kid10_part658_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part658) = true := by rfl

def kid10_part659 : Audit := .split 12 (5,true) (byMove [
.cycle 2 15 true (1),
.last 13 (1,true),
.cycle 20 1 false (0),
.last 15 (1,true),
.cycle 15 1 false (-1),
.cycle 37 1 true (-3),
.cycle 6 7 true (1),
.last 13 (1,true),
.cycle 13 10 true (3),
.cycle 2 13 true (1),
.cycle 10 13 true (1),
.cycle 15 1 true (5),
.cycle 10 21 true (1),
.last 13 (1,true),
.cycle 10 4 true (1),
.cycle 2 19 true (1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 24 true (0),
.last 13 (1,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 12 2 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part659_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part659) = true := by rfl

def kid10_part635 : Audit := .split 11 (5,false) (byMove [(kid10_part636),(kid10_part637),(kid10_part638),(kid10_part639),(kid10_part640),(kid10_part641),(kid10_part642),(kid10_part643),(kid10_part644),(kid10_part645),(kid10_part646),(kid10_part647),(kid10_part648),(kid10_part649),(kid10_part650),(kid10_part651),(kid10_part652),(kid10_part653),(kid10_part654),(kid10_part655),(kid10_part656),(kid10_part657),(kid10_part658),(kid10_part659)])

theorem kid10_part635_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part635) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part636),(kid10_part637),(kid10_part638),(kid10_part639),(kid10_part640),(kid10_part641),(kid10_part642),(kid10_part643),(kid10_part644),(kid10_part645),(kid10_part646),(kid10_part647),(kid10_part648),(kid10_part649),(kid10_part650),(kid10_part651),(kid10_part652),(kid10_part653),(kid10_part654),(kid10_part655),(kid10_part656),(kid10_part657),(kid10_part658),(kid10_part659)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part636_checked

  · exact kid10_part642_checked

  · exact kid10_part648_checked

  · exact kid10_part654_checked

  · exact kid10_part637_checked

  · exact kid10_part643_checked

  · exact kid10_part649_checked

  · exact kid10_part655_checked

  · exact kid10_part638_checked

  · exact kid10_part644_checked

  · exact kid10_part650_checked

  · exact kid10_part656_checked

  · exact kid10_part639_checked

  · exact kid10_part645_checked

  · exact kid10_part651_checked

  · exact kid10_part657_checked

  · exact kid10_part640_checked

  · exact kid10_part646_checked

  · exact kid10_part652_checked

  · exact kid10_part658_checked

  · exact kid10_part641_checked

  · exact kid10_part647_checked

  · exact kid10_part653_checked

  · exact kid10_part659_checked

def kid10_part660 : Audit := .cycle 6 5 true (2)
theorem kid10_part660_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part660) = true := by rfl

def kid10_part661 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 20 true (1),
.cycle 19 1 false (1),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 1 22 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 1 28 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 21 3 false (1),
.last 21 (5,false),
.cycle 0 20 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
]),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 1 19 true (1),
.cycle 1 19 true (1),
.last 13 (5,false),
.last 15 (5,false),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 1 16 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.split 12 (5,true) (byMove [
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 28 true (0),
.cycle 1 39 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.last 15 (5,false),
.cycle 10 8 true (0),
.cycle 1 20 true (1),
.cycle 5 9 true (1),
.cycle 1 24 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.last 15 (5,false)
]),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 14 (5,false),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid10_part661_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part661) = true := by rfl

def kid10_part662 : Audit := .cycle 2 11 true (1)
theorem kid10_part662_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part662) = true := by rfl

def kid10_part663 : Audit := .cycle 2 11 true (1)
theorem kid10_part663_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part663) = true := by rfl

def kid10_part664 : Audit := .cycle 11 3 true (3)
theorem kid10_part664_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part664) = true := by rfl

def kid10_part666 : Audit := .cycle 0 15 true (0)
theorem kid10_part666_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part666) = true := by rfl

def kid10_part667 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (0),
.last 21 (5,false),
.cycle 25 1 false (1),
.last 23 (5,false),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 29 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 21 9 false (2),
.last 24 (5,false),
.last 19 (5,false),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
])
theorem kid10_part667_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part667) = true := by rfl

def kid10_part668 : Audit := .cycle 19 1 false (1)
theorem kid10_part668_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part668) = true := by rfl

def kid10_part669 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 26 1 false (2),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (5,false),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.last 15 (5,false),
.cycle 6 9 true (2),
.last 19 (5,false),
.last 17 (5,false),
.cycle 2 15 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 0 19 true (0),
.last 15 (5,false)
])
theorem kid10_part669_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part669) = true := by rfl

def kid10_part670 : Audit := .split 13 (5,false) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 23 1 false (1),
.last 16 (1,true),
.cycle 12 2 true (2),
.cycle 21 1 false (-1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 22 9 true (4),
.cycle 0 15 true (0),
.cycle 8 8 true (2),
.cycle 19 1 true (3),
.cycle 6 12 true (2),
.last 14 (1,true),
.cycle 17 3 true (3),
.cycle 5 9 true (1),
.cycle 10 4 true (2),
.cycle 21 1 false (-1),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 14 5 true (4),
.cycle 16 1 true (4)
])
theorem kid10_part670_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part670) = true := by rfl

def kid10_part671 : Audit := .split 13 (5,false) (byMove [
.cycle 38 23 true (0),
.last 14 (1,true),
.cycle 15 1 false (1),
.cycle 0 19 true (0),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 28 true (0),
.cycle 0 17 true (0),
.cycle 24 9 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 1 true (3),
.last 23 (1,true),
.last 14 (1,true),
.cycle 0 27 true (0),
.cycle 0 49 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 98 27 false (4),
.cycle 0 17 true (0),
.cycle 2 20 true (1),
.cycle 0 19 true (0),
.cycle 17 5 false (1),
.cycle 21 1 true (-1)
])
theorem kid10_part671_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part671) = true := by rfl

def kid10_part672 : Audit := .cycle 2 11 true (1)
theorem kid10_part672_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part672) = true := by rfl

def kid10_part673 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 22 true (1),
.last 20 (5,false),
.last 20 (5,false),
.last 13 (5,false),
.cycle 6 9 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 13 (5,false)
])
theorem kid10_part673_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part673) = true := by rfl

def kid10_part674 : Audit := .split 20 (5,false) (byMove [
.cycle 2 20 true (1),
.last 21 (1,true),
.cycle 12 28 true (2),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 10 21 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 18 9 true (4),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.last 21 (1,true),
.cycle 18 3 true (4),
.cycle 2 21 true (1),
.cycle 18 11 true (4),
.cycle 10 21 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.cycle 18 12 true (4),
.cycle 20 1 true (6)
])
theorem kid10_part674_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part674) = true := by rfl

def kid10_part675 : Audit := .cycle 0 13 true (0)
theorem kid10_part675_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part675) = true := by rfl

def kid10_part676 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 8 14 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 8 14 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 9 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 12 3 true (4),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 8 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part676_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part676) = true := by rfl

def kid10_part677 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 41 true (1),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 21 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (2),
.cycle 3 29 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 13 1 true (5),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 2 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 32, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part677_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part677) = true := by rfl

def kid10_part678 : Audit := .split 15 (5,false) (byMove [
.cycle 2 15 true (1),
.last 16 (1,true),
.cycle 6 20 true (2),
.cycle 0 17 true (0),
.cycle 14 2 true (4),
.last 18 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 9 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 13 3 true (3),
.cycle 2 16 true (1),
.cycle 6 12 true (2),
.last 18 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 6 13 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part678_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part678) = true := by rfl

def kid10_part679 : Audit := .split 12 (1,true) (byMove [
.last 17 (5,false),
.cycle 2 15 true (1),
.last 29 (5,false),
.last 37 (5,false),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 2 13 true (1),
.last 17 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.last 21 (5,false),
.cycle 5 9 true (1),
.last 25 (5,false),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 2 13 true (1),
.last 17 (5,false),
.cycle 11 2 true (2)
])
theorem kid10_part679_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part679) = true := by rfl

def kid10_part680 : Audit := .split 17 (5,false) (byMove [
.cycle 2 17 true (1),
.last 18 (1,true),
.cycle 42 1 false (6),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 15 9 true (3),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 17 1 true (5),
.cycle 6 12 true (2),
.last 18 (1,true),
.cycle 15 3 true (3),
.cycle 2 18 true (1),
.cycle 13 5 true (3),
.cycle 2 20 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 13 6 true (3),
.cycle 17 1 true (5)
])
theorem kid10_part680_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part680) = true := by rfl

def kid10_part681 : Audit := .cycle 5 7 true (1)
theorem kid10_part681_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part681) = true := by rfl

def kid10_part682 : Audit := .cycle 10 2 true (2)
theorem kid10_part682_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part682) = true := by rfl

def kid10_part683 : Audit := .split 13 (5,false) (byMove [
.cycle 16 23 true (1),
.last 14 (1,true),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.last 14 (1,true),
.cycle 19 9 true (3),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.cycle 12 2 true (1),
.cycle 10 6 true (0),
.last 14 (1,true),
.cycle 35 3 true (3),
.cycle 10 42 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.last 14 (1,true),
.cycle 2 20 true (1),
.cycle 5 9 true (1),
.cycle 16 5 false (2),
.cycle 15 3 false (1)
])
theorem kid10_part683_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part683) = true := by rfl

def kid10_part684 : Audit := .cycle 2 11 true (1)
theorem kid10_part684_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part684) = true := by rfl

def kid10_part685 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 18 true (1),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 13 (5,false)
])
theorem kid10_part685_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part685) = true := by rfl

def kid10_part686 : Audit := .cycle 7 5 true (2)
theorem kid10_part686_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part686) = true := by rfl

def kid10_part687 : Audit := .cycle 0 13 true (0)
theorem kid10_part687_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part687) = true := by rfl

def kid10_part688 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.cycle 14 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 9 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 12 3 true (4),
.cycle 2 14 true (1),
.cycle 14 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 14 3 true (5),
.cycle 13 1 true (5)
])
theorem kid10_part688_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part688) = true := by rfl

def kid10_part689 : Audit := .split 13 (5,false) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 13 2 true (4),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 13 9 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 13 3 true (4),
.cycle 2 14 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part689_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part689) = true := by rfl

def kid10_part665 : Audit := .split 11 (5,true) (byMove [(kid10_part666),(kid10_part667),(kid10_part668),(kid10_part669),(kid10_part670),(kid10_part671),(kid10_part672),(kid10_part673),(kid10_part674),(kid10_part675),(kid10_part676),(kid10_part677),(kid10_part678),(kid10_part679),(kid10_part680),(kid10_part681),(kid10_part682),(kid10_part683),(kid10_part684),(kid10_part685),(kid10_part686),(kid10_part687),(kid10_part688),(kid10_part689)])

theorem kid10_part665_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part665) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part666),(kid10_part667),(kid10_part668),(kid10_part669),(kid10_part670),(kid10_part671),(kid10_part672),(kid10_part673),(kid10_part674),(kid10_part675),(kid10_part676),(kid10_part677),(kid10_part678),(kid10_part679),(kid10_part680),(kid10_part681),(kid10_part682),(kid10_part683),(kid10_part684),(kid10_part685),(kid10_part686),(kid10_part687),(kid10_part688),(kid10_part689)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part666_checked

  · exact kid10_part672_checked

  · exact kid10_part678_checked

  · exact kid10_part684_checked

  · exact kid10_part667_checked

  · exact kid10_part673_checked

  · exact kid10_part679_checked

  · exact kid10_part685_checked

  · exact kid10_part668_checked

  · exact kid10_part674_checked

  · exact kid10_part680_checked

  · exact kid10_part686_checked

  · exact kid10_part669_checked

  · exact kid10_part675_checked

  · exact kid10_part681_checked

  · exact kid10_part687_checked

  · exact kid10_part670_checked

  · exact kid10_part676_checked

  · exact kid10_part682_checked

  · exact kid10_part688_checked

  · exact kid10_part671_checked

  · exact kid10_part677_checked

  · exact kid10_part683_checked

  · exact kid10_part689_checked

def kid10_part569 : Audit := .split 10 (4,true) (byMove [(kid10_part570),(kid10_part571),(kid10_part572),(kid10_part573),(kid10_part574),(kid10_part575),(kid10_part600),(kid10_part601),(kid10_part602),(kid10_part603),(kid10_part604),(kid10_part605),(kid10_part630),(kid10_part631),(kid10_part632),(kid10_part633),(kid10_part634),(kid10_part635),(kid10_part660),(kid10_part661),(kid10_part662),(kid10_part663),(kid10_part664),(kid10_part665)])

theorem kid10_part569_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid10_part569) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part570),(kid10_part571),(kid10_part572),(kid10_part573),(kid10_part574),(kid10_part575),(kid10_part600),(kid10_part601),(kid10_part602),(kid10_part603),(kid10_part604),(kid10_part605),(kid10_part630),(kid10_part631),(kid10_part632),(kid10_part633),(kid10_part634),(kid10_part635),(kid10_part660),(kid10_part661),(kid10_part662),(kid10_part663),(kid10_part664),(kid10_part665)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part570_checked

  · exact kid10_part600_checked

  · exact kid10_part630_checked

  · exact kid10_part660_checked

  · exact kid10_part571_checked

  · exact kid10_part601_checked

  · exact kid10_part631_checked

  · exact kid10_part661_checked

  · exact kid10_part572_checked

  · exact kid10_part602_checked

  · exact kid10_part632_checked

  · exact kid10_part662_checked

  · exact kid10_part573_checked

  · exact kid10_part603_checked

  · exact kid10_part633_checked

  · exact kid10_part663_checked

  · exact kid10_part574_checked

  · exact kid10_part604_checked

  · exact kid10_part634_checked

  · exact kid10_part664_checked

  · exact kid10_part575_checked

  · exact kid10_part605_checked

  · exact kid10_part635_checked

  · exact kid10_part665_checked

def kid10_part691 : Audit := .cycle 0 13 true (0)
theorem kid10_part691_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part691) = true := by rfl

def kid10_part693 : Audit := .cycle 0 15 true (0)
theorem kid10_part693_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part693) = true := by rfl

def kid10_part694 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 0 34 true (0),
.cycle 13 7 true (1),
.cycle 0 24 true (0),
.cycle 1 19 true (1),
.cycle 1 22 true (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (5,true),
.cycle 9 10 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.last 20 (5,true),
.cycle 1 20 true (1)
])
theorem kid10_part694_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part694) = true := by rfl

def kid10_part695 : Audit := .cycle 21 1 false (1)
theorem kid10_part695_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part695) = true := by rfl

def kid10_part696 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (2),
.cycle 33 1 false (3),
.last 22 (5,true),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 0 41 true (0),
.cycle 0 36 true (0),
.cycle 15 7 true (1),
.cycle 0 26 true (0),
.cycle 40 1 false (2),
.cycle 0 24 true (0),
.cycle 21 7 true (2),
.cycle 0 23 true (0),
.cycle 28 1 false (2),
.last 22 (5,true),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 38 1 false (2),
.cycle 0 45 true (0),
.last 22 (5,true),
.cycle 35 1 false (3)
])
theorem kid10_part696_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part696) = true := by rfl

def kid10_part697 : Audit := .split 12 (5,true) (byMove [
.last 19 (4,true),
.last 22 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 21 (4,true),
.last 20 (4,true),
.cycle 0 23 true (-2),
.last 21 (4,true),
.last 20 (4,true),
.last 13 (4,true),
.last 22 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.last 22 (4,true),
.cycle 13 1 false (-1),
.last 37 (4,true),
.last 24 (4,true),
.last 20 (4,true),
.last 14 (4,true),
.last 28 (4,true),
.last 20 (4,true),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part697_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part697) = true := by rfl

def kid10_part698 : Audit := .cycle 11 11 false (1)
theorem kid10_part698_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part698) = true := by rfl

def kid10_part699 : Audit := .cycle 0 13 true (0)
theorem kid10_part699_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part699) = true := by rfl

def kid10_part700 : Audit := .cycle 7 5 true (2)
theorem kid10_part700_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part700) = true := by rfl

def kid10_part701 : Audit := .cycle 0 13 true (0)
theorem kid10_part701_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part701) = true := by rfl

def kid10_part702 : Audit := .split 17 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.cycle 0 23 true (0),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 0 40 true (0),
.cycle 11 9 true (0),
.cycle 0 24 true (0),
.cycle 0 19 true (0),
.cycle 0 24 true (0),
.last 18 (5,true),
.cycle 0 21 true (0),
.cycle 19 11 true (2),
.cycle 0 46 true (0),
.cycle 30 1 false (4),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 2 17 true (0),
.cycle 0 37 true (0),
.cycle 7 11 true (0),
.cycle 0 19 true (0),
.last 20 (5,true),
.last 18 (5,true)
])
theorem kid10_part702_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part702) = true := by rfl

def kid10_part703 : Audit := .cycle 2 15 true (1)
theorem kid10_part703_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part703) = true := by rfl

def kid10_part704 : Audit := .cycle 0 15 true (0)
theorem kid10_part704_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part704) = true := by rfl

def kid10_part705 : Audit := .cycle 17 7 false (2)
theorem kid10_part705_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part705) = true := by rfl

def kid10_part706 : Audit := .split 19 (4,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 1, 64, 64],64⟩,
.cycle 0 31 true (-1),
.cycle 25 5 false (2),
.cycle 0 35 true (-1),
.last 21 (5,true),
.cycle 20 5 false (0),
.cycle 0 64 true (-1),
.cycle 20 36 true (1),
.cycle 0 87 true (-2),
.cycle 0 74 true (-1),
.cycle 0 59 true (-2),
.cycle 65 23 true (4),
.cycle 15 7 false (1),
.cycle 11 9 false (3),
.cycle 0 74 true (-1),
.cycle 23 5 false (2),
.last 21 (5,true),
.cycle 20 5 false (0),
.cycle 2 42 true (-1),
.cycle 1 22 true (-1),
.cycle 59 21 true (4),
.cycle 0 92 true (-1),
.last 21 (5,true),
.cycle 9 11 false (3)
])
theorem kid10_part706_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part706) = true := by rfl

def kid10_part707 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 49 1 false (5),
.cycle 42 1 false (4),
.cycle 0 22 true (0),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 36 true (0),
.cycle 0 60 true (0),
.cycle 0 22 true (0),
.cycle 1 17 true (1),
.cycle 13 4 true (3),
.cycle 7 11 true (1),
.cycle 0 19 true (0),
.cycle 42 1 false (4),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 18 (5,true),
.cycle 0 21 true (0)
])
theorem kid10_part707_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part707) = true := by rfl

def kid10_part708 : Audit := .cycle 18 1 false (0)
theorem kid10_part708_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part708) = true := by rfl

def kid10_part709 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 19 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 44 true (-2),
.last 83 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 0 19 true (0),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 46 true (-2),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 79 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 13 (4,true),
.last 17 (4,true)
])
theorem kid10_part709_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part709) = true := by rfl

def kid10_part710 : Audit := .split 19 (5,true) (byMove [
.last 43 (4,true),
.cycle 0 29 true (-2),
.last 27 (4,true),
.cycle 11 15 false (2),
.cycle 11 10 false (2),
.last 28 (4,true),
.cycle 0 23 true (-2),
.cycle 0 33 true (-2),
.cycle 0 49 true (-2),
.cycle 0 25 true (-2),
.last 20 (4,true),
.cycle 0 25 true (-2),
.last 28 (4,true),
.last 22 (4,true),
.cycle 0 25 true (-2),
.last 25 (4,true),
.cycle 11 10 false (2),
.cycle 0 27 true (-2),
.cycle 0 23 true (-2),
.cycle 18 2 true (1),
.last 32 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 327936, 4097, 32906, 128, 256, 32768, 260, 4096, 130, 2, 4, 8, 65552, 4097, 32768, 262144],[256, 4097, 16, 1, 262144, 512, 256, 4096, 65536, 4096, 262144, 512, 4, 4097, 16, 1, 262144, 8, 262144],287276⟩,
.last 20 (4,true),
.cycle 18 4 true (1)
])
theorem kid10_part710_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part710) = true := by rfl

def kid10_part711 : Audit := .cycle 0 13 true (0)
theorem kid10_part711_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part711) = true := by rfl

def kid10_part712 : Audit := .cycle 7 5 true (2)
theorem kid10_part712_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part712) = true := by rfl

def kid10_part713 : Audit := .cycle 0 13 true (0)
theorem kid10_part713_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part713) = true := by rfl

def kid10_part714 : Audit := .cycle 4 7 true (1)
theorem kid10_part714_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part714) = true := by rfl

def kid10_part715 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 2 15 true (1),
.last 19 (4,true),
.last 36 (4,true),
.last 24 (4,true),
.last 25 (4,true),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 1 15 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.last 22 (4,true),
.last 23 (4,true),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 13 5 true (3)
])
theorem kid10_part715_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part715) = true := by rfl

def kid10_part716 : Audit := .cycle 9 2 true (2)
theorem kid10_part716_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part716) = true := by rfl

def kid10_part692 : Audit := .split 10 (1,true) (byMove [(kid10_part693),(kid10_part694),(kid10_part695),(kid10_part696),(kid10_part697),(kid10_part698),(kid10_part699),(kid10_part700),(kid10_part701),(kid10_part702),(kid10_part703),(kid10_part704),(kid10_part705),(kid10_part706),(kid10_part707),(kid10_part708),(kid10_part709),(kid10_part710),(kid10_part711),(kid10_part712),(kid10_part713),(kid10_part714),(kid10_part715),(kid10_part716)])

theorem kid10_part692_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part692) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part693),(kid10_part694),(kid10_part695),(kid10_part696),(kid10_part697),(kid10_part698),(kid10_part699),(kid10_part700),(kid10_part701),(kid10_part702),(kid10_part703),(kid10_part704),(kid10_part705),(kid10_part706),(kid10_part707),(kid10_part708),(kid10_part709),(kid10_part710),(kid10_part711),(kid10_part712),(kid10_part713),(kid10_part714),(kid10_part715),(kid10_part716)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part693_checked

  · exact kid10_part699_checked

  · exact kid10_part705_checked

  · exact kid10_part711_checked

  · exact kid10_part694_checked

  · exact kid10_part700_checked

  · exact kid10_part706_checked

  · exact kid10_part712_checked

  · exact kid10_part695_checked

  · exact kid10_part701_checked

  · exact kid10_part707_checked

  · exact kid10_part713_checked

  · exact kid10_part696_checked

  · exact kid10_part702_checked

  · exact kid10_part708_checked

  · exact kid10_part714_checked

  · exact kid10_part697_checked

  · exact kid10_part703_checked

  · exact kid10_part709_checked

  · exact kid10_part715_checked

  · exact kid10_part698_checked

  · exact kid10_part704_checked

  · exact kid10_part710_checked

  · exact kid10_part716_checked

def kid10_part718 : Audit := .cycle 35 1 false (1)
theorem kid10_part718_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part718) = true := by rfl

def kid10_part719 : Audit := .cycle 0 23 true (0)
theorem kid10_part719_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part719) = true := by rfl

def kid10_part720 : Audit := .cycle 39 1 false (3)
theorem kid10_part720_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part720) = true := by rfl

def kid10_part721 : Audit := .cycle 0 25 true (0)
theorem kid10_part721_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part721) = true := by rfl

def kid10_part722 : Audit := .split 21 (5,true) (byMove [
.cycle 34 1 false (0),
.last 26 (1,true),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 25 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 26 1 false (2),
.last 24 (1,true),
.cycle 26 1 false (0),
.cycle 25 1 false (3),
.last 23 (1,true),
.cycle 18 5 false (3),
.cycle 0 27 true (0),
.cycle 22 1 false (0),
.cycle 25 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 25 true (0),
.last 22 (1,true),
.cycle 29 1 false (1),
.last 24 (1,true),
.cycle 27 1 false (-1),
.cycle 31 1 false (1)
])
theorem kid10_part722_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part722) = true := by rfl

def kid10_part723 : Audit := .cycle 25 1 false (1)
theorem kid10_part723_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part723) = true := by rfl

def kid10_part724 : Audit := .cycle 0 44 true (0)
theorem kid10_part724_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part724) = true := by rfl

def kid10_part725 : Audit := .split 20 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 14 48 true (0),
.cycle 32 1 false (2),
.cycle 27 1 false (1),
.cycle 34 1 false (2),
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 32, 4, 64],[12, 8, 12, 8, 8, 64, 64],64⟩,
.cycle 23 13 true (1),
.cycle 14 9 true (0),
.cycle 14 11 true (0),
.cycle 14 11 true (0),
.cycle 6 17 true (0),
.cycle 7 15 true (0),
.cycle 0 23 true (0),
.cycle 14 42 true (0),
.cycle 27 1 false (1),
.cycle 12 48 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 21 24 true (1),
.cycle 5 41 true (0),
.last 22 (5,true),
.cycle 14 13 true (0)
])
theorem kid10_part725_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part725) = true := by rfl

def kid10_part726 : Audit := .cycle 14 11 true (0)
theorem kid10_part726_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part726) = true := by rfl

def kid10_part727 : Audit := .cycle 0 21 true (0)
theorem kid10_part727_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part727) = true := by rfl

def kid10_part728 : Audit := .cycle 14 11 true (0)
theorem kid10_part728_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part728) = true := by rfl

def kid10_part729 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 21 9 true (1),
.cycle 32 1 false (2),
.cycle 27 1 false (1),
.cycle 34 1 false (2),
.cycle 0 21 true (0),
.last 44 (1,true),
.cycle 23 13 true (1),
.cycle 14 9 true (0),
.cycle 14 11 true (0),
.cycle 14 11 true (0),
.last 22 (1,true),
.cycle 7 15 true (0),
.cycle 0 23 true (0),
.cycle 21 9 true (1),
.cycle 27 1 false (1),
.cycle 23 9 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 42 9 true (5),
.cycle 5 41 true (0),
.cycle 22 49 true (1),
.cycle 14 13 true (0)
])
theorem kid10_part729_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part729) = true := by rfl

def kid10_part730 : Audit := .split 21 (1,true) (byMove [
.cycle 0 25 true (0),
.cycle 37 1 false (1),
.cycle 29 1 false (1),
.cycle 0 26 true (0),
.cycle 31 1 false (1),
.last 22 (5,true),
.cycle 6 38 true (0),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 32, 4, 64],[12, 8, 12, 8, 1, 64, 64],64⟩,
.cycle 26 10 true (2),
.cycle 0 23 true (0),
.cycle 37 1 false (1),
.last 22 (5,true),
.cycle 41 1 false (1),
.cycle 18 7 false (3),
.cycle 18 4 true (2),
.cycle 5 17 true (0),
.cycle 17 6 true (1),
.last 22 (5,true),
.cycle 2 21 true (0),
.cycle 1 22 true (0),
.cycle 35 1 false (1),
.cycle 0 23 true (0),
.cycle 37 1 false (1),
.last 22 (5,true)
])
theorem kid10_part730_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part730) = true := by rfl

def kid10_part731 : Audit := .cycle 37 1 false (1)
theorem kid10_part731_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part731) = true := by rfl

def kid10_part732 : Audit := .cycle 0 50 true (0)
theorem kid10_part732_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part732) = true := by rfl

def kid10_part733 : Audit := .cycle 35 1 false (3)
theorem kid10_part733_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part733) = true := by rfl

def kid10_part734 : Audit := .split 21 (5,true) (byMove [
.cycle 16 86 true (0),
.cycle 16 62 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 25 1 false (-1),
.cycle 24 1 false (0),
.cycle 35 1 false (3),
.last 22 (1,true),
.cycle 27 1 false (1),
.cycle 31 1 false (3),
.cycle 26 1 false (0),
.cycle 27 1 false (5),
.last 23 (1,true),
.cycle 18 5 false (3),
.cycle 39 1 false (3),
.cycle 22 1 false (0),
.cycle 25 1 false (-1),
.cycle 24 1 false (0),
.cycle 41 1 false (1),
.last 22 (1,true),
.cycle 18 4 true (1),
.cycle 5 17 true (0),
.cycle 27 1 false (-1),
.cycle 39 1 false (1)
])
theorem kid10_part734_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part734) = true := by rfl

def kid10_part735 : Audit := .cycle 25 1 false (1)
theorem kid10_part735_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part735) = true := by rfl

def kid10_part736 : Audit := .cycle 2 19 true (0)
theorem kid10_part736_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part736) = true := by rfl

def kid10_part737 : Audit := .split 20 (1,true) (byMove [
.cycle 0 45 true (0),
.cycle 1 21 true (0),
.cycle 1 30 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 21 (5,true),
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 32, 4, 64],[12, 8, 12, 8, 12, 64, 64],64⟩,
.cycle 1 28 true (0),
.cycle 0 41 true (0),
.cycle 8 13 true (0),
.last 42 (5,true),
.cycle 6 15 true (0),
.cycle 1 24 true (0),
.cycle 1 22 true (0),
.cycle 1 47 true (0),
.cycle 19 2 true (3),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 0 45 true (0),
.last 22 (5,true),
.cycle 7 15 true (0)
])
theorem kid10_part737_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part737) = true := by rfl

def kid10_part738 : Audit := .cycle 7 13 true (0)
theorem kid10_part738_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part738) = true := by rfl

def kid10_part739 : Audit := .cycle 0 21 true (0)
theorem kid10_part739_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part739) = true := by rfl

def kid10_part740 : Audit := .split 22 (5,true) (byMove [
.cycle 0 26 true (0),
.last 23 (1,true),
.cycle 10 13 true (0),
.last 25 (1,true),
.cycle 31 1 false (-1),
.cycle 29 1 false (1),
.cycle 19 24 true (3),
.last 23 (1,true),
.cycle 14 26 true (0),
.cycle 0 24 true (0),
.cycle 20 3 true (4),
.cycle 14 26 true (0),
.last 29 (1,true),
.last 23 (1,true),
.cycle 18 5 true (2),
.cycle 5 38 true (0),
.cycle 19 5 true (3),
.cycle 29 1 false (1),
.cycle 2 22 true (0),
.last 23 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 20, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 0 24 true (0),
.cycle 20 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 48, 52, 64],[4, 64, 16, 1, 16, 32, 64],64⟩
])
theorem kid10_part740_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part740) = true := by rfl

def kid10_part741 : Audit := .split 20 (5,true) (byMove [
.cycle 0 45 true (0),
.last 21 (1,true),
.cycle 21 11 true (1),
.cycle 0 22 true (0),
.cycle 21 11 true (1),
.cycle 27 1 false (1),
.cycle 0 21 true (0),
.last 42 (1,true),
.cycle 23 11 true (3),
.cycle 0 41 true (0),
.cycle 8 13 true (0),
.cycle 46 11 true (4),
.cycle 6 15 true (0),
.last 21 (1,true),
.cycle 14 15 true (0),
.cycle 44 11 true (4),
.cycle 19 2 true (3),
.cycle 27 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 0 45 true (0),
.cycle 22 19 true (1),
.cycle 7 15 true (0)
])
theorem kid10_part741_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part741) = true := by rfl

def kid10_part717 : Audit := .split 19 (4,true) (byMove [(kid10_part718),(kid10_part719),(kid10_part720),(kid10_part721),(kid10_part722),(kid10_part723),(kid10_part724),(kid10_part725),(kid10_part726),(kid10_part727),(kid10_part728),(kid10_part729),(kid10_part730),(kid10_part731),(kid10_part732),(kid10_part733),(kid10_part734),(kid10_part735),(kid10_part736),(kid10_part737),(kid10_part738),(kid10_part739),(kid10_part740),(kid10_part741)])

theorem kid10_part717_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part717) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (4,true) (some mv)) (byMove [(kid10_part718),(kid10_part719),(kid10_part720),(kid10_part721),(kid10_part722),(kid10_part723),(kid10_part724),(kid10_part725),(kid10_part726),(kid10_part727),(kid10_part728),(kid10_part729),(kid10_part730),(kid10_part731),(kid10_part732),(kid10_part733),(kid10_part734),(kid10_part735),(kid10_part736),(kid10_part737),(kid10_part738),(kid10_part739),(kid10_part740),(kid10_part741)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part718_checked

  · exact kid10_part724_checked

  · exact kid10_part730_checked

  · exact kid10_part736_checked

  · exact kid10_part719_checked

  · exact kid10_part725_checked

  · exact kid10_part731_checked

  · exact kid10_part737_checked

  · exact kid10_part720_checked

  · exact kid10_part726_checked

  · exact kid10_part732_checked

  · exact kid10_part738_checked

  · exact kid10_part721_checked

  · exact kid10_part727_checked

  · exact kid10_part733_checked

  · exact kid10_part739_checked

  · exact kid10_part722_checked

  · exact kid10_part728_checked

  · exact kid10_part734_checked

  · exact kid10_part740_checked

  · exact kid10_part723_checked

  · exact kid10_part729_checked

  · exact kid10_part735_checked

  · exact kid10_part741_checked

def kid10_part743 : Audit := .cycle 2 12 true (1)
theorem kid10_part743_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part743) = true := by rfl

def kid10_part744 : Audit := .cycle 1 13 true (1)
theorem kid10_part744_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part744) = true := by rfl

def kid10_part745 : Audit := .cycle 29 1 false (1)
theorem kid10_part745_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part745) = true := by rfl

def kid10_part746 : Audit := .cycle 0 14 true (0)
theorem kid10_part746_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part746) = true := by rfl

def kid10_part747 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.cycle 22 1 false (-2),
.cycle 31 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 80 1 false (12),
.cycle 0 23 true (0),
.cycle 29 1 false (1),
.cycle 35 1 false (3),
.cycle 25 3 false (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.cycle 22 1 false (-2),
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 15 (5,true),
.cycle 0 16 true (0)
])
theorem kid10_part747_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part747) = true := by rfl

def kid10_part748 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 22 1 false (-2),
.cycle 31 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (4,true),
.last 21 (4,true),
.cycle 29 1 false (1),
.last 21 (4,true),
.cycle 25 3 false (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 22 1 false (-2),
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 16 (4,true),
.cycle 0 16 true (0)
])
theorem kid10_part748_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part748) = true := by rfl

def kid10_part749 : Audit := .cycle 0 13 true (0)
theorem kid10_part749_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part749) = true := by rfl

def kid10_part750 : Audit := .cycle 1 12 true (1)
theorem kid10_part750_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part750) = true := by rfl

def kid10_part751 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 22 (5,true),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 51 true (0),
.cycle 14 7 true (3),
.cycle 0 28 true (0),
.cycle 3 19 true (1),
.cycle 11 10 true (3),
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 22 (5,true),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 2 22 true (1),
.last 22 (5,true),
.cycle 0 23 true (0)
])
theorem kid10_part751_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part751) = true := by rfl

def kid10_part752 : Audit := .cycle 3 10 true (1)
theorem kid10_part752_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part752) = true := by rfl

def kid10_part753 : Audit := .cycle 8 5 true (2)
theorem kid10_part753_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part753) = true := by rfl

def kid10_part754 : Audit := .cycle 2 15 true (1)
theorem kid10_part754_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part754) = true := by rfl

def kid10_part755 : Audit := .cycle 6 7 true (2)
theorem kid10_part755_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part755) = true := by rfl

def kid10_part756 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 18 (5,true),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 24 17 true (3),
.cycle 15 7 true (2),
.cycle 0 24 true (0),
.cycle 3 15 true (1),
.cycle 26 7 false (2),
.cycle 7 11 true (2),
.cycle 0 19 true (0),
.cycle 4 13 true (1),
.last 18 (5,true),
.cycle 9 8 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 18 (5,true),
.cycle 0 19 true (0)
])
theorem kid10_part756_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part756) = true := by rfl

def kid10_part757 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 45 1 false (5),
.cycle 38 1 false (4),
.cycle 0 22 true (0),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 57 1 false (9),
.cycle 0 56 true (0),
.cycle 112 1 false (10),
.last 24 (5,true),
.cycle 11 4 true (3),
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.last 46 (5,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 16 (5,true),
.cycle 0 17 true (0)
])
theorem kid10_part757_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part757) = true := by rfl

def kid10_part758 : Audit := .cycle 2 13 true (1)
theorem kid10_part758_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part758) = true := by rfl

def kid10_part759 : Audit := .split 13 (4,true) (byMove [
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.cycle 42 1 false (4),
.cycle 25 1 false (1),
.cycle 22 1 false (-2),
.cycle 0 27 true (0),
.cycle 2 13 true (1),
.cycle 23 26 true (1),
.cycle 0 26 true (0),
.cycle 0 15 true (0),
.cycle 112 1 false (10),
.last 14 (5,true),
.cycle 16 6 true (0),
.cycle 7 11 true (2),
.cycle 2 15 true (1),
.cycle 35 1 false (3),
.cycle 22 1 false (-2),
.cycle 47 1 false (1),
.cycle 2 13 true (1),
.cycle 12 2 true (3),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid10_part759_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part759) = true := by rfl

def kid10_part760 : Audit := .split 13 (5,true) (byMove [
.cycle 7 9 true (2),
.cycle 0 17 true (0),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 22 1 false (-2),
.last 24 (4,true),
.cycle 2 13 true (1),
.cycle 29 1 false (1),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 23 (4,true),
.last 22 (4,true),
.last 16 (4,true),
.cycle 2 15 true (1),
.last 19 (4,true),
.cycle 22 1 false (-2),
.last 40 (4,true),
.cycle 2 13 true (1),
.cycle 12 2 true (3),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 17 true (0)
])
theorem kid10_part760_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part760) = true := by rfl

def kid10_part761 : Audit := .cycle 0 13 true (0)
theorem kid10_part761_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part761) = true := by rfl

def kid10_part762 : Audit := .cycle 1 12 true (1)
theorem kid10_part762_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part762) = true := by rfl

def kid10_part763 : Audit := .cycle 2 11 true (1)
theorem kid10_part763_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part763) = true := by rfl

def kid10_part764 : Audit := .cycle 2 14 true (1)
theorem kid10_part764_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part764) = true := by rfl

def kid10_part765 : Audit := .split 14 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.last 28 (4,true),
.cycle 10 5 true (2),
.last 15 (4,true),
.last 31 (4,true),
.cycle 2 14 true (1),
.cycle 12 3 true (4),
.cycle 0 23 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 3 14 true (1),
.last 17 (4,true),
.last 16 (4,true),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 43 (4,true),
.cycle 2 14 true (1),
.cycle 12 3 true (4),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0)
])
theorem kid10_part765_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part765) = true := by rfl

def kid10_part766 : Audit := .cycle 0 15 true (0)
theorem kid10_part766_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part766) = true := by rfl

def kid10_part742 : Audit := .split 12 (1,true) (byMove [(kid10_part743),(kid10_part744),(kid10_part745),(kid10_part746),(kid10_part747),(kid10_part748),(kid10_part749),(kid10_part750),(kid10_part751),(kid10_part752),(kid10_part753),(kid10_part754),(kid10_part755),(kid10_part756),(kid10_part757),(kid10_part758),(kid10_part759),(kid10_part760),(kid10_part761),(kid10_part762),(kid10_part763),(kid10_part764),(kid10_part765),(kid10_part766)])

theorem kid10_part742_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part742) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (1,true) (some mv)) (byMove [(kid10_part743),(kid10_part744),(kid10_part745),(kid10_part746),(kid10_part747),(kid10_part748),(kid10_part749),(kid10_part750),(kid10_part751),(kid10_part752),(kid10_part753),(kid10_part754),(kid10_part755),(kid10_part756),(kid10_part757),(kid10_part758),(kid10_part759),(kid10_part760),(kid10_part761),(kid10_part762),(kid10_part763),(kid10_part764),(kid10_part765),(kid10_part766)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part743_checked

  · exact kid10_part749_checked

  · exact kid10_part755_checked

  · exact kid10_part761_checked

  · exact kid10_part744_checked

  · exact kid10_part750_checked

  · exact kid10_part756_checked

  · exact kid10_part762_checked

  · exact kid10_part745_checked

  · exact kid10_part751_checked

  · exact kid10_part757_checked

  · exact kid10_part763_checked

  · exact kid10_part746_checked

  · exact kid10_part752_checked

  · exact kid10_part758_checked

  · exact kid10_part764_checked

  · exact kid10_part747_checked

  · exact kid10_part753_checked

  · exact kid10_part759_checked

  · exact kid10_part765_checked

  · exact kid10_part748_checked

  · exact kid10_part754_checked

  · exact kid10_part760_checked

  · exact kid10_part766_checked

def kid10_part768 : Audit := .cycle 0 15 true (0)
theorem kid10_part768_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part768) = true := by rfl

def kid10_part769 : Audit := .cycle 1 18 true (1)
theorem kid10_part769_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part769) = true := by rfl

def kid10_part770 : Audit := .cycle 21 1 false (1)
theorem kid10_part770_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part770) = true := by rfl

def kid10_part771 : Audit := .cycle 33 1 false (3)
theorem kid10_part771_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part771) = true := by rfl

def kid10_part772 : Audit := .split 12 (5,true) (byMove [
.cycle 20 2 false (-2),
.cycle 26 2 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 33 2 false (3),
.last 13 (1,true),
.cycle 14 2 false (2),
.cycle 21 2 false (1),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 37 2 false (3),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 2 22 true (0),
.last 13 (1,true),
.cycle 17 2 false (-1),
.cycle 0 28 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
])
theorem kid10_part772_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part772) = true := by rfl

def kid10_part773 : Audit := .cycle 13 2 false (-1)
theorem kid10_part773_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part773) = true := by rfl

def kid10_part774 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 22 2 false (2),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 21 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 2 13 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 0 15 true (0)
])
theorem kid10_part774_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part774) = true := by rfl

def kid10_part775 : Audit := .cycle 7 5 true (2)
theorem kid10_part775_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part775) = true := by rfl

def kid10_part776 : Audit := .cycle 0 13 true (0)
theorem kid10_part776_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part776) = true := by rfl

def kid10_part777 : Audit := .cycle 0 19 true (0)
theorem kid10_part777_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part777) = true := by rfl

def kid10_part778 : Audit := .split 14 (5,true) (byMove [
.cycle 24 2 false (0),
.last 19 (1,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 38 (1,true),
.last 15 (1,true),
.cycle 16 2 false (2),
.last 17 (1,true),
.cycle 16 2 false (2),
.cycle 16 2 false (2),
.last 16 (1,true),
.cycle 10 7 false (3),
.last 42 (1,true),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 38 (1,true),
.last 15 (1,true),
.cycle 19 2 false (1),
.last 17 (1,true),
.cycle 19 2 false (1),
.cycle 21 2 false (1)
])
theorem kid10_part778_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part778) = true := by rfl

def kid10_part779 : Audit := .cycle 15 2 false (1)
theorem kid10_part779_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part779) = true := by rfl

def kid10_part780 : Audit := .split 12 (1,true) (byMove [
.cycle 2 22 true (1),
.cycle 13 13 false (2),
.cycle 20 2 false (0),
.cycle 0 35 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 0 15 true (0),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.cycle 3 18 true (1),
.cycle 18 5 false (2),
.last 15 (5,true),
.cycle 18 7 false (2),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 0 17 true (0),
.cycle 10 6 true (0),
.last 13 (5,true),
.cycle 0 15 true (0),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 16, 64],[1, 1, 17, 1, 1, 64, 64],64⟩,
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 18 9 false (2)
])
theorem kid10_part780_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part780) = true := by rfl

def kid10_part781 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (3),
.cycle 10 85 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 61 true (0),
.cycle 28 5 false (6),
.cycle 18 2 false (2),
.cycle 0 21 true (0),
.cycle 17 5 false (2),
.last 17 (5,true),
.cycle 10 11 false (3),
.cycle 10 9 false (3),
.cycle 0 67 true (-1),
.cycle 17 1 false (-1),
.cycle 17 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 61 true (0),
.cycle 21 7 true (2),
.cycle 17 5 false (2),
.cycle 0 21 true (0),
.cycle 15 2 true (0),
.last 17 (5,true)
])
theorem kid10_part781_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part781) = true := by rfl

def kid10_part782 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 26 2 false (2),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 25 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.last 17 (5,true),
.cycle 6 9 true (1),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 2 15 true (1),
.cycle 2 17 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 16 (5,true),
.cycle 0 21 true (0)
])
theorem kid10_part782_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part782) = true := by rfl

def kid10_part783 : Audit := .cycle 18 1 false (0)
theorem kid10_part783_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part783) = true := by rfl

def kid10_part784 : Audit := .split 12 (5,true) (byMove [
.cycle 0 25 true (-1),
.cycle 0 19 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 18 2 false (0),
.last 13 (1,true),
.cycle 15 2 false (1),
.cycle 0 17 true (0),
.cycle 14 2 false (0),
.cycle 15 2 false (3),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 20 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 0 17 true (0),
.cycle 15 2 false (-1),
.cycle 19 2 false (-1)
])
theorem kid10_part784_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part784) = true := by rfl

def kid10_part785 : Audit := .cycle 13 2 false (-1)
theorem kid10_part785_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part785) = true := by rfl

def kid10_part786 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 21 true (0),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 2 17 true (1),
.cycle 0 15 true (0),
.cycle 2 13 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 0 15 true (0)
])
theorem kid10_part786_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part786) = true := by rfl

def kid10_part787 : Audit := .cycle 7 5 true (2)
theorem kid10_part787_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part787) = true := by rfl

def kid10_part788 : Audit := .cycle 0 13 true (0)
theorem kid10_part788_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part788) = true := by rfl

def kid10_part789 : Audit := .cycle 4 7 true (1)
theorem kid10_part789_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part789) = true := by rfl

def kid10_part790 : Audit := .split 12 (5,true) (byMove [
.cycle 2 29 true (1),
.cycle 2 15 true (1),
.cycle 29 1 false (1),
.cycle 61 1 false (3),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 40 2 false (8),
.cycle 2 13 true (1),
.cycle 14 3 true (4),
.cycle 25 2 false (3),
.last 14 (1,true),
.last 19 (1,true),
.cycle 5 9 true (1),
.cycle 5 34 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 7 10 true (2),
.cycle 2 13 true (1),
.cycle 14 3 true (4),
.cycle 13 5 true (3)
])
theorem kid10_part790_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part790) = true := by rfl

def kid10_part791 : Audit := .cycle 9 2 true (2)
theorem kid10_part791_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part791) = true := by rfl

def kid10_part767 : Audit := .split 10 (4,true) (byMove [(kid10_part768),(kid10_part769),(kid10_part770),(kid10_part771),(kid10_part772),(kid10_part773),(kid10_part774),(kid10_part775),(kid10_part776),(kid10_part777),(kid10_part778),(kid10_part779),(kid10_part780),(kid10_part781),(kid10_part782),(kid10_part783),(kid10_part784),(kid10_part785),(kid10_part786),(kid10_part787),(kid10_part788),(kid10_part789),(kid10_part790),(kid10_part791)])

theorem kid10_part767_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part767) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part768),(kid10_part769),(kid10_part770),(kid10_part771),(kid10_part772),(kid10_part773),(kid10_part774),(kid10_part775),(kid10_part776),(kid10_part777),(kid10_part778),(kid10_part779),(kid10_part780),(kid10_part781),(kid10_part782),(kid10_part783),(kid10_part784),(kid10_part785),(kid10_part786),(kid10_part787),(kid10_part788),(kid10_part789),(kid10_part790),(kid10_part791)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part768_checked

  · exact kid10_part774_checked

  · exact kid10_part780_checked

  · exact kid10_part786_checked

  · exact kid10_part769_checked

  · exact kid10_part775_checked

  · exact kid10_part781_checked

  · exact kid10_part787_checked

  · exact kid10_part770_checked

  · exact kid10_part776_checked

  · exact kid10_part782_checked

  · exact kid10_part788_checked

  · exact kid10_part771_checked

  · exact kid10_part777_checked

  · exact kid10_part783_checked

  · exact kid10_part789_checked

  · exact kid10_part772_checked

  · exact kid10_part778_checked

  · exact kid10_part784_checked

  · exact kid10_part790_checked

  · exact kid10_part773_checked

  · exact kid10_part779_checked

  · exact kid10_part785_checked

  · exact kid10_part791_checked

def kid10_part793 : Audit := .cycle 0 15 true (0)
theorem kid10_part793_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part793) = true := by rfl

def kid10_part794 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 0 24 true (0),
.cycle 1 20 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 0 54 true (0),
.cycle 13 7 true (1),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 3, 1],[128, 256, 8, 16, 16, 16, 8192, 16384, 8, 256, 262145, 16, 8192, 16384, 2097152, 256, 16777216, 16777216, 128, 256, 2097152, 16, 16777216, 16777216, 16777216],[256, 16777216, 16, 1, 16, 2097160, 16384, 16777216, 16, 1, 16, 16777216, 16384, 16777216, 4194304, 262144, 4194304, 16777216, 256, 16777216, 4194304, 262144, 4194304, 2097160, 16777216],29556736⟩,
.cycle 1 22 true (1),
.last 20 (1,true),
.last 24 (1,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 2 23 true (1),
.cycle 9 10 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 0 24 true (0),
.cycle 1 20 true (1)
])
theorem kid10_part794_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part794) = true := by rfl

def kid10_part795 : Audit := .cycle 21 1 false (1)
theorem kid10_part795_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part795) = true := by rfl

def kid10_part796 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (2),
.cycle 33 1 false (3),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 0 41 true (0),
.cycle 36 1 false (2),
.cycle 15 7 true (1),
.cycle 25 1 false (1),
.cycle 25 1 false (1),
.last 22 (1,true),
.cycle 21 7 true (2),
.cycle 0 23 true (0),
.cycle 28 1 false (2),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 38 1 false (2),
.cycle 0 45 true (0),
.cycle 0 28 true (0),
.cycle 35 1 false (3)
])
theorem kid10_part796_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part796) = true := by rfl

def kid10_part797 : Audit := .cycle 14 1 false (-2)
theorem kid10_part797_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part797) = true := by rfl

def kid10_part798 : Audit := .cycle 13 1 false (-1)
theorem kid10_part798_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part798) = true := by rfl

def kid10_part799 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 0 23 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 16 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 0 15 true (0)
])
theorem kid10_part799_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part799) = true := by rfl

def kid10_part800 : Audit := .cycle 7 5 true (2)
theorem kid10_part800_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part800) = true := by rfl

def kid10_part801 : Audit := .cycle 0 13 true (0)
theorem kid10_part801_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part801) = true := by rfl

def kid10_part802 : Audit := .split 17 (4,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.cycle 0 23 true (0),
.last 22 (1,true),
.cycle 20 1 false (2),
.cycle 0 40 true (0),
.last 18 (1,true),
.cycle 24 1 false (2),
.cycle 0 19 true (0),
.cycle 24 1 false (2),
.cycle 11 9 true (0),
.last 19 (1,true),
.cycle 19 11 true (2),
.cycle 0 46 true (0),
.cycle 30 1 false (4),
.cycle 26 1 false (4),
.cycle 20 1 false (2),
.cycle 2 17 true (0),
.last 18 (1,true),
.cycle 7 11 true (0),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.cycle 0 37 true (0)
])
theorem kid10_part802_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part802) = true := by rfl

def kid10_part803 : Audit := .cycle 16 1 false (0)
theorem kid10_part803_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part803) = true := by rfl

def kid10_part804 : Audit := .cycle 15 1 false (1)
theorem kid10_part804_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part804) = true := by rfl

def kid10_part805 : Audit := .split 12 (1,true) (byMove [
.last 20 (4,true),
.cycle 13 13 false (2),
.cycle 21 1 false (-1),
.last 31 (4,true),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 0 15 true (0),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 18 (4,true),
.cycle 18 5 false (2),
.cycle 19 5 false (1),
.cycle 18 7 false (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 17 true (0),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 37 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 17 (4,true),
.cycle 18 9 false (2)
])
theorem kid10_part805_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part805) = true := by rfl

def kid10_part806 : Audit := .split 16 (1,true) (byMove [
.cycle 11 7 false (3),
.last 30 (4,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 51 (4,true),
.last 20 (4,true),
.cycle 19 1 false (1),
.cycle 0 21 true (0),
.last 17 (4,true),
.cycle 17 5 false (2),
.last 21 (4,true),
.last 19 (4,true),
.last 55 (4,true),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 51 (4,true),
.last 20 (4,true),
.cycle 17 5 false (2),
.cycle 0 21 true (0),
.last 17 (4,true),
.cycle 15 2 true (0)
])
theorem kid10_part806_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part806) = true := by rfl

def kid10_part807 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 0 27 true (-1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 3 12 true (1),
.cycle 8 7 true (1),
.cycle 0 20 true (0),
.cycle 6 9 true (1),
.last 18 (4,true),
.last 16 (4,true),
.cycle 2 15 true (1),
.last 15 (4,true),
.cycle 2 17 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 18 (4,true),
.last 18 (4,true)
])
theorem kid10_part807_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part807) = true := by rfl

def kid10_part808 : Audit := .cycle 18 1 false (0)
theorem kid10_part808_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part808) = true := by rfl

def kid10_part809 : Audit := .cycle 14 1 false (-2)
theorem kid10_part809_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part809) = true := by rfl

def kid10_part810 : Audit := .cycle 13 1 false (-1)
theorem kid10_part810_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part810) = true := by rfl

def kid10_part811 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 0 15 true (0)
])
theorem kid10_part811_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part811) = true := by rfl

def kid10_part812 : Audit := .cycle 7 5 true (2)
theorem kid10_part812_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part812) = true := by rfl

def kid10_part813 : Audit := .cycle 0 13 true (0)
theorem kid10_part813_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part813) = true := by rfl

def kid10_part814 : Audit := .cycle 4 7 true (1)
theorem kid10_part814_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part814) = true := by rfl

def kid10_part815 : Audit := .split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 24 1 false (0),
.last 16 (1,true),
.cycle 20 1 false (-2),
.cycle 10 4 true (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 0 24 true (0),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 14 6 true (4),
.last 18 (1,true),
.last 14 (1,true),
.cycle 2 17 true (1),
.cycle 5 9 true (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 14 3 true (4),
.cycle 14 5 true (4)
])
theorem kid10_part815_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part815) = true := by rfl

def kid10_part816 : Audit := .cycle 9 2 true (2)
theorem kid10_part816_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part816) = true := by rfl

def kid10_part792 : Audit := .split 10 (5,true) (byMove [(kid10_part793),(kid10_part794),(kid10_part795),(kid10_part796),(kid10_part797),(kid10_part798),(kid10_part799),(kid10_part800),(kid10_part801),(kid10_part802),(kid10_part803),(kid10_part804),(kid10_part805),(kid10_part806),(kid10_part807),(kid10_part808),(kid10_part809),(kid10_part810),(kid10_part811),(kid10_part812),(kid10_part813),(kid10_part814),(kid10_part815),(kid10_part816)])

theorem kid10_part792_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part792) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part793),(kid10_part794),(kid10_part795),(kid10_part796),(kid10_part797),(kid10_part798),(kid10_part799),(kid10_part800),(kid10_part801),(kid10_part802),(kid10_part803),(kid10_part804),(kid10_part805),(kid10_part806),(kid10_part807),(kid10_part808),(kid10_part809),(kid10_part810),(kid10_part811),(kid10_part812),(kid10_part813),(kid10_part814),(kid10_part815),(kid10_part816)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part793_checked

  · exact kid10_part799_checked

  · exact kid10_part805_checked

  · exact kid10_part811_checked

  · exact kid10_part794_checked

  · exact kid10_part800_checked

  · exact kid10_part806_checked

  · exact kid10_part812_checked

  · exact kid10_part795_checked

  · exact kid10_part801_checked

  · exact kid10_part807_checked

  · exact kid10_part813_checked

  · exact kid10_part796_checked

  · exact kid10_part802_checked

  · exact kid10_part808_checked

  · exact kid10_part814_checked

  · exact kid10_part797_checked

  · exact kid10_part803_checked

  · exact kid10_part809_checked

  · exact kid10_part815_checked

  · exact kid10_part798_checked

  · exact kid10_part804_checked

  · exact kid10_part810_checked

  · exact kid10_part816_checked

def kid10_part817 : Audit := .cycle 2 9 true (1)
theorem kid10_part817_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part817) = true := by rfl

def kid10_part818 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 15 3 false (-1),
.cycle 7 8 true (1),
.cycle 2 12 true (1),
.cycle 19 3 false (1),
.cycle 26 3 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 17 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 2 12 true (1),
.last 14 (4,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1)
]),
.cycle 1 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.last 21 (5,true),
.cycle 7 15 true (2),
.cycle 2 19 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 8, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 8, 64, 64],64⟩,
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 8, 64, 64],64⟩,
.last 20 (5,true),
.cycle 38 10 true (8),
.cycle 7 17 true (2),
.cycle 2 21 true (1),
.cycle 4 21 true (1),
.last 21 (5,true),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 2 19 true (1),
.cycle 1 28 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.last 19 (5,true),
.cycle 1 18 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 8, 64, 64],64⟩,
.cycle 11 7 true (2),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 32, 8, 64],[0, 8, 8, 0, 8, 64, 64],64⟩,
.cycle 1 18 true (1),
.cycle 3 17 true (1),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 9 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.last 19 (5,true),
.cycle 1 18 true (1)
]),
.cycle 8 3 true (3),
.cycle 1 11 true (1),
.cycle 6 7 true (2),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 2 15 true (1),
.last 19 (4,true),
.last 36 (4,true),
.cycle 15 3 false (-1),
.last 16 (4,true),
.cycle 6 7 true (2),
.cycle 19 3 false (1),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 1 15 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 1 15 true (1)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 15 5 false (1),
.cycle 7 8 true (3),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 2 14 true (1),
.last 17 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid10_part818_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part818) = true := by rfl

def kid10_part819 : Audit := .cycle 7 3 true (3)
theorem kid10_part819_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part819) = true := by rfl

def kid10_part820 : Audit := .cycle 0 11 true (0)
theorem kid10_part820_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part820) = true := by rfl

def kid10_part821 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.cycle 0 18 true (0),
.cycle 15 3 false (-1),
.cycle 20 3 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 26 3 false (2),
.cycle 0 14 true (0),
.cycle 19 3 false (1),
.cycle 31 3 false (3),
.last 14 (1,true),
.last 18 (1,true),
.cycle 2 14 true (1),
.cycle 20 1 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 8 7 true (2)
]),
.cycle 8 4 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 256, 4096, 16, 4096],[256, 4096, 16, 1, 4, 4096, 256, 4096, 16, 1, 4, 4096, 4096],5120⟩,
.cycle 10 7 true (2),
.cycle 8 3 true (3),
.cycle 8 4 true (3),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 6 8 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 8 6 true (3),
.cycle 6 7 true (2),
.cycle 20 7 false (2),
.cycle 10 4 true (3),
.cycle 2 13 true (1),
.cycle 10 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 8 6 true (3)
]),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 2 21 true (1),
.cycle 2 15 true (1),
.cycle 23 1 false (1),
.cycle 39 1 false (1),
.cycle 15 3 false (-1),
.cycle 20 3 false (0),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 24 3 false (2),
.cycle 2 13 true (1),
.cycle 19 3 false (1),
.cycle 40 3 false (8),
.last 14 (1,true),
.last 18 (1,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 10 4 true (2),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 8 8 true (2)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 12 (5,true) (byMove [
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 10 9 true (2),
.cycle 0 18 true (0),
.cycle 15 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 10 5 true (3),
.cycle 2 14 true (1),
.cycle 10 7 true (2),
.cycle 23 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 7 true (3)
]),
.cycle 8 4 true (3)
])
theorem kid10_part821_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part821) = true := by rfl

def kid10_part822 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 14 3 false (0),
.cycle 11 1 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.cycle 67 1 false (11),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 20, 32, 64],[4, 64, 16, 1, 40, 4, 64],64⟩,
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 32, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 32, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 20, 32, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.last 21 (1,true),
.cycle 7 17 true (2),
.cycle 2 21 true (1),
.cycle 4 21 true (1),
.cycle 92 1 false (12),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 32, 64],[4, 64, 16, 1, 20, 4, 64],64⟩,
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 19 18 true (5),
.cycle 29 1 true (9)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 18 1 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 9, 32, 64],[4, 64, 16, 1, 4, 8, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 9, 32, 64],[4, 64, 16, 1, 16, 8, 64],64⟩,
.cycle 18 1 true (6),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 2 20 true (1),
.cycle 9 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 18 1 true (6)
]),
.cycle 8 3 true (3),
.cycle 11 1 true (5),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 17 (4,true),
.cycle 13 1 true (5)
]),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 14 3 false (0),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 13 (4,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 19 7 false (1),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 24 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 14 1 true (6),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 0 18 true (0),
.cycle 2 14 true (1),
.cycle 20 5 false (1),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 11 3 true (4),
.cycle 14 1 true (6)
]),
.cycle 11 1 true (5)
])
theorem kid10_part822_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part822) = true := by rfl

def kid10_part824 : Audit := .cycle 0 13 true (0)
theorem kid10_part824_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part824) = true := by rfl

def kid10_part825 : Audit := .cycle 1 12 true (1)
theorem kid10_part825_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part825) = true := by rfl

def kid10_part826 : Audit := .cycle 2 11 true (1)
theorem kid10_part826_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part826) = true := by rfl

def kid10_part827 : Audit := .cycle 2 14 true (1)
theorem kid10_part827_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part827) = true := by rfl

def kid10_part828 : Audit := .split 14 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.last 20 (1,true),
.last 27 (1,true),
.cycle 2 14 true (1),
.last 15 (1,true),
.last 19 (1,true),
.cycle 0 16 true (0),
.last 27 (1,true),
.last 18 (1,true),
.last 16 (1,true),
.last 20 (1,true),
.cycle 2 16 true (1),
.cycle 22 1 false (0),
.last 20 (1,true),
.last 23 (1,true),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.last 24 (1,true),
.cycle 6 11 true (2)
])
theorem kid10_part828_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part828) = true := by rfl

def kid10_part829 : Audit := .cycle 6 8 true (2)
theorem kid10_part829_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part829) = true := by rfl

def kid10_part830 : Audit := .cycle 0 13 true (0)
theorem kid10_part830_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part830) = true := by rfl

def kid10_part831 : Audit := .cycle 1 12 true (1)
theorem kid10_part831_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part831) = true := by rfl

def kid10_part832 : Audit := .split 26 (1,true) (byMove [
.cycle 0 30 true (0),
.cycle 10 23 true (2),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 32, 1, 64],[9, 4, 9, 9, 9, 64, 64],64⟩,
.cycle 0 31 true (0),
.cycle 0 30 true (0),
.last 27 (5,true),
.cycle 2 26 true (1),
.cycle 1 27 true (1),
.cycle 22 5 true (5),
.cycle 0 28 true (0),
.cycle 12 15 true (2),
.last 27 (5,true),
.cycle 10 17 true (2),
.cycle 20 9 true (4),
.cycle 20 7 true (4),
.cycle 5 22 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 1, 64],[8, 16, 9, 8, 8, 64, 64],64⟩,
.last 27 (5,true),
.cycle 2 26 true (1),
.cycle 1 27 true (1),
.cycle 7 20 true (2),
.cycle 0 28 true (0),
.cycle 10 23 true (2),
.last 27 (5,true)
])
theorem kid10_part832_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part832) = true := by rfl

def kid10_part833 : Audit := .cycle 10 7 true (2)
theorem kid10_part833_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part833) = true := by rfl

def kid10_part834 : Audit := .split 16 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 10 32 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 1, 64],[1, 4, 1, 1, 1, 64, 64],64⟩,
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 32, 1, 64],[1, 16, 1, 1, 1, 64, 64],64⟩,
.last 17 (5,true),
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 13 5 true (3),
.cycle 0 18 true (0),
.cycle 12 5 true (3),
.last 17 (5,true),
.cycle 10 7 true (2),
.cycle 22 9 true (3),
.cycle 12 7 true (3),
.cycle 5 12 true (1),
.cycle 12 7 true (3),
.last 17 (5,true),
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 8 10 true (2),
.last 17 (5,true)
])
theorem kid10_part834_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part834) = true := by rfl

def kid10_part835 : Audit := .split 15 (1,true) (byMove [
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.last 27 (5,true),
.cycle 0 17 true (0),
.cycle 12 4 true (4),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 11 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.cycle 13 3 true (4),
.cycle 6 10 true (2),
.cycle 11 7 true (3),
.cycle 11 5 true (3),
.cycle 2 16 true (1),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.last 17 (5,true),
.cycle 6 11 true (2)
])
theorem kid10_part835_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part835) = true := by rfl

def kid10_part836 : Audit := .split 14 (1,true) (byMove [
.cycle 2 14 true (1),
.cycle 1 16 true (1),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 6 10 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 10 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.cycle 13 3 true (3),
.cycle 6 9 true (2),
.cycle 22 7 false (2),
.cycle 11 4 true (3),
.cycle 2 15 true (1),
.cycle 10 6 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 16 (5,true),
.cycle 6 10 true (2)
])
theorem kid10_part836_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part836) = true := by rfl

def kid10_part837 : Audit := .cycle 7 7 true (2)
theorem kid10_part837_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part837) = true := by rfl

def kid10_part838 : Audit := .cycle 0 15 true (0)
theorem kid10_part838_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part838) = true := by rfl

def kid10_part839 : Audit := .cycle 4 9 true (1)
theorem kid10_part839_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part839) = true := by rfl

def kid10_part840 : Audit := .split 14 (5,true) (byMove [
.cycle 2 23 true (1),
.cycle 2 17 true (1),
.cycle 25 1 false (1),
.cycle 43 1 false (1),
.last 20 (1,true),
.last 27 (1,true),
.cycle 6 9 true (2),
.last 15 (1,true),
.last 20 (1,true),
.cycle 2 15 true (1),
.last 27 (1,true),
.last 19 (1,true),
.last 16 (1,true),
.last 20 (1,true),
.cycle 5 11 true (1),
.cycle 22 1 false (0),
.last 20 (1,true),
.last 23 (1,true),
.cycle 6 9 true (2),
.last 15 (1,true),
.cycle 11 4 true (2),
.cycle 2 15 true (1),
.last 24 (1,true),
.cycle 6 12 true (2)
])
theorem kid10_part840_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part840) = true := by rfl

def kid10_part841 : Audit := .cycle 9 4 true (2)
theorem kid10_part841_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part841) = true := by rfl

def kid10_part842 : Audit := .cycle 0 13 true (0)
theorem kid10_part842_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part842) = true := by rfl

def kid10_part843 : Audit := .cycle 1 12 true (1)
theorem kid10_part843_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part843) = true := by rfl

def kid10_part844 : Audit := .cycle 2 11 true (1)
theorem kid10_part844_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part844) = true := by rfl

def kid10_part845 : Audit := .cycle 2 14 true (1)
theorem kid10_part845_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part845) = true := by rfl

def kid10_part846 : Audit := .split 14 (5,true) (byMove [
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 10 9 true (2),
.cycle 0 20 true (0),
.last 22 (1,true),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 2, 3],[128, 256, 8, 4194304, 16777216, 16777216, 128, 256, 32768, 1048832, 16777216, 65536, 524288, 1048576, 8, 65536, 4194304, 16777216, 524288, 1048576, 32768, 1048832, 4194304, 65536, 16777216],[256, 16777216, 16, 1, 1024, 16777216, 256, 16777216, 65536, 4096, 1024, 16777216, 1048576, 16777216, 16, 1, 4194304, 4194304, 1048576, 16777216, 65536, 4096, 4194304, 4194304, 16777216],16909360⟩,
.cycle 2 14 true (1),
.last 15 (1,true),
.last 19 (1,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.last 18 (1,true),
.last 16 (1,true),
.cycle 11 5 true (3),
.cycle 2 16 true (1),
.cycle 10 7 true (2),
.last 22 (1,true),
.far false 4 ⟨0,[0, 1, 2, 1, 0, 3, 2, 3],[128, 256, 8, 4194304, 16777216, 16777216, 128, 256, 32768, 1048832, 16777216, 65536, 524288, 1048576, 8, 65536, 4194304, 16777216, 524288, 1048576, 32768, 1048832, 4194304, 65536, 16777216],[256, 16777216, 16, 1, 1024, 16777216, 256, 16777216, 65536, 4096, 1024, 16777216, 1048576, 16777216, 16, 1, 4194304, 4194304, 1048576, 16777216, 65536, 4096, 4194304, 4194304, 16777216],16909360⟩,
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 6 11 true (2)
])
theorem kid10_part846_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part846) = true := by rfl

def kid10_part847 : Audit := .cycle 6 8 true (2)
theorem kid10_part847_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part847) = true := by rfl

def kid10_part823 : Audit := .split 12 (4,true) (byMove [(kid10_part824),(kid10_part825),(kid10_part826),(kid10_part827),(kid10_part828),(kid10_part829),(kid10_part830),(kid10_part831),(kid10_part832),(kid10_part833),(kid10_part834),(kid10_part835),(kid10_part836),(kid10_part837),(kid10_part838),(kid10_part839),(kid10_part840),(kid10_part841),(kid10_part842),(kid10_part843),(kid10_part844),(kid10_part845),(kid10_part846),(kid10_part847)])

theorem kid10_part823_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part823) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (4,true) (some mv)) (byMove [(kid10_part824),(kid10_part825),(kid10_part826),(kid10_part827),(kid10_part828),(kid10_part829),(kid10_part830),(kid10_part831),(kid10_part832),(kid10_part833),(kid10_part834),(kid10_part835),(kid10_part836),(kid10_part837),(kid10_part838),(kid10_part839),(kid10_part840),(kid10_part841),(kid10_part842),(kid10_part843),(kid10_part844),(kid10_part845),(kid10_part846),(kid10_part847)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part824_checked

  · exact kid10_part830_checked

  · exact kid10_part836_checked

  · exact kid10_part842_checked

  · exact kid10_part825_checked

  · exact kid10_part831_checked

  · exact kid10_part837_checked

  · exact kid10_part843_checked

  · exact kid10_part826_checked

  · exact kid10_part832_checked

  · exact kid10_part838_checked

  · exact kid10_part844_checked

  · exact kid10_part827_checked

  · exact kid10_part833_checked

  · exact kid10_part839_checked

  · exact kid10_part845_checked

  · exact kid10_part828_checked

  · exact kid10_part834_checked

  · exact kid10_part840_checked

  · exact kid10_part846_checked

  · exact kid10_part829_checked

  · exact kid10_part835_checked

  · exact kid10_part841_checked

  · exact kid10_part847_checked

def kid10_part849 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 16 (5,true),
.cycle 0 20 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 15 true (2),
.cycle 13 7 true (2),
.cycle 12 5 true (2),
.cycle 7 10 true (1),
.cycle 2 16 true (1),
.cycle 2 22 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 2 19 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.last 16 (5,true),
.cycle 2 25 true (1)
])
theorem kid10_part849_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part849) = true := by rfl

def kid10_part850 : Audit := .cycle 2 13 true (1)
theorem kid10_part850_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part850) = true := by rfl

def kid10_part851 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 0 23 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 40 true (0),
.cycle 12 46 true (0),
.cycle 12 15 true (0),
.cycle 0 19 true (0),
.cycle 18 5 true (3),
.last 18 (5,true),
.cycle 25 1 false (1),
.cycle 31 1 false (1),
.cycle 0 46 true (0),
.cycle 31 1 false (3),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 2 17 true (0),
.cycle 1 24 true (0),
.cycle 7 11 true (0),
.cycle 0 19 true (0),
.last 20 (5,true),
.last 18 (5,true)
])
theorem kid10_part851_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part851) = true := by rfl

def kid10_part852 : Audit := .split 32 (4,true) (byMove [
.cycle 14 21 true (1),
.cycle 0 44 true (0),
.cycle 42 1 false (2),
.cycle 0 48 true (0),
.last 34 (5,true),
.cycle 35 1 false (1),
.cycle 0 39 true (0),
.cycle 17 20 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 2, 64],[8, 8, 10, 8, 8, 64, 64],64⟩,
.cycle 0 66 true (0),
.cycle 39 5 true (6),
.last 37 (5,true),
.cycle 0 43 true (0),
.cycle 0 51 true (0),
.cycle 0 41 true (0),
.cycle 40 1 false (2),
.last 34 (5,true),
.cycle 35 1 false (1),
.cycle 0 39 true (0),
.cycle 1 35 true (0),
.cycle 14 19 true (1),
.cycle 15 24 true (1),
.last 34 (5,true),
.cycle 53 1 false (3)
])
theorem kid10_part852_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part852) = true := by rfl

def kid10_part853 : Audit := .split 12 (5,true) (byMove [
.last 19 (4,true),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 23 (4,true),
.last 30 (4,true),
.last 18 (4,true),
.last 18 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 17 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.last 32 (4,true),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 16 (4,true),
.last 30 (4,true),
.last 14 (4,true),
.last 21 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part853_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part853) = true := by rfl

def kid10_part854 : Audit := .cycle 11 6 false (1)
theorem kid10_part854_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part854) = true := by rfl

def kid10_part855 : Audit := .cycle 6 5 true (2)
theorem kid10_part855_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part855) = true := by rfl

def kid10_part856 : Audit := .cycle 1 12 true (1)
theorem kid10_part856_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part856) = true := by rfl

def kid10_part857 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 34 1 false (4),
.last 19 (5,true),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 15 true (4),
.cycle 0 52 true (0),
.cycle 11 5 true (3),
.cycle 7 8 true (2),
.cycle 11 10 true (3),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.last 19 (5,true),
.cycle 9 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 11 8 true (3)
])
theorem kid10_part857_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part857) = true := by rfl

def kid10_part858 : Audit := .cycle 2 11 true (1)
theorem kid10_part858_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part858) = true := by rfl

def kid10_part859 : Audit := .split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.last 22 (5,true),
.cycle 19 7 false (1),
.cycle 2 11 true (1),
.cycle 1 17 true (1),
.cycle 11 15 true (3),
.cycle 0 13 true (0),
.cycle 12 5 true (3),
.last 12 (5,true),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.cycle 2 13 true (1),
.cycle 31 1 false (3),
.last 22 (5,true),
.cycle 18 7 false (2),
.cycle 2 11 true (1),
.cycle 8 5 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part859_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part859) = true := by rfl

def kid10_part860 : Audit := .split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.last 20 (4,true),
.cycle 19 7 false (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 7 8 true (2),
.cycle 7 12 true (2),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 17 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (4)
])
theorem kid10_part860_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part860) = true := by rfl

def kid10_part861 : Audit := .split 15 (4,true) (byMove [
.cycle 12 9 true (1),
.cycle 0 19 true (0),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 17 7 false (2),
.cycle 2 15 true (1),
.cycle 6 13 true (1),
.cycle 13 15 true (1),
.cycle 0 17 true (0),
.cycle 16 5 true (3),
.last 16 (5,true),
.cycle 12 15 true (1),
.cycle 12 11 true (1),
.cycle 2 17 true (1),
.cycle 4 17 true (1),
.last 17 (5,true),
.cycle 17 7 false (2),
.cycle 2 15 true (1),
.cycle 6 11 true (1),
.cycle 7 9 true (1),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid10_part861_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part861) = true := by rfl

def kid10_part862 : Audit := .split 13 (4,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 1, 64, 64],64⟩,
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 0 19 true (0),
.last 15 (5,true),
.cycle 16 5 false (1),
.cycle 2 13 true (1),
.cycle 7 9 true (1),
.cycle 12 15 true (2),
.cycle 0 15 true (0),
.cycle 14 5 true (3),
.last 14 (5,true),
.cycle 16 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 2 15 true (1),
.cycle 4 15 true (1),
.last 15 (5,true),
.cycle 16 5 false (1),
.cycle 2 13 true (1),
.cycle 1 18 true (1),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid10_part862_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part862) = true := by rfl

def kid10_part863 : Audit := .cycle 5 7 true (1)
theorem kid10_part863_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part863) = true := by rfl

def kid10_part864 : Audit := .split 15 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 36 true (0),
.cycle 11 38 true (0),
.cycle 11 15 true (0),
.cycle 0 17 true (0),
.cycle 16 5 true (3),
.last 16 (5,true),
.cycle 5 13 true (0),
.cycle 17 9 true (2),
.cycle 0 42 true (0),
.cycle 28 1 false (2),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 2 15 true (0),
.cycle 1 39 true (0),
.cycle 7 9 true (0),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid10_part864_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part864) = true := by rfl

def kid10_part865 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 23 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 27 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 17 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 19 (4,true)
])
theorem kid10_part865_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part865) = true := by rfl

def kid10_part866 : Audit := .split 16 (4,true) (byMove [
.last 38 (5,true),
.cycle 1 22 true (-2),
.cycle 29 27 true (0),
.cycle 26 19 true (2),
.last 18 (5,true),
.cycle 11 6 false (1),
.cycle 25 9 true (3),
.cycle 22 24 true (0),
.cycle 36 15 true (4),
.cycle 17 7 true (1),
.cycle 20 5 true (3),
.last 17 (5,true),
.last 19 (5,true),
.last 34 (5,true),
.cycle 28 11 true (3),
.cycle 25 21 true (0),
.last 18 (5,true),
.cycle 11 6 false (1),
.last 34 (5,true),
.last 18 (5,true),
.cycle 17 15 true (1),
.cycle 22 15 true (4),
.last 22 (5,true),
.last 17 (5,true)
])
theorem kid10_part866_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part866) = true := by rfl

def kid10_part867 : Audit := .cycle 6 5 true (2)
theorem kid10_part867_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part867) = true := by rfl

def kid10_part868 : Audit := .cycle 1 12 true (1)
theorem kid10_part868_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part868) = true := by rfl

def kid10_part869 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 15 true (2),
.cycle 11 7 true (2),
.cycle 11 5 true (3),
.cycle 7 8 true (2),
.cycle 2 13 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 7 8 true (2)
])
theorem kid10_part869_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part869) = true := by rfl

def kid10_part870 : Audit := .cycle 2 11 true (1)
theorem kid10_part870_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part870) = true := by rfl

def kid10_part871 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 2 23 true (1),
.last 16 (5,true),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 11 15 true (3),
.cycle 0 13 true (0),
.cycle 12 5 true (3),
.last 12 (5,true),
.last 18 (5,true),
.cycle 10 2 true (2),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part871_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part871) = true := by rfl

def kid10_part872 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 9 4 true (2),
.last 17 (4,true),
.cycle 0 19 true (0),
.last 12 (4,true),
.cycle 13 8 false (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 7 8 true (2),
.last 14 (4,true),
.cycle 10 2 true (2),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 20 (4,true),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (4)
])
theorem kid10_part872_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part872) = true := by rfl

def kid10_part848 : Audit := .split 10 (1,true) (byMove [(kid10_part849),(kid10_part850),(kid10_part851),(kid10_part852),(kid10_part853),(kid10_part854),(kid10_part855),(kid10_part856),(kid10_part857),(kid10_part858),(kid10_part859),(kid10_part860),(kid10_part861),(kid10_part862),(kid10_part863),(kid10_part864),(kid10_part865),(kid10_part866),(kid10_part867),(kid10_part868),(kid10_part869),(kid10_part870),(kid10_part871),(kid10_part872)])

theorem kid10_part848_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part848) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part849),(kid10_part850),(kid10_part851),(kid10_part852),(kid10_part853),(kid10_part854),(kid10_part855),(kid10_part856),(kid10_part857),(kid10_part858),(kid10_part859),(kid10_part860),(kid10_part861),(kid10_part862),(kid10_part863),(kid10_part864),(kid10_part865),(kid10_part866),(kid10_part867),(kid10_part868),(kid10_part869),(kid10_part870),(kid10_part871),(kid10_part872)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part849_checked

  · exact kid10_part855_checked

  · exact kid10_part861_checked

  · exact kid10_part867_checked

  · exact kid10_part850_checked

  · exact kid10_part856_checked

  · exact kid10_part862_checked

  · exact kid10_part868_checked

  · exact kid10_part851_checked

  · exact kid10_part857_checked

  · exact kid10_part863_checked

  · exact kid10_part869_checked

  · exact kid10_part852_checked

  · exact kid10_part858_checked

  · exact kid10_part864_checked

  · exact kid10_part870_checked

  · exact kid10_part853_checked

  · exact kid10_part859_checked

  · exact kid10_part865_checked

  · exact kid10_part871_checked

  · exact kid10_part854_checked

  · exact kid10_part860_checked

  · exact kid10_part866_checked

  · exact kid10_part872_checked

def kid10_part874 : Audit := .cycle 7 7 true (2)
theorem kid10_part874_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part874) = true := by rfl

def kid10_part875 : Audit := .cycle 0 15 true (0)
theorem kid10_part875_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part875) = true := by rfl

def kid10_part876 : Audit := .cycle 38 1 false (4)
theorem kid10_part876_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part876) = true := by rfl

def kid10_part877 : Audit := .cycle 21 1 false (1)
theorem kid10_part877_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part877) = true := by rfl

def kid10_part878 : Audit := .split 24 (1,true) (byMove [
.cycle 0 43 true (-2),
.cycle 0 44 true (-2),
.cycle 0 48 true (-2),
.cycle 0 26 true (-2),
.cycle 0 37 true (-2),
.last 25 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 0, 1, 4, 5, 5, 5, 5, 5],[128, 256, 8, 68719476736, 256, 1, 524288, 1048576, 32768, 256, 68719476736, 32896, 128, 256, 8, 65536, 4097, 1, 2147483648, 4294967296, 134217728, 256, 68719476736, 68719476736, 2147483648, 4294967296, 8589934592, 65536, 68719476736, 1073741824, 2147483648, 4294967296, 8589934592, 102409277825, 102409277825, 102409277825, 68719476736],[256, 1, 16, 1, 32896, 68719476736, 1048576, 4096, 65536, 4096, 68720590848, 68719476736, 256, 1, 16, 1, 68719476736, 68719476736, 4294967296, 16777216, 268435456, 16777216, 68853698561, 68719476736, 4294967296, 1073741824, 17179869184, 1073741824, 68719476736, 68719476736, 4294967296, 1073741824, 17179869184, 1073741824, 102409277825, 68719476736, 68719476736],137301345356⟩,
.cycle 0 43 true (-2),
.last 34 (5,true),
.cycle 0 41 true (-2),
.cycle 0 36 true (-2),
.cycle 0 28 true (-2),
.cycle 0 38 true (-2),
.last 30 (5,true),
.cycle 0 49 true (-2),
.cycle 0 44 true (-2),
.cycle 11 14 true (-2),
.last 25 (5,true),
.last 42 (5,true),
.last 41 (5,true),
.cycle 2 23 true (-2),
.cycle 0 45 true (-2),
.last 26 (5,true),
.last 29 (5,true)
])
theorem kid10_part878_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part878) = true := by rfl

def kid10_part879 : Audit := .split 16 (1,true) (byMove [
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.cycle 2 21 true (1),
.cycle 0 18 true (0),
.cycle 0 21 true (0),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 0 31 true (0),
.cycle 3 14 true (1),
.cycle 8 9 true (1),
.cycle 0 20 true (0),
.cycle 6 11 true (1),
.cycle 0 27 true (0),
.cycle 0 22 true (0),
.cycle 2 17 true (1),
.cycle 11 6 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 2 18 true (1),
.last 18 (5,true),
.cycle 0 26 true (0)
])
theorem kid10_part879_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part879) = true := by rfl

def kid10_part880 : Audit := .cycle 2 11 true (1)
theorem kid10_part880_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part880) = true := by rfl

def kid10_part881 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 15 50 true (0),
.cycle 52 1 false (4),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 32, 4, 64],[12, 8, 12, 8, 8, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 6 9 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 14 42 true (0),
.cycle 5 11 true (1),
.cycle 2 15 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 1 15 true (1)
])
theorem kid10_part881_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part881) = true := by rfl

def kid10_part882 : Audit := .cycle 2 16 true (1)
theorem kid10_part882_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part882) = true := by rfl

def kid10_part883 : Audit := .cycle 0 13 true (0)
theorem kid10_part883_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part883) = true := by rfl

def kid10_part884 : Audit := .cycle 2 16 true (1)
theorem kid10_part884_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part884) = true := by rfl

def kid10_part885 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 34 true (0),
.cycle 0 23 true (0),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 30 true (0),
.cycle 0 24 true (0),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 0 30 true (0),
.cycle 5 11 true (1),
.cycle 2 15 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 0 19 true (0),
.cycle 0 19 true (0)
])
theorem kid10_part885_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part885) = true := by rfl

def kid10_part886 : Audit := .split 13 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 26 true (1),
.cycle 5 13 true (1),
.cycle 0 18 true (0),
.cycle 23 3 false (1),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 2 18 true (1),
.cycle 0 15 true (0),
.cycle 8 9 true (2),
.last 14 (5,true),
.cycle 6 13 true (2),
.cycle 20 7 false (2),
.cycle 10 4 true (2),
.cycle 5 9 true (1),
.cycle 14 6 true (0),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 6 9 true (2),
.last 14 (5,true)
])
theorem kid10_part886_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part886) = true := by rfl

def kid10_part887 : Audit := .cycle 7 9 true (2)
theorem kid10_part887_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part887) = true := by rfl

def kid10_part888 : Audit := .cycle 2 13 true (1)
theorem kid10_part888_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part888) = true := by rfl

def kid10_part889 : Audit := .cycle 31 1 false (3)
theorem kid10_part889_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part889) = true := by rfl

def kid10_part890 : Audit := .split 24 (5,true) (byMove [
.cycle 32 29 true (0),
.cycle 26 23 true (0),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 55 27 true (-1),
.last 29 (1,true),
.cycle 30 15 true (1),
.last 25 (1,true),
.cycle 36 21 true (0),
.cycle 25 21 true (1),
.cycle 15 10 true (-2),
.cycle 0 32 true (-2),
.last 26 (1,true),
.cycle 21 5 false (2),
.cycle 32 17 true (0),
.cycle 25 1 false (-1),
.cycle 16 9 false (2),
.cycle 17 8 true (-2),
.cycle 26 13 true (1),
.last 25 (1,true),
.cycle 21 4 true (0),
.cycle 25 21 true (1),
.cycle 15 11 false (2),
.cycle 26 7 true (2)
])
theorem kid10_part890_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part890) = true := by rfl

def kid10_part891 : Audit := .cycle 5 9 true (1)
theorem kid10_part891_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part891) = true := by rfl

def kid10_part892 : Audit := .cycle 2 11 true (1)
theorem kid10_part892_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part892) = true := by rfl

def kid10_part893 : Audit := .split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 2 17 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 1 15 true (1)
])
theorem kid10_part893_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part893) = true := by rfl

def kid10_part894 : Audit := .cycle 7 5 true (2)
theorem kid10_part894_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part894) = true := by rfl

def kid10_part895 : Audit := .cycle 0 13 true (0)
theorem kid10_part895_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part895) = true := by rfl

def kid10_part896 : Audit := .split 14 (5,true) (byMove [
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 5 14 true (1),
.last 17 (1,true),
.cycle 81 24 true (4),
.last 39 (1,true),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 2 19 true (1),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 0 19 true (0),
.last 21 (1,true),
.last 15 (1,true),
.cycle 10 5 true (2),
.cycle 5 10 true (1),
.cycle 11 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 17, 64],[4, 64, 16, 1, 16, 20, 64],64⟩,
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 12 6 true (4)
])
theorem kid10_part896_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part896) = true := by rfl

def kid10_part897 : Audit := .split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 2 17 true (1),
.cycle 0 14 true (0),
.cycle 13 3 true (3),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 3 true (5),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 0 16 true (0),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 13 3 true (3),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 5 11 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 15 3 true (5),
.cycle 13 3 true (4)
])
theorem kid10_part897_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part897) = true := by rfl

def kid10_part873 : Audit := .split 11 (4,true) (byMove [(kid10_part874),(kid10_part875),(kid10_part876),(kid10_part877),(kid10_part878),(kid10_part879),(kid10_part880),(kid10_part881),(kid10_part882),(kid10_part883),(kid10_part884),(kid10_part885),(kid10_part886),(kid10_part887),(kid10_part888),(kid10_part889),(kid10_part890),(kid10_part891),(kid10_part892),(kid10_part893),(kid10_part894),(kid10_part895),(kid10_part896),(kid10_part897)])

theorem kid10_part873_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part873) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (4,true) (some mv)) (byMove [(kid10_part874),(kid10_part875),(kid10_part876),(kid10_part877),(kid10_part878),(kid10_part879),(kid10_part880),(kid10_part881),(kid10_part882),(kid10_part883),(kid10_part884),(kid10_part885),(kid10_part886),(kid10_part887),(kid10_part888),(kid10_part889),(kid10_part890),(kid10_part891),(kid10_part892),(kid10_part893),(kid10_part894),(kid10_part895),(kid10_part896),(kid10_part897)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part874_checked

  · exact kid10_part880_checked

  · exact kid10_part886_checked

  · exact kid10_part892_checked

  · exact kid10_part875_checked

  · exact kid10_part881_checked

  · exact kid10_part887_checked

  · exact kid10_part893_checked

  · exact kid10_part876_checked

  · exact kid10_part882_checked

  · exact kid10_part888_checked

  · exact kid10_part894_checked

  · exact kid10_part877_checked

  · exact kid10_part883_checked

  · exact kid10_part889_checked

  · exact kid10_part895_checked

  · exact kid10_part878_checked

  · exact kid10_part884_checked

  · exact kid10_part890_checked

  · exact kid10_part896_checked

  · exact kid10_part879_checked

  · exact kid10_part885_checked

  · exact kid10_part891_checked

  · exact kid10_part897_checked

def kid10_part898 : Audit := .cycle 5 5 true (1)
theorem kid10_part898_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part898) = true := by rfl

def kid10_part900 : Audit := .cycle 0 15 true (0)
theorem kid10_part900_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part900) = true := by rfl

def kid10_part901 : Audit := .cycle 2 13 true (1)
theorem kid10_part901_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part901) = true := by rfl

def kid10_part902 : Audit := .cycle 35 1 false (3)
theorem kid10_part902_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part902) = true := by rfl

def kid10_part903 : Audit := .cycle 0 48 true (0)
theorem kid10_part903_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part903) = true := by rfl

def kid10_part904 : Audit := .split 12 (5,true) (byMove [
.cycle 20 2 false (-2),
.last 17 (1,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 48 true (0),
.last 13 (1,true),
.cycle 14 2 false (2),
.last 15 (1,true),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 0 56 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 48 true (0),
.last 13 (1,true),
.cycle 17 2 false (-1),
.last 15 (1,true),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
])
theorem kid10_part904_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part904) = true := by rfl

def kid10_part905 : Audit := .cycle 13 2 false (-1)
theorem kid10_part905_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part905) = true := by rfl

def kid10_part906 : Audit := .cycle 6 5 true (2)
theorem kid10_part906_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part906) = true := by rfl

def kid10_part907 : Audit := .split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 10 48 true (0),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 10 40 true (0),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true)
])
theorem kid10_part907_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part907) = true := by rfl

def kid10_part908 : Audit := .cycle 41 1 false (9)
theorem kid10_part908_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part908) = true := by rfl

def kid10_part909 : Audit := .cycle 2 11 true (1)
theorem kid10_part909_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part909) = true := by rfl

def kid10_part910 : Audit := .split 18 (5,true) (byMove [
.cycle 56 2 false (8),
.cycle 52 2 false (8),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.last 19 (1,true),
.cycle 24 2 false (6),
.cycle 33 2 false (7),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.last 20 (1,true),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 1],[524288, 2048, 2097152, 512, 2048, 1024, 1073741824, 4194304, 1078460416, 2097152, 8388608, 4194304, 1087057024, 1087057024, 1089187456, 32768, 131072, 65536, 1073741824, 524288, 1074268160, 512, 2048, 1024, 1073741824, 1074266112, 2097152, 512, 2048, 1024, 1073741824],[2048, 1073741824, 4194304, 524288, 4194304, 128, 4194304, 1073741824, 2048, 1078460416, 2048, 524288, 1087057024, 1073741824, 12782592, 1087057024, 12782592, 8192, 524288, 1073741824, 4194304, 2048, 4194304, 128, 1074266112, 1073741824, 4194304, 1073741824, 4194304, 128, 1073741824],1125413184⟩,
.cycle 10 13 true (-1),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.last 19 (1,true),
.cycle 37 2 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 17, 20, 64],[4, 64, 16, 1, 16, 8, 64],64⟩,
.cycle 37 2 false (7),
.cycle 20 10 true (2)
])
theorem kid10_part910_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part910) = true := by rfl

def kid10_part911 : Audit := .split 11 (5,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 35 1 false (3),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 24 2 false (6),
.cycle 0 13 true (0),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.last 13 (1,true),
.cycle 7 18 true (2),
.cycle 2 13 true (1),
.cycle 30 1 false (2),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 11 8 true (3),
.cycle 12 3 true (4)
])
theorem kid10_part911_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part911) = true := by rfl

def kid10_part912 : Audit := .split 12 (1,true) (byMove [
.cycle 2 15 true (1),
.cycle 10 25 false (2),
.cycle 20 2 false (0),
.cycle 0 20 true (0),
.cycle 18 3 false (0),
.last 13 (5,true),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.cycle 13 10 true (3),
.cycle 2 13 true (1),
.cycle 13 11 true (2),
.last 13 (5,true),
.cycle 13 15 true (1),
.cycle 10 7 false (2),
.cycle 10 4 true (1),
.cycle 2 19 true (1),
.cycle 10 6 true (0),
.last 13 (5,true),
.cycle 2 22 true (1),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.last 20 (5,true),
.last 13 (5,true)
])
theorem kid10_part912_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part912) = true := by rfl

def kid10_part913 : Audit := .split 22 (1,true) (byMove [
.cycle 5 20 true (1),
.cycle 10 172 false (7),
.cycle 54 2 false (0),
.cycle 0 33 true (0),
.cycle 25 2 false (-1),
.last 23 (5,true),
.cycle 15 9 true (2),
.cycle 1 25 true (1),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 10 13 true (1),
.last 23 (5,true),
.cycle 10 15 true (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 16, 64],[2, 2, 18, 2, 2, 64, 64],64⟩,
.cycle 10 17 true (1),
.cycle 12 13 true (1),
.cycle 25 2 false (-1),
.last 23 (5,true),
.cycle 15 9 true (2),
.cycle 1 25 true (1),
.cycle 12 11 true (2),
.cycle 5 18 true (1),
.cycle 21 2 true (2),
.last 23 (5,true)
])
theorem kid10_part913_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part913) = true := by rfl

def kid10_part914 : Audit := .cycle 5 7 true (1)
theorem kid10_part914_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part914) = true := by rfl

def kid10_part915 : Audit := .cycle 28 1 false (2)
theorem kid10_part915_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part915) = true := by rfl

def kid10_part916 : Audit := .split 12 (5,true) (byMove [
.cycle 10 51 true (-1),
.cycle 10 33 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 28 2 false (2),
.last 13 (1,true),
.cycle 15 2 false (1),
.cycle 30 2 false (4),
.cycle 14 2 false (0),
.cycle 17 2 false (5),
.last 14 (1,true),
.cycle 10 5 false (2),
.cycle 34 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 31 2 false (-1),
.last 13 (1,true),
.cycle 10 4 true (0),
.cycle 5 42 true (0),
.cycle 15 2 false (-1),
.cycle 23 2 false (-1)
])
theorem kid10_part916_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part916) = true := by rfl

def kid10_part917 : Audit := .cycle 13 2 false (-1)
theorem kid10_part917_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part917) = true := by rfl

def kid10_part918 : Audit := .cycle 6 5 true (2)
theorem kid10_part918_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part918) = true := by rfl

def kid10_part919 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 20 true (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 1 16 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true)
])
theorem kid10_part919_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part919) = true := by rfl

def kid10_part920 : Audit := .cycle 2 11 true (1)
theorem kid10_part920_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part920) = true := by rfl

def kid10_part921 : Audit := .cycle 2 11 true (1)
theorem kid10_part921_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part921) = true := by rfl

def kid10_part922 : Audit := .split 14 (5,true) (byMove [
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 10 9 true (2),
.last 17 (1,true),
.cycle 23 2 false (-1),
.cycle 23 2 false (-1),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 11 10 true (3),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 10 10 true (2),
.last 21 (1,true),
.last 15 (1,true),
.cycle 11 5 true (3),
.cycle 5 10 true (1),
.cycle 10 5 true (2),
.cycle 31 2 false (-1),
.cycle 2 14 true (1),
.last 15 (1,true),
.cycle 7 8 true (2),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 11 6 true (3)
])
theorem kid10_part922_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part922) = true := by rfl

def kid10_part923 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 18 1 false (0),
.last 14 (1,true),
.cycle 9 4 true (2),
.cycle 17 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 18 11 true (4),
.cycle 0 13 true (0),
.cycle 8 8 true (2),
.cycle 61 2 false (9),
.cycle 6 12 true (2),
.last 12 (1,true),
.cycle 13 5 true (3),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.cycle 17 2 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 11 6 true (3),
.cycle 12 3 true (4)
])
theorem kid10_part923_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part923) = true := by rfl

def kid10_part899 : Audit := .split 10 (4,true) (byMove [(kid10_part900),(kid10_part901),(kid10_part902),(kid10_part903),(kid10_part904),(kid10_part905),(kid10_part906),(kid10_part907),(kid10_part908),(kid10_part909),(kid10_part910),(kid10_part911),(kid10_part912),(kid10_part913),(kid10_part914),(kid10_part915),(kid10_part916),(kid10_part917),(kid10_part918),(kid10_part919),(kid10_part920),(kid10_part921),(kid10_part922),(kid10_part923)])

theorem kid10_part899_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part899) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part900),(kid10_part901),(kid10_part902),(kid10_part903),(kid10_part904),(kid10_part905),(kid10_part906),(kid10_part907),(kid10_part908),(kid10_part909),(kid10_part910),(kid10_part911),(kid10_part912),(kid10_part913),(kid10_part914),(kid10_part915),(kid10_part916),(kid10_part917),(kid10_part918),(kid10_part919),(kid10_part920),(kid10_part921),(kid10_part922),(kid10_part923)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part900_checked

  · exact kid10_part906_checked

  · exact kid10_part912_checked

  · exact kid10_part918_checked

  · exact kid10_part901_checked

  · exact kid10_part907_checked

  · exact kid10_part913_checked

  · exact kid10_part919_checked

  · exact kid10_part902_checked

  · exact kid10_part908_checked

  · exact kid10_part914_checked

  · exact kid10_part920_checked

  · exact kid10_part903_checked

  · exact kid10_part909_checked

  · exact kid10_part915_checked

  · exact kid10_part921_checked

  · exact kid10_part904_checked

  · exact kid10_part910_checked

  · exact kid10_part916_checked

  · exact kid10_part922_checked

  · exact kid10_part905_checked

  · exact kid10_part911_checked

  · exact kid10_part917_checked

  · exact kid10_part923_checked

def kid10_part925 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 0 20 true (0),
.cycle 0 20 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 21, 21, 64],[4, 64, 16, 1, 4, 12, 64],64⟩,
.cycle 13 7 true (2),
.cycle 5 16 true (1),
.cycle 5 16 true (1),
.last 16 (1,true),
.cycle 2 22 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 2 19 true (1),
.cycle 2 19 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 2 25 true (1),
.cycle 2 25 true (1)
])
theorem kid10_part925_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part925) = true := by rfl

def kid10_part926 : Audit := .cycle 2 13 true (1)
theorem kid10_part926_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part926) = true := by rfl

def kid10_part927 : Audit := .split 17 (4,true) (byMove [
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 40 true (0),
.last 18 (1,true),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 32 1 false (2),
.last 19 (1,true),
.cycle 31 1 false (1),
.cycle 0 46 true (0),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 2 17 true (0),
.last 18 (1,true),
.cycle 7 11 true (0),
.cycle 0 19 true (0),
.cycle 27 1 false (1),
.cycle 25 1 false (1)
])
theorem kid10_part927_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part927) = true := by rfl

def kid10_part928 : Audit := .split 32 (4,true) (byMove [
.cycle 14 21 true (1),
.cycle 0 44 true (0),
.cycle 42 1 false (2),
.cycle 0 48 true (0),
.cycle 35 1 false (1),
.cycle 35 1 false (1),
.last 34 (1,true),
.cycle 17 20 true (1),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 20, 276, 276, 8192, 16384, 8, 256, 21, 21, 524288, 1048576, 32768, 276, 16777216, 16777216, 524288, 1048576, 2097152, 5242880, 22282517, 22282517, 16777216],[256, 16777216, 16, 1, 4, 284, 16384, 16777216, 16, 1, 4, 128, 1048576, 16777216, 65536, 4096, 16384, 412, 1048576, 16777216, 4194304, 262144, 1048576, 24903957, 16777216],33501248⟩,
.last 61 (1,true),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.last 34 (1,true),
.last 40 (1,true),
.last 36 (1,true),
.cycle 40 1 false (2),
.cycle 35 1 false (1),
.cycle 35 1 false (1),
.last 34 (1,true),
.cycle 1 35 true (0),
.cycle 14 19 true (1),
.cycle 15 24 true (1),
.cycle 53 1 false (3),
.cycle 53 1 false (3)
])
theorem kid10_part928_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part928) = true := by rfl

def kid10_part929 : Audit := .cycle 14 1 false (-2)
theorem kid10_part929_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part929) = true := by rfl

def kid10_part930 : Audit := .cycle 13 1 false (-1)
theorem kid10_part930_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part930) = true := by rfl

def kid10_part931 : Audit := .cycle 6 5 true (2)
theorem kid10_part931_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part931) = true := by rfl

def kid10_part932 : Audit := .split 11 (1,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.last 16 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 17 (4,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1)
])
theorem kid10_part932_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part932) = true := by rfl

def kid10_part933 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 34 1 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (9),
.cycle 0 52 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 27 10 true (5),
.cycle 25 27 true (3)
])
theorem kid10_part933_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part933) = true := by rfl

def kid10_part934 : Audit := .cycle 2 11 true (1)
theorem kid10_part934_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part934) = true := by rfl

def kid10_part935 : Audit := .split 11 (4,true) (byMove [
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 25 1 false (7),
.cycle 0 13 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.last 13 (1,true),
.cycle 7 9 true (2),
.cycle 2 13 true (1),
.cycle 31 1 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 8 5 true (2)
])
theorem kid10_part935_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part935) = true := by rfl

def kid10_part936 : Audit := .cycle 24 1 false (6)
theorem kid10_part936_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part936) = true := by rfl

def kid10_part937 : Audit := .split 12 (1,true) (byMove [
.cycle 2 15 true (1),
.last 35 (4,true),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.last 13 (4,true),
.cycle 18 3 false (0),
.cycle 6 7 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 24 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part937_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part937) = true := by rfl

def kid10_part938 : Audit := .split 13 (4,true) (byMove [
.last 20 (1,true),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 0 19 true (0),
.last 16 (1,true),
.last 16 (1,true),
.cycle 2 13 true (1),
.last 14 (1,true),
.last 20 (1,true),
.cycle 0 15 true (0),
.last 20 (1,true),
.cycle 7 9 true (1),
.last 15 (1,true),
.last 22 (1,true),
.cycle 2 15 true (1),
.cycle 4 15 true (1),
.last 16 (1,true),
.last 16 (1,true),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (1),
.cycle 0 15 true (0),
.last 17 (1,true),
.last 15 (1,true)
])
theorem kid10_part938_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part938) = true := by rfl

def kid10_part939 : Audit := .cycle 5 7 true (1)
theorem kid10_part939_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part939) = true := by rfl

def kid10_part940 : Audit := .split 15 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 0 21 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 36 true (0),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 1 false (1),
.last 17 (1,true),
.cycle 17 9 true (2),
.cycle 0 42 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 2 15 true (0),
.last 16 (1,true),
.cycle 7 9 true (0),
.cycle 0 17 true (0),
.cycle 5 30 true (0),
.cycle 36 7 true (4)
])
theorem kid10_part940_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part940) = true := by rfl

def kid10_part941 : Audit := .cycle 14 1 false (-2)
theorem kid10_part941_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part941) = true := by rfl

def kid10_part942 : Audit := .cycle 13 1 false (-1)
theorem kid10_part942_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part942) = true := by rfl

def kid10_part943 : Audit := .cycle 6 5 true (2)
theorem kid10_part943_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part943) = true := by rfl

def kid10_part944 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 20 (4,true),
.cycle 20 1 false (0),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 7 7 true (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.last 19 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.last 14 (4,true),
.last 15 (4,true),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1)
])
theorem kid10_part944_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part944) = true := by rfl

def kid10_part945 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 20, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 2 18 true (1),
.last 14 (1,true),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 4 true (2),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2)
])
theorem kid10_part945_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part945) = true := by rfl

def kid10_part946 : Audit := .cycle 2 11 true (1)
theorem kid10_part946_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part946) = true := by rfl

def kid10_part947 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 20 1 false (0),
.last 14 (1,true),
.cycle 18 1 false (-2),
.cycle 10 4 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 20, 20, 64],[4, 64, 16, 1, 4, 16, 64],64⟩,
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 9 8 true (2),
.last 16 (1,true),
.last 12 (1,true),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.cycle 18 1 false (-2),
.cycle 10 2 true (2),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (2),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part947_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part947) = true := by rfl

def kid10_part948 : Audit := .cycle 11 3 true (3)
theorem kid10_part948_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part948) = true := by rfl

def kid10_part924 : Audit := .split 10 (5,true) (byMove [(kid10_part925),(kid10_part926),(kid10_part927),(kid10_part928),(kid10_part929),(kid10_part930),(kid10_part931),(kid10_part932),(kid10_part933),(kid10_part934),(kid10_part935),(kid10_part936),(kid10_part937),(kid10_part938),(kid10_part939),(kid10_part940),(kid10_part941),(kid10_part942),(kid10_part943),(kid10_part944),(kid10_part945),(kid10_part946),(kid10_part947),(kid10_part948)])

theorem kid10_part924_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part924) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part925),(kid10_part926),(kid10_part927),(kid10_part928),(kid10_part929),(kid10_part930),(kid10_part931),(kid10_part932),(kid10_part933),(kid10_part934),(kid10_part935),(kid10_part936),(kid10_part937),(kid10_part938),(kid10_part939),(kid10_part940),(kid10_part941),(kid10_part942),(kid10_part943),(kid10_part944),(kid10_part945),(kid10_part946),(kid10_part947),(kid10_part948)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part925_checked

  · exact kid10_part931_checked

  · exact kid10_part937_checked

  · exact kid10_part943_checked

  · exact kid10_part926_checked

  · exact kid10_part932_checked

  · exact kid10_part938_checked

  · exact kid10_part944_checked

  · exact kid10_part927_checked

  · exact kid10_part933_checked

  · exact kid10_part939_checked

  · exact kid10_part945_checked

  · exact kid10_part928_checked

  · exact kid10_part934_checked

  · exact kid10_part940_checked

  · exact kid10_part946_checked

  · exact kid10_part929_checked

  · exact kid10_part935_checked

  · exact kid10_part941_checked

  · exact kid10_part947_checked

  · exact kid10_part930_checked

  · exact kid10_part936_checked

  · exact kid10_part942_checked

  · exact kid10_part948_checked

def kid10_part949 : Audit := .cycle 2 9 true (1)
theorem kid10_part949_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part949) = true := by rfl

def kid10_part951 : Audit := .cycle 2 10 true (1)
theorem kid10_part951_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part951) = true := by rfl

def kid10_part952 : Audit := .cycle 1 12 true (1)
theorem kid10_part952_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part952) = true := by rfl

def kid10_part953 : Audit := .cycle 7 4 true (3)
theorem kid10_part953_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part953) = true := by rfl

def kid10_part954 : Audit := .cycle 0 12 true (0)
theorem kid10_part954_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part954) = true := by rfl

def kid10_part955 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 16, 8, 8, 8, 64, 64],64⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.cycle 1 12 true (1)
])
theorem kid10_part955_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part955) = true := by rfl

def kid10_part956 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 13 true (1),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 1 12 true (1),
.cycle 6 6 true (2),
.cycle 20 16 false (2),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 14 (4,true),
.cycle 1 12 true (1)
])
theorem kid10_part956_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part956) = true := by rfl

def kid10_part957 : Audit := .cycle 0 11 true (0)
theorem kid10_part957_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part957) = true := by rfl

def kid10_part958 : Audit := .cycle 1 10 true (1)
theorem kid10_part958_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part958) = true := by rfl

def kid10_part959 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.last 20 (5,true),
.cycle 1 19 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 7 21 true (3),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.cycle 1 19 true (1),
.cycle 10 10 true (3),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (5,true),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.last 20 (5,true),
.cycle 1 19 true (1)
])
theorem kid10_part959_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part959) = true := by rfl

def kid10_part960 : Audit := .cycle 3 8 true (1)
theorem kid10_part960_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part960) = true := by rfl

def kid10_part961 : Audit := .cycle 8 3 true (3)
theorem kid10_part961_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part961) = true := by rfl

def kid10_part962 : Audit := .cycle 1 11 true (1)
theorem kid10_part962_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part962) = true := by rfl

def kid10_part963 : Audit := .cycle 6 5 true (2)
theorem kid10_part963_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part963) = true := by rfl

def kid10_part964 : Audit := .split 15 (4,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 1, 64, 64],64⟩,
.cycle 0 19 true (0),
.cycle 2 21 true (1),
.cycle 0 21 true (0),
.last 17 (5,true),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 2 15 true (1),
.cycle 7 11 true (1),
.cycle 14 17 true (2),
.cycle 0 17 true (0),
.cycle 16 7 true (3),
.last 16 (5,true),
.cycle 18 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 2 17 true (1),
.cycle 4 17 true (1),
.last 17 (5,true),
.cycle 18 7 false (2),
.cycle 2 15 true (1),
.cycle 1 20 true (1),
.cycle 7 9 true (1),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid10_part964_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part964) = true := by rfl

def kid10_part965 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 32, 8, 64],[8, 4, 8, 8, 8, 64, 64],64⟩,
.cycle 11 7 true (2),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 10 4 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 14 (5,true),
.cycle 1 13 true (1)
])
theorem kid10_part965_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part965) = true := by rfl

def kid10_part966 : Audit := .cycle 2 11 true (1)
theorem kid10_part966_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part966) = true := by rfl

def kid10_part967 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 47 1 false (3),
.cycle 29 1 false (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.last 14 (5,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.last 12 (5,true),
.cycle 10 6 true (2),
.last 14 (5,true),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 10 2 true (3),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part967_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part967) = true := by rfl

def kid10_part968 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 35 true (-2),
.last 23 (4,true),
.cycle 29 1 false (1),
.last 12 (4,true),
.cycle 0 17 true (0),
.cycle 2 11 true (1),
.cycle 9 4 true (3),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 true (1),
.last 14 (4,true),
.last 22 (4,true),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 2 11 true (1),
.cycle 10 2 true (3),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 13 true (1)
])
theorem kid10_part968_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part968) = true := by rfl

def kid10_part969 : Audit := .cycle 0 11 true (0)
theorem kid10_part969_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part969) = true := by rfl

def kid10_part970 : Audit := .cycle 1 10 true (1)
theorem kid10_part970_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part970) = true := by rfl

def kid10_part971 : Audit := .cycle 2 9 true (1)
theorem kid10_part971_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part971) = true := by rfl

def kid10_part972 : Audit := .cycle 2 12 true (1)
theorem kid10_part972_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part972) = true := by rfl

def kid10_part973 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 5 16 true (1),
.last 17 (4,true),
.cycle 10 5 true (3),
.last 13 (4,true),
.last 23 (4,true),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 2 12 true (1),
.cycle 10 3 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 14 true (1)
])
theorem kid10_part973_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part973) = true := by rfl

def kid10_part974 : Audit := .cycle 1 11 true (1)
theorem kid10_part974_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part974) = true := by rfl

def kid10_part950 : Audit := .split 10 (1,true) (byMove [(kid10_part951),(kid10_part952),(kid10_part953),(kid10_part954),(kid10_part955),(kid10_part956),(kid10_part957),(kid10_part958),(kid10_part959),(kid10_part960),(kid10_part961),(kid10_part962),(kid10_part963),(kid10_part964),(kid10_part965),(kid10_part966),(kid10_part967),(kid10_part968),(kid10_part969),(kid10_part970),(kid10_part971),(kid10_part972),(kid10_part973),(kid10_part974)])

theorem kid10_part950_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part950) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid10_part951),(kid10_part952),(kid10_part953),(kid10_part954),(kid10_part955),(kid10_part956),(kid10_part957),(kid10_part958),(kid10_part959),(kid10_part960),(kid10_part961),(kid10_part962),(kid10_part963),(kid10_part964),(kid10_part965),(kid10_part966),(kid10_part967),(kid10_part968),(kid10_part969),(kid10_part970),(kid10_part971),(kid10_part972),(kid10_part973),(kid10_part974)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part951_checked

  · exact kid10_part957_checked

  · exact kid10_part963_checked

  · exact kid10_part969_checked

  · exact kid10_part952_checked

  · exact kid10_part958_checked

  · exact kid10_part964_checked

  · exact kid10_part970_checked

  · exact kid10_part953_checked

  · exact kid10_part959_checked

  · exact kid10_part965_checked

  · exact kid10_part971_checked

  · exact kid10_part954_checked

  · exact kid10_part960_checked

  · exact kid10_part966_checked

  · exact kid10_part972_checked

  · exact kid10_part955_checked

  · exact kid10_part961_checked

  · exact kid10_part967_checked

  · exact kid10_part973_checked

  · exact kid10_part956_checked

  · exact kid10_part962_checked

  · exact kid10_part968_checked

  · exact kid10_part974_checked

def kid10_part975 : Audit := .cycle 7 3 true (3)
theorem kid10_part975_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part975) = true := by rfl

def kid10_part976 : Audit := .cycle 0 11 true (0)
theorem kid10_part976_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part976) = true := by rfl

def kid10_part978 : Audit := .cycle 2 10 true (1)
theorem kid10_part978_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part978) = true := by rfl

def kid10_part979 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 19 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 16 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid10_part979_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part979) = true := by rfl

def kid10_part980 : Audit := .cycle 7 4 true (3)
theorem kid10_part980_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part980) = true := by rfl

def kid10_part981 : Audit := .cycle 0 12 true (0)
theorem kid10_part981_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part981) = true := by rfl

def kid10_part982 : Audit := .split 14 (5,true) (byMove [
.cycle 22 4 false (0),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 13 3 false (1),
.cycle 25 4 false (3),
.last 15 (1,true),
.cycle 16 4 false (2),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 13 4 true (0),
.last 16 (1,true),
.cycle 12 5 false (2),
.cycle 27 4 false (3),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.cycle 2 14 true (0),
.last 15 (1,true),
.cycle 19 4 false (1),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 13 4 true (0)
])
theorem kid10_part982_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part982) = true := by rfl

def kid10_part983 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 19 4 false (-1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 24, 16, 64],[4, 64, 16, 1, 24, 4, 64],64⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 11 4 true (3),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 2 18 true (1),
.cycle 2 12 true (1),
.cycle 19 4 false (-1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 10 4 true (3),
.cycle 11 4 true (3)
])
theorem kid10_part983_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part983) = true := by rfl

def kid10_part984 : Audit := .cycle 0 11 true (0)
theorem kid10_part984_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part984) = true := by rfl

def kid10_part985 : Audit := .cycle 1 10 true (1)
theorem kid10_part985_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part985) = true := by rfl

def kid10_part986 : Audit := .cycle 7 21 true (3)
theorem kid10_part986_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part986) = true := by rfl

def kid10_part987 : Audit := .cycle 3 8 true (1)
theorem kid10_part987_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part987) = true := by rfl

def kid10_part988 : Audit := .cycle 8 3 true (3)
theorem kid10_part988_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part988) = true := by rfl

def kid10_part989 : Audit := .split 13 (5,true) (byMove [
.cycle 7 9 true (3),
.cycle 0 17 true (0),
.cycle 15 20 true (3),
.cycle 0 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 22 3 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5),
.last 15 (1,true),
.cycle 10 6 true (4),
.cycle 2 15 true (1),
.cycle 14 16 true (3),
.cycle 25 6 false (1),
.cycle 9 8 true (3),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5)
])
theorem kid10_part989_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part989) = true := by rfl

def kid10_part990 : Audit := .cycle 6 5 true (2)
theorem kid10_part990_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part990) = true := by rfl

def kid10_part991 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 409, 1024, 128, 256, 8, 256, 4096, 1024, 4096],[256, 8, 16, 1, 16, 4096, 256, 409, 16, 1, 409, 4096, 4096],7200⟩,
.cycle 49 1 false (1),
.cycle 0 16 true (0),
.cycle 19 4 false (1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 7 7 true (3),
.last 12 (5,true),
.cycle 7 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 1024, 128, 256, 8, 256, 4096, 1024, 4096],[256, 16, 16, 1, 16, 4096, 256, 16, 16, 1, 16, 4096, 4096],7200⟩,
.cycle 7 11 true (2),
.cycle 5 7 true (1),
.cycle 27 4 false (1),
.last 12 (5,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true)
])
theorem kid10_part991_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part991) = true := by rfl

def kid10_part992 : Audit := .cycle 0 15 true (0)
theorem kid10_part992_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part992) = true := by rfl

def kid10_part993 : Audit := .cycle 2 11 true (1)
theorem kid10_part993_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part993) = true := by rfl

def kid10_part994 : Audit := .split 14 (5,true) (byMove [
.cycle 12 55 true (-1),
.cycle 12 37 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 13 3 false (1),
.cycle 30 4 false (4),
.last 15 (1,true),
.cycle 16 4 false (2),
.cycle 32 4 false (6),
.cycle 15 4 false (1),
.cycle 17 4 true (3),
.last 16 (1,true),
.cycle 12 5 false (2),
.cycle 36 4 false (4),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.cycle 33 4 false (1),
.last 15 (1,true),
.cycle 12 4 true (0),
.cycle 5 48 true (0),
.cycle 15 4 false (1),
.cycle 17 4 true (3)
])
theorem kid10_part994_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part994) = true := by rfl

def kid10_part995 : Audit := .split 11 (5,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 33 1 false (1),
.last 14 (1,true),
.cycle 17 4 false (0),
.cycle 16 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 11 4 true (3),
.cycle 9 6 true (2),
.last 12 (1,true),
.cycle 5 13 true (1),
.cycle 5 7 true (1),
.cycle 17 4 false (0),
.cycle 16 3 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 11 4 true (3)
])
theorem kid10_part995_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part995) = true := by rfl

def kid10_part996 : Audit := .cycle 0 11 true (0)
theorem kid10_part996_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part996) = true := by rfl

def kid10_part997 : Audit := .cycle 1 10 true (1)
theorem kid10_part997_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part997) = true := by rfl

def kid10_part998 : Audit := .cycle 2 9 true (1)
theorem kid10_part998_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part998) = true := by rfl

def kid10_part999 : Audit := .cycle 2 12 true (1)
theorem kid10_part999_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part999) = true := by rfl

def kid10_part1000 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 10 7 true (3),
.last 15 (1,true),
.cycle 19 8 false (1),
.cycle 18 3 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 4 true (4),
.last 19 (1,true),
.last 13 (1,true),
.cycle 10 5 true (3),
.cycle 5 8 true (1),
.cycle 10 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 16, 16, 64],[4, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 4 true (4)
])
theorem kid10_part1000_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part1000) = true := by rfl

def kid10_part1001 : Audit := .split 13 (5,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 7 12 true (3),
.last 16 (1,true),
.cycle 9 6 true (3),
.cycle 20 3 false (0),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5),
.cycle 10 6 true (4),
.last 14 (1,true),
.cycle 10 8 true (4),
.cycle 5 9 true (1),
.cycle 13 2 true (4),
.cycle 20 5 false (2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5)
])
theorem kid10_part1001_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part1001) = true := by rfl

def kid10_part977 : Audit := .split 10 (4,true) (byMove [(kid10_part978),(kid10_part979),(kid10_part980),(kid10_part981),(kid10_part982),(kid10_part983),(kid10_part984),(kid10_part985),(kid10_part986),(kid10_part987),(kid10_part988),(kid10_part989),(kid10_part990),(kid10_part991),(kid10_part992),(kid10_part993),(kid10_part994),(kid10_part995),(kid10_part996),(kid10_part997),(kid10_part998),(kid10_part999),(kid10_part1000),(kid10_part1001)])

theorem kid10_part977_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part977) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid10_part978),(kid10_part979),(kid10_part980),(kid10_part981),(kid10_part982),(kid10_part983),(kid10_part984),(kid10_part985),(kid10_part986),(kid10_part987),(kid10_part988),(kid10_part989),(kid10_part990),(kid10_part991),(kid10_part992),(kid10_part993),(kid10_part994),(kid10_part995),(kid10_part996),(kid10_part997),(kid10_part998),(kid10_part999),(kid10_part1000),(kid10_part1001)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part978_checked

  · exact kid10_part984_checked

  · exact kid10_part990_checked

  · exact kid10_part996_checked

  · exact kid10_part979_checked

  · exact kid10_part985_checked

  · exact kid10_part991_checked

  · exact kid10_part997_checked

  · exact kid10_part980_checked

  · exact kid10_part986_checked

  · exact kid10_part992_checked

  · exact kid10_part998_checked

  · exact kid10_part981_checked

  · exact kid10_part987_checked

  · exact kid10_part993_checked

  · exact kid10_part999_checked

  · exact kid10_part982_checked

  · exact kid10_part988_checked

  · exact kid10_part994_checked

  · exact kid10_part1000_checked

  · exact kid10_part983_checked

  · exact kid10_part989_checked

  · exact kid10_part995_checked

  · exact kid10_part1001_checked

def kid10_part1003 : Audit := .cycle 2 10 true (1)
theorem kid10_part1003_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part1003) = true := by rfl

def kid10_part1004 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 15 (4,true),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 0 16 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 2 19 true (1),
.cycle 12 1 true (4)
])
theorem kid10_part1004_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part1004) = true := by rfl

def kid10_part1005 : Audit := .cycle 7 4 true (3)
theorem kid10_part1005_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part1005) = true := by rfl

def kid10_part1006 : Audit := .cycle 0 12 true (0)
theorem kid10_part1006_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part1006) = true := by rfl

def kid10_part1007 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 33 1 false (1),
.cycle 0 13 true (0),
.cycle 15 4 false (-1),
.cycle 32 1 true (-6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 2048, 128, 256, 8, 256, 4117, 2048, 4096],[256, 4096, 16, 1, 4, 4252, 256, 4096, 16, 1, 4, 8, 4096],5120⟩,
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 15 4 false (-1),
.cycle 16 3 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 17 6 false (1),
.cycle 12 1 true (4)
])
theorem kid10_part1007_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part1007) = true := by rfl

def kid10_part1008 : Audit := .cycle 13 1 true (1)
theorem kid10_part1008_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part1008) = true := by rfl

def kid10_part1009 : Audit := .cycle 0 11 true (0)
theorem kid10_part1009_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part1009) = true := by rfl

def kid10_part1010 : Audit := .cycle 1 10 true (1)
theorem kid10_part1010_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part1010) = true := by rfl

def kid10_part1011 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 7 14 true (3),
.cycle 19 1 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 7 21 true (3),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.cycle 19 1 true (7),
.last 20 (1,true),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 7 19 true (3),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 2 20 true (1),
.cycle 7 14 true (3),
.cycle 19 1 true (7)
])
theorem kid10_part1011_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part1011) = true := by rfl

def kid10_part1012 : Audit := .cycle 3 8 true (1)
theorem kid10_part1012_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part1012) = true := by rfl

def kid10_part1013 : Audit := .cycle 8 3 true (3)
theorem kid10_part1013_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part1013) = true := by rfl

def kid10_part1014 : Audit := .cycle 11 1 true (5)
theorem kid10_part1014_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part1014) = true := by rfl

def kid10_part1015 : Audit := .cycle 6 5 true (2)
theorem kid10_part1015_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part1015) = true := by rfl

def kid10_part1016 : Audit := .split 11 (1,true) (byMove [
.cycle 0 15 true (0),
.last 20 (4,true),
.last 23 (4,true),
.cycle 0 16 true (0),
.last 12 (4,true),
.cycle 22 7 false (1),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 7 7 true (3),
.last 14 (4,true),
.last 15 (4,true),
.last 13 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 15 (4,true),
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3)
])
theorem kid10_part1016_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part1016) = true := by rfl

def kid10_part1017 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 2 16 true (1),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 21, 32, 64],[4, 64, 16, 1, 4, 5, 64],64⟩,
.cycle 11 7 true (2),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 5 11 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 2 16 true (1),
.cycle 13 1 true (5)
])
theorem kid10_part1017_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part1017) = true := by rfl

def kid10_part1018 : Audit := .cycle 2 11 true (1)
theorem kid10_part1018_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part1018) = true := by rfl

def kid10_part1019 : Audit := .split 11 (4,true) (byMove [
.cycle 0 15 true (0),
.last 12 (1,true),
.cycle 47 1 false (3),
.last 14 (1,true),
.cycle 15 4 false (-1),
.cycle 14 9 false (0),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 16 5 false (0),
.last 16 (1,true),
.last 12 (1,true),
.cycle 2 15 true (1),
.cycle 5 7 true (1),
.cycle 15 4 false (-1),
.cycle 16 3 false (-1),
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 11 5 true (3),
.cycle 10 2 true (3)
])
theorem kid10_part1019_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part1019) = true := by rfl

def kid10_part1020 : Audit := .cycle 15 3 false (1)
theorem kid10_part1020_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part1020) = true := by rfl

def kid10_part1021 : Audit := .cycle 0 11 true (0)
theorem kid10_part1021_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part1021) = true := by rfl

def kid10_part1022 : Audit := .cycle 1 10 true (1)
theorem kid10_part1022_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part1022) = true := by rfl

def kid10_part1023 : Audit := .cycle 2 9 true (1)
theorem kid10_part1023_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part1023) = true := by rfl

def kid10_part1024 : Audit := .cycle 2 12 true (1)
theorem kid10_part1024_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part1024) = true := by rfl

def kid10_part1025 : Audit := .split 13 (4,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 19 8 false (1),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 24 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 14 1 true (6),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 0 18 true (0),
.cycle 2 14 true (1),
.cycle 19 6 false (1),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 11 3 true (4),
.cycle 14 1 true (6)
])
theorem kid10_part1025_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part1025) = true := by rfl

def kid10_part1026 : Audit := .cycle 11 1 true (5)
theorem kid10_part1026_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part1026) = true := by rfl

def kid10_part1002 : Audit := .split 10 (5,true) (byMove [(kid10_part1003),(kid10_part1004),(kid10_part1005),(kid10_part1006),(kid10_part1007),(kid10_part1008),(kid10_part1009),(kid10_part1010),(kid10_part1011),(kid10_part1012),(kid10_part1013),(kid10_part1014),(kid10_part1015),(kid10_part1016),(kid10_part1017),(kid10_part1018),(kid10_part1019),(kid10_part1020),(kid10_part1021),(kid10_part1022),(kid10_part1023),(kid10_part1024),(kid10_part1025),(kid10_part1026)])

theorem kid10_part1002_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part1002) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part1003),(kid10_part1004),(kid10_part1005),(kid10_part1006),(kid10_part1007),(kid10_part1008),(kid10_part1009),(kid10_part1010),(kid10_part1011),(kid10_part1012),(kid10_part1013),(kid10_part1014),(kid10_part1015),(kid10_part1016),(kid10_part1017),(kid10_part1018),(kid10_part1019),(kid10_part1020),(kid10_part1021),(kid10_part1022),(kid10_part1023),(kid10_part1024),(kid10_part1025),(kid10_part1026)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1003_checked

  · exact kid10_part1009_checked

  · exact kid10_part1015_checked

  · exact kid10_part1021_checked

  · exact kid10_part1004_checked

  · exact kid10_part1010_checked

  · exact kid10_part1016_checked

  · exact kid10_part1022_checked

  · exact kid10_part1005_checked

  · exact kid10_part1011_checked

  · exact kid10_part1017_checked

  · exact kid10_part1023_checked

  · exact kid10_part1006_checked

  · exact kid10_part1012_checked

  · exact kid10_part1018_checked

  · exact kid10_part1024_checked

  · exact kid10_part1007_checked

  · exact kid10_part1013_checked

  · exact kid10_part1019_checked

  · exact kid10_part1025_checked

  · exact kid10_part1008_checked

  · exact kid10_part1014_checked

  · exact kid10_part1020_checked

  · exact kid10_part1026_checked

def kid10_part690 : Audit := .split 9 (5,false) (byMove [(kid10_part691),(kid10_part692),(kid10_part717),(kid10_part742),(kid10_part767),(kid10_part792),(kid10_part817),(kid10_part818),(kid10_part819),(kid10_part820),(kid10_part821),(kid10_part822),(kid10_part823),(kid10_part848),(kid10_part873),(kid10_part898),(kid10_part899),(kid10_part924),(kid10_part949),(kid10_part950),(kid10_part975),(kid10_part976),(kid10_part977),(kid10_part1002)])

theorem kid10_part690_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid10_part690) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part691),(kid10_part692),(kid10_part717),(kid10_part742),(kid10_part767),(kid10_part792),(kid10_part817),(kid10_part818),(kid10_part819),(kid10_part820),(kid10_part821),(kid10_part822),(kid10_part823),(kid10_part848),(kid10_part873),(kid10_part898),(kid10_part899),(kid10_part924),(kid10_part949),(kid10_part950),(kid10_part975),(kid10_part976),(kid10_part977),(kid10_part1002)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part691_checked

  · exact kid10_part817_checked

  · exact kid10_part823_checked

  · exact kid10_part949_checked

  · exact kid10_part692_checked

  · exact kid10_part818_checked

  · exact kid10_part848_checked

  · exact kid10_part950_checked

  · exact kid10_part717_checked

  · exact kid10_part819_checked

  · exact kid10_part873_checked

  · exact kid10_part975_checked

  · exact kid10_part742_checked

  · exact kid10_part820_checked

  · exact kid10_part898_checked

  · exact kid10_part976_checked

  · exact kid10_part767_checked

  · exact kid10_part821_checked

  · exact kid10_part899_checked

  · exact kid10_part977_checked

  · exact kid10_part792_checked

  · exact kid10_part822_checked

  · exact kid10_part924_checked

  · exact kid10_part1002_checked

def kid10_part1027 : Audit := .cycle 0 9 true (0)
theorem kid10_part1027_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid10_part1027) = true := by rfl

def kid10_part1028 : Audit := .cycle 1 8 true (1)
theorem kid10_part1028_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid10_part1028) = true := by rfl

def kid10_part1029 : Audit := .cycle 2 7 true (1)
theorem kid10_part1029_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid10_part1029) = true := by rfl

def kid10_part1030 : Audit := .cycle 2 10 true (1)
theorem kid10_part1030_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid10_part1030) = true := by rfl

def kid10_part1031 : Audit := .cycle 8 1 true (4)
theorem kid10_part1031_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid10_part1031) = true := by rfl

def kid10_part1033 : Audit := .cycle 2 9 true (1)
theorem kid10_part1033_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part1033) = true := by rfl

def kid10_part1034 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 31 1 false (1),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 39 1 false (3),
.cycle 14 7 true (0),
.cycle 25 3 false (2),
.cycle 1 15 true (1),
.cycle 25 3 false (1),
.cycle 24 3 false (0),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.last 16 (5,true),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 11 4 true (2),
.cycle 21 3 false (1)
]),
.cycle 11 13 false (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 35 1 false (3),
.cycle 2 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[4, 4, 16, 1, 2, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 4, 16, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 4, 16, 1, 16, 64, 64],64⟩,
.last 20 (5,true),
.cycle 38 10 true (8),
.cycle 7 17 true (2),
.cycle 2 21 true (1),
.cycle 4 21 true (1),
.last 21 (5,true),
.cycle 2 23 true (1),
.cycle 2 19 true (1),
.cycle 1 28 true (1),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.last 20 (5,true)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 18 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 28, 64],[4, 8, 16, 1, 4, 64, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 28, 64],[4, 8, 16, 1, 16, 64, 64],64⟩,
.cycle 1 18 true (1),
.cycle 3 17 true (1),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 18 true (1),
.cycle 9 9 true (2)
]),
.cycle 8 3 true (4),
.cycle 1 11 true (1),
.cycle 6 7 true (2),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 14 (4,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 15 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.cycle 25 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.last 16 (4,true),
.last 15 (4,true)
]),
.split 21 (5,true) (byMove [
.cycle 20 33 true (0),
.cycle 0 31 true (-2),
.last 29 (4,true),
.cycle 20 17 true (-2),
.cycle 11 12 false (3),
.last 30 (4,true),
.cycle 0 25 true (-2),
.cycle 0 35 true (-2),
.last 32 (4,true),
.cycle 0 27 true (-2),
.last 22 (4,true),
.cycle 0 27 true (-2),
.last 30 (4,true),
.last 24 (4,true),
.cycle 0 27 true (-2),
.last 27 (4,true),
.last 24 (4,true),
.cycle 0 29 true (-2),
.cycle 0 25 true (-2),
.cycle 20 2 true (1),
.cycle 0 52 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2048, 32768, 128, 256, 32768, 256, 2048, 128, 128, 256, 8, 65536, 2048, 32768, 262144],[256, 1, 16, 1, 262144, 512, 256, 4096, 65536, 4096, 262144, 512, 256, 4096, 16, 1, 262144, 512, 262144],278540⟩,
.last 22 (4,true),
.cycle 20 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1034_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part1034) = true := by rfl

def kid10_part1035 : Audit := .cycle 7 3 true (3)
theorem kid10_part1035_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part1035) = true := by rfl

def kid10_part1036 : Audit := .cycle 0 11 true (0)
theorem kid10_part1036_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part1036) = true := by rfl

def kid10_part1037 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 18 3 false (0),
.cycle 13 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 8, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 10 7 true (2),
.cycle 8 3 true (4),
.cycle 8 4 true (4),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 6 8 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 6 11 true (2),
.cycle 6 7 true (2),
.cycle 20 7 false (2),
.cycle 10 4 true (3),
.cycle 2 13 true (1),
.cycle 10 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 10 true (2),
.cycle 6 9 true (2)
]),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 0, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 10 4 true (3),
.cycle 2 13 true (1),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 22 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 0, 64],[4, 64, 16, 1, 32, 32, 64],64⟩
]),
.cycle 13 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1037_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part1037) = true := by rfl

def kid10_part1038 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 31 1 false (1),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 39 1 false (3),
.cycle 14 7 true (0),
.cycle 25 3 false (2),
.cycle 17 3 false (1),
.last 16 (1,true),
.last 24 (1,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 18 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 2 16 true (1),
.cycle 11 4 true (2),
.cycle 21 3 false (1)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 7 15 true (2),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 35 1 false (3),
.cycle 2 19 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 60, 64],[4, 64, 16, 1, 4, 4, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 60, 64],[4, 64, 16, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 60, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.last 21 (1,true),
.cycle 7 17 true (2),
.cycle 2 21 true (1),
.cycle 4 21 true (1),
.cycle 38 10 true (8),
.cycle 2 23 true (1),
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (2),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.cycle 9 20 true (2)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 18 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 60, 64],[4, 64, 16, 1, 4, 8, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 60, 64],[4, 64, 16, 1, 16, 8, 64],64⟩,
.cycle 21 9 true (0),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 3 17 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 3 18 true (1),
.cycle 9 9 true (2)
]),
.cycle 8 3 true (4),
.cycle 19 1 false (1),
.split 12 (1,true) (byMove [
.cycle 2 12 true (1),
.cycle 1 14 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 6 10 true (2),
.cycle 6 7 true (2),
.last 17 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 2 14 true (1),
.cycle 6 10 true (2),
.cycle 6 9 true (2)
]),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 13 (4,true) (byMove [
.cycle 0 17 true (0),
.last 14 (1,true),
.cycle 50 1 false (4),
.last 16 (1,true),
.cycle 17 6 false (1),
.cycle 22 1 false (-2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 10 4 true (3),
.last 18 (1,true),
.last 14 (1,true),
.cycle 2 17 true (1),
.cycle 5 9 true (1),
.cycle 18 3 false (0),
.cycle 22 1 false (-2),
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 12 5 true (3),
.cycle 12 2 true (3)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 2 12 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1038_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part1038) = true := by rfl

def kid10_part1039 : Audit := .cycle 0 10 true (0)
theorem kid10_part1039_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part1039) = true := by rfl

def kid10_part1040 : Audit := .cycle 1 9 true (1)
theorem kid10_part1040_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part1040) = true := by rfl

def kid10_part1041 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 8 10 true (4),
.cycle 9 9 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 7 20 true (3),
.cycle 11 7 true (4),
.cycle 8 10 true (4),
.split 29 (5,true) (byMove [
.cycle 7 25 true (3),
.cycle 0 33 true (0),
.cycle 10 29 true (4),
.cycle 0 38 true (0),
.cycle 7 25 true (3),
.cycle 0 33 true (0),
.cycle 2 29 true (1),
.last 30 (1,true),
.cycle 7 23 true (3),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.last 31 (1,true),
.cycle 16 15 true (5),
.cycle 2 31 true (1),
.cycle 12 25 true (4),
.cycle 28 4 true (8),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 48, 64],64⟩,
.cycle 2 29 true (1),
.last 30 (1,true),
.cycle 7 23 true (3),
.cycle 0 31 true (0),
.cycle 8 34 true (4),
.cycle 9 22 true (4)
]),
.split 19 (1,true) (byMove [
.cycle 2 19 true (1),
.cycle 1 21 true (1),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 6 15 true (2),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.cycle 8 12 true (4),
.last 32 (5,true),
.cycle 6 14 true (2),
.cycle 42 7 false (2),
.cycle 16 4 true (6),
.cycle 2 20 true (1),
.cycle 15 6 true (5),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4)
]),
.cycle 7 12 true (3),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (5,true) (byMove [
.cycle 2 19 true (1),
.last 20 (1,true),
.cycle 7 13 true (3),
.cycle 0 21 true (0),
.cycle 32 3 false (0),
.cycle 52 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.cycle 8 12 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 32, 64],64⟩,
.cycle 6 14 true (2),
.last 20 (1,true),
.cycle 16 4 true (6),
.cycle 2 20 true (1),
.cycle 32 3 false (0),
.cycle 20 6 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 2 21 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4)
]),
.cycle 7 12 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 8 10 true (4),
.cycle 9 9 true (4)
])
theorem kid10_part1041_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part1041) = true := by rfl

def kid10_part1042 : Audit := .cycle 3 7 true (1)
theorem kid10_part1042_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part1042) = true := by rfl

def kid10_part1043 : Audit := .cycle 8 2 true (4)
theorem kid10_part1043_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part1043) = true := by rfl

def kid10_part1044 : Audit := .cycle 9 1 true (5)
theorem kid10_part1044_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part1044) = true := by rfl

def kid10_part1045 : Audit := .cycle 6 4 true (2)
theorem kid10_part1045_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part1045) = true := by rfl

def kid10_part1047 : Audit := .cycle 7 6 true (3)
theorem kid10_part1047_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part1047) = true := by rfl

def kid10_part1048 : Audit := .cycle 0 14 true (0)
theorem kid10_part1048_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part1048) = true := by rfl

def kid10_part1049 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.last 23 (5,true),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 20, 2048, 16, 8192, 16384, 8, 256, 131072, 20, 8192, 16384, 8, 256, 131072, 262144, 262144],[256, 20, 16, 1, 4, 262144, 16384, 2048, 16, 1, 4, 262144, 16384, 2048, 16, 1, 4, 262144, 262144],459776⟩,
.cycle 12 7 true (2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 2048, 16, 8192, 16384, 8, 256, 131072, 16, 8192, 16384, 8, 256, 131072, 262144, 262144],[256, 16, 16, 1, 16, 262144, 16384, 2048, 16, 1, 16, 262144, 16384, 2048, 16, 1, 16, 262144, 262144],459776⟩,
.cycle 7 13 true (2),
.cycle 7 13 true (2),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.last 23 (5,true),
.cycle 9 9 true (2)
])
theorem kid10_part1049_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part1049) = true := by rfl

def kid10_part1050 : Audit := .cycle 0 16 true (0)
theorem kid10_part1050_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part1050) = true := by rfl

def kid10_part1051 : Audit := .split 14 (4,true) (byMove [
.cycle 2 18 true (1),
.cycle 0 26 true (0),
.last 22 (5,true),
.cycle 0 30 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 21 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 0 52 true (0),
.last 16 (5,true),
.last 19 (5,true),
.cycle 25 3 false (1),
.last 18 (5,true),
.cycle 0 27 true (0),
.last 20 (5,true),
.last 16 (5,true),
.cycle 15 3 false (1),
.cycle 0 21 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 21 true (1),
.last 16 (5,true),
.cycle 21 3 false (1)
])
theorem kid10_part1051_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part1051) = true := by rfl

def kid10_part1052 : Audit := .split 19 (5,true) (byMove [
.last 27 (4,true),
.cycle 12 8 false (2),
.cycle 41 9 true (3),
.cycle 0 27 true (-2),
.last 20 (4,true),
.cycle 13 8 false (1),
.cycle 19 12 true (1),
.cycle 16 37 true (-2),
.last 35 (4,true),
.last 25 (4,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 327936, 2048, 65552, 128, 256, 32768, 260, 2048, 65552, 2, 4, 8, 65552, 32, 65536, 262144],[256, 2080, 16, 1, 262144, 16, 256, 2080, 65536, 4096, 262144, 65536, 4, 2080, 16, 1, 262144, 16, 262144],287244⟩,
.last 23 (4,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 2048, 65536, 524288, 1048576, 32768, 67109120, 8388608, 65536, 128, 256, 134217728, 268500992, 2048, 17179869184, 33554432, 67108864, 8589934592, 256, 536870912, 68719542272, 33554432, 67108864, 134217728, 69055021056, 536870912, 69524850688, 33554432, 67108864, 134217728, 65536, 536870912, 268435456, 68719476736],[256, 2048, 16, 1, 68719476736, 67584, 1048576, 67584, 65536, 4096, 68719476736, 65536, 256, 2048, 268435456, 16777216, 68719476736, 2048, 67108864, 2048, 17179869184, 1073741824, 68719476736, 17179869184, 67108864, 69524850688, 268435456, 16777216, 68719476736, 69524850688, 67108864, 68719478784, 268435456, 16777216, 68719476736, 69524850688, 68719476736],128847898434⟩,
.cycle 12 8 false (2),
.last 21 (4,true),
.last 32 (4,true),
.last 20 (4,true),
.cycle 13 8 false (1),
.cycle 19 12 true (1),
.cycle 19 31 true (1),
.cycle 0 43 true (-2),
.cycle 17 45 true (-1),
.cycle 21 6 true (3),
.cycle 11 12 false (3)
])
theorem kid10_part1052_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part1052) = true := by rfl

def kid10_part1053 : Audit := .cycle 2 10 true (1)
theorem kid10_part1053_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part1053) = true := by rfl

def kid10_part1054 : Audit := .cycle 1 11 true (1)
theorem kid10_part1054_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part1054) = true := by rfl

def kid10_part1055 : Audit := .cycle 7 4 true (3)
theorem kid10_part1055_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part1055) = true := by rfl

def kid10_part1056 : Audit := .cycle 0 12 true (0)
theorem kid10_part1056_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part1056) = true := by rfl

def kid10_part1057 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 16, 16, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.last 13 (5,true),
.cycle 28 7 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1057_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part1057) = true := by rfl

def kid10_part1058 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 7 9 true (3),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1058_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part1058) = true := by rfl

def kid10_part1059 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 12 6 true (3),
.cycle 29 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 18 true (3),
.cycle 13 7 true (3),
.cycle 8 8 true (3),
.cycle 7 11 true (3),
.cycle 6 12 true (2),
.cycle 7 10 true (3),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 29 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 12 6 true (3),
.cycle 9 7 true (3)
])
theorem kid10_part1059_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part1059) = true := by rfl

def kid10_part1060 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 25 7 false (1),
.cycle 22 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 16 true (3),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.cycle 7 9 true (3),
.cycle 24 7 false (2),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 22 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 16, 16, 1, 16, 64, 64],64⟩,
.cycle 9 5 true (3)
])
theorem kid10_part1060_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part1060) = true := by rfl

def kid10_part1061 : Audit := .cycle 2 12 true (1)
theorem kid10_part1061_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part1061) = true := by rfl

def kid10_part1062 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 20, 16, 1, 4, 64, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 20, 16, 1, 16, 64, 64],64⟩,
.cycle 7 11 true (2),
.cycle 2 18 true (1),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 5 14 true (1),
.cycle 9 7 true (2)
])
theorem kid10_part1062_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part1062) = true := by rfl

def kid10_part1063 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 14 (4,true),
.cycle 7 9 true (3),
.last 16 (4,true),
.last 13 (4,true),
.cycle 18 10 false (0),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 7 9 true (3),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 23 (4,true),
.cycle 2 12 true (1),
.last 14 (4,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part1063_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part1063) = true := by rfl

def kid10_part1064 : Audit := .split 18 (4,true) (byMove [
.last 35 (5,true),
.cycle 0 28 true (-2),
.cycle 31 36 true (0),
.cycle 0 32 true (-2),
.last 22 (5,true),
.cycle 13 6 false (1),
.cycle 0 36 true (-2),
.cycle 24 31 true (0),
.cycle 21 8 true (3),
.cycle 0 24 true (-2),
.cycle 22 8 true (4),
.last 19 (5,true),
.last 21 (5,true),
.last 41 (5,true),
.cycle 0 44 true (-2),
.cycle 27 28 true (0),
.last 20 (5,true),
.cycle 13 6 false (1),
.last 29 (5,true),
.last 20 (5,true),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 2048, 65536, 524288, 1048576, 32768, 67109120, 8388608, 65536, 128, 256, 134217728, 268500992, 2048, 17179869184, 33554432, 67108864, 8589934592, 256, 536870912, 68719476736, 33554432, 67108864, 134217728, 335610112, 536870912, 68987977728, 33554432, 67108864, 134217728, 65536, 536870912, 268435456, 68719476736],[256, 256, 16, 1, 256, 68719476736, 1048576, 68719476736, 65536, 4096, 1048576, 68719476736, 256, 256, 268435456, 16777216, 256, 68719476736, 67108864, 68719476736, 17179869184, 1073741824, 67108864, 68719476736, 67108864, 68786585856, 268435456, 16777216, 67108864, 68719476736, 67108864, 68719476736, 268435456, 16777216, 67108864, 68719476736, 68719476736],128847898434⟩,
.far false 6 ⟨0,[0, 1, 2, 3, 4, 1, 5, 4, 4, 4, 4, 4],[128, 256, 8, 0, 2048, 65536, 524288, 1048576, 32768, 67109120, 8388608, 69632, 128, 256, 134217728, 268500992, 2048, 17179869184, 33554432, 67108864, 8589934592, 256, 536870912, 68719476736, 33554432, 67108864, 134217728, 486609664, 536870912, 69004759040, 33554432, 67108864, 134217728, 65536, 536870912, 268435456, 68719476736],[256, 512, 16, 1, 512, 68719476736, 1048576, 68719476736, 65536, 4096, 2097152, 68719476736, 256, 768, 268435456, 16777216, 512, 68719476736, 67108864, 68719476736, 17179869184, 1073741824, 134217728, 68719476736, 67108864, 68920804096, 268435456, 16777216, 134217728, 68719476736, 67108864, 68719476736, 268435456, 16777216, 134217728, 68719476736, 68719476736],128847898434⟩,
.last 27 (5,true),
.last 19 (5,true)
])
theorem kid10_part1064_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part1064) = true := by rfl

def kid10_part1065 : Audit := .cycle 2 10 true (1)
theorem kid10_part1065_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part1065) = true := by rfl

def kid10_part1066 : Audit := .cycle 1 11 true (1)
theorem kid10_part1066_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part1066) = true := by rfl

def kid10_part1067 : Audit := .cycle 7 4 true (3)
theorem kid10_part1067_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part1067) = true := by rfl

def kid10_part1068 : Audit := .cycle 0 12 true (0)
theorem kid10_part1068_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part1068) = true := by rfl

def kid10_part1069 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.cycle 8 5 true (4),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 22 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1069_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part1069) = true := by rfl

def kid10_part1070 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.cycle 9 4 true (4),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 12 false (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 7 7 true (3),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.last 24 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1070_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part1070) = true := by rfl

def kid10_part1046 : Audit := .split 10 (1,true) (byMove [(kid10_part1047),(kid10_part1048),(kid10_part1049),(kid10_part1050),(kid10_part1051),(kid10_part1052),(kid10_part1053),(kid10_part1054),(kid10_part1055),(kid10_part1056),(kid10_part1057),(kid10_part1058),(kid10_part1059),(kid10_part1060),(kid10_part1061),(kid10_part1062),(kid10_part1063),(kid10_part1064),(kid10_part1065),(kid10_part1066),(kid10_part1067),(kid10_part1068),(kid10_part1069),(kid10_part1070)])

theorem kid10_part1046_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part1046) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part1047),(kid10_part1048),(kid10_part1049),(kid10_part1050),(kid10_part1051),(kid10_part1052),(kid10_part1053),(kid10_part1054),(kid10_part1055),(kid10_part1056),(kid10_part1057),(kid10_part1058),(kid10_part1059),(kid10_part1060),(kid10_part1061),(kid10_part1062),(kid10_part1063),(kid10_part1064),(kid10_part1065),(kid10_part1066),(kid10_part1067),(kid10_part1068),(kid10_part1069),(kid10_part1070)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1047_checked

  · exact kid10_part1053_checked

  · exact kid10_part1059_checked

  · exact kid10_part1065_checked

  · exact kid10_part1048_checked

  · exact kid10_part1054_checked

  · exact kid10_part1060_checked

  · exact kid10_part1066_checked

  · exact kid10_part1049_checked

  · exact kid10_part1055_checked

  · exact kid10_part1061_checked

  · exact kid10_part1067_checked

  · exact kid10_part1050_checked

  · exact kid10_part1056_checked

  · exact kid10_part1062_checked

  · exact kid10_part1068_checked

  · exact kid10_part1051_checked

  · exact kid10_part1057_checked

  · exact kid10_part1063_checked

  · exact kid10_part1069_checked

  · exact kid10_part1052_checked

  · exact kid10_part1058_checked

  · exact kid10_part1064_checked

  · exact kid10_part1070_checked

def kid10_part1071 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 5, 64],[4, 64, 16, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.split 13 (1,true) (byMove [
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 6 12 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.cycle 28 7 false (2),
.cycle 10 4 true (4),
.cycle 2 14 true (1),
.cycle 14 6 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4)
]),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.split 13 (5,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 22 3 false (0),
.cycle 0 30 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 10 4 true (4),
.cycle 2 14 true (1),
.cycle 22 3 false (0),
.cycle 25 10 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4)
]),
.cycle 2 14 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1071_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part1071) = true := by rfl

def kid10_part1072 : Audit := .cycle 2 10 true (1)
theorem kid10_part1072_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part1072) = true := by rfl

def kid10_part1074 : Audit := .cycle 7 6 true (3)
theorem kid10_part1074_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part1074) = true := by rfl

def kid10_part1075 : Audit := .cycle 0 14 true (0)
theorem kid10_part1075_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part1075) = true := by rfl

def kid10_part1076 : Audit := .cycle 2 16 true (1)
theorem kid10_part1076_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part1076) = true := by rfl

def kid10_part1077 : Audit := .cycle 0 16 true (0)
theorem kid10_part1077_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part1077) = true := by rfl

def kid10_part1078 : Audit := .cycle 18 3 false (0)
theorem kid10_part1078_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part1078) = true := by rfl

def kid10_part1079 : Audit := .split 17 (5,true) (byMove [
.cycle 12 13 false (2),
.last 18 (1,true),
.cycle 13 7 false (1),
.cycle 30 29 false (6),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.last 19 (1,true),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 338176, 2048, 8192, 128, 256, 32768, 256, 2048, 73728, 128, 256, 8, 65536, 2048, 8192, 262144],[256, 262144, 16, 1, 256, 2, 256, 262144, 65536, 4096, 256, 8192, 256, 262144, 16, 1, 2304, 2, 262144],278540⟩,
.last 21 (1,true),
.cycle 12 11 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 16, 64],[4, 64, 16, 1, 32, 16, 64],64⟩,
.cycle 29 3 true (5),
.far true 5 ⟨0,[0, 1, 2, 3, 4, 1, 4, 1, 4, 4],[131072, 1024, 2097152, 512, 131072, 1024, 1073741824, 131072, 1073872896, 2097152, 131072, 4194304, 64, 1073741888, 512, 512, 536870912, 1024, 1073741824, 537001984, 1895957568, 512, 537001984, 1024, 1895957568, 1895957568, 2032272448, 134217728, 1895957568, 268435456, 1073741824],[1024, 1073741824, 1024, 1024, 32, 64, 131072, 1073741824, 268436480, 1342309376, 131072, 262144, 1073741888, 1073741824, 1024, 1073741824, 536870912, 64, 537001984, 1073741824, 1024, 1024, 536870912, 64, 1895957568, 1073741824, 1895957568, 1895957568, 536870912, 16777216, 1073741824],2002598208⟩,
.last 18 (1,true),
.cycle 14 5 false (0),
.last 23 (1,true),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.last 19 (1,true),
.cycle 17 31 true (-1),
.last 21 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2833, 2048, 512, 128, 256, 8, 256, 2048, 528, 4096],[256, 4096, 16, 1, 2304, 512, 256, 4096, 16, 1, 256, 512, 4096],4096⟩,
.cycle 21 6 true (3),
.cycle 13 8 false (1)
])
theorem kid10_part1079_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part1079) = true := by rfl

def kid10_part1080 : Audit := .cycle 2 10 true (1)
theorem kid10_part1080_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part1080) = true := by rfl

def kid10_part1081 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 19 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 22, 2048, 4096, 128, 256, 8, 256, 2048, 4, 4096],[256, 4, 16, 1, 2, 4096, 256, 4, 16, 1, 2, 4096, 4096],4128⟩,
.cycle 10 9 true (2),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 6 8 true (2),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 1 17 true (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1081_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part1081) = true := by rfl

def kid10_part1082 : Audit := .cycle 7 4 true (3)
theorem kid10_part1082_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part1082) = true := by rfl

def kid10_part1083 : Audit := .cycle 0 12 true (0)
theorem kid10_part1083_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part1083) = true := by rfl

def kid10_part1084 : Audit := .cycle 8 4 true (4)
theorem kid10_part1084_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part1084) = true := by rfl

def kid10_part1085 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 26 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 4, 64],[4, 64, 16, 1, 32, 4, 64],64⟩,
.cycle 10 9 true (2),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 2 21 true (1),
.cycle 10 4 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1085_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part1085) = true := by rfl

def kid10_part1086 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.last 23 (5,true),
.last 15 (5,true),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 8 8 true (3),
.last 13 (5,true),
.cycle 6 12 true (2),
.cycle 20 7 false (2),
.cycle 10 4 true (3),
.cycle 5 8 true (1),
.cycle 10 6 true (2),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 6 8 true (2),
.last 13 (5,true)
])
theorem kid10_part1086_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part1086) = true := by rfl

def kid10_part1087 : Audit := .cycle 7 8 true (3)
theorem kid10_part1087_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part1087) = true := by rfl

def kid10_part1088 : Audit := .cycle 2 12 true (1)
theorem kid10_part1088_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part1088) = true := by rfl

def kid10_part1089 : Audit := .cycle 4 12 true (1)
theorem kid10_part1089_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part1089) = true := by rfl

def kid10_part1090 : Audit := .split 12 (5,true) (byMove [
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 7 9 true (3),
.last 15 (1,true),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 8 8 true (3),
.cycle 13 3 true (5),
.cycle 6 12 true (2),
.last 13 (1,true),
.cycle 10 4 true (3),
.cycle 5 8 true (1),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 2 12 true (1),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 20 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 32, 32, 64],[4, 64, 16, 1, 32, 32, 64],64⟩
])
theorem kid10_part1090_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part1090) = true := by rfl

def kid10_part1091 : Audit := .split 17 (5,true) (byMove [
.cycle 34 24 true (0),
.last 18 (1,true),
.cycle 28 13 true (2),
.last 20 (1,true),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.cycle 10 10 false (4),
.last 18 (1,true),
.cycle 34 12 true (2),
.cycle 30 20 true (0),
.cycle 12 6 false (2),
.cycle 23 3 true (5),
.cycle 12 8 false (2),
.last 18 (1,true),
.cycle 14 5 false (0),
.cycle 12 9 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.cycle 17 6 true (-1),
.last 18 (1,true),
.cycle 12 12 false (2),
.cycle 10 20 false (4),
.cycle 17 2 true (-1),
.cycle 21 5 true (3)
])
theorem kid10_part1091_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part1091) = true := by rfl

def kid10_part1092 : Audit := .cycle 2 10 true (1)
theorem kid10_part1092_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part1092) = true := by rfl

def kid10_part1093 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 19 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1093_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part1093) = true := by rfl

def kid10_part1094 : Audit := .cycle 7 4 true (3)
theorem kid10_part1094_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part1094) = true := by rfl

def kid10_part1095 : Audit := .cycle 0 12 true (0)
theorem kid10_part1095_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part1095) = true := by rfl

def kid10_part1096 : Audit := .cycle 8 4 true (4)
theorem kid10_part1096_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part1096) = true := by rfl

def kid10_part1097 : Audit := .split 11 (5,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 9 4 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 9 5 true (4),
.cycle 2 12 true (1),
.cycle 10 2 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1097_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part1097) = true := by rfl

def kid10_part1073 : Audit := .split 10 (4,true) (byMove [(kid10_part1074),(kid10_part1075),(kid10_part1076),(kid10_part1077),(kid10_part1078),(kid10_part1079),(kid10_part1080),(kid10_part1081),(kid10_part1082),(kid10_part1083),(kid10_part1084),(kid10_part1085),(kid10_part1086),(kid10_part1087),(kid10_part1088),(kid10_part1089),(kid10_part1090),(kid10_part1091),(kid10_part1092),(kid10_part1093),(kid10_part1094),(kid10_part1095),(kid10_part1096),(kid10_part1097)])

theorem kid10_part1073_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part1073) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part1074),(kid10_part1075),(kid10_part1076),(kid10_part1077),(kid10_part1078),(kid10_part1079),(kid10_part1080),(kid10_part1081),(kid10_part1082),(kid10_part1083),(kid10_part1084),(kid10_part1085),(kid10_part1086),(kid10_part1087),(kid10_part1088),(kid10_part1089),(kid10_part1090),(kid10_part1091),(kid10_part1092),(kid10_part1093),(kid10_part1094),(kid10_part1095),(kid10_part1096),(kid10_part1097)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1074_checked

  · exact kid10_part1080_checked

  · exact kid10_part1086_checked

  · exact kid10_part1092_checked

  · exact kid10_part1075_checked

  · exact kid10_part1081_checked

  · exact kid10_part1087_checked

  · exact kid10_part1093_checked

  · exact kid10_part1076_checked

  · exact kid10_part1082_checked

  · exact kid10_part1088_checked

  · exact kid10_part1094_checked

  · exact kid10_part1077_checked

  · exact kid10_part1083_checked

  · exact kid10_part1089_checked

  · exact kid10_part1095_checked

  · exact kid10_part1078_checked

  · exact kid10_part1084_checked

  · exact kid10_part1090_checked

  · exact kid10_part1096_checked

  · exact kid10_part1079_checked

  · exact kid10_part1085_checked

  · exact kid10_part1091_checked

  · exact kid10_part1097_checked

def kid10_part1099 : Audit := .cycle 7 6 true (3)
theorem kid10_part1099_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part1099) = true := by rfl

def kid10_part1100 : Audit := .cycle 0 14 true (0)
theorem kid10_part1100_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part1100) = true := by rfl

def kid10_part1101 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 58 1 false (6),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 4, 52, 64],64⟩,
.cycle 12 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 52, 64],[4, 64, 16, 1, 16, 52, 64],64⟩,
.cycle 62 1 false (4),
.last 19 (1,true),
.cycle 7 12 true (2),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 7 13 true (2),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 19 true (1),
.cycle 37 19 true (7),
.cycle 9 9 true (2)
])
theorem kid10_part1101_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part1101) = true := by rfl

def kid10_part1102 : Audit := .cycle 0 16 true (0)
theorem kid10_part1102_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part1102) = true := by rfl

def kid10_part1103 : Audit := .split 14 (4,true) (byMove [
.cycle 2 18 true (1),
.cycle 0 26 true (0),
.cycle 47 1 false (3),
.cycle 0 30 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.last 16 (1,true),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 0 52 true (0),
.cycle 52 3 false (7),
.cycle 17 3 false (1),
.last 16 (1,true),
.last 34 (1,true),
.last 18 (1,true),
.cycle 40 1 false (2),
.cycle 18 3 false (0),
.cycle 15 3 false (1),
.last 16 (1,true),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 2 21 true (1),
.cycle 16 7 true (3),
.cycle 21 3 false (1)
])
theorem kid10_part1103_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part1103) = true := by rfl

def kid10_part1104 : Audit := .cycle 15 1 false (-1)
theorem kid10_part1104_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part1104) = true := by rfl

def kid10_part1105 : Audit := .cycle 2 10 true (1)
theorem kid10_part1105_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part1105) = true := by rfl

def kid10_part1106 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 4 true (4),
.cycle 1 20 true (1),
.cycle 6 8 true (2),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1106_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part1106) = true := by rfl

def kid10_part1107 : Audit := .cycle 7 4 true (3)
theorem kid10_part1107_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part1107) = true := by rfl

def kid10_part1108 : Audit := .cycle 0 12 true (0)
theorem kid10_part1108_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part1108) = true := by rfl

def kid10_part1109 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 16, 64],64⟩,
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 44 1 false (10),
.last 13 (1,true),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.cycle 8 6 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1109_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part1109) = true := by rfl

def kid10_part1110 : Audit := .cycle 36 1 false (8)
theorem kid10_part1110_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part1110) = true := by rfl

def kid10_part1111 : Audit := .split 12 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 6 18 true (1),
.cycle 6 10 true (2),
.cycle 0 17 true (0),
.last 13 (4,true),
.cycle 6 12 true (2),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 2 12 true (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 6 8 true (2)
])
theorem kid10_part1111_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part1111) = true := by rfl

def kid10_part1112 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 17 (1,true),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 16 true (3),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.last 18 (1,true),
.last 15 (1,true),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (1,true),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 2 15 true (1),
.last 17 (1,true),
.cycle 9 5 true (3)
])
theorem kid10_part1112_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part1112) = true := by rfl

def kid10_part1113 : Audit := .cycle 2 12 true (1)
theorem kid10_part1113_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part1113) = true := by rfl

def kid10_part1114 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 20, 64],64⟩,
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 16, 64],[4, 64, 16, 1, 16, 20, 64],64⟩,
.cycle 51 1 false (3),
.last 17 (1,true),
.cycle 7 10 true (2),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 2 18 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 2 17 true (1),
.cycle 5 14 true (1),
.cycle 9 7 true (2)
])
theorem kid10_part1114_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part1114) = true := by rfl

def kid10_part1115 : Audit := .split 13 (4,true) (byMove [
.cycle 2 16 true (1),
.last 14 (1,true),
.cycle 57 1 false (5),
.last 16 (1,true),
.cycle 17 6 false (1),
.cycle 22 1 false (-2),
.cycle 6 8 true (2),
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 32, 20, 64],[4, 64, 16, 1, 4, 16, 64],64⟩,
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 10 4 true (3),
.last 18 (1,true),
.last 14 (1,true),
.cycle 5 12 true (1),
.cycle 4 14 true (1),
.cycle 18 3 false (0),
.cycle 22 1 false (-2),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 12 6 true (3),
.cycle 12 2 true (3)
])
theorem kid10_part1115_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part1115) = true := by rfl

def kid10_part1116 : Audit := .cycle 15 1 false (-1)
theorem kid10_part1116_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part1116) = true := by rfl

def kid10_part1117 : Audit := .cycle 2 10 true (1)
theorem kid10_part1117_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part1117) = true := by rfl

def kid10_part1118 : Audit := .split 11 (1,true) (byMove [
.cycle 2 11 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 1 16 true (1),
.cycle 6 6 true (2),
.last 15 (4,true),
.last 13 (4,true),
.cycle 2 12 true (1),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1118_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part1118) = true := by rfl

def kid10_part1119 : Audit := .cycle 7 4 true (3)
theorem kid10_part1119_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part1119) = true := by rfl

def kid10_part1120 : Audit := .cycle 0 12 true (0)
theorem kid10_part1120_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part1120) = true := by rfl

def kid10_part1121 : Audit := .split 11 (4,true) (byMove [
.cycle 2 11 true (1),
.last 12 (1,true),
.cycle 7 5 true (3),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.cycle 8 5 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 22 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 8 9 true (4),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 0 16 true (0),
.cycle 2 12 true (1),
.cycle 22 5 false (2),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 13 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1121_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part1121) = true := by rfl

def kid10_part1122 : Audit := .cycle 9 3 true (4)
theorem kid10_part1122_checked : zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part1122) = true := by rfl

def kid10_part1098 : Audit := .split 10 (5,true) (byMove [(kid10_part1099),(kid10_part1100),(kid10_part1101),(kid10_part1102),(kid10_part1103),(kid10_part1104),(kid10_part1105),(kid10_part1106),(kid10_part1107),(kid10_part1108),(kid10_part1109),(kid10_part1110),(kid10_part1111),(kid10_part1112),(kid10_part1113),(kid10_part1114),(kid10_part1115),(kid10_part1116),(kid10_part1117),(kid10_part1118),(kid10_part1119),(kid10_part1120),(kid10_part1121),(kid10_part1122)])

theorem kid10_part1098_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part1098) = true := by

  change (zipQueryOK 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1882 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part1099),(kid10_part1100),(kid10_part1101),(kid10_part1102),(kid10_part1103),(kid10_part1104),(kid10_part1105),(kid10_part1106),(kid10_part1107),(kid10_part1108),(kid10_part1109),(kid10_part1110),(kid10_part1111),(kid10_part1112),(kid10_part1113),(kid10_part1114),(kid10_part1115),(kid10_part1116),(kid10_part1117),(kid10_part1118),(kid10_part1119),(kid10_part1120),(kid10_part1121),(kid10_part1122)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1099_checked

  · exact kid10_part1105_checked

  · exact kid10_part1111_checked

  · exact kid10_part1117_checked

  · exact kid10_part1100_checked

  · exact kid10_part1106_checked

  · exact kid10_part1112_checked

  · exact kid10_part1118_checked

  · exact kid10_part1101_checked

  · exact kid10_part1107_checked

  · exact kid10_part1113_checked

  · exact kid10_part1119_checked

  · exact kid10_part1102_checked

  · exact kid10_part1108_checked

  · exact kid10_part1114_checked

  · exact kid10_part1120_checked

  · exact kid10_part1103_checked

  · exact kid10_part1109_checked

  · exact kid10_part1115_checked

  · exact kid10_part1121_checked

  · exact kid10_part1104_checked

  · exact kid10_part1110_checked

  · exact kid10_part1116_checked

  · exact kid10_part1122_checked

def kid10_part1123 : Audit := .cycle 0 10 true (0)
theorem kid10_part1123_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part1123) = true := by rfl

def kid10_part1124 : Audit := .cycle 1 9 true (1)
theorem kid10_part1124_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part1124) = true := by rfl

def kid10_part1125 : Audit := .cycle 2 8 true (1)
theorem kid10_part1125_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part1125) = true := by rfl

def kid10_part1126 : Audit := .cycle 2 11 true (1)
theorem kid10_part1126_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part1126) = true := by rfl

def kid10_part1127 : Audit := .cycle 8 2 true (4)
theorem kid10_part1127_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part1127) = true := by rfl

def kid10_part1128 : Audit := .cycle 9 1 true (5)
theorem kid10_part1128_checked : zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part1128) = true := by rfl

def kid10_part1032 : Audit := .split 9 (5,false) (byMove [(kid10_part1033),(kid10_part1034),(kid10_part1035),(kid10_part1036),(kid10_part1037),(kid10_part1038),(kid10_part1039),(kid10_part1040),(kid10_part1041),(kid10_part1042),(kid10_part1043),(kid10_part1044),(kid10_part1045),(kid10_part1046),(kid10_part1071),(kid10_part1072),(kid10_part1073),(kid10_part1098),(kid10_part1123),(kid10_part1124),(kid10_part1125),(kid10_part1126),(kid10_part1127),(kid10_part1128)])

theorem kid10_part1032_checked : zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid10_part1032) = true := by

  change (zipQueryOK 1882 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 1882 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part1033),(kid10_part1034),(kid10_part1035),(kid10_part1036),(kid10_part1037),(kid10_part1038),(kid10_part1039),(kid10_part1040),(kid10_part1041),(kid10_part1042),(kid10_part1043),(kid10_part1044),(kid10_part1045),(kid10_part1046),(kid10_part1071),(kid10_part1072),(kid10_part1073),(kid10_part1098),(kid10_part1123),(kid10_part1124),(kid10_part1125),(kid10_part1126),(kid10_part1127),(kid10_part1128)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1033_checked

  · exact kid10_part1039_checked

  · exact kid10_part1045_checked

  · exact kid10_part1123_checked

  · exact kid10_part1034_checked

  · exact kid10_part1040_checked

  · exact kid10_part1046_checked

  · exact kid10_part1124_checked

  · exact kid10_part1035_checked

  · exact kid10_part1041_checked

  · exact kid10_part1071_checked

  · exact kid10_part1125_checked

  · exact kid10_part1036_checked

  · exact kid10_part1042_checked

  · exact kid10_part1072_checked

  · exact kid10_part1126_checked

  · exact kid10_part1037_checked

  · exact kid10_part1043_checked

  · exact kid10_part1073_checked

  · exact kid10_part1127_checked

  · exact kid10_part1038_checked

  · exact kid10_part1044_checked

  · exact kid10_part1098_checked

  · exact kid10_part1128_checked

def kid10 : Audit := .split 8 (4,false) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part54),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part322),(kid10_part371),(kid10_part372),(kid10_part469),(kid10_part566),(kid10_part567),(kid10_part568),(kid10_part569),(kid10_part690),(kid10_part1027),(kid10_part1028),(kid10_part1029),(kid10_part1030),(kid10_part1031),(kid10_part1032)])

theorem check10 : zipCheck 1882 (child ⟨false,true,4⟩) (kid10) = true := by

  change (zipQueryOK 1882 (child ⟨false,true,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 1882 (refine (child ⟨false,true,4⟩) (4,false) (some mv)) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part54),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part322),(kid10_part371),(kid10_part372),(kid10_part469),(kid10_part566),(kid10_part567),(kid10_part568),(kid10_part569),(kid10_part690),(kid10_part1027),(kid10_part1028),(kid10_part1029),(kid10_part1030),(kid10_part1031),(kid10_part1032)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1_checked

  · exact kid10_part199_checked

  · exact kid10_part469_checked

  · exact kid10_part1027_checked

  · exact kid10_part2_checked

  · exact kid10_part200_checked

  · exact kid10_part566_checked

  · exact kid10_part1028_checked

  · exact kid10_part3_checked

  · exact kid10_part201_checked

  · exact kid10_part567_checked

  · exact kid10_part1029_checked

  · exact kid10_part4_checked

  · exact kid10_part322_checked

  · exact kid10_part568_checked

  · exact kid10_part1030_checked

  · exact kid10_part5_checked

  · exact kid10_part371_checked

  · exact kid10_part569_checked

  · exact kid10_part1031_checked

  · exact kid10_part54_checked

  · exact kid10_part372_checked

  · exact kid10_part690_checked

  · exact kid10_part1032_checked

end BB6.Agent11Raw39B1RC
