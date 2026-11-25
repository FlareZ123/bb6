import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid10_part1 : Audit := .cycle 0 9 true (0)
theorem kid10_part1_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid10_part1) = true := by rfl

def kid10_part2 : Audit := .cycle 1 8 true (1)
theorem kid10_part2_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid10_part2) = true := by rfl

def kid10_part3 : Audit := .cycle 2 7 true (1)
theorem kid10_part3_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid10_part3) = true := by rfl

def kid10_part4 : Audit := .cycle 1 11 true (1)
theorem kid10_part4_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid10_part4) = true := by rfl

def kid10_part6 : Audit := .cycle 0 11 true (0)
theorem kid10_part6_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part6) = true := by rfl

def kid10_part7 : Audit := .cycle 1 10 true (1)
theorem kid10_part7_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part7) = true := by rfl

def kid10_part8 : Audit := .cycle 21 1 false (1)
theorem kid10_part8_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part8) = true := by rfl

def kid10_part9 : Audit := .cycle 1 13 true (0)
theorem kid10_part9_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part9) = true := by rfl

def kid10_part10 : Audit := .cycle 13 1 false (-1)
theorem kid10_part10_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part10) = true := by rfl

def kid10_part11 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 1 false (1),
.split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
]),
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
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 1 false (0),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 9 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.cycle 13 6 false (2),
.split 16 (2,true) (byMove [
.cycle 1 17 false (4),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 0 17 true (-1),
.cycle 13 13 true (-1),
.cycle 10 14 true (-1),
.cycle 13 11 false (2),
.cycle 13 6 false (1),
.cycle 14 3 true (-1),
.cycle 13 8 false (1),
.cycle 12 5 false (1),
.cycle 1 20 true (-2),
.cycle 1 18 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 10 23 false (5),
.cycle 10 19 false (4),
.cycle 2 15 false (4),
.cycle 1 19 true (-1),
.last 19 (5,true),
.cycle 10 9 false (2)
]),
.split 12 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 14 1 false (2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 17 true (-1),
.last 13 (5,true),
.cycle 10 5 false (2),
.cycle 0 28 true (-2),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 0 20 true (-2),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
]),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 14 1 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 13 true (0),
.cycle 17 1 false (-1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.cycle 11 3 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
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
.cycle 18 3 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 22 3 false (2),
.cycle 1 17 true (0),
.cycle 15 3 false (1),
.cycle 11 4 true (0)
]),
.cycle 11 1 true (1)
])
theorem kid10_part11_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part11) = true := by rfl

def kid10_part12 : Audit := .cycle 0 11 true (0)
theorem kid10_part12_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part12) = true := by rfl

def kid10_part13 : Audit := .cycle 1 10 true (1)
theorem kid10_part13_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part13) = true := by rfl

def kid10_part14 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (3),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 32 1 false (4),
.cycle 1 24 true (0),
.cycle 25 1 false (3),
.last 23 (5,true),
.cycle 0 22 true (0),
.last 47 (5,true),
.cycle 11 11 true (0),
.cycle 10 18 true (0),
.cycle 27 1 false (3),
.cycle 21 1 true (3),
.cycle 10 24 true (0),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 30 1 false (4),
.cycle 0 26 true (0),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 0 45 true (0),
.cycle 1 24 true (0),
.cycle 9 13 true (0),
.cycle 21 1 true (3)
]),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 30, 64, 64],[2, 16, 2, 1, 4, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 30, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 12 9 true (0),
.cycle 27 1 false (3),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.last 44 (5,true),
.cycle 11 11 true (0),
.cycle 10 18 true (0),
.cycle 27 1 false (3),
.last 25 (5,true),
.cycle 0 22 true (0),
.last 46 (5,true),
.last 34 (5,true),
.last 32 (5,true),
.cycle 29 1 false (3),
.cycle 21 1 true (5),
.last 38 (5,true),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 13 9 true (0),
.cycle 27 1 false (3),
.last 25 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 44 (5,true),
.cycle 1 24 true (0),
.last 36 (5,true),
.cycle 21 1 true (5)
]),
.cycle 7 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 30, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.cycle 25 1 false (3),
.split 21 (5,false) (byMove [
.last 25 (5,true),
.cycle 0 25 true (0),
.cycle 10 18 true (0),
.last 27 (5,true),
.cycle 25 1 false (3),
.last 23 (5,true),
.cycle 1 22 true (0),
.cycle 29 1 false (3),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 28, 16, 128, 256, 8, 128, 8, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.last 22 (5,true),
.cycle 10 14 true (0),
.last 24 (5,true),
.cycle 1 24 true (0),
.cycle 10 16 true (0),
.cycle 1 26 true (0),
.last 23 (5,true),
.cycle 1 22 true (0),
.cycle 7 15 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 10 20 true (0),
.last 22 (5,true)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 42 true (0),
.cycle 1 23 true (0),
.cycle 10 32 true (0),
.split 21 (5,false) (byMove [
.cycle 1 22 true (0),
.cycle 29 1 false (3),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.last 34 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.last 43 (5,true),
.cycle 10 19 true (0),
.last 42 (5,true),
.last 36 (5,true),
.cycle 21 1 true (5),
.last 38 (5,true),
.last 36 (5,true),
.last 23 (5,true),
.cycle 1 23 true (0),
.cycle 19 3 true (3),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 24 true (0),
.cycle 10 21 true (0),
.cycle 21 1 true (5)
])
])
theorem kid10_part14_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part14) = true := by rfl

def kid10_part15 : Audit := .cycle 10 7 true (0)
theorem kid10_part15_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part15) = true := by rfl

def kid10_part16 : Audit := .cycle 15 1 false (1)
theorem kid10_part16_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part16) = true := by rfl

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
.cycle 20 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 1 false (2),
.cycle 1 17 true (0),
.cycle 17 1 false (1),
.cycle 13 2 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 10 29 true (0),
.cycle 0 34 true (0),
.cycle 28 1 false (4),
.cycle 0 26 true (0),
.cycle 1 23 true (0),
.cycle 32 1 false (4),
.last 23 (2,true),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 62, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 62, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 10 15 true (0),
.last 24 (2,true),
.cycle 1 25 true (0),
.cycle 10 25 true (0),
.cycle 1 29 true (0),
.last 24 (2,true),
.cycle 1 23 true (0),
.cycle 10 31 true (0),
.last 23 (2,true),
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
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 62, 8, 64],[2, 16, 64, 1, 32, 2, 64],64⟩,
.last 32 (2,true),
.cycle 12 9 true (0),
.cycle 27 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 62, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 15 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 42 (2,true),
.cycle 1 23 true (0),
.cycle 10 32 true (0),
.cycle 3 42 true (0)
]),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
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
.cycle 10 5 true (2),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.cycle 10 6 true (2)
]),
.cycle 0 14 true (0),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 10 23 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.cycle 28 1 false (6),
.last 15 (2,true),
.cycle 21 1 false (3),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 10 11 true (-1),
.last 16 (2,true),
.cycle 10 9 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 10 7 true (0),
.cycle 1 17 true (0),
.last 15 (2,true),
.cycle 5 10 true (0),
.cycle 9 14 true (0),
.cycle 16 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid10_part17_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part17) = true := by rfl

def kid10_part18 : Audit := .cycle 17 5 false (2)
theorem kid10_part18_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part18) = true := by rfl

def kid10_part19 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 15 3 false (1),
.split 13 (5,true) (byMove [
.cycle 1 14 true (0),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.last 14 (5,false),
.cycle 15 8 false (2),
.cycle 16 3 false (1),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 5 false (1),
.last 14 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 17 5 false (2),
.split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 5 false (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.cycle 10 10 true (1),
.cycle 19 7 false (3),
.cycle 13 1 true (3),
.cycle 10 10 true (1),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 5 false (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (1),
.cycle 13 1 true (3)
]),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.cycle 15 3 false (1),
.split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.last 15 (5,false),
.cycle 10 6 true (0),
.cycle 16 3 false (1),
.last 15 (5,false),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 10 6 true (1),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 6 true (1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.cycle 10 6 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (1),
.cycle 3 11 true (1),
.cycle 10 8 true (1),
.cycle 13 1 true (3),
.cycle 10 10 true (1),
.cycle 10 5 true (1),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 19 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 10 7 true (1),
.cycle 13 1 true (3)
])
])
theorem kid10_part19_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part19) = true := by rfl

def kid10_part20 : Audit := .cycle 0 13 true (0)
theorem kid10_part20_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part20) = true := by rfl

def kid10_part21 : Audit := .cycle 18 1 false (0)
theorem kid10_part21_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part21) = true := by rfl

def kid10_part22 : Audit := .cycle 13 1 false (-1)
theorem kid10_part22_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part22) = true := by rfl

def kid10_part24 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 14 true (1),
.cycle 10 12 true (0),
.cycle 3 12 true (0),
.last 18 (5,true),
.cycle 0 16 true (0),
.last 20 (5,true),
.cycle 10 6 true (0),
.cycle 13 13 false (3),
.cycle 1 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 17 (5,true),
.cycle 1 16 true (0)
])
theorem kid10_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part24) = true := by rfl

def kid10_part25 : Audit := .cycle 13 1 false (1)
theorem kid10_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part25) = true := by rfl

def kid10_part26 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 20 1 false (0),
.cycle 10 22 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (5,true),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part26) = true := by rfl

def kid10_part27 : Audit := .cycle 19 1 false (-1)
theorem kid10_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part27) = true := by rfl

def kid10_part28 : Audit := .cycle 14 1 false (-2)
theorem kid10_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part28) = true := by rfl

def kid10_part29 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part29) = true := by rfl

def kid10_part30 : Audit := .cycle 1 12 true (1)
theorem kid10_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part30) = true := by rfl

def kid10_part31 : Audit := .cycle 19 1 false (1)
theorem kid10_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part31) = true := by rfl

def kid10_part32 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 10 11 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 20, 28, 4, 8192, 16384, 8, 128, 8, 4, 33554432, 67108864, 2097152, 128, 1073741824, 1048576, 33554432, 67108864, 2097152, 20, 1073741824, 1048576, 33554432, 67108864, 134217728, 1442840576, 1579155484, 67108864, 1073741824],[128, 16, 4, 1, 4, 1073741824, 8192, 16, 4, 1, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1048576, 1073741824, 33554432, 268435456, 67108864, 16777216, 1140850688, 1073741824, 1073741824],2135765056⟩,
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.last 26 (5,true),
.last 18 (5,true),
.cycle 10 6 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (1),
.cycle 10 11 true (1)
])
theorem kid10_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part32) = true := by rfl

def kid10_part33 : Audit := .cycle 0 13 true (0)
theorem kid10_part33_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part33) = true := by rfl

def kid10_part34 : Audit := .cycle 10 2 true (1)
theorem kid10_part34_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part34) = true := by rfl

def kid10_part35 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 13 1 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 13 1 true (3),
.cycle 10 11 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (1),
.cycle 13 1 true (3)
])
theorem kid10_part35_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part35) = true := by rfl

def kid10_part36 : Audit := .cycle 10 4 true (0)
theorem kid10_part36_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part36) = true := by rfl

def kid10_part37 : Audit := .split 16 (2,true) (byMove [
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 4398046576640, 1048576, 524288, 1048576, 32768, 128, 8589934592, 274877906944, 33554432, 67108864, 8, 65536, 65536, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 524288, 1048576, 32768, 128, 8589934592, 274877906944, 33554432, 67108864, 8, 65536, 4398046511104, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 4398046511104],[128, 16, 1048576, 1, 274877906944, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 274877906944, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 274877906944, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],5514742202384⟩,
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 10 10 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 6 11 false (4),
.last 27 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048596, 3145756, 1048580, 8192, 16384, 8, 128, 2097160, 1048580, 33554432, 67108864, 2097152, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 1048596, 1073741824, 67108864, 33554432, 67108864, 134217728, 1443889156, 1580204060, 1141899268, 1073741824],[128, 16, 4, 1, 1048580, 1073741824, 8192, 16, 4, 1, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 68157444, 1073741824, 33554432, 268435456, 67108864, 16777216, 1141899268, 1073741824, 1073741824],2144153664⟩,
.cycle 1 18 true (-1),
.cycle 10 7 false (2),
.last 17 (5,true),
.cycle 10 9 false (2),
.cycle 12 5 false (1),
.cycle 10 12 true (-2),
.cycle 10 10 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.last 22 (5,true),
.cycle 10 11 false (2),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 4398046576640, 1048576, 524288, 1048576, 32768, 128, 8589934592, 274877906944, 33554432, 67108864, 8, 65536, 65536, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 524288, 1048576, 32768, 128, 8589934592, 274877906944, 33554432, 67108864, 8, 65536, 4398046511104, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 4398046511104],[128, 16, 256, 1, 274877906944, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 67108864, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 67108864, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],5514742202384⟩,
.cycle 1 18 true (-1),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid10_part37_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part37) = true := by rfl

def kid10_part38 : Audit := .split 12 (2,true) (byMove [
.cycle 14 19 true (0),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 1 21 true (-1),
.cycle 1 18 true (0),
.cycle 16 1 false (4),
.cycle 1 14 true (0),
.cycle 1 25 true (-1),
.last 13 (5,true),
.cycle 10 5 false (2),
.cycle 10 12 true (-2),
.cycle 1 23 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.last 18 (5,true),
.cycle 10 4 true (0),
.cycle 2 13 true (0),
.cycle 1 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part38_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part38) = true := by rfl

def kid10_part39 : Audit := .cycle 19 1 false (-1)
theorem kid10_part39_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part39) = true := by rfl

def kid10_part40 : Audit := .cycle 14 1 false (-2)
theorem kid10_part40_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part40) = true := by rfl

def kid10_part41 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 15 1 false (1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 1 19 true (0),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 12 2 true (0),
.cycle 13 3 true (1)
])
theorem kid10_part41_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part41) = true := by rfl

def kid10_part42 : Audit := .cycle 1 12 true (1)
theorem kid10_part42_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part42) = true := by rfl

def kid10_part43 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 19 (2,true),
.cycle 1 17 true (0),
.cycle 18 1 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 17 5 false (2),
.cycle 1 18 true (0),
.cycle 10 9 false (3),
.last 18 (2,true),
.cycle 1 19 true (-1),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 9 false (3),
.cycle 1 17 true (0),
.cycle 17 5 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 15 2 true (0),
.cycle 1 18 true (0)
])
theorem kid10_part43_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part43) = true := by rfl

def kid10_part44 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.last 16 (5,true),
.cycle 2 12 true (1),
.last 18 (5,true),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 2 12 true (1)
])
theorem kid10_part44_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part44) = true := by rfl

def kid10_part45 : Audit := .cycle 0 13 true (0)
theorem kid10_part45_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part45) = true := by rfl

def kid10_part46 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 14 6 false (0),
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (1),
.cycle 9 7 true (1),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 14 3 false (0),
.cycle 1 14 true (1),
.cycle 17 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.cycle 12 5 true (1)
])
theorem kid10_part46_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part46) = true := by rfl

def kid10_part47 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 1 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 17 5 false (2),
.cycle 13 1 true (3),
.cycle 10 11 false (3),
.cycle 10 4 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 14 2 true (1),
.cycle 13 1 true (3)
])
theorem kid10_part47_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part47) = true := by rfl

def kid10_part23 : Audit := .split 11 (5,false) (byMove [(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44),(kid10_part45),(kid10_part46),(kid10_part47)])

theorem kid10_part23_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part23) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44),(kid10_part45),(kid10_part46),(kid10_part47)] mv))) = true

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
theorem kid10_part48_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part48) = true := by rfl

def kid10_part49 : Audit := .cycle 1 10 true (1)
theorem kid10_part49_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part49) = true := by rfl

def kid10_part50 : Audit := .cycle 2 9 true (1)
theorem kid10_part50_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part50) = true := by rfl

def kid10_part51 : Audit := .cycle 1 13 true (1)
theorem kid10_part51_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part51) = true := by rfl

def kid10_part52 : Audit := .cycle 9 2 true (2)
theorem kid10_part52_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part52) = true := by rfl

def kid10_part53 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 19 1 false (1),
.split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 10 11 true (0),
.cycle 21 7 false (2),
.cycle 10 6 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2)
]),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 20 true (0),
.cycle 10 9 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
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
.cycle 10 3 true (2),
.split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.cycle 13 10 true (-2),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 24 (5,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true),
.cycle 10 5 true (1),
.last 17 (5,true),
.cycle 1 15 true (1),
.cycle 10 7 true (0),
.cycle 17 1 false (-1),
.last 21 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.last 13 (5,true)
]),
.cycle 1 13 true (1),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (2),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 11 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 6 8 true (2),
.cycle 10 5 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (2),
.cycle 20 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (2),
.cycle 11 3 true (2)
]),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 9 true (0),
.last 17 (2,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 23 1 false (5),
.cycle 10 5 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 7 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (2),
.cycle 11 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
theorem kid10_part53_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part53) = true := by rfl

def kid10_part5 : Audit := .split 10 (4,true) (byMove [(kid10_part6),(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part48),(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53)])

theorem kid10_part5_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid10_part5) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part6),(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part48),(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53)] mv))) = true

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

def kid10_part55 : Audit := .cycle 1 10 true (1)
theorem kid10_part55_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part55) = true := by rfl

def kid10_part56 : Audit := .cycle 1 12 true (1)
theorem kid10_part56_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part56) = true := by rfl

def kid10_part58 : Audit := .cycle 0 11 true (0)
theorem kid10_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part58) = true := by rfl

def kid10_part59 : Audit := .cycle 1 10 true (1)
theorem kid10_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part59) = true := by rfl

def kid10_part60 : Audit := .cycle 21 1 false (1)
theorem kid10_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part60) = true := by rfl

def kid10_part61 : Audit := .cycle 1 13 true (0)
theorem kid10_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part61) = true := by rfl

def kid10_part62 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
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
.cycle 21 1 false (-3),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 25 1 false (-1),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 18 1 false (-2)
])
theorem kid10_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part62) = true := by rfl

def kid10_part63 : Audit := .cycle 15 1 false (-1)
theorem kid10_part63_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part63) = true := by rfl

def kid10_part64 : Audit := .cycle 0 11 true (0)
theorem kid10_part64_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part64) = true := by rfl

def kid10_part65 : Audit := .cycle 1 10 true (1)
theorem kid10_part65_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part65) = true := by rfl

def kid10_part66 : Audit := .split 19 (4,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 1 35 true (0),
.last 21 (5,true),
.cycle 23 1 false (3),
.cycle 1 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 274, 18, 128, 256, 8, 128, 4096, 8, 4096],[128, 16, 4, 1, 2, 4096, 128, 16, 4, 1, 2, 4096, 4096],5120⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 28, 20, 128, 256, 8, 128, 4096, 8, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 21 true (0),
.cycle 43 1 false (5),
.last 20 (5,true),
.cycle 21 13 true (2),
.cycle 10 12 true (0),
.cycle 1 22 true (0),
.cycle 33 1 false (5),
.last 21 (5,true),
.cycle 1 24 true (0),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.cycle 10 39 true (0),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid10_part66_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part66) = true := by rfl

def kid10_part67 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 1 20 true (0),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 256, 18, 128, 256, 8, 128, 4096, 18, 4096],[128, 16, 8, 1, 2, 4096, 128, 16, 8, 1, 2, 4096, 4096],5120⟩,
.cycle 19 9 true (1),
.cycle 11 7 true (0),
.cycle 29 1 false (3),
.cycle 11 9 true (0),
.cycle 31 1 false (3),
.cycle 3 17 true (0),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 19 17 true (1),
.cycle 1 20 true (0),
.last 19 (5,true),
.cycle 9 9 true (0)
])
theorem kid10_part67_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part67) = true := by rfl

def kid10_part68 : Audit := .cycle 25 1 false (1)
theorem kid10_part68_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part68) = true := by rfl

def kid10_part69 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (3),
.cycle 1 22 true (0),
.last 21 (5,true),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 256, 18, 128, 256, 8, 128, 4096, 18, 4096],[128, 16, 32, 1, 2, 4096, 128, 16, 32, 1, 2, 4096, 4096],5120⟩,
.cycle 20 11 true (1),
.cycle 13 7 true (0),
.cycle 33 1 false (3),
.cycle 11 9 true (0),
.cycle 37 1 false (3),
.cycle 2 21 true (0),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.last 21 (5,true),
.cycle 24 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 20 21 true (1),
.cycle 1 22 true (0),
.last 21 (5,true),
.cycle 9 11 true (0)
])
theorem kid10_part69_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part69) = true := by rfl

def kid10_part70 : Audit := .cycle 17 5 false (2)
theorem kid10_part70_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part70) = true := by rfl

def kid10_part71 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.last 16 (5,true),
.cycle 23 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 28, 20, 128, 256, 8, 128, 4096, 8, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 13 7 true (0),
.cycle 33 1 false (1),
.cycle 13 9 true (0),
.cycle 19 9 false (2),
.cycle 11 4 true (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.last 16 (5,true),
.cycle 23 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 9 6 true (1)
])
theorem kid10_part71_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part71) = true := by rfl

def kid10_part72 : Audit := .cycle 0 13 true (0)
theorem kid10_part72_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part72) = true := by rfl

def kid10_part73 : Audit := .cycle 18 1 false (0)
theorem kid10_part73_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part73) = true := by rfl

def kid10_part74 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 21 1 false (-1),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 21 1 false (-3),
.last 15 (4,true),
.cycle 23 1 false (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 0 15 true (0),
.cycle 23 1 false (-1),
.cycle 11 2 true (0),
.cycle 18 1 false (-2)
])
theorem kid10_part74_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part74) = true := by rfl

def kid10_part75 : Audit := .cycle 15 1 false (-1)
theorem kid10_part75_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part75) = true := by rfl

def kid10_part76 : Audit := .cycle 0 11 true (0)
theorem kid10_part76_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part76) = true := by rfl

def kid10_part77 : Audit := .cycle 1 10 true (1)
theorem kid10_part77_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part77) = true := by rfl

def kid10_part78 : Audit := .cycle 2 9 true (1)
theorem kid10_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part78) = true := by rfl

def kid10_part79 : Audit := .cycle 1 13 true (1)
theorem kid10_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part79) = true := by rfl

def kid10_part80 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 18 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 29 1 false (1),
.last 21 (4,true),
.cycle 21 7 false (2),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
])
theorem kid10_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part80) = true := by rfl

def kid10_part81 : Audit := .cycle 9 2 true (2)
theorem kid10_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part81) = true := by rfl

def kid10_part57 : Audit := .split 10 (2,true) (byMove [(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78),(kid10_part79),(kid10_part80),(kid10_part81)])

theorem kid10_part57_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part57) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78),(kid10_part79),(kid10_part80),(kid10_part81)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part63_checked

  · exact kid10_part69_checked

  · exact kid10_part75_checked

  · exact kid10_part81_checked

def kid10_part82 : Audit := .cycle 0 11 true (0)
theorem kid10_part82_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part82) = true := by rfl

def kid10_part83 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
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
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 22 2 false (0),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
]),
.cycle 13 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 45 true (0),
.cycle 10 18 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (3),
.last 23 (5,true),
.cycle 0 21 true (0),
.proven (BB6.Agent11Raw39Pumps.M551.table) (fun m hm => BB6.Agent11Raw39Pumps.M551.never m hm),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668544, 1074790400, 1075838976, 2, 4, 32768, 128, 1073741824, 2097160, 33554432, 67108864, 2097152, 65536, 34668544, 1073741824, 128, 256, 2097152, 1048576, 1110507532, 1110507532, 2, 4, 32768, 128, 1073741824, 2097152, 1073741824],[128, 16, 4, 1, 4, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 33554432, 4194304, 1048576, 262144, 1048576, 1073741824, 128, 4194304, 1048576, 262144, 1048576, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 12 9 true (0),
.cycle 27 1 false (3),
.last 25 (5,true),
.cycle 7 15 true (0),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668548, 1110507532, 1110507532, 2, 4, 32768, 128, 1073741824, 2097160, 33554432, 67108864, 2097152, 65536, 34668548, 1073741824, 128, 256, 2097152, 1048580, 1110507532, 1110507532, 2, 4, 32768, 128, 1073741824, 2097152, 1073741824],[128, 16, 1048580, 1, 4, 1073741824, 2, 65536, 1048580, 4096, 16384, 1073741824, 33554432, 4194304, 1048580, 262144, 1048576, 1073741824, 128, 4194304, 1048580, 262144, 1048576, 1073741824, 2, 65536, 1048576, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (0),
.cycle 25 1 false (3),
.last 23 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 42 true (0),
.cycle 1 23 true (0),
.last 22 (5,true),
.last 34 (5,true)
]),
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
.cycle 20 2 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 24 2 false (2),
.cycle 1 17 true (0),
.cycle 13 2 true (0),
.cycle 17 2 false (1)
]),
.cycle 15 2 false (1),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (1),
.cycle 3 10 true (1),
.cycle 17 5 false (2),
.last 15 (5,true),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 10 6 true (1)
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
.cycle 18 2 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 20 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 2 false (0),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
]),
.cycle 13 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 22 true (0),
.cycle 10 9 true (0),
.cycle 17 2 false (1),
.cycle 19 2 false (1),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.cycle 9 4 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid10_part83_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part83) = true := by rfl

def kid10_part84 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.last 24 (2,true),
.cycle 23 1 false (3),
.cycle 23 1 false (3),
.cycle 1 20 true (0),
.cycle 27 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.last 32 (2,true),
.cycle 21 13 true (2),
.last 21 (2,true),
.cycle 1 22 true (0),
.cycle 33 1 false (5),
.cycle 1 24 true (0),
.cycle 1 24 true (0),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 22 true (0),
.cycle 9 20 true (0)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (3),
.cycle 1 20 true (0),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 30, 30, 64],[2, 16, 64, 1, 2, 8, 64],64⟩,
.last 27 (2,true),
.cycle 11 7 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 31 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 25 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 35 (2,true),
.cycle 1 20 true (0),
.cycle 10 9 true (0),
.cycle 9 9 true (0)
]),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.last 17 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.last 16 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 9 2 true (2)
])
theorem kid10_part84_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part84) = true := by rfl

def kid10_part85 : Audit := .cycle 0 10 true (0)
theorem kid10_part85_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part85) = true := by rfl

def kid10_part86 : Audit := .cycle 1 9 true (1)
theorem kid10_part86_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part86) = true := by rfl

def kid10_part88 : Audit := .cycle 0 18 true (0)
theorem kid10_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part88) = true := by rfl

def kid10_part89 : Audit := .cycle 1 17 true (1)
theorem kid10_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part89) = true := by rfl

def kid10_part90 : Audit := .cycle 2 16 true (1)
theorem kid10_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part90) = true := by rfl

def kid10_part91 : Audit := .cycle 1 20 true (1)
theorem kid10_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part91) = true := by rfl

def kid10_part92 : Audit := .split 19 (5,true) (byMove [
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
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 28 1 false (0),
.cycle 0 24 true (0),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (3),
.cycle 9 11 true (2)
])
theorem kid10_part92_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part92) = true := by rfl

def kid10_part93 : Audit := .cycle 9 9 true (2)
theorem kid10_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part93) = true := by rfl

def kid10_part94 : Audit := .cycle 0 18 true (0)
theorem kid10_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part94) = true := by rfl

def kid10_part95 : Audit := .cycle 1 17 true (1)
theorem kid10_part95_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part95) = true := by rfl

def kid10_part96 : Audit := .split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (2),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 18 11 true (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 19 9 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 16, 1, 4, 4096, 4096],5120⟩,
.last 41 (5,true),
.cycle 7 22 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (2),
.cycle 0 32 true (0),
.cycle 27 2 true (6),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.last 29 (5,true),
.cycle 9 19 true (2)
])
theorem kid10_part96_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part96) = true := by rfl

def kid10_part97 : Audit := .cycle 11 7 true (2)
theorem kid10_part97_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part97) = true := by rfl

def kid10_part98 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4096, 1, 16, 4096, 128, 16, 4096, 1, 16, 4096, 4096],5120⟩
theorem kid10_part98_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part98) = true := by rfl

def kid10_part99 : Audit := .split 29 (5,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 10 29 true (2),
.cycle 0 39 true (0),
.cycle 8 33 true (2),
.cycle 0 33 true (0),
.cycle 1 30 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 12, 4, 64],[2, 16, 64, 1, 32, 2, 64],64⟩,
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 12, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 16 15 true (3),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 25 true (2),
.cycle 1 34 true (1),
.last 31 (2,true),
.cycle 1 30 true (1),
.cycle 7 23 true (2),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 41 2 true (11),
.cycle 9 22 true (2)
])
theorem kid10_part99_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part99) = true := by rfl

def kid10_part100 : Audit := .cycle 7 12 true (2)
theorem kid10_part100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part100) = true := by rfl

def kid10_part101 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 35 1 false (1),
.cycle 0 21 true (0),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.last 32 (5,true),
.cycle 6 14 true (2),
.cycle 16 4 true (4),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 9 11 true (2)
])
theorem kid10_part101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part101) = true := by rfl

def kid10_part102 : Audit := .cycle 0 20 true (0)
theorem kid10_part102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part102) = true := by rfl

def kid10_part103 : Audit := .cycle 4 14 true (1)
theorem kid10_part103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part103) = true := by rfl

def kid10_part104 : Audit := .split 19 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 34 1 false (2),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.cycle 0 24 true (0),
.last 21 (2,true),
.cycle 0 26 true (0),
.last 21 (2,true),
.cycle 7 16 true (2),
.cycle 28 1 false (0),
.cycle 7 18 true (1),
.last 21 (2,true),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (3),
.last 21 (2,true)
])
theorem kid10_part104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part104) = true := by rfl

def kid10_part105 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],5120⟩,
.cycle 11 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 16, 1, 16, 4096, 128, 16, 16, 1, 4096, 4096, 4096],5120⟩,
.last 33 (5,true),
.cycle 7 14 true (2),
.cycle 16 6 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 9 11 true (2)
])
theorem kid10_part105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part105) = true := by rfl

def kid10_part106 : Audit := .cycle 0 18 true (0)
theorem kid10_part106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part106) = true := by rfl

def kid10_part107 : Audit := .cycle 1 17 true (1)
theorem kid10_part107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part107) = true := by rfl

def kid10_part108 : Audit := .cycle 2 16 true (1)
theorem kid10_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part108) = true := by rfl

def kid10_part109 : Audit := .cycle 1 20 true (1)
theorem kid10_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part109) = true := by rfl

def kid10_part110 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 39 1 false (1),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 22 true (2),
.cycle 11 9 true (2),
.cycle 8 26 true (2),
.cycle 31 13 true (7),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 7 20 true (1),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 2 true (5),
.cycle 9 11 true (2)
])
theorem kid10_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part110) = true := by rfl

def kid10_part111 : Audit := .cycle 9 9 true (2)
theorem kid10_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part111) = true := by rfl

def kid10_part87 : Audit := .split 17 (4,true) (byMove [(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111)])

theorem kid10_part87_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part87) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part88_checked

  · exact kid10_part94_checked

  · exact kid10_part100_checked

  · exact kid10_part106_checked

  · exact kid10_part89_checked

  · exact kid10_part95_checked

  · exact kid10_part101_checked

  · exact kid10_part107_checked

  · exact kid10_part90_checked

  · exact kid10_part96_checked

  · exact kid10_part102_checked

  · exact kid10_part108_checked

  · exact kid10_part91_checked

  · exact kid10_part97_checked

  · exact kid10_part103_checked

  · exact kid10_part109_checked

  · exact kid10_part92_checked

  · exact kid10_part98_checked

  · exact kid10_part104_checked

  · exact kid10_part110_checked

  · exact kid10_part93_checked

  · exact kid10_part99_checked

  · exact kid10_part105_checked

  · exact kid10_part111_checked

def kid10_part112 : Audit := .cycle 3 7 true (1)
theorem kid10_part112_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part112) = true := by rfl

def kid10_part113 : Audit := .cycle 8 2 true (3)
theorem kid10_part113_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part113) = true := by rfl

def kid10_part114 : Audit := .cycle 9 1 true (3)
theorem kid10_part114_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part114) = true := by rfl

def kid10_part115 : Audit := .cycle 6 4 true (2)
theorem kid10_part115_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part115) = true := by rfl

def kid10_part117 : Audit := .cycle 0 12 true (0)
theorem kid10_part117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part117) = true := by rfl

def kid10_part118 : Audit := .cycle 1 11 true (1)
theorem kid10_part118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part118) = true := by rfl

def kid10_part119 : Audit := .cycle 31 1 false (3)
theorem kid10_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part119) = true := by rfl

def kid10_part120 : Audit := .cycle 21 1 false (1)
theorem kid10_part120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part120) = true := by rfl

def kid10_part121 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 false (4),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.cycle 0 21 false (4),
.cycle 15 5 false (1),
.last 20 (5,true),
.cycle 8 24 false (4),
.cycle 12 15 true (-2),
.last 29 (5,true),
.cycle 12 13 false (2),
.cycle 12 8 false (2),
.cycle 17 3 true (-2),
.cycle 12 10 false (2),
.cycle 14 6 false (1),
.cycle 1 23 false (4),
.cycle 1 21 false (4),
.cycle 15 5 false (1),
.last 20 (5,true),
.last 37 (5,true),
.last 36 (5,true),
.cycle 2 18 false (4),
.cycle 8 26 false (4),
.last 21 (5,true),
.last 24 (5,true)
])
theorem kid10_part121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part121) = true := by rfl

def kid10_part122 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (1),
.cycle 3 12 true (1),
.cycle 19 7 false (1),
.cycle 12 3 true (1),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 31 true (-1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 18 9 false (2)
])
theorem kid10_part122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part122) = true := by rfl

def kid10_part123 : Audit := .cycle 0 12 true (0)
theorem kid10_part123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part123) = true := by rfl

def kid10_part124 : Audit := .cycle 1 11 true (1)
theorem kid10_part124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part124) = true := by rfl

def kid10_part125 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (0),
.cycle 0 26 true (0),
.cycle 24 18 true (1),
.cycle 0 34 true (0),
.cycle 28 1 false (4),
.last 26 (5,true),
.cycle 1 23 true (0),
.cycle 20 80 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 24 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 16, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 16, 1, 4, 4096, 4096],5120⟩,
.last 23 (5,true),
.cycle 7 30 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 1 25 true (0),
.cycle 23 16 true (1),
.cycle 1 29 true (0),
.last 26 (5,true),
.cycle 1 23 true (0),
.cycle 1 51 true (0),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.last 43 (5,true),
.last 23 (5,true)
])
theorem kid10_part125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part125) = true := by rfl

def kid10_part126 : Audit := .cycle 0 21 true (0)
theorem kid10_part126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part126) = true := by rfl

def kid10_part127 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 26 5 false (2),
.cycle 33 1 false (1),
.cycle 0 17 true (0),
.cycle 25 5 false (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 12 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.cycle 13 3 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 1 19 true (1),
.cycle 1 17 true (1),
.cycle 11 6 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.last 17 (5,true),
.cycle 9 7 true (2)
])
theorem kid10_part127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part127) = true := by rfl

def kid10_part128 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 30 5 false (2),
.cycle 43 1 false (3),
.cycle 0 16 true (0),
.cycle 11 4 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.cycle 12 3 true (3),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 9 6 true (2)
])
theorem kid10_part128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part128) = true := by rfl

def kid10_part129 : Audit := .cycle 7 6 true (2)
theorem kid10_part129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part129) = true := by rfl

def kid10_part130 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 24 5 false (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.cycle 19 3 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 12 3 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.cycle 19 3 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 9 5 true (2)
])
theorem kid10_part130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part130) = true := by rfl

def kid10_part131 : Audit := .cycle 0 14 true (0)
theorem kid10_part131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part131) = true := by rfl

def kid10_part132 : Audit := .cycle 26 1 false (2)
theorem kid10_part132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part132) = true := by rfl

def kid10_part133 : Audit := .split 19 (2,true) (byMove [
.cycle 0 38 true (-2),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[131072, 128, 2097152, 512, 32, 128, 131072, 128, 128, 2097152, 131072, 524288, 131072, 131072, 134217728, 512, 8388608, 128, 1073741824, 1644298368, 2097280, 134217728, 536870912, 33554432, 1644298240, 1644298368, 1778516096, 134217728, 536870912, 33554432, 1073741824],[131072, 128, 8, 128, 1024, 1073741824, 131072, 131072, 32768, 128, 4194304, 1073741824, 131072, 128, 2097152, 128, 1024, 1073741824, 1073741824, 570425344, 134217728, 128, 268435456, 1073741824, 1644298240, 570425344, 134217728, 1644298368, 268435456, 1073741824, 1073741824],2009925632⟩,
.cycle 15 5 false (1),
.last 20 (5,true),
.cycle 7 14 false (4),
.cycle 20 17 true (0),
.cycle 0 34 true (-2),
.last 27 (5,true),
.cycle 12 8 false (2),
.last 23 (5,true),
.cycle 12 10 false (2),
.cycle 14 6 false (1),
.cycle 12 20 true (-3),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[131072, 128, 2097152, 512, 32, 128, 131072, 128, 128, 2097152, 131072, 524288, 131072, 131072, 134217728, 512, 8388608, 128, 1073741824, 1644298368, 2097280, 134217728, 536870912, 33554432, 1644298240, 1644298368, 1778516096, 134217728, 536870912, 33554432, 1073741824],[131072, 128, 512, 128, 1024, 1073741824, 131072, 131072, 2097152, 128, 4194304, 1073741824, 131072, 128, 512, 128, 1024, 1073741824, 1073741824, 570425344, 134217728, 128, 268435456, 1073741824, 1644298240, 570425344, 134217728, 1644298368, 268435456, 1073741824, 1073741824],2009925632⟩,
.cycle 15 5 false (1),
.last 20 (5,true),
.last 27 (5,true),
.last 40 (5,true),
.cycle 0 34 true (-2),
.cycle 4 16 false (4),
.last 21 (5,true),
.last 24 (5,true)
])
theorem kid10_part133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part133) = true := by rfl

def kid10_part134 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],5120⟩,
.cycle 0 16 true (0),
.cycle 18 7 false (2),
.last 15 (5,true),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 18 11 false (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid10_part134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part134) = true := by rfl

def kid10_part135 : Audit := .cycle 0 12 true (0)
theorem kid10_part135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part135) = true := by rfl

def kid10_part136 : Audit := .cycle 1 11 true (1)
theorem kid10_part136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part136) = true := by rfl

def kid10_part137 : Audit := .cycle 2 10 true (1)
theorem kid10_part137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part137) = true := by rfl

def kid10_part138 : Audit := .cycle 1 14 true (1)
theorem kid10_part138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part138) = true := by rfl

def kid10_part139 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.last 23 (2,true),
.last 16 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 24 22 true (4),
.cycle 3 46 true (0),
.last 17 (2,true),
.last 16 (2,true),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.last 23 (2,true),
.last 16 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (3),
.cycle 9 5 true (2)
])
theorem kid10_part139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part139) = true := by rfl

def kid10_part140 : Audit := .cycle 9 3 true (2)
theorem kid10_part140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part140) = true := by rfl

def kid10_part116 : Audit := .split 11 (4,true) (byMove [(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132),(kid10_part133),(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140)])

theorem kid10_part116_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part116) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some mv)) (byMove [(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132),(kid10_part133),(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part117_checked

  · exact kid10_part123_checked

  · exact kid10_part129_checked

  · exact kid10_part135_checked

  · exact kid10_part118_checked

  · exact kid10_part124_checked

  · exact kid10_part130_checked

  · exact kid10_part136_checked

  · exact kid10_part119_checked

  · exact kid10_part125_checked

  · exact kid10_part131_checked

  · exact kid10_part137_checked

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

def kid10_part142 : Audit := .cycle 1 14 true (1)
theorem kid10_part142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part142) = true := by rfl

def kid10_part143 : Audit := .cycle 0 14 true (0)
theorem kid10_part143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part143) = true := by rfl

def kid10_part144 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 1 20 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 410, 1, 128, 256, 8, 128, 4096, 411, 4096],[128, 16, 18, 1, 2, 4096, 128, 16, 410, 1, 2, 4096, 4096],5120⟩,
.cycle 12 18 true (0),
.cycle 12 7 true (0),
.cycle 0 22 true (0),
.cycle 0 21 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 47 1 false (3),
.cycle 1 20 true (0),
.last 19 (5,true),
.cycle 9 9 true (0)
])
theorem kid10_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part144) = true := by rfl

def kid10_part145 : Audit := .cycle 0 17 true (0)
theorem kid10_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part145) = true := by rfl

def kid10_part146 : Audit := .split 12 (5,true) (byMove [
.last 21 (4,true),
.last 30 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (4,true),
.cycle 0 20 true (-2),
.last 16 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 20 (4,true),
.last 28 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.last 29 (4,true),
.cycle 0 20 true (-2),
.last 16 (4,true),
.cycle 0 16 true (0),
.last 19 (4,true),
.last 18 (4,true),
.cycle 11 2 true (0),
.last 22 (4,true)
])
theorem kid10_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part146) = true := by rfl

def kid10_part147 : Audit := .cycle 11 8 true (-2)
theorem kid10_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part147) = true := by rfl

def kid10_part148 : Audit := .cycle 1 11 true (1)
theorem kid10_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part148) = true := by rfl

def kid10_part149 : Audit := .cycle 0 16 true (0)
theorem kid10_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part149) = true := by rfl

def kid10_part150 : Audit := .split 21 (4,true) (byMove [
.cycle 0 46 true (0),
.cycle 1 25 true (0),
.cycle 47 1 false (7),
.cycle 1 52 true (0),
.last 23 (5,true),
.cycle 1 27 true (0),
.cycle 0 42 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 136, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 2, 4096, 128, 16, 4, 1, 2, 4096, 4096],5120⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 136, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 1 23 true (0),
.cycle 0 28 true (0),
.last 22 (5,true),
.cycle 23 18 true (3),
.cycle 10 14 true (0),
.cycle 0 48 true (0),
.cycle 41 1 false (7),
.last 23 (5,true),
.cycle 29 1 false (7),
.cycle 1 37 true (0),
.cycle 1 23 true (0),
.cycle 10 54 true (0),
.cycle 1 23 true (0),
.last 25 (5,true),
.last 22 (5,true)
])
theorem kid10_part150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part150) = true := by rfl

def kid10_part151 : Audit := .cycle 0 12 true (0)
theorem kid10_part151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part151) = true := by rfl

def kid10_part152 : Audit := .split 11 (4,true) (byMove [
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
.cycle 7 6 true (2),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 12 10 true (-2),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part152) = true := by rfl

def kid10_part153 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 0 20 true (-2),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 7 6 true (2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 12 10 true (-2),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part153) = true := by rfl

def kid10_part154 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (1),
.cycle 12 7 true (1),
.cycle 0 18 true (0),
.cycle 0 17 true (0),
.cycle 12 8 true (1),
.cycle 12 10 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 9 5 true (1)
])
theorem kid10_part154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part154) = true := by rfl

def kid10_part155 : Audit := .split 14 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 36 1 false (2),
.cycle 1 24 true (0),
.last 16 (5,true),
.cycle 15 12 true (-2),
.cycle 1 15 true (1),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 136, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 16 true (0),
.cycle 0 20 true (0),
.last 15 (5,true),
.cycle 12 10 true (1),
.cycle 11 4 true (1),
.cycle 1 17 true (1),
.cycle 31 1 false (1),
.last 16 (5,true),
.cycle 13 12 true (-2),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 17 (5,true),
.last 15 (5,true)
])
theorem kid10_part155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part155) = true := by rfl

def kid10_part156 : Audit := .cycle 1 13 true (1)
theorem kid10_part156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part156) = true := by rfl

def kid10_part157 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 1 18 true (0),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 384, 1, 128, 256, 8, 128, 4096, 18, 4096],[128, 16, 18, 1, 2, 4096, 128, 16, 128, 1, 2, 4096, 4096],5120⟩,
.cycle 11 16 true (0),
.cycle 11 7 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.cycle 27 1 false (1),
.cycle 1 19 true (0),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 1 33 true (0),
.cycle 1 18 true (0),
.last 17 (5,true),
.cycle 9 7 true (0)
])
theorem kid10_part157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part157) = true := by rfl

def kid10_part158 : Audit := .split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.last 20 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 37 (4,true),
.last 19 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.last 19 (4,true),
.last 27 (4,true),
.last 24 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 28 (4,true),
.last 19 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (0),
.last 17 (4,true),
.cycle 11 2 true (0),
.last 21 (4,true)
])
theorem kid10_part158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part158) = true := by rfl

def kid10_part159 : Audit := .split 18 (4,true) (byMove [
.last 22 (5,true),
.cycle 0 22 true (-2),
.cycle 29 8 true (0),
.last 24 (5,true),
.last 20 (5,true),
.cycle 19 8 true (-2),
.cycle 1 19 true (-2),
.cycle 0 24 true (-2),
.cycle 1 23 true (-2),
.cycle 0 20 true (-2),
.cycle 0 24 true (-2),
.last 19 (5,true),
.last 27 (5,true),
.last 21 (5,true),
.cycle 1 21 true (-2),
.cycle 25 8 true (0),
.last 20 (5,true),
.cycle 11 8 true (-2),
.last 32 (5,true),
.cycle 7 12 true (-2),
.last 20 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 657, 128, 1, 8192, 16384, 8, 144, 16777216, 17, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 7119936, 17301504, 21233664, 16777216],[128, 16, 640, 1, 512, 16777216, 8192, 16, 16777216, 1, 32768, 16777216, 524288, 1024, 16777216, 64, 2097152, 16777216, 524288, 4194304, 19398656, 262144, 2097152, 16777216, 16777216],33502272⟩,
.last 21 (5,true),
.last 19 (5,true)
])
theorem kid10_part159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part159) = true := by rfl

def kid10_part160 : Audit := .cycle 1 11 true (1)
theorem kid10_part160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part160) = true := by rfl

def kid10_part161 : Audit := .cycle 7 4 true (2)
theorem kid10_part161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part161) = true := by rfl

def kid10_part162 : Audit := .cycle 2 10 true (1)
theorem kid10_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part162) = true := by rfl

def kid10_part163 : Audit := .cycle 0 12 true (0)
theorem kid10_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part163) = true := by rfl

def kid10_part164 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 31 (5,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 17 (5,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part164) = true := by rfl

def kid10_part165 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 17 true (0),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 20 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 22 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part165) = true := by rfl

def kid10_part141 : Audit := .split 10 (2,true) (byMove [(kid10_part142),(kid10_part143),(kid10_part144),(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165)])

theorem kid10_part141_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part141) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part142),(kid10_part143),(kid10_part144),(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part142_checked

  · exact kid10_part148_checked

  · exact kid10_part154_checked

  · exact kid10_part160_checked

  · exact kid10_part143_checked

  · exact kid10_part149_checked

  · exact kid10_part155_checked

  · exact kid10_part161_checked

  · exact kid10_part144_checked

  · exact kid10_part150_checked

  · exact kid10_part156_checked

  · exact kid10_part162_checked

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

def kid10_part166 : Audit := .cycle 1 11 true (1)
theorem kid10_part166_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part166) = true := by rfl

def kid10_part168 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.cycle 12 6 true (1),
.last 16 (5,true),
.cycle 12 8 true (1),
.cycle 0 16 true (0),
.cycle 10 34 true (-1),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 12 5 true (2)
])
theorem kid10_part168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part168) = true := by rfl

def kid10_part169 : Audit := .cycle 0 14 true (0)
theorem kid10_part169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part169) = true := by rfl

def kid10_part170 : Audit := .cycle 28 1 false (2)
theorem kid10_part170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part170) = true := by rfl

def kid10_part171 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.far true 5 ⟨0,[0, 1, 0, 2, 3, 3, 4, 4, 4, 4],[0, 512, 2129920, 512, 32, 1024, 8, 512, 32768, 32768, 32, 65536, 0, 1073741824, 0, 2097152, 8388608, 4194304, 1073741824, 512, 134250496, 134217728, 536870912, 268435456, 1207959552, 1207960064, 1207959552, 134217728, 536870912, 268435456, 1073741824],[0, 1024, 32768, 512, 8, 1073741824, 8, 512, 32, 0, 8, 1073741824, 0, 512, 32768, 512, 2097152, 1073741824, 1073741824, 402653184, 1073774592, 0, 134217728, 1073741824, 1207959552, 402653184, 1744863232, 1207959552, 134217728, 1073741824, 1073741824],1191452672⟩,
.cycle 1 26 true (0),
.cycle 3 13 true (0),
.cycle 25 1 false (1),
.last 18 (5,true),
.cycle 27 1 false (1),
.cycle 1 20 true (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 17 (5,true),
.cycle 7 13 true (0)
])
theorem kid10_part171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part171) = true := by rfl

def kid10_part172 : Audit := .split 12 (5,true) (byMove [
.cycle 14 24 true (-1),
.cycle 23 2 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 31 2 false (1),
.last 17 (2,true),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid10_part172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part172) = true := by rfl

def kid10_part173 : Audit := .cycle 13 2 false (-1)
theorem kid10_part173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part173) = true := by rfl

def kid10_part174 : Audit := .cycle 1 11 true (1)
theorem kid10_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part174) = true := by rfl

def kid10_part175 : Audit := .cycle 18 2 false (2)
theorem kid10_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part175) = true := by rfl

def kid10_part176 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 18 true (0),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668544, 1075839112, 1075118081, 2, 4, 32768, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 65536, 2097160, 1073741824, 128, 256, 2097152, 1048576, 1075839112, 1074069505, 2, 4, 32768, 128, 1073741824, 1048576, 1073741824],[128, 16, 4, 1, 4, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 33554432, 4194304, 1048576, 262144, 1048576, 1073741824, 128, 4194304, 1048576, 262144, 1048576, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 10 9 true (0),
.cycle 18 2 false (2),
.last 16 (5,true),
.cycle 7 6 true (2),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668548, 1075839112, 1075118085, 2, 4, 32768, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 65536, 2097160, 1073741824, 128, 256, 2097152, 1048580, 1075839112, 1074069505, 2, 4, 32768, 128, 1073741824, 1048580, 1073741824],[128, 16, 1048580, 1, 4, 1073741824, 2, 65536, 1048580, 4096, 16384, 1073741824, 33554432, 4194304, 1048580, 262144, 1048576, 1073741824, 128, 4194304, 1048580, 262144, 1048576, 1073741824, 2, 65536, 1048576, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 0 14 true (0),
.cycle 10 16 true (0),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part176) = true := by rfl

def kid10_part177 : Audit := .cycle 0 12 true (0)
theorem kid10_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part177) = true := by rfl

def kid10_part178 : Audit := .cycle 18 2 false (2)
theorem kid10_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part178) = true := by rfl

def kid10_part179 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 10 9 true (0),
.cycle 18 2 false (2),
.cycle 17 2 false (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part179) = true := by rfl

def kid10_part180 : Audit := .cycle 12 8 true (1)
theorem kid10_part180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part180) = true := by rfl

def kid10_part181 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.last 17 (5,true),
.cycle 10 12 true (1),
.cycle 0 14 true (0),
.cycle 10 10 true (1),
.last 13 (5,true),
.cycle 10 14 true (1),
.cycle 10 4 true (1),
.cycle 22 10 true (0),
.cycle 5 8 true (1),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 10 8 true (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 19 (5,true),
.last 13 (5,true)
])
theorem kid10_part181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part181) = true := by rfl

def kid10_part182 : Audit := .cycle 1 13 true (1)
theorem kid10_part182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part182) = true := by rfl

def kid10_part183 : Audit := .cycle 23 1 false (1)
theorem kid10_part183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part183) = true := by rfl

def kid10_part184 : Audit := .split 12 (5,true) (byMove [
.cycle 1 17 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 23 2 false (1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 18 2 false (-2),
.last 14 (2,true),
.cycle 27 2 false (1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 25 2 false (-1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 27 2 false (1),
.cycle 11 2 true (0),
.cycle 15 2 false (-1)
])
theorem kid10_part184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part184) = true := by rfl

def kid10_part185 : Audit := .cycle 13 2 false (-1)
theorem kid10_part185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part185) = true := by rfl

def kid10_part186 : Audit := .cycle 1 11 true (1)
theorem kid10_part186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part186) = true := by rfl

def kid10_part187 : Audit := .cycle 7 4 true (2)
theorem kid10_part187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part187) = true := by rfl

def kid10_part188 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 16 (5,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 9 3 true (2)
])
theorem kid10_part188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part188) = true := by rfl

def kid10_part189 : Audit := .cycle 0 12 true (0)
theorem kid10_part189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part189) = true := by rfl

def kid10_part190 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 28 true (-1),
.last 14 (2,true),
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
.last 19 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 25 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (3),
.cycle 9 5 true (2)
])
theorem kid10_part190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part190) = true := by rfl

def kid10_part191 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 9 16 true (-1),
.last 12 (2,true),
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
.cycle 9 5 true (2),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part191) = true := by rfl

def kid10_part167 : Audit := .split 10 (4,true) (byMove [(kid10_part168),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part174),(kid10_part175),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181),(kid10_part182),(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part189),(kid10_part190),(kid10_part191)])

theorem kid10_part167_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part167) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part168),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part174),(kid10_part175),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181),(kid10_part182),(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part189),(kid10_part190),(kid10_part191)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part168_checked

  · exact kid10_part174_checked

  · exact kid10_part180_checked

  · exact kid10_part186_checked

  · exact kid10_part169_checked

  · exact kid10_part175_checked

  · exact kid10_part181_checked

  · exact kid10_part187_checked

  · exact kid10_part170_checked

  · exact kid10_part176_checked

  · exact kid10_part182_checked

  · exact kid10_part188_checked

  · exact kid10_part171_checked

  · exact kid10_part177_checked

  · exact kid10_part183_checked

  · exact kid10_part189_checked

  · exact kid10_part172_checked

  · exact kid10_part178_checked

  · exact kid10_part184_checked

  · exact kid10_part190_checked

  · exact kid10_part173_checked

  · exact kid10_part179_checked

  · exact kid10_part185_checked

  · exact kid10_part191_checked

def kid10_part193 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 12 6 true (1),
.cycle 0 21 true (0),
.cycle 12 8 true (1),
.last 15 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 12 4 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (2)
])
theorem kid10_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part193) = true := by rfl

def kid10_part194 : Audit := .cycle 0 14 true (0)
theorem kid10_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part194) = true := by rfl

def kid10_part195 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (2),
.cycle 1 20 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 18, 256, 18, 8192, 16384, 8, 128, 256, 18, 33554432, 67108864, 2097152, 128, 1073741824, 1073741824, 33554432, 67108864, 2097152, 18, 1073741824, 1073741824, 33554432, 67108864, 134217728, 301989888, 1140850944, 1375731730, 1073741824],[128, 16, 1073741824, 1, 2, 18, 8192, 16, 1073741824, 1, 2, 1073741824, 33554432, 4194304, 1073741824, 262144, 524288, 1073741824, 33554432, 4194304, 1073741824, 262144, 524288, 18, 33554432, 268435456, 1073741824, 16777216, 33554432, 1375731712, 1073741824],2144284736⟩,
.last 27 (2,true),
.cycle 12 7 true (0),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.last 23 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 35 (2,true),
.cycle 1 20 true (0),
.cycle 30 1 false (2),
.cycle 9 9 true (0)
])
theorem kid10_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part195) = true := by rfl

def kid10_part196 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.far true 5 ⟨0,[0, 1, 2, 3, 3, 1, 4, 4, 4, 4],[0, 512, 2097152, 512, 32, 2048, 32768, 512, 2097152, 2097152, 131072, 8388608, 0, 512, 134217728, 512, 8388608, 2048, 1073741824, 1207959552, 2097152, 134217728, 536870912, 536870912, 1207959552, 1207960064, 1210056704, 134217728, 536870912, 536870912, 1073741824],[0, 2048, 2097152, 0, 1073741824, 8, 32768, 1073741824, 8388608, 0, 1073741824, 32768, 0, 2048, 2097152, 512, 1073741824, 2097152, 1073741824, 1610612736, 1075838976, 512, 1073741824, 134217728, 1207959552, 1610612736, 1746927616, 1207959552, 1073741824, 134217728, 1073741824],1191968768⟩,
.last 23 (4,true),
.cycle 3 13 true (0),
.cycle 25 1 false (1),
.last 22 (4,true),
.cycle 27 1 false (1),
.last 17 (4,true),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.last 16 (4,true),
.cycle 23 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 0 19 true (0),
.cycle 7 13 true (0)
])
theorem kid10_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part196) = true := by rfl

def kid10_part197 : Audit := .cycle 14 1 false (-2)
theorem kid10_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part197) = true := by rfl

def kid10_part198 : Audit := .cycle 13 1 false (-1)
theorem kid10_part198_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part198) = true := by rfl

def kid10_part199 : Audit := .cycle 1 11 true (1)
theorem kid10_part199_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part199) = true := by rfl

def kid10_part200 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 1 19 true (0),
.cycle 21 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 false (3),
.cycle 32 1 false (6),
.cycle 41 1 false (3),
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 1 19 true (0),
.cycle 25 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 23 true (2),
.cycle 51 1 false (7)
])
theorem kid10_part200_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part200) = true := by rfl

def kid10_part201 : Audit := .split 11 (2,true) (byMove [
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
.cycle 22 1 false (6),
.cycle 7 6 true (2),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 23 (4,true),
.cycle 9 3 true (2)
])
theorem kid10_part201_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part201) = true := by rfl

def kid10_part202 : Audit := .cycle 0 12 true (0)
theorem kid10_part202_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part202) = true := by rfl

def kid10_part203 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 false (3),
.cycle 22 1 false (4),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 26 1 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 45 1 false (3),
.cycle 9 3 true (2)
])
theorem kid10_part203_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part203) = true := by rfl

def kid10_part204 : Audit := .cycle 21 1 false (5)
theorem kid10_part204_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part204) = true := by rfl

def kid10_part205 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 17 10 false (2),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 12 7 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 19 11 true (1),
.cycle 12 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 10 false (2),
.cycle 17 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 10 true (1),
.cycle 9 5 true (1)
])
theorem kid10_part205_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part205) = true := by rfl

def kid10_part206 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.last 19 (4,true),
.last 22 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.last 18 (4,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid10_part206_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part206) = true := by rfl

def kid10_part207 : Audit := .cycle 1 13 true (1)
theorem kid10_part207_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part207) = true := by rfl

def kid10_part208 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 25 1 false (1),
.cycle 1 18 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 18, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 25 (2,true),
.cycle 11 7 true (0),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 27 1 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 23 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 31 (2,true),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.cycle 9 7 true (0)
])
theorem kid10_part208_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part208) = true := by rfl

def kid10_part209 : Audit := .cycle 14 1 false (-2)
theorem kid10_part209_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part209) = true := by rfl

def kid10_part210 : Audit := .cycle 13 1 false (-1)
theorem kid10_part210_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part210) = true := by rfl

def kid10_part211 : Audit := .cycle 1 11 true (1)
theorem kid10_part211_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part211) = true := by rfl

def kid10_part212 : Audit := .cycle 7 4 true (2)
theorem kid10_part212_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part212) = true := by rfl

def kid10_part213 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 2 15 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 12 true (1),
.cycle 9 3 true (2)
])
theorem kid10_part213_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part213) = true := by rfl

def kid10_part214 : Audit := .cycle 0 12 true (0)
theorem kid10_part214_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part214) = true := by rfl

def kid10_part215 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 20 1 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 2 true (0),
.cycle 12 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (2),
.cycle 16 2 true (4),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 2 true (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (3),
.cycle 9 3 true (2)
])
theorem kid10_part215_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part215) = true := by rfl

def kid10_part216 : Audit := .cycle 9 3 true (2)
theorem kid10_part216_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part216) = true := by rfl

def kid10_part192 : Audit := .split 10 (5,true) (byMove [(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197),(kid10_part198),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216)])

theorem kid10_part192_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part192) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197),(kid10_part198),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part193_checked

  · exact kid10_part199_checked

  · exact kid10_part205_checked

  · exact kid10_part211_checked

  · exact kid10_part194_checked

  · exact kid10_part200_checked

  · exact kid10_part206_checked

  · exact kid10_part212_checked

  · exact kid10_part195_checked

  · exact kid10_part201_checked

  · exact kid10_part207_checked

  · exact kid10_part213_checked

  · exact kid10_part196_checked

  · exact kid10_part202_checked

  · exact kid10_part208_checked

  · exact kid10_part214_checked

  · exact kid10_part197_checked

  · exact kid10_part203_checked

  · exact kid10_part209_checked

  · exact kid10_part215_checked

  · exact kid10_part198_checked

  · exact kid10_part204_checked

  · exact kid10_part210_checked

  · exact kid10_part216_checked

def kid10_part217 : Audit := .cycle 0 10 true (0)
theorem kid10_part217_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part217) = true := by rfl

def kid10_part218 : Audit := .cycle 1 9 true (1)
theorem kid10_part218_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part218) = true := by rfl

def kid10_part219 : Audit := .cycle 2 8 true (1)
theorem kid10_part219_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part219) = true := by rfl

def kid10_part220 : Audit := .cycle 1 12 true (1)
theorem kid10_part220_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part220) = true := by rfl

def kid10_part222 : Audit := .cycle 1 12 true (1)
theorem kid10_part222_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part222) = true := by rfl

def kid10_part223 : Audit := .cycle 1 16 true (1)
theorem kid10_part223_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part223) = true := by rfl

def kid10_part224 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 33 1 false (1),
.last 23 (4,true),
.cycle 21 7 false (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 9 4 true (2)
])
theorem kid10_part224_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part224) = true := by rfl

def kid10_part225 : Audit := .cycle 0 13 true (0)
theorem kid10_part225_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part225) = true := by rfl

def kid10_part226 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 13 4 false (1),
.cycle 17 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 12 7 true (0),
.cycle 17 4 false (1),
.cycle 21 4 false (2),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 13 4 false (1),
.cycle 19 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 4 false (1),
.cycle 9 4 true (2)
])
theorem kid10_part226_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part226) = true := by rfl

def kid10_part227 : Audit := .cycle 16 3 false (0)
theorem kid10_part227_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part227) = true := by rfl

def kid10_part228 : Audit := .cycle 0 12 true (0)
theorem kid10_part228_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part228) = true := by rfl

def kid10_part229 : Audit := .cycle 1 11 true (1)
theorem kid10_part229_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part229) = true := by rfl

def kid10_part230 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (3),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (2,true),
.cycle 13 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 16, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 34 (2,true),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 0 24 true (0),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 10 22 true (2),
.cycle 9 11 true (2)
])
theorem kid10_part230_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part230) = true := by rfl

def kid10_part231 : Audit := .cycle 3 9 true (1)
theorem kid10_part231_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part231) = true := by rfl

def kid10_part232 : Audit := .cycle 8 4 true (3)
theorem kid10_part232_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part232) = true := by rfl

def kid10_part233 : Audit := .cycle 9 3 true (3)
theorem kid10_part233_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part233) = true := by rfl

def kid10_part234 : Audit := .cycle 6 6 true (2)
theorem kid10_part234_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part234) = true := by rfl

def kid10_part235 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.last 25 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.last 19 (2,true),
.last 18 (2,true),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.last 25 (2,true),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 17 (2,true),
.cycle 9 5 true (2)
])
theorem kid10_part235_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part235) = true := by rfl

def kid10_part236 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 0 19 true (0),
.last 20 (4,true),
.cycle 13 12 true (-2),
.cycle 1 13 true (1),
.cycle 0 20 true (0),
.last 23 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (2)
])
theorem kid10_part236_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part236) = true := by rfl

def kid10_part237 : Audit := .cycle 1 13 true (1)
theorem kid10_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part237) = true := by rfl

def kid10_part238 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.last 17 (2,true),
.cycle 13 4 false (1),
.cycle 17 4 false (0),
.cycle 1 13 true (1),
.cycle 24 4 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 24 4 false (2),
.cycle 19 4 false (1),
.cycle 14 10 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.cycle 13 4 false (1),
.cycle 19 4 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 4 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part238) = true := by rfl

def kid10_part239 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 20 7 false (0),
.last 15 (2,true),
.cycle 7 10 true (1),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 1 15 true (1),
.cycle 1 21 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 15 5 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.last 18 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 15 7 false (1),
.cycle 16 3 false (0),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 16, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 0, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 16 5 false (2)
])
theorem kid10_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part239) = true := by rfl

def kid10_part240 : Audit := .cycle 0 12 true (0)
theorem kid10_part240_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part240) = true := by rfl

def kid10_part241 : Audit := .cycle 1 11 true (1)
theorem kid10_part241_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part241) = true := by rfl

def kid10_part242 : Audit := .cycle 2 10 true (1)
theorem kid10_part242_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part242) = true := by rfl

def kid10_part243 : Audit := .cycle 1 14 true (1)
theorem kid10_part243_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part243) = true := by rfl

def kid10_part244 : Audit := .cycle 10 2 true (3)
theorem kid10_part244_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part244) = true := by rfl

def kid10_part245 : Audit := .cycle 9 3 true (3)
theorem kid10_part245_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part245) = true := by rfl

def kid10_part221 : Audit := .split 11 (5,true) (byMove [(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245)])

theorem kid10_part221_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part221) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (5,true) (some mv)) (byMove [(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part222_checked

  · exact kid10_part228_checked

  · exact kid10_part234_checked

  · exact kid10_part240_checked

  · exact kid10_part223_checked

  · exact kid10_part229_checked

  · exact kid10_part235_checked

  · exact kid10_part241_checked

  · exact kid10_part224_checked

  · exact kid10_part230_checked

  · exact kid10_part236_checked

  · exact kid10_part242_checked

  · exact kid10_part225_checked

  · exact kid10_part231_checked

  · exact kid10_part237_checked

  · exact kid10_part243_checked

  · exact kid10_part226_checked

  · exact kid10_part232_checked

  · exact kid10_part238_checked

  · exact kid10_part244_checked

  · exact kid10_part227_checked

  · exact kid10_part233_checked

  · exact kid10_part239_checked

  · exact kid10_part245_checked

def kid10_part246 : Audit := .cycle 9 1 true (3)
theorem kid10_part246_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part246) = true := by rfl

def kid10_part54 : Audit := .split 9 (5,false) (byMove [(kid10_part55),(kid10_part56),(kid10_part57),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116),(kid10_part141),(kid10_part166),(kid10_part167),(kid10_part192),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part246)])

theorem kid10_part54_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid10_part54) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part55),(kid10_part56),(kid10_part57),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116),(kid10_part141),(kid10_part166),(kid10_part167),(kid10_part192),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part55_checked

  · exact kid10_part85_checked

  · exact kid10_part115_checked

  · exact kid10_part217_checked

  · exact kid10_part56_checked

  · exact kid10_part86_checked

  · exact kid10_part116_checked

  · exact kid10_part218_checked

  · exact kid10_part57_checked

  · exact kid10_part87_checked

  · exact kid10_part141_checked

  · exact kid10_part219_checked

  · exact kid10_part82_checked

  · exact kid10_part112_checked

  · exact kid10_part166_checked

  · exact kid10_part220_checked

  · exact kid10_part83_checked

  · exact kid10_part113_checked

  · exact kid10_part167_checked

  · exact kid10_part221_checked

  · exact kid10_part84_checked

  · exact kid10_part114_checked

  · exact kid10_part192_checked

  · exact kid10_part246_checked

def kid10_part247 : Audit := .cycle 0 9 true (0)
theorem kid10_part247_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid10_part247) = true := by rfl

def kid10_part248 : Audit := .cycle 1 8 true (1)
theorem kid10_part248_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid10_part248) = true := by rfl

def kid10_part250 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 32 true (0),
.cycle 0 22 true (0),
.cycle 1 22 true (1),
.split 21 (5,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 1 23 true (1),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 0 30 true (0),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.last 22 (5,false),
.cycle 6 16 true (2),
.cycle 0 24 true (0),
.cycle 7 20 true (2),
.cycle 1 23 true (1),
.cycle 39 5 false (2),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 0 31 true (0),
.last 22 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 29 true (0),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.split 21 (5,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 0 31 true (0),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 9 13 true (2),
.cycle 0 29 true (0),
.last 36 (5,true),
.cycle 21 1 true (7),
.cycle 7 16 true (2),
.cycle 19 3 true (5),
.cycle 0 24 true (0),
.cycle 4 18 true (1),
.cycle 20 3 true (6),
.last 23 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 0 31 true (0),
.cycle 21 1 true (7)
]),
.cycle 6 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 22 true (1),
.cycle 19 4 true (4),
.split 21 (5,true) (byMove [
.cycle 19 4 true (4),
.last 25 (5,false),
.cycle 39 1 false (1),
.cycle 7 17 true (2),
.cycle 0 27 true (0),
.last 24 (5,false),
.cycle 1 22 true (1),
.cycle 0 40 true (0),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.last 23 (5,false),
.cycle 0 25 true (0),
.cycle 16 6 true (4),
.cycle 0 29 true (0),
.cycle 5 17 true (1),
.cycle 39 5 false (2),
.last 24 (5,false),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 20 2 true (5),
.cycle 0 23 true (0),
.cycle 1 23 true (1),
.last 23 (5,false)
]),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 0 30 true (0),
.split 21 (5,false) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 20 2 true (6),
.cycle 0 23 true (0),
.cycle 1 23 true (1),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 0 30 true (0),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.cycle 21 1 true (7),
.cycle 6 16 true (2),
.cycle 0 24 true (0),
.last 23 (5,true),
.cycle 1 23 true (1),
.cycle 19 5 true (5),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 0 31 true (0),
.cycle 21 1 true (7)
])
])
theorem kid10_part250_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part250) = true := by rfl

def kid10_part251 : Audit := .cycle 0 21 true (0)
theorem kid10_part251_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part251) = true := by rfl

def kid10_part252 : Audit := .cycle 2 23 true (1)
theorem kid10_part252_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part252) = true := by rfl

def kid10_part253 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.cycle 0 25 true (0),
.split 23 (5,true) (byMove [
.cycle 1 24 true (1),
.cycle 69 1 false (11),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 1 34 true (0),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 1 34 true (1),
.cycle 3 21 true (1),
.cycle 8 16 true (2),
.last 24 (5,false),
.cycle 6 18 true (2),
.cycle 42 1 false (2),
.last 25 (5,false),
.cycle 1 25 true (1),
.cycle 0 38 true (0),
.last 25 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 1 35 true (1),
.last 24 (5,false)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.split 23 (5,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 1 35 true (1),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 9 15 true (2),
.cycle 1 33 true (1),
.last 40 (5,true),
.cycle 23 1 true (7),
.cycle 7 18 true (2),
.cycle 21 3 true (5),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.cycle 22 3 true (6),
.last 25 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 1 35 true (1),
.cycle 23 1 true (7)
]),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.cycle 7 19 true (2),
.split 23 (5,true) (byMove [
.cycle 20 4 true (4),
.last 27 (5,false),
.last 25 (5,false),
.cycle 7 19 true (2),
.cycle 1 45 true (0),
.last 25 (5,false),
.cycle 1 24 true (1),
.cycle 3 41 true (1),
.last 25 (5,false),
.cycle 0 25 true (0),
.cycle 1 27 true (1),
.last 25 (5,false),
.cycle 1 29 true (1),
.cycle 42 1 false (2),
.last 25 (5,false),
.cycle 5 19 true (1),
.cycle 1 38 true (0),
.last 25 (5,false),
.cycle 1 24 true (1),
.cycle 7 17 true (2),
.cycle 22 2 true (5),
.cycle 0 25 true (0),
.cycle 0 26 true (0),
.last 25 (5,false)
]),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 1 34 true (1),
.split 23 (5,false) (byMove [
.cycle 1 24 true (1),
.cycle 7 17 true (2),
.cycle 22 2 true (6),
.cycle 0 25 true (0),
.cycle 0 26 true (0),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 1 34 true (1),
.cycle 3 21 true (1),
.cycle 8 16 true (2),
.cycle 23 1 true (7),
.cycle 6 18 true (2),
.cycle 1 28 true (1),
.last 25 (5,true),
.cycle 1 25 true (1),
.cycle 7 20 true (2),
.last 24 (5,true),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 1 35 true (1),
.cycle 23 1 true (7)
])
])
theorem kid10_part253_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part253) = true := by rfl

def kid10_part254 : Audit := .cycle 0 21 true (0)
theorem kid10_part254_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part254) = true := by rfl

def kid10_part256 : Audit := .cycle 0 23 true (0)
theorem kid10_part256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part256) = true := by rfl

def kid10_part257 : Audit := .cycle 0 23 true (0)
theorem kid10_part257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part257) = true := by rfl

def kid10_part258 : Audit := .split 19 (2,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 28 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 41 1 false (1),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 23 true (0),
.cycle 34 1 false (2),
.cycle 0 25 true (0),
.cycle 49 1 false (1),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 19 2 true (2),
.cycle 32 1 false (0),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 1 27 true (1),
.cycle 0 23 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part258) = true := by rfl

def kid10_part259 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 33 true (0),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.cycle 1 26 true (1),
.cycle 6 17 true (2),
.cycle 0 27 true (0),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 0 34 true (0),
.cycle 0 25 true (0)
])
theorem kid10_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part259) = true := by rfl

def kid10_part260 : Audit := .cycle 35 1 false (1)
theorem kid10_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part260) = true := by rfl

def kid10_part261 : Audit := .split 19 (5,true) (byMove [
.cycle 0 31 true (0),
.last 28 (2,true),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 23 true (0),
.cycle 25 1 false (1),
.cycle 0 25 true (0),
.last 21 (2,true),
.last 24 (2,true),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 23 1 false (-1),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 18 2 true (3)
])
theorem kid10_part261_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part261) = true := by rfl

def kid10_part262 : Audit := .cycle 7 13 true (2)
theorem kid10_part262_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part262) = true := by rfl

def kid10_part263 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 1 38 true (1),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 1 29 true (1),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 1 21 true (1),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 30 true (1),
.cycle 1 21 true (1)
])
theorem kid10_part263_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part263) = true := by rfl

def kid10_part264 : Audit := .cycle 0 21 true (0)
theorem kid10_part264_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part264) = true := by rfl

def kid10_part265 : Audit := .cycle 3 23 true (1)
theorem kid10_part265_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part265) = true := by rfl

def kid10_part266 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 8 22 true (2),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 10 11 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.last 38 (5,true),
.cycle 7 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 23 true (0),
.cycle 8 20 true (2),
.cycle 19 2 true (5),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 8 23 true (2),
.cycle 8 14 true (2)
])
theorem kid10_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part266) = true := by rfl

def kid10_part267 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 29 1 true (5),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 21 1 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 34 (2,true),
.cycle 10 11 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 48, 4, 32, 128, 256, 8, 128, 4, 32, 4096],[128, 16, 4096, 1, 32, 16, 128, 16, 4096, 1, 4, 16, 4096],4096⟩,
.cycle 21 1 true (7),
.cycle 7 15 true (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 27 1 true (5),
.last 22 (2,true),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 30 1 true (8),
.cycle 21 1 true (7)
])
theorem kid10_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part267) = true := by rfl

def kid10_part268 : Audit := .split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 6 26 true (2),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.cycle 7 18 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 10 13 true (2),
.cycle 20 23 true (3),
.cycle 7 18 true (2),
.cycle 7 17 true (2),
.cycle 7 22 true (2),
.cycle 0 25 true (0),
.cycle 6 24 true (2),
.cycle 21 2 true (5),
.cycle 6 22 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 6 27 true (2),
.cycle 6 18 true (2)
])
theorem kid10_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part268) = true := by rfl

def kid10_part269 : Audit := .split 23 (2,true) (byMove [
.cycle 1 39 true (1),
.cycle 45 1 false (3),
.cycle 49 1 false (1),
.cycle 0 29 true (0),
.cycle 27 4 false (1),
.last 24 (5,true),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 11 14 true (2),
.cycle 10 21 true (2),
.cycle 0 27 true (0),
.last 30 (5,true),
.cycle 0 29 true (0),
.cycle 32 5 false (1),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 27 4 false (1),
.last 24 (5,true),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 2 35 true (1),
.cycle 1 31 true (1),
.cycle 0 27 true (0),
.cycle 36 9 false (2)
])
theorem kid10_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part269) = true := by rfl

def kid10_part270 : Audit := .split 19 (2,true) (byMove [
.cycle 0 27 true (0),
.cycle 7 17 true (2),
.cycle 31 1 false (1),
.cycle 0 35 true (0),
.cycle 7 17 true (2),
.cycle 0 30 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.cycle 8 19 true (2),
.last 20 (5,true),
.cycle 31 5 false (2),
.cycle 0 38 true (0),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 19 2 true (2),
.cycle 1 30 true (1),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 0 23 true (0),
.cycle 7 15 true (2),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part270_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part270) = true := by rfl

def kid10_part271 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.cycle 4 20 true (1),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.last 24 (5,true),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 1 34 true (1),
.cycle 1 25 true (1)
])
theorem kid10_part271_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part271) = true := by rfl

def kid10_part272 : Audit := .split 22 (2,true) (byMove [
.cycle 7 21 true (1),
.cycle 32 13 false (2),
.cycle 45 1 false (1),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17053, 4, 17053, 8192, 16384, 8, 144, 4, 17053, 524288, 1048576, 512, 128, 256, 16777216, 524288, 1048576, 2097152, 24929949, 1048576, 24929949, 16777216],[128, 16, 17053, 1, 17053, 16777216, 8192, 16, 16512, 1, 16777216, 16777216, 524288, 1024, 128, 64, 16777216, 16777216, 524288, 4194304, 24929949, 262144, 24929949, 16777216, 16777216],33435712⟩,
.cycle 39 1 false (1),
.cycle 25 3 false (-1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 7 19 true (1),
.cycle 35 1 false (1),
.cycle 69 1 false (11),
.last 26 (5,true),
.cycle 7 25 true (1),
.cycle 28 7 false (0),
.cycle 0 31 true (0),
.cycle 40 1 false (0),
.cycle 21 2 true (1),
.cycle 25 3 false (-1),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 7 19 true (1),
.cycle 1 31 true (1),
.cycle 23 16 true (3),
.cycle 25 5 false (1)
])
theorem kid10_part272_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part272) = true := by rfl

def kid10_part273 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 7 17 true (2),
.cycle 31 1 false (1),
.last 26 (2,true),
.cycle 7 17 true (2),
.cycle 23 1 false (-1),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 26 1 false (0),
.cycle 33 1 false (7),
.cycle 31 5 false (2),
.last 21 (2,true),
.last 24 (2,true),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 23 1 false (-1),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 0 25 true (0),
.cycle 23 3 true (5)
])
theorem kid10_part273_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part273) = true := by rfl

def kid10_part274 : Audit := .cycle 7 13 true (2)
theorem kid10_part274_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part274) = true := by rfl

def kid10_part275 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 1 32 true (0),
.cycle 0 22 true (0),
.last 22 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 1 29 true (1),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 1 21 true (1),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.cycle 1 29 true (1),
.cycle 1 22 true (1),
.last 22 (5,true),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 30 true (1),
.cycle 1 21 true (1)
])
theorem kid10_part275_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part275) = true := by rfl

def kid10_part276 : Audit := .cycle 0 21 true (0)
theorem kid10_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part276) = true := by rfl

def kid10_part277 : Audit := .cycle 4 15 true (1)
theorem kid10_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part277) = true := by rfl

def kid10_part278 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 10 true (4),
.cycle 21 10 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (2),
.cycle 21 10 true (4),
.cycle 35 10 true (8),
.cycle 21 10 true (7),
.cycle 7 15 true (2),
.cycle 23 10 true (5),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.cycle 19 2 true (5),
.last 23 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 21 10 true (6),
.cycle 21 10 true (7)
])
theorem kid10_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part278) = true := by rfl

def kid10_part279 : Audit := .split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
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
.cycle 23 1 true (5),
.last 21 (2,true),
.cycle 1 22 true (1),
.last 30 (2,true),
.cycle 29 3 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 30 1 true (8),
.cycle 21 1 true (7)
])
theorem kid10_part279_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part279) = true := by rfl

def kid10_part255 : Audit := .split 18 (5,false) (byMove [(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part259),(kid10_part260),(kid10_part261),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279)])

theorem kid10_part255_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part255) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part259),(kid10_part260),(kid10_part261),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part256_checked

  · exact kid10_part262_checked

  · exact kid10_part268_checked

  · exact kid10_part274_checked

  · exact kid10_part257_checked

  · exact kid10_part263_checked

  · exact kid10_part269_checked

  · exact kid10_part275_checked

  · exact kid10_part258_checked

  · exact kid10_part264_checked

  · exact kid10_part270_checked

  · exact kid10_part276_checked

  · exact kid10_part259_checked

  · exact kid10_part265_checked

  · exact kid10_part271_checked

  · exact kid10_part277_checked

  · exact kid10_part260_checked

  · exact kid10_part266_checked

  · exact kid10_part272_checked

  · exact kid10_part278_checked

  · exact kid10_part261_checked

  · exact kid10_part267_checked

  · exact kid10_part273_checked

  · exact kid10_part279_checked

def kid10_part280 : Audit := .cycle 1 18 true (1)
theorem kid10_part280_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part280) = true := by rfl

def kid10_part281 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 64, 64],[2, 16, 64, 1, 2, 64, 64],96⟩
theorem kid10_part281_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part281) = true := by rfl

def kid10_part282 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (2),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 9 18 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.cycle 19 1 true (5),
.cycle 7 14 true (2),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 33 3 false (1),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (2),
.cycle 19 1 true (5)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 16, 1, 4, 64, 64],96⟩,
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 9 18 true (2),
.last 32 (5,true),
.last 23 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (5,true),
.last 30 (5,true),
.last 34 (5,true),
.cycle 19 1 true (7),
.cycle 7 14 true (2),
.cycle 18 3 true (6),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.cycle 18 3 true (6),
.last 23 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (2),
.cycle 19 1 true (7)
]),
.cycle 7 13 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 21 true (0),
.cycle 9 16 true (2),
.cycle 18 2 true (5),
.split 19 (5,false) (byMove [
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 9 18 true (2),
.last 25 (5,true),
.cycle 0 23 true (0),
.last 21 (5,true),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 2, 128, 256, 8, 128, 4, 2, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.last 20 (5,true),
.cycle 9 14 true (2),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 9 16 true (2),
.cycle 33 3 false (1),
.last 21 (5,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 9 20 true (2),
.last 20 (5,true)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 19 true (2),
.split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.last 34 (5,true),
.cycle 18 2 true (6),
.cycle 0 21 true (0),
.last 32 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 19 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.last 34 (5,true),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 20 true (2),
.cycle 19 1 true (7)
])
])
theorem kid10_part282_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part282) = true := by rfl

def kid10_part283 : Audit := .cycle 0 19 true (0)
theorem kid10_part283_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part283) = true := by rfl

def kid10_part284 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 64, 64],[2, 16, 64, 1, 16, 64, 64],96⟩
theorem kid10_part284_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part284) = true := by rfl

def kid10_part286 : Audit := .cycle 0 19 true (0)
theorem kid10_part286_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part286) = true := by rfl

def kid10_part287 : Audit := .cycle 1 18 true (1)
theorem kid10_part287_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part287) = true := by rfl

def kid10_part288 : Audit := .split 27 (5,false) (byMove [
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
.cycle 7 22 true (2),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 21 7 true (3),
.last 29 (2,true),
.cycle 81 1 false (5),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 19 10 true (3),
.cycle 27 1 true (7)
])
theorem kid10_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part288) = true := by rfl

def kid10_part289 : Audit := .cycle 3 16 true (1)
theorem kid10_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part289) = true := by rfl

def kid10_part290 : Audit := .cycle 8 11 true (2)
theorem kid10_part290_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part290) = true := by rfl

def kid10_part291 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 22 true (2),
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 10 18 true (2),
.last 34 (2,true),
.cycle 19 1 true (5),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 25 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 10 true (5),
.cycle 19 1 true (5)
])
theorem kid10_part291_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part291) = true := by rfl

def kid10_part292 : Audit := .cycle 0 19 true (0)
theorem kid10_part292_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part292) = true := by rfl

def kid10_part293 : Audit := .cycle 1 18 true (1)
theorem kid10_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part293) = true := by rfl

def kid10_part294 : Audit := .split 30 (2,true) (byMove [
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 9 22 true (2),
.last 38 (5,false),
.cycle 19 13 true (3),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 4, 16777216, 128, 256, 32768, 128, 16384, 16777216, 128, 256, 2097152, 65536, 1048576, 16777216, 128, 256, 8, 8388608, 4, 16777216, 16777216],[128, 16, 4, 1, 32, 4, 128, 65536, 16384, 4096, 131072, 16384, 128, 4194304, 1048576, 262144, 8388608, 1048576, 128, 16, 4, 1, 32, 4, 16777216],27413536⟩,
.cycle 20 11 true (3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 33554816, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 8388608, 256, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 1073741824],[128, 16, 16, 1, 32, 4, 128, 65536, 65536, 4096, 131072, 16384, 33554432, 4194304, 4194304, 262144, 8388608, 1048576, 128, 1024, 1024, 64, 2048, 256, 128, 65536, 65536, 4096, 131072, 16384, 1073741824],1889684512⟩,
.last 31 (5,false),
.cycle 7 25 true (2),
.last 35 (5,false),
.cycle 0 33 true (0),
.cycle 11 20 true (2),
.cycle 30 2 true (7),
.last 31 (5,false),
.cycle 0 31 true (0),
.cycle 1 30 true (1),
.cycle 2 29 true (1),
.cycle 1 33 true (1),
.last 40 (5,false),
.last 31 (5,false)
])
theorem kid10_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part294) = true := by rfl

def kid10_part295 : Audit := .cycle 10 9 true (2)
theorem kid10_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part295) = true := by rfl

def kid10_part296 : Audit := .far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 128, 256, 2097152, 65536, 1048576, 1073741824, 128, 256, 134217728, 8388608, 67108864, 1073741824, 128, 256, 2097152, 268435456, 1048576, 1073741824, 1073741824],[128, 16, 1073741824, 1, 32, 16, 128, 65536, 1073741824, 4096, 131072, 65536, 128, 4194304, 1073741824, 262144, 8388608, 4194304, 128, 268435456, 1073741824, 16777216, 536870912, 268435456, 128, 4194304, 1073741824, 262144, 8388608, 4194304, 1073741824],1692552224⟩
theorem kid10_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part296) = true := by rfl

def kid10_part297 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 29 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 19 1 true (7),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 11 9 true (2),
.last 21 (2,true),
.cycle 45 1 false (9),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part297) = true := by rfl

def kid10_part298 : Audit := .cycle 7 13 true (2)
theorem kid10_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part298) = true := by rfl

def kid10_part299 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 1 38 true (1),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.last 22 (5,false),
.last 27 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 6 15 true (2),
.last 23 (5,false),
.cycle 1 24 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (5),
.cycle 42 3 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 30 (5,false),
.last 21 (5,false)
])
theorem kid10_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part299) = true := by rfl

def kid10_part300 : Audit := .cycle 0 21 true (0)
theorem kid10_part300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part300) = true := by rfl

def kid10_part301 : Audit := .split 25 (5,false) (byMove [
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
.cycle 7 20 true (2),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 19 7 true (3),
.last 27 (2,true),
.cycle 68 1 false (4),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 19 10 true (3),
.cycle 25 1 true (7)
])
theorem kid10_part301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part301) = true := by rfl

def kid10_part302 : Audit := .split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 29 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 4, 16777216, 128, 256, 32768, 128, 16384, 16777216, 128, 256, 2097152, 65536, 1048576, 16777216, 128, 256, 8, 8388608, 4, 16777216, 16777216],[128, 16, 4, 1, 32, 4, 128, 65536, 16384, 4096, 131072, 1048580, 128, 4194304, 1048576, 262144, 8388608, 1048576, 128, 16, 4, 1, 32, 4, 16777216],27413536⟩,
.cycle 10 11 true (2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 128, 256, 2097152, 65536, 1048576, 1073741824, 128, 256, 134217728, 8388608, 67108864, 1073741824, 128, 256, 2097152, 268435456, 1048576, 1073741824, 1073741824],[128, 16, 16, 1, 32, 16, 128, 65536, 65536, 4096, 131072, 272629776, 128, 4194304, 4194304, 262144, 8388608, 4194304, 128, 268435456, 268435456, 16777216, 536870912, 268435456, 128, 4194304, 4194304, 262144, 8388608, 4194304, 1073741824],1692552224⟩,
.last 21 (5,false),
.cycle 7 15 true (2),
.last 25 (5,false),
.cycle 0 23 true (0),
.last 27 (5,false),
.cycle 19 2 true (5),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 30 (5,false),
.last 21 (5,false)
])
theorem kid10_part302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part302) = true := by rfl

def kid10_part303 : Audit := .split 19 (5,false) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 9 true (3),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 25 1 false (-1),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 2, 64],[2, 16, 64, 1, 32, 48, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 18 2 true (5),
.cycle 7 18 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 20 7 true (3),
.last 21 (2,true),
.cycle 25 1 false (-1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 20 10 true (6),
.cycle 31 3 false (1)
])
theorem kid10_part303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part303) = true := by rfl

def kid10_part304 : Audit := .cycle 0 19 true (0)
theorem kid10_part304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part304) = true := by rfl

def kid10_part305 : Audit := .cycle 1 18 true (1)
theorem kid10_part305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part305) = true := by rfl

def kid10_part306 : Audit := .cycle 2 17 true (1)
theorem kid10_part306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part306) = true := by rfl

def kid10_part307 : Audit := .cycle 1 21 true (1)
theorem kid10_part307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part307) = true := by rfl

def kid10_part308 : Audit := .split 28 (5,false) (byMove [
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
.cycle 7 23 true (2),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 22 7 true (6),
.last 30 (2,true),
.cycle 17 21 true (5),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 19 10 true (6),
.cycle 28 1 true (10)
])
theorem kid10_part308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part308) = true := by rfl

def kid10_part309 : Audit := .split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 30 true (2),
.last 20 (2,true),
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
.last 24 (2,true),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part309_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part309) = true := by rfl

def kid10_part285 : Audit := .split 18 (5,true) (byMove [(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295),(kid10_part296),(kid10_part297),(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309)])

theorem kid10_part285_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part285) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295),(kid10_part296),(kid10_part297),(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part286_checked

  · exact kid10_part292_checked

  · exact kid10_part298_checked

  · exact kid10_part304_checked

  · exact kid10_part287_checked

  · exact kid10_part293_checked

  · exact kid10_part299_checked

  · exact kid10_part305_checked

  · exact kid10_part288_checked

  · exact kid10_part294_checked

  · exact kid10_part300_checked

  · exact kid10_part306_checked

  · exact kid10_part289_checked

  · exact kid10_part295_checked

  · exact kid10_part301_checked

  · exact kid10_part307_checked

  · exact kid10_part290_checked

  · exact kid10_part296_checked

  · exact kid10_part302_checked

  · exact kid10_part308_checked

  · exact kid10_part291_checked

  · exact kid10_part297_checked

  · exact kid10_part303_checked

  · exact kid10_part309_checked

def kid10_part310 : Audit := .cycle 7 15 true (2)
theorem kid10_part310_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part310) = true := by rfl

def kid10_part311 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.cycle 33 3 false (1),
.split 20 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 22 (5,false),
.cycle 0 27 true (0),
.cycle 43 1 false (1),
.last 22 (5,false),
.cycle 7 15 true (2),
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.last 23 (5,false),
.last 21 (5,false),
.last 25 (5,false),
.cycle 34 3 false (1),
.last 22 (5,false),
.cycle 1 27 true (1),
.last 27 (5,false),
.last 22 (5,false),
.cycle 7 15 true (2),
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 23 (5,false),
.last 21 (5,false)
]),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 32 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 9 12 true (2),
.last 30 (5,false),
.last 38 (5,false),
.last 21 (5,false),
.cycle 7 15 true (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 32 (5,false),
.last 21 (5,false)
]),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.cycle 33 3 false (1),
.split 20 (5,true) (byMove [
.cycle 18 4 true (3),
.last 24 (5,false),
.last 22 (5,false),
.cycle 7 23 true (2),
.cycle 7 35 true (1),
.last 22 (5,false),
.cycle 6 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 16, 4096, 1, 16, 2, 128, 16, 16, 1, 16, 2, 4096],6176⟩,
.last 22 (5,false),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 23 (5,false),
.cycle 15 6 true (3),
.cycle 34 3 false (1),
.last 22 (5,false),
.cycle 5 23 true (1),
.last 27 (5,false),
.last 22 (5,false),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.cycle 19 2 true (4),
.cycle 1 22 true (1),
.cycle 16 6 true (4),
.last 23 (5,false)
]),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 21 11 true (5),
.split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 26 (5,false),
.last 24 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 6 15 true (2),
.last 25 (5,false),
.cycle 19 2 true (5),
.cycle 1 22 true (1),
.cycle 16 6 true (4),
.last 24 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 32 (5,false),
.last 21 (5,false)
])
])
theorem kid10_part311_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part311) = true := by rfl

def kid10_part312 : Audit := .cycle 1 20 true (1)
theorem kid10_part312_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part312) = true := by rfl

def kid10_part313 : Audit := .cycle 4 19 true (1)
theorem kid10_part313_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part313) = true := by rfl

def kid10_part314 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.split 20 (5,false) (byMove [
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 45 1 false (1),
.last 25 (5,true),
.cycle 43 1 false (1),
.last 21 (5,true),
.cycle 7 15 true (2),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.last 22 (5,true),
.cycle 7 20 true (2),
.last 28 (5,true),
.cycle 0 32 true (0),
.last 25 (5,true),
.cycle 29 3 false (0),
.last 21 (5,true),
.cycle 7 15 true (2),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.cycle 21 12 true (5),
.last 22 (5,true)
]),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 64, 64],[2, 16, 2, 1, 18, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 64, 64],[2, 16, 16, 1, 16, 64, 64],96⟩,
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 35 (5,false),
.cycle 10 11 true (2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 128, 256, 2097152, 65536, 1048576, 1073741824, 128, 256, 134217728, 8388608, 67108864, 1073741824, 128, 256, 2097152, 268435456, 1048576, 1073741824, 1073741824],[128, 16, 32, 1, 32, 16, 128, 65536, 131072, 4096, 817889328, 65536, 128, 4194304, 8388608, 262144, 8388608, 4194304, 128, 268435456, 536870912, 16777216, 536870912, 268435456, 128, 4194304, 8388608, 262144, 8388608, 4194304, 1073741824],1692552224⟩,
.last 21 (5,false),
.cycle 7 15 true (2),
.last 23 (5,false),
.cycle 0 23 true (0),
.last 29 (5,false),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 32 (5,false),
.last 21 (5,false)
]),
.cycle 7 19 true (2),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (4),
.split 20 (5,false) (byMove [
.last 24 (5,true),
.cycle 1 28 true (1),
.cycle 36 1 false (0),
.cycle 7 23 true (2),
.cycle 7 35 true (1),
.last 21 (5,true),
.cycle 6 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 2, 128, 256, 8, 128, 4, 2, 4096],[128, 16, 16, 1, 16, 4096, 128, 16, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 19 2 true (4),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 21 (5,true),
.cycle 15 6 true (3),
.last 28 (5,true),
.cycle 14 10 true (1),
.cycle 5 23 true (1),
.cycle 29 3 false (0),
.last 21 (5,true),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 33 5 false (1),
.last 21 (5,true)
]),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 17 4 true (4),
.split 20 (5,true) (byMove [
.cycle 1 21 true (1),
.last 39 (5,false),
.last 22 (5,false),
.cycle 0 22 true (0),
.last 24 (5,false),
.last 22 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 31 (5,false),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.last 21 (5,false),
.cycle 6 15 true (2),
.last 25 (5,false),
.cycle 19 2 true (5),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.last 22 (5,false),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 32 (5,false),
.last 21 (5,false)
])
])
theorem kid10_part314_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part314) = true := by rfl

def kid10_part316 : Audit := .split 21 (2,true) (byMove [
.cycle 1 25 true (1),
.cycle 1 24 true (1),
.cycle 39 1 false (1),
.cycle 7 17 true (2),
.last 23 (5,true),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 1 43 true (1),
.cycle 9 14 true (2),
.cycle 0 23 true (0),
.cycle 8 19 true (2),
.last 22 (5,true),
.cycle 6 23 true (2),
.cycle 16 6 true (3),
.cycle 5 31 true (1),
.cycle 5 17 true (1),
.last 23 (5,true),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 2 21 true (1),
.cycle 0 23 true (0),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid10_part316_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part316) = true := by rfl

def kid10_part317 : Audit := .split 21 (2,true) (byMove [
.cycle 1 25 true (1),
.cycle 0 25 true (0),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 0 25 true (0),
.cycle 1 35 true (1),
.cycle 1 22 true (1),
.cycle 14 33 true (0),
.cycle 46 1 false (10),
.cycle 0 23 true (0),
.cycle 0 27 true (0),
.last 22 (5,true),
.cycle 7 23 true (2),
.cycle 1 30 true (1),
.cycle 1 24 true (1),
.cycle 34 1 false (2),
.cycle 20 2 true (4),
.cycle 1 26 true (1),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 2 21 true (1),
.cycle 0 23 true (0),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid10_part317_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part317) = true := by rfl

def kid10_part318 : Audit := .split 19 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 1 28 true (0),
.cycle 34 1 false (2),
.cycle 1 30 true (0),
.cycle 7 19 true (2),
.cycle 1 51 true (1),
.cycle 1 22 true (1),
.cycle 30 1 false (2),
.cycle 41 1 false (3),
.cycle 34 1 false (2),
.cycle 7 27 true (2),
.cycle 40 1 false (0),
.cycle 7 23 true (2),
.cycle 28 1 false (0),
.cycle 19 2 true (2),
.cycle 32 1 false (0),
.cycle 7 19 true (2),
.cycle 7 15 true (2),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.last 23 (5,true),
.cycle 18 2 true (3)
])
theorem kid10_part318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part318) = true := by rfl

def kid10_part319 : Audit := .cycle 7 19 true (2)
theorem kid10_part319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part319) = true := by rfl

def kid10_part320 : Audit := .cycle 7 27 true (1)
theorem kid10_part320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part320) = true := by rfl

def kid10_part321 : Audit := .split 19 (5,true) (byMove [
.cycle 1 24 true (1),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 1 28 true (0),
.cycle 34 1 false (2),
.cycle 23 1 false (-1),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 30 1 false (2),
.last 21 (2,true),
.cycle 25 1 false (1),
.last 23 (2,true),
.last 21 (2,true),
.cycle 7 23 true (2),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 23 1 false (-1),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.last 21 (2,true),
.cycle 18 2 true (3)
])
theorem kid10_part321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part321) = true := by rfl

def kid10_part322 : Audit := .cycle 6 13 true (2)
theorem kid10_part322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part322) = true := by rfl

def kid10_part323 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 2, 128, 256, 8, 128, 4, 2, 4096],[128, 16, 4096, 1, 16, 4096, 128, 16, 4096, 1, 4096, 4096, 4096],4096⟩
theorem kid10_part323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part323) = true := by rfl

def kid10_part324 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 2, 1, 2, 4096, 128, 16, 2, 1, 4096, 4096, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 16, 1, 16, 4096, 128, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.last 20 (5,true),
.cycle 7 19 true (2),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 19 2 true (4),
.cycle 18 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part324) = true := by rfl

def kid10_part325 : Audit := .cycle 1 20 true (1)
theorem kid10_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part325) = true := by rfl

def kid10_part326 : Audit := .cycle 17 2 true (4)
theorem kid10_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part326) = true := by rfl

def kid10_part327 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 23 1 true (5),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 32, 64],[2, 16, 64, 1, 18, 2, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 32, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 21 1 true (7),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.last 21 (2,true),
.cycle 18 2 true (4),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 2 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part327) = true := by rfl

def kid10_part328 : Audit := .cycle 15 4 true (3)
theorem kid10_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part328) = true := by rfl

def kid10_part329 : Audit := .split 23 (2,true) (byMove [
.cycle 1 33 true (1),
.cycle 1 30 true (1),
.cycle 49 1 false (1),
.cycle 16 10 true (2),
.cycle 27 4 false (1),
.last 24 (5,true),
.cycle 6 27 true (2),
.cycle 19 33 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 5 19 true (1),
.cycle 34 7 false (2),
.last 24 (5,true),
.cycle 37 9 false (2),
.cycle 32 5 false (1),
.cycle 14 12 true (1),
.cycle 14 10 true (2),
.cycle 27 4 false (1),
.last 24 (5,true),
.cycle 43 15 false (4),
.cycle 38 11 false (3),
.cycle 2 25 true (1),
.cycle 5 19 true (1),
.last 25 (5,true),
.last 24 (5,true)
])
theorem kid10_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part329) = true := by rfl

def kid10_part330 : Audit := .split 19 (2,true) (byMove [
.cycle 1 29 true (1),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.cycle 58 1 false (4),
.cycle 5 17 true (1),
.cycle 16 8 true (1),
.cycle 6 19 true (2),
.cycle 5 19 true (1),
.cycle 46 1 false (10),
.cycle 5 15 true (1),
.cycle 5 27 true (1),
.last 20 (5,true),
.cycle 31 5 false (2),
.cycle 14 12 true (1),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.cycle 19 2 true (2),
.cycle 14 8 true (1),
.cycle 6 19 true (2),
.cycle 16 4 true (3),
.cycle 2 21 true (1),
.cycle 5 15 true (1),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part330) = true := by rfl

def kid10_part331 : Audit := .cycle 5 19 true (1)
theorem kid10_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part331) = true := by rfl

def kid10_part332 : Audit := .split 22 (2,true) (byMove [
.cycle 1 35 true (1),
.cycle 5 31 true (1),
.cycle 36 1 false (0),
.cycle 39 1 false (-1),
.cycle 5 31 true (1),
.cycle 25 3 false (-1),
.cycle 15 8 true (1),
.cycle 102 1 false (12),
.cycle 54 1 false (10),
.cycle 5 27 true (1),
.cycle 19 4 true (1),
.last 23 (5,true),
.last 28 (5,true),
.cycle 28 7 false (0),
.cycle 14 10 true (1),
.cycle 33 1 false (-1),
.cycle 21 2 true (1),
.cycle 25 3 false (-1),
.last 28 (5,true),
.cycle 26 7 false (2),
.cycle 2 25 true (1),
.cycle 28 11 false (4),
.last 24 (5,true),
.last 23 (5,true)
])
theorem kid10_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part332) = true := by rfl

def kid10_part333 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 5 17 true (1),
.cycle 31 1 false (1),
.last 26 (2,true),
.cycle 5 17 true (1),
.cycle 23 1 false (-1),
.cycle 6 19 true (2),
.cycle 29 1 false (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 26 1 false (0),
.cycle 38 1 false (8),
.cycle 31 5 false (2),
.last 21 (2,true),
.cycle 5 23 true (1),
.cycle 28 1 false (0),
.last 21 (2,true),
.cycle 23 1 false (-1),
.cycle 6 19 true (2),
.cycle 16 4 true (3),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 19 2 true (3),
.cycle 21 3 true (5)
])
theorem kid10_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part333) = true := by rfl

def kid10_part334 : Audit := .cycle 6 13 true (2)
theorem kid10_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part334) = true := by rfl

def kid10_part335 : Audit := .cycle 7 15 true (2)
theorem kid10_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part335) = true := by rfl

def kid10_part336 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.last 21 (5,true),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.last 20 (5,true),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
])
theorem kid10_part336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part336) = true := by rfl

def kid10_part337 : Audit := .cycle 1 20 true (1)
theorem kid10_part337_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part337) = true := by rfl

def kid10_part338 : Audit := .split 20 (5,true) (byMove [
.last 23 (2,true),
.last 23 (2,true),
.last 21 (2,true),
.cycle 7 23 true (2),
.cycle 7 35 true (1),
.cycle 1 26 true (1),
.cycle 6 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 4, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.cycle 21 14 true (5),
.cycle 15 6 true (3),
.last 27 (2,true),
.last 21 (2,true),
.cycle 5 23 true (1),
.last 26 (2,true),
.cycle 28 3 false (0),
.cycle 6 15 true (2),
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 19 2 true (4),
.cycle 21 14 true (5)
])
theorem kid10_part338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part338) = true := by rfl

def kid10_part339 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.cycle 7 15 true (2),
.cycle 7 19 true (2),
.cycle 31 1 true (1),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.cycle 21 1 true (7),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.last 20 (2,true),
.cycle 5 15 true (1),
.last 23 (2,true),
.cycle 27 3 false (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 2 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part339_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part339) = true := by rfl

def kid10_part315 : Audit := .split 18 (5,false) (byMove [(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320),(kid10_part321),(kid10_part322),(kid10_part323),(kid10_part324),(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339)])

theorem kid10_part315_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part315) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320),(kid10_part321),(kid10_part322),(kid10_part323),(kid10_part324),(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part316_checked

  · exact kid10_part322_checked

  · exact kid10_part328_checked

  · exact kid10_part334_checked

  · exact kid10_part317_checked

  · exact kid10_part323_checked

  · exact kid10_part329_checked

  · exact kid10_part335_checked

  · exact kid10_part318_checked

  · exact kid10_part324_checked

  · exact kid10_part330_checked

  · exact kid10_part336_checked

  · exact kid10_part319_checked

  · exact kid10_part325_checked

  · exact kid10_part331_checked

  · exact kid10_part337_checked

  · exact kid10_part320_checked

  · exact kid10_part326_checked

  · exact kid10_part332_checked

  · exact kid10_part338_checked

  · exact kid10_part321_checked

  · exact kid10_part327_checked

  · exact kid10_part333_checked

  · exact kid10_part339_checked

def kid10_part340 : Audit := .cycle 1 18 true (1)
theorem kid10_part340_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part340) = true := by rfl

def kid10_part341 : Audit := .cycle 7 11 true (2)
theorem kid10_part341_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part341) = true := by rfl

def kid10_part342 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 34 true (1),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 2 18 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 2 25 true (1),
.last 35 (5,false),
.last 20 (5,false),
.cycle 7 14 true (2),
.cycle 2 23 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 22 (5,false),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.last 20 (5,false)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 25 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 2 25 true (1),
.last 32 (5,true),
.cycle 19 1 true (7),
.cycle 7 14 true (2),
.cycle 18 3 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 3 true (6),
.last 21 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.cycle 19 1 true (7)
]),
.cycle 6 13 true (2),
.cycle 2 19 true (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 17 2 true (5),
.split 19 (5,true) (byMove [
.cycle 21 4 true (4),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 7 21 true (2),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 272, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 16, 4096, 1, 256, 2, 128, 16, 16, 1, 256, 2, 4096],6176⟩,
.last 21 (5,false),
.cycle 0 21 true (0),
.cycle 2 19 true (1),
.last 21 (5,false),
.cycle 2 21 true (1),
.cycle 38 3 false (2),
.cycle 1 22 true (1),
.cycle 2 23 true (1),
.last 22 (5,false),
.last 20 (5,false),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.cycle 2 19 true (1),
.last 21 (5,false)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 26 true (1),
.split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 18 2 true (6),
.cycle 0 21 true (0),
.cycle 2 19 true (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 26 true (1),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 19 1 true (7),
.cycle 6 14 true (2),
.cycle 2 20 true (1),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 27 true (1),
.cycle 19 1 true (7)
])
])
theorem kid10_part342_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part342) = true := by rfl

def kid10_part343 : Audit := .cycle 0 19 true (0)
theorem kid10_part343_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part343) = true := by rfl

def kid10_part344 : Audit := .cycle 18 9 true (6)
theorem kid10_part344_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part344) = true := by rfl

def kid10_part346 : Audit := .cycle 1 19 true (1)
theorem kid10_part346_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part346) = true := by rfl

def kid10_part347 : Audit := .split 34 (2,true) (byMove [
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.cycle 9 26 true (2),
.last 42 (5,false),
.cycle 20 15 true (3),
.last 35 (5,false),
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 4, 16777216, 128, 256, 32768, 128, 16384, 16777216, 128, 256, 2097152, 65536, 1048576, 16777216, 128, 256, 8, 2048, 4, 16777216, 16777216],[128, 16, 4, 1, 2048, 32768, 128, 65536, 16384, 4096, 2048, 1048580, 128, 4194304, 1048576, 262144, 2048, 32768, 128, 16, 4, 1, 2048, 32768, 16777216],27413536⟩,
.cycle 22 13 true (3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 33554816, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 536870912, 256, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 1073741824],[128, 16, 16, 1, 2048, 32768, 128, 65536, 65536, 4096, 2048, 1097732, 33554432, 4194304, 4194304, 262144, 536870912, 32768, 128, 1024, 1024, 64, 2048, 32768, 128, 65536, 65536, 4096, 2048, 256, 1073741824],1889684512⟩,
.last 35 (5,false),
.cycle 7 29 true (2),
.last 39 (5,false),
.cycle 0 37 true (0),
.cycle 11 24 true (2),
.cycle 33 2 true (7),
.last 35 (5,false),
.cycle 0 35 true (0),
.cycle 1 34 true (1),
.cycle 2 33 true (1),
.cycle 1 37 true (1),
.last 44 (5,false),
.last 35 (5,false)
])
theorem kid10_part347_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part347) = true := by rfl

def kid10_part348 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 29 (5,false),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.last 27 (5,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 1, 1, 2, 1],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 33554816, 16384, 1073741824, 33554432, 67108864, 2097152, 65536, 1048576, 1073741824, 128, 256, 512, 536870912, 256, 1073741824, 128, 256, 32768, 128, 16384, 1073741824, 1073741824],[128, 16, 16, 1, 2048, 0, 128, 65536, 65536, 4096, 2048, 34619780, 33554432, 4194304, 4194304, 262144, 536870912, 65536, 128, 1024, 1024, 64, 2048, 536870912, 128, 65536, 65536, 4096, 2048, 256, 1073741824],1889684512⟩,
.last 20 (5,false),
.cycle 7 14 true (2),
.last 24 (5,false),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 19 2 true (4),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 29 (5,false),
.last 20 (5,false)
])
theorem kid10_part348_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part348) = true := by rfl

def kid10_part349 : Audit := .cycle 0 20 true (0)
theorem kid10_part349_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part349) = true := by rfl

def kid10_part350 : Audit := .split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.last 38 (2,true),
.last 21 (2,true),
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
.cycle 19 3 true (5),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 17 4 true (5),
.cycle 0 25 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 19 10 true (5),
.cycle 20 1 true (6)
])
theorem kid10_part350_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part350) = true := by rfl

def kid10_part351 : Audit := .split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.cycle 40 1 false (4),
.last 21 (2,true),
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
.cycle 20 3 true (3),
.last 21 (2,true),
.cycle 1 22 true (1),
.last 26 (2,true),
.cycle 25 1 false (-1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 10 true (4),
.cycle 20 1 true (4)
])
theorem kid10_part351_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part351) = true := by rfl

def kid10_part352 : Audit := .cycle 0 19 true (0)
theorem kid10_part352_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part352) = true := by rfl

def kid10_part353 : Audit := .cycle 1 18 true (1)
theorem kid10_part353_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part353) = true := by rfl

def kid10_part354 : Audit := .split 27 (5,false) (byMove [
.cycle 1 28 true (1),
.last 41 (2,true),
.last 28 (2,true),
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
.cycle 25 3 true (7),
.last 28 (2,true),
.cycle 1 29 true (1),
.cycle 17 11 true (5),
.last 29 (2,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 19 10 true (5),
.cycle 27 1 true (9)
])
theorem kid10_part354_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part354) = true := by rfl

def kid10_part355 : Audit := .cycle 3 16 true (1)
theorem kid10_part355_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part355) = true := by rfl

def kid10_part356 : Audit := .cycle 8 11 true (2)
theorem kid10_part356_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part356) = true := by rfl

def kid10_part357 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 28 2 true (8),
.cycle 31 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 11 true (2),
.cycle 3 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 19 1 true (7),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (2,true),
.cycle 54 1 false (10),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part357_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part357) = true := by rfl

def kid10_part358 : Audit := .cycle 6 13 true (2)
theorem kid10_part358_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part358) = true := by rfl

def kid10_part359 : Audit := .split 21 (5,false) (byMove [
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 4, 8, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 4096, 1, 2048, 4096, 128, 16, 4096, 1, 2048, 2048, 4096],4096⟩,
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 20 2 true (6),
.last 24 (2,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 19 9 true (5),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.cycle 21 1 true (7),
.cycle 6 16 true (2),
.cycle 19 3 true (5),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 17 5 true (5),
.last 24 (2,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 19 10 true (5),
.cycle 21 1 true (7)
])
theorem kid10_part359_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part359) = true := by rfl

def kid10_part360 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 0 23 true (0),
.last 27 (5,false),
.cycle 0 26 true (0),
.cycle 0 23 true (0),
.last 20 (5,false),
.cycle 1 20 true (1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 1, 3, 3],[128, 256, 8, 0, 4, 1073741824, 128, 256, 32768, 524416, 16384, 1073741824, 524288, 1048576, 2097152, 268500992, 1048576, 1073741824, 128, 256, 134217728, 8913024, 67108864, 1073741824, 524288, 1048576, 2097152, 285278208, 1048576, 1073741824, 1073741824],[128, 16, 2, 1, 2048, 1, 128, 65536, 8192, 4096, 2048, 4194320, 524288, 4194304, 524288, 262144, 8388608, 262144, 128, 268435456, 33554432, 16777216, 2048, 285212672, 524288, 4194304, 524288, 262144, 8388608, 262144, 1073741824],1692552224⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 4, 16777216, 128, 256, 32768, 128, 16384, 16777216, 128, 256, 2097152, 65536, 1048576, 16777216, 128, 256, 8, 2048, 4, 16777216, 16777216],[128, 16, 4, 1, 2048, 1, 128, 65536, 16384, 4096, 2048, 1048580, 128, 4194304, 1048576, 262144, 2048, 262144, 128, 16, 4, 1, 2048, 1, 16777216],27413536⟩,
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 0 23 true (0),
.last 23 (5,false),
.cycle 16 6 true (4),
.cycle 1 22 true (1),
.last 25 (5,false),
.cycle 19 2 true (4),
.last 20 (5,false),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.last 21 (5,false),
.cycle 18 2 true (5)
])
theorem kid10_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part360) = true := by rfl

def kid10_part361 : Audit := .cycle 1 20 true (1)
theorem kid10_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part361) = true := by rfl

def kid10_part362 : Audit := .cycle 17 2 true (5)
theorem kid10_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part362) = true := by rfl

def kid10_part363 : Audit := .split 20 (5,false) (byMove [
.last 23 (2,true),
.last 23 (2,true),
.last 21 (2,true),
.cycle 0 27 true (0),
.cycle 20 2 true (3),
.cycle 25 1 false (-1),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 17 4 true (4),
.cycle 19 2 true (4),
.cycle 15 6 true (3),
.last 27 (2,true),
.last 21 (2,true),
.cycle 1 27 true (1),
.last 26 (2,true),
.cycle 25 1 false (-1),
.cycle 6 15 true (2),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 34 5 false (2),
.cycle 29 3 false (1)
])
theorem kid10_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part363) = true := by rfl

def kid10_part364 : Audit := .cycle 0 19 true (0)
theorem kid10_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part364) = true := by rfl

def kid10_part365 : Audit := .cycle 1 18 true (1)
theorem kid10_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part365) = true := by rfl

def kid10_part366 : Audit := .cycle 2 17 true (1)
theorem kid10_part366_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part366) = true := by rfl

def kid10_part367 : Audit := .cycle 1 21 true (1)
theorem kid10_part367_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part367) = true := by rfl

def kid10_part368 : Audit := .split 28 (5,false) (byMove [
.cycle 1 29 true (1),
.cycle 7 37 true (2),
.last 29 (2,true),
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
.cycle 26 3 true (8),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 17 12 true (5),
.cycle 27 3 true (9),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.cycle 19 10 true (6),
.cycle 28 1 true (10)
])
theorem kid10_part368_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part368) = true := by rfl

def kid10_part369 : Audit := .split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
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
.cycle 19 3 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.cycle 18 3 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 10 true (7),
.cycle 19 1 true (7)
])
theorem kid10_part369_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part369) = true := by rfl

def kid10_part345 : Audit := .split 18 (5,true) (byMove [(kid10_part346),(kid10_part347),(kid10_part348),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360),(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369)])

theorem kid10_part345_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part345) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) 18 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part346),(kid10_part347),(kid10_part348),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360),(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part346_checked

  · exact kid10_part352_checked

  · exact kid10_part358_checked

  · exact kid10_part364_checked

  · exact kid10_part347_checked

  · exact kid10_part353_checked

  · exact kid10_part359_checked

  · exact kid10_part365_checked

  · exact kid10_part348_checked

  · exact kid10_part354_checked

  · exact kid10_part360_checked

  · exact kid10_part366_checked

  · exact kid10_part349_checked

  · exact kid10_part355_checked

  · exact kid10_part361_checked

  · exact kid10_part367_checked

  · exact kid10_part350_checked

  · exact kid10_part356_checked

  · exact kid10_part362_checked

  · exact kid10_part368_checked

  · exact kid10_part351_checked

  · exact kid10_part357_checked

  · exact kid10_part363_checked

  · exact kid10_part369_checked

def kid10_part249 : Audit := .split 17 (4,true) (byMove [(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254),(kid10_part255),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part340),(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345)])

theorem kid10_part249_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid10_part249) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254),(kid10_part255),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part340),(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part250_checked

  · exact kid10_part280_checked

  · exact kid10_part310_checked

  · exact kid10_part340_checked

  · exact kid10_part251_checked

  · exact kid10_part281_checked

  · exact kid10_part311_checked

  · exact kid10_part341_checked

  · exact kid10_part252_checked

  · exact kid10_part282_checked

  · exact kid10_part312_checked

  · exact kid10_part342_checked

  · exact kid10_part253_checked

  · exact kid10_part283_checked

  · exact kid10_part313_checked

  · exact kid10_part343_checked

  · exact kid10_part254_checked

  · exact kid10_part284_checked

  · exact kid10_part314_checked

  · exact kid10_part344_checked

  · exact kid10_part255_checked

  · exact kid10_part285_checked

  · exact kid10_part315_checked

  · exact kid10_part345_checked

def kid10_part371 : Audit := .cycle 0 16 true (0)
theorem kid10_part371_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part371) = true := by rfl

def kid10_part372 : Audit := .cycle 1 15 true (1)
theorem kid10_part372_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part372) = true := by rfl

def kid10_part373 : Audit := .cycle 2 14 true (1)
theorem kid10_part373_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part373) = true := by rfl

def kid10_part374 : Audit := .cycle 1 18 true (1)
theorem kid10_part374_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part374) = true := by rfl

def kid10_part375 : Audit := .cycle 3 14 true (1)
theorem kid10_part375_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part375) = true := by rfl

def kid10_part376 : Audit := .split 16 (5,false) (byMove [
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 37 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 32 1 false (2),
.cycle 7 12 true (2),
.cycle 45 1 false (1),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 30 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (3)
]),
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
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 26 1 false (0),
.cycle 0 20 true (0),
.cycle 21 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
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
.split 21 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 40 1 false (2),
.cycle 45 1 false (1),
.cycle 0 23 true (0),
.cycle 25 4 false (1),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 9 14 true (2),
.cycle 3 19 true (1),
.cycle 8 14 true (2),
.cycle 19 3 true (2),
.cycle 6 16 true (2),
.cycle 30 5 false (1),
.cycle 1 25 true (1),
.cycle 1 23 true (1),
.cycle 25 4 false (1),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 3 20 true (1),
.cycle 34 9 false (2)
]),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 29 1 false (1),
.cycle 7 15 true (1),
.cycle 1 18 true (1),
.cycle 49 1 false (9),
.cycle 49 1 false (9),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.last 18 (5,true),
.cycle 29 5 false (2),
.cycle 7 19 true (1),
.cycle 1 20 true (1),
.cycle 26 1 false (0),
.cycle 1 20 true (1),
.cycle 5 15 true (1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true)
]),
.cycle 1 18 true (1),
.cycle 7 15 true (1),
.split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 29 1 false (1),
.cycle 0 25 true (0),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 1 18 true (1),
.cycle 49 1 false (9),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 24 1 false (0),
.cycle 30 1 false (6),
.cycle 29 5 false (2),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 26 1 false (0),
.cycle 1 20 true (1),
.cycle 21 1 false (-1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 3 18 true (1),
.cycle 16 3 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (4)
])
theorem kid10_part376_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part376) = true := by rfl

def kid10_part377 : Audit := .cycle 0 16 true (0)
theorem kid10_part377_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part377) = true := by rfl

def kid10_part378 : Audit := .cycle 1 15 true (1)
theorem kid10_part378_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part378) = true := by rfl

def kid10_part379 : Audit := .split 25 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 9 18 true (2),
.cycle 3 23 true (1),
.cycle 8 18 true (2),
.split 26 (5,false) (byMove [
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 3 25 true (1),
.last 28 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 16 11 true (3),
.cycle 9 18 true (2),
.cycle 17 11 true (3),
.cycle 26 1 true (6),
.cycle 7 21 true (2),
.last 29 (5,true),
.cycle 0 29 true (0),
.cycle 4 23 true (1),
.cycle 0 29 true (0),
.last 28 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 3 25 true (1),
.cycle 26 1 true (6)
]),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 8, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 17 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 8, 64, 64],[2, 16, 16, 1, 4, 64, 64],96⟩,
.split 26 (5,false) (byMove [
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 16 11 true (3),
.cycle 9 18 true (2),
.cycle 17 11 true (3),
.last 30 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.last 39 (5,true),
.last 37 (5,true),
.last 39 (5,true),
.cycle 26 1 true (8),
.cycle 7 21 true (2),
.cycle 25 3 true (7),
.cycle 0 29 true (0),
.cycle 18 9 true (3),
.cycle 0 29 true (0),
.last 30 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 3 25 true (1),
.cycle 26 1 true (8)
]),
.cycle 7 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 8, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.cycle 0 28 true (0),
.split 26 (5,false) (byMove [
.last 30 (5,true),
.cycle 0 30 true (0),
.cycle 10 18 true (2),
.last 32 (5,true),
.cycle 10 18 true (2),
.last 28 (5,true),
.cycle 1 27 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 2, 128, 256, 8, 128, 8, 2, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.cycle 25 2 true (6),
.cycle 0 28 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 16, 128, 256, 8, 128, 8, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.last 27 (5,true),
.cycle 14 14 true (3),
.last 29 (5,true),
.cycle 1 29 true (1),
.cycle 11 16 true (2),
.cycle 1 29 true (1),
.last 28 (5,true),
.cycle 1 27 true (1),
.cycle 7 20 true (2),
.last 28 (5,true),
.cycle 0 28 true (0),
.cycle 9 20 true (2),
.last 27 (5,true)
]),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 3 24 true (1),
.split 26 (5,false) (byMove [
.cycle 1 27 true (1),
.last 39 (5,true),
.cycle 25 2 true (7),
.cycle 0 28 true (0),
.last 39 (5,true),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 9 19 true (2),
.cycle 3 24 true (1),
.cycle 8 19 true (2),
.cycle 26 1 true (8),
.cycle 6 21 true (2),
.last 41 (5,true),
.last 28 (5,true),
.cycle 1 28 true (1),
.cycle 24 3 true (6),
.last 27 (5,true),
.cycle 0 27 true (0),
.cycle 1 26 true (1),
.cycle 2 25 true (1),
.cycle 1 29 true (1),
.cycle 3 25 true (1),
.cycle 26 1 true (8)
])
])
theorem kid10_part379_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part379) = true := by rfl

def kid10_part380 : Audit := .cycle 9 7 true (2)
theorem kid10_part380_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part380) = true := by rfl

def kid10_part381 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 64, 64],[2, 16, 64, 1, 16, 64, 64],96⟩
theorem kid10_part381_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part381) = true := by rfl

def kid10_part382 : Audit := .split 16 (5,false) (byMove [
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
.last 31 (2,true),
.cycle 19 9 true (0),
.cycle 39 1 false (3),
.cycle 25 1 false (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 30 1 false (0),
.cycle 0 22 true (0),
.cycle 23 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.cycle 18 2 true (3)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.split 27 (5,true) (byMove [
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 8 29 true (2),
.cycle 0 31 true (0),
.cycle 1 28 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 16, 64, 1, 32, 2, 64],64⟩,
.last 28 (2,true),
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 14 15 true (3),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 10 25 true (2),
.cycle 1 30 true (1),
.last 29 (2,true),
.cycle 1 28 true (1),
.cycle 7 21 true (2),
.last 28 (2,true),
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
.last 37 (2,true),
.cycle 17 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 20 true (2),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 3 24 true (1),
.cycle 3 24 true (1)
]),
.split 27 (5,true) (byMove [
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 9 29 true (2),
.cycle 0 35 true (0),
.cycle 8 29 true (2),
.cycle 0 31 true (0),
.cycle 1 28 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 16, 64, 1, 32, 2, 64],64⟩,
.last 28 (2,true),
.cycle 0 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 14 15 true (3),
.last 29 (2,true),
.cycle 1 30 true (1),
.cycle 10 25 true (2),
.cycle 1 30 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 1 28 true (1),
.cycle 7 21 true (2),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 3 38 true (1),
.cycle 8 22 true (2)
]),
.cycle 16 1 true (6),
.cycle 7 11 true (2),
.split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.last 29 (5,true),
.cycle 2 18 true (1),
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
.cycle 14 5 true (4),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.last 20 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 14 6 true (4)
]),
.cycle 0 19 true (0),
.cycle 10 7 true (2),
.cycle 0 19 true (0),
.split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 5 17 true (1),
.cycle 60 1 false (4),
.cycle 1 71 true (0),
.cycle 60 1 false (4),
.cycle 23 1 false (-1),
.cycle 13 7 true (3),
.cycle 1 22 true (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 38 1 false (8),
.cycle 38 1 false (8),
.cycle 14 11 true (2),
.last 21 (2,true),
.cycle 12 9 true (2),
.cycle 51 1 false (3),
.cycle 12 9 true (2),
.cycle 23 1 false (-1),
.cycle 13 7 true (3),
.cycle 1 22 true (1),
.last 20 (2,true),
.cycle 5 15 true (1),
.cycle 3 26 true (1),
.cycle 21 3 true (5)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (6)
])
theorem kid10_part382_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part382) = true := by rfl

def kid10_part383 : Audit := .cycle 7 10 true (2)
theorem kid10_part383_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part383) = true := by rfl

def kid10_part384 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.cycle 31 3 false (1),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 35 1 false (3),
.last 20 (5,false),
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
.cycle 32 3 false (1),
.last 20 (5,false),
.cycle 1 20 true (1),
.cycle 7 19 true (1),
.last 20 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
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
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (5,true),
.cycle 9 10 true (2),
.last 30 (5,true),
.cycle 18 1 true (6),
.cycle 7 13 true (2),
.cycle 16 3 true (4),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 0 21 true (0),
.last 20 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 18 1 true (6)
]),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.cycle 31 3 false (1),
.split 18 (5,true) (byMove [
.cycle 16 4 true (3),
.cycle 0 22 true (0),
.last 20 (5,false),
.cycle 7 14 true (2),
.cycle 38 1 false (0),
.last 20 (5,false),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4096, 128, 256, 8, 128, 8, 4096, 4096],[128, 16, 4096, 1, 16, 2, 128, 16, 16, 1, 16, 2, 4096],6176⟩,
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 15 4 true (4),
.last 20 (5,false),
.cycle 13 6 true (3),
.cycle 32 3 false (1),
.last 20 (5,false),
.cycle 5 14 true (1),
.cycle 12 12 true (1),
.last 20 (5,false),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 17 2 true (4),
.cycle 0 20 true (0),
.cycle 14 6 true (4),
.last 20 (5,false)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.split 18 (5,false) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 17 2 true (5),
.cycle 0 20 true (0),
.cycle 14 6 true (4),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 11 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 18 1 true (6),
.cycle 6 13 true (2),
.cycle 14 5 true (4),
.last 20 (5,true),
.cycle 1 20 true (1),
.last 24 (5,true),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 18 1 true (6)
])
])
theorem kid10_part384_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part384) = true := by rfl

def kid10_part385 : Audit := .cycle 0 18 true (0)
theorem kid10_part385_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part385) = true := by rfl

def kid10_part386 : Audit := .cycle 4 12 true (1)
theorem kid10_part386_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part386) = true := by rfl

def kid10_part387 : Audit := .cycle 0 18 true (0)
theorem kid10_part387_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part387) = true := by rfl

def kid10_part389 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 37 1 false (1),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 9 12 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 0 21 true (0),
.cycle 6 14 true (2),
.cycle 14 6 true (3),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 3 18 true (1),
.cycle 1 21 true (1)
])
theorem kid10_part389_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part389) = true := by rfl

def kid10_part390 : Audit := .cycle 0 20 true (0)
theorem kid10_part390_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part390) = true := by rfl

def kid10_part391 : Audit := .split 17 (2,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 37 1 false (1),
.cycle 7 12 true (2),
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 0 20 true (0),
.cycle 32 1 false (2),
.cycle 0 22 true (0),
.cycle 38 1 false (0),
.cycle 7 14 true (2),
.cycle 26 1 false (0),
.cycle 7 14 true (2),
.cycle 30 1 false (0),
.cycle 7 12 true (2),
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (3)
])
theorem kid10_part391_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part391) = true := by rfl

def kid10_part392 : Audit := .cycle 7 12 true (2)
theorem kid10_part392_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part392) = true := by rfl

def kid10_part393 : Audit := .cycle 30 1 false (0)
theorem kid10_part393_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part393) = true := by rfl

def kid10_part394 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 10 10 true (2),
.cycle 29 1 false (1),
.cycle 33 1 false (1),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.cycle 0 20 true (0),
.cycle 23 1 false (1),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 7 14 true (2),
.cycle 26 1 false (0),
.cycle 7 14 true (2),
.cycle 21 1 false (-1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (3)
])
theorem kid10_part394_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part394) = true := by rfl

def kid10_part395 : Audit := .cycle 1 17 true (1)
theorem kid10_part395_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part395) = true := by rfl

def kid10_part396 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 2, 128, 256, 8, 128, 8, 2, 4096],[128, 16, 4096, 1, 16, 4096, 128, 16, 4096, 1, 4096, 4096, 4096],4096⟩
theorem kid10_part396_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part396) = true := by rfl

def kid10_part397 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 9 11 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 8, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 9 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 8, 4, 4096],[128, 16, 16, 1, 16, 4096, 128, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.last 31 (5,true),
.cycle 7 12 true (2),
.cycle 14 6 true (4),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 9 11 true (2)
])
theorem kid10_part397_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part397) = true := by rfl

def kid10_part398 : Audit := .cycle 0 18 true (0)
theorem kid10_part398_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part398) = true := by rfl

def kid10_part399 : Audit := .cycle 15 2 true (4)
theorem kid10_part399_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part399) = true := by rfl

def kid10_part400 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (2,true),
.cycle 9 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 32, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 18 1 true (6),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (6)
])
theorem kid10_part400_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part400) = true := by rfl

def kid10_part401 : Audit := .cycle 13 4 true (3)
theorem kid10_part401_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part401) = true := by rfl

def kid10_part402 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.cycle 1 25 true (1),
.cycle 1 31 true (0),
.cycle 14 10 true (2),
.cycle 25 4 false (1),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 17 26 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 8, 4, 128, 256, 8, 128, 8, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 23 true (1),
.cycle 32 7 false (2),
.last 22 (5,true),
.cycle 35 9 false (2),
.cycle 30 5 false (1),
.cycle 12 12 true (1),
.cycle 12 10 true (2),
.cycle 25 4 false (1),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 36 11 false (3),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid10_part402_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part402) = true := by rfl

def kid10_part403 : Audit := .split 17 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 1 21 true (1),
.cycle 29 1 false (1),
.cycle 1 25 true (0),
.cycle 29 1 false (1),
.cycle 14 8 true (1),
.cycle 6 12 true (2),
.cycle 1 23 true (1),
.cycle 41 1 false (9),
.cycle 1 19 true (1),
.cycle 5 16 true (1),
.last 18 (5,true),
.cycle 29 5 false (2),
.cycle 12 12 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.cycle 12 8 true (1),
.cycle 6 12 true (2),
.cycle 14 4 true (3),
.cycle 2 18 true (1),
.cycle 1 19 true (1),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid10_part403_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part403) = true := by rfl

def kid10_part404 : Audit := .cycle 5 12 true (1)
theorem kid10_part404_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part404) = true := by rfl

def kid10_part405 : Audit := .cycle 12 8 true (1)
theorem kid10_part405_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part405) = true := by rfl

def kid10_part406 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 29 1 false (1),
.cycle 1 25 true (0),
.cycle 29 1 false (1),
.cycle 21 1 false (-1),
.cycle 6 12 true (2),
.cycle 27 1 false (1),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 24 1 false (0),
.cycle 33 1 false (7),
.cycle 29 5 false (2),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 5 14 true (1),
.cycle 21 1 false (-1),
.cycle 6 12 true (2),
.cycle 14 4 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 17 2 true (3),
.cycle 18 3 true (4)
])
theorem kid10_part406_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part406) = true := by rfl

def kid10_part407 : Audit := .cycle 1 17 true (1)
theorem kid10_part407_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part407) = true := by rfl

def kid10_part408 : Audit := .cycle 7 10 true (2)
theorem kid10_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part408) = true := by rfl

def kid10_part409 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 2 17 true (1),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.last 19 (5,true),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 2 17 true (1)
])
theorem kid10_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part409) = true := by rfl

def kid10_part410 : Audit := .cycle 0 18 true (0)
theorem kid10_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part410) = true := by rfl

def kid10_part411 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.last 19 (2,true),
.cycle 7 14 true (2),
.cycle 38 1 false (0),
.cycle 10 12 true (2),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 8, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 15 4 true (4),
.cycle 3 19 true (1),
.cycle 13 6 true (3),
.last 25 (2,true),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 12 12 true (1),
.cycle 26 3 false (0),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 17 2 true (4),
.cycle 3 19 true (1)
])
theorem kid10_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part411) = true := by rfl

def kid10_part412 : Audit := .split 17 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
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
.cycle 14 4 true (4),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 5 16 true (1),
.cycle 25 3 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 18 1 true (6)
])
theorem kid10_part412_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part412) = true := by rfl

def kid10_part388 : Audit := .split 16 (5,false) (byMove [(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398),(kid10_part399),(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409),(kid10_part410),(kid10_part411),(kid10_part412)])

theorem kid10_part388_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part388) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) 16 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398),(kid10_part399),(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409),(kid10_part410),(kid10_part411),(kid10_part412)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part392_checked

  · exact kid10_part398_checked

  · exact kid10_part404_checked

  · exact kid10_part410_checked

  · exact kid10_part393_checked

  · exact kid10_part399_checked

  · exact kid10_part405_checked

  · exact kid10_part411_checked

  · exact kid10_part394_checked

  · exact kid10_part400_checked

  · exact kid10_part406_checked

  · exact kid10_part412_checked

def kid10_part413 : Audit := .cycle 0 16 true (0)
theorem kid10_part413_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part413) = true := by rfl

def kid10_part414 : Audit := .cycle 1 15 true (1)
theorem kid10_part414_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part414) = true := by rfl

def kid10_part415 : Audit := .cycle 2 14 true (1)
theorem kid10_part415_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part415) = true := by rfl

def kid10_part416 : Audit := .cycle 1 18 true (1)
theorem kid10_part416_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part416) = true := by rfl

def kid10_part417 : Audit := .cycle 3 14 true (1)
theorem kid10_part417_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part417) = true := by rfl

def kid10_part418 : Audit := .split 16 (5,false) (byMove [
.cycle 1 17 true (1),
.split 27 (5,true) (byMove [
.cycle 1 28 true (1),
.cycle 17 11 true (3),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 15 13 true (3),
.cycle 47 1 false (3),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 9 20 true (2),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 1 28 true (1),
.cycle 6 22 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2064, 8, 8, 128, 256, 8, 128, 8, 8, 4096],[128, 16, 4096, 1, 2048, 4096, 128, 16, 4096, 1, 2048, 2048, 4096],4096⟩,
.last 28 (2,true),
.cycle 1 29 true (1),
.cycle 26 2 true (6),
.cycle 1 33 true (1),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 3 26 true (1),
.cycle 7 22 true (2)
]),
.split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 41 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (5,true),
.cycle 9 9 true (2),
.last 27 (5,true),
.cycle 9 11 true (2),
.cycle 7 12 true (2),
.cycle 14 6 true (4),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 34 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 16 2 true (5)
]),
.cycle 0 18 true (0),
.cycle 15 2 true (5),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 16 true (1),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 9 20 true (2),
.cycle 9 9 true (2),
.cycle 8 20 true (2),
.cycle 27 1 false (1),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 20 true (0),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
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
.cycle 14 3 true (4),
.split 17 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.cycle 0 24 true (0),
.cycle 10 9 true (2),
.cycle 0 27 true (0),
.cycle 1 18 true (1),
.last 29 (5,true),
.last 29 (5,true),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.last 18 (5,true),
.cycle 14 5 true (4),
.last 22 (5,true),
.cycle 1 20 true (1),
.cycle 11 7 true (2),
.cycle 1 20 true (1),
.last 26 (5,true),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.last 18 (5,true)
]),
.cycle 1 18 true (1),
.split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 17 11 true (3),
.last 19 (2,true),
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
.cycle 14 5 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 17 2 true (5),
.cycle 17 12 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 16 3 true (5)
]),
.split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 10 9 true (2),
.last 22 (2,true),
.cycle 10 9 true (2),
.cycle 23 1 false (-1),
.cycle 1 18 true (1),
.cycle 1 40 true (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.cycle 45 1 false (9),
.cycle 14 5 true (4),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 11 7 true (2),
.cycle 1 20 true (1),
.cycle 23 1 false (-1),
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 15 3 true (5),
.cycle 16 3 true (5)
]),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 1 19 true (1),
.cycle 3 15 true (1),
.cycle 16 1 true (6)
])
theorem kid10_part418_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part418) = true := by rfl

def kid10_part370 : Audit := .split 15 (4,true) (byMove [(kid10_part371),(kid10_part372),(kid10_part373),(kid10_part374),(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part413),(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418)])

theorem kid10_part370_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid10_part370) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) 15 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (4,true) (some mv)) (byMove [(kid10_part371),(kid10_part372),(kid10_part373),(kid10_part374),(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part413),(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part371_checked

  · exact kid10_part377_checked

  · exact kid10_part383_checked

  · exact kid10_part413_checked

  · exact kid10_part372_checked

  · exact kid10_part378_checked

  · exact kid10_part384_checked

  · exact kid10_part414_checked

  · exact kid10_part373_checked

  · exact kid10_part379_checked

  · exact kid10_part385_checked

  · exact kid10_part415_checked

  · exact kid10_part374_checked

  · exact kid10_part380_checked

  · exact kid10_part386_checked

  · exact kid10_part416_checked

  · exact kid10_part375_checked

  · exact kid10_part381_checked

  · exact kid10_part387_checked

  · exact kid10_part417_checked

  · exact kid10_part376_checked

  · exact kid10_part382_checked

  · exact kid10_part388_checked

  · exact kid10_part418_checked

def kid10_part419 : Audit := .cycle 8 1 true (4)
theorem kid10_part419_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid10_part419) = true := by rfl

def kid10_part421 : Audit := .cycle 0 10 true (0)
theorem kid10_part421_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part421) = true := by rfl

def kid10_part422 : Audit := .cycle 1 9 true (1)
theorem kid10_part422_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part422) = true := by rfl

def kid10_part423 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 2 18 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 37 1 false (3),
.cycle 34 1 false (2),
.cycle 7 14 true (2),
.cycle 49 1 false (1),
.cycle 0 22 true (0),
.cycle 28 1 false (0),
.last 21 (5,true),
.cycle 32 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.cycle 18 2 true (3)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (2),
.cycle 3 25 true (1),
.cycle 8 20 true (2),
.cycle 2 27 true (1),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 30, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 19 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 54, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.cycle 18 11 true (3),
.cycle 7 22 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 30, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (2),
.last 29 (5,true),
.cycle 12 18 true (2),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 2 28 true (1),
.cycle 27 2 true (7)
]),
.cycle 11 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 16, 128, 256, 8, 128, 32, 4096, 4096],[128, 16, 4096, 1, 16, 4096, 128, 16, 4096, 1, 16, 4096, 4096],6144⟩,
.cycle 9 9 true (2),
.cycle 7 12 true (2),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 35 1 false (1),
.cycle 0 21 true (0),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (2),
.cycle 3 17 true (1),
.cycle 8 12 true (2),
.cycle 2 19 true (1),
.cycle 6 14 true (2),
.cycle 16 4 true (4),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.cycle 19 2 true (5)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 31 (2,true),
.cycle 11 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 16, 128, 256, 8, 128, 32, 4096, 4096],[128, 16, 4096, 1, 16, 16, 128, 16, 4096, 1, 16, 16, 4096],6144⟩,
.cycle 9 11 true (2),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.last 21 (2,true)
]),
.split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 10 true (2),
.cycle 31 1 false (1),
.cycle 37 1 false (1),
.cycle 35 1 false (1),
.cycle 41 1 false (1),
.cycle 7 14 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.last 21 (5,true),
.cycle 34 1 false (2),
.last 23 (5,true),
.cycle 40 1 false (0),
.cycle 7 16 true (2),
.cycle 28 1 false (0),
.last 21 (5,true),
.cycle 32 1 false (0),
.cycle 7 14 true (2),
.cycle 1 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 18 2 true (3)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 2 18 true (1),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.cycle 45 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (5,true),
.cycle 11 9 true (2),
.last 31 (5,true),
.cycle 9 11 true (2),
.cycle 7 14 true (2),
.cycle 16 6 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 36 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 20 true (1),
.cycle 18 2 true (5)
])
])
theorem kid10_part423_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part423) = true := by rfl

def kid10_part424 : Audit := .cycle 3 7 true (1)
theorem kid10_part424_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part424) = true := by rfl

def kid10_part425 : Audit := .cycle 8 2 true (4)
theorem kid10_part425_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part425) = true := by rfl

def kid10_part426 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.last 26 (2,true),
.cycle 27 1 false (3),
.cycle 25 1 false (3),
.cycle 1 22 true (0),
.cycle 31 1 false (3),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 31 1 false (3),
.last 34 (2,true),
.cycle 23 15 true (2),
.last 23 (2,true),
.cycle 1 24 true (0),
.cycle 37 1 false (5),
.last 24 (2,true),
.cycle 1 26 true (0),
.cycle 1 22 true (0),
.cycle 7 15 true (0),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 10 26 true (0),
.cycle 11 20 true (0)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (3),
.cycle 1 22 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 62, 64],[2, 16, 64, 1, 2, 8, 64],64⟩,
.last 29 (2,true),
.cycle 13 7 true (0),
.cycle 26 1 false (2),
.cycle 24 1 false (2),
.cycle 37 1 false (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 12 9 true (0),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.last 39 (2,true),
.cycle 1 22 true (0),
.cycle 10 11 true (0),
.cycle 11 9 true (0)
]),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.cycle 21 7 false (3),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 22 (4,true),
.cycle 3 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.cycle 1 31 true (-1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 20 (4,true),
.last 18 (4,true)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 12 2 true (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (2)
])
theorem kid10_part426_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part426) = true := by rfl

def kid10_part427 : Audit := .cycle 0 10 true (0)
theorem kid10_part427_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part427) = true := by rfl

def kid10_part428 : Audit := .cycle 1 9 true (1)
theorem kid10_part428_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part428) = true := by rfl

def kid10_part430 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.last 25 (5,true),
.last 43 (5,true),
.cycle 7 18 true (2),
.cycle 0 28 true (0),
.last 23 (5,true),
.cycle 1 23 true (1),
.cycle 0 42 true (0),
.cycle 0 44 true (0),
.cycle 0 24 true (0),
.cycle 0 24 true (0),
.last 23 (5,true),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 0 42 true (0),
.cycle 5 18 true (1),
.cycle 21 4 true (4),
.last 23 (5,true),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.cycle 1 24 true (1),
.last 23 (5,true)
])
theorem kid10_part430_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part430) = true := by rfl

def kid10_part431 : Audit := .cycle 1 23 true (1)
theorem kid10_part431_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part431) = true := by rfl

def kid10_part432 : Audit := .cycle 2 32 true (1)
theorem kid10_part432_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part432) = true := by rfl

def kid10_part433 : Audit := .split 24 (2,true) (byMove [
.cycle 1 28 true (1),
.last 27 (5,true),
.cycle 44 1 false (2),
.cycle 7 20 true (2),
.cycle 0 32 true (0),
.last 25 (5,true),
.cycle 1 25 true (1),
.cycle 3 43 true (1),
.cycle 1 50 true (1),
.cycle 0 26 true (0),
.cycle 1 28 true (1),
.last 25 (5,true),
.cycle 1 30 true (1),
.cycle 1 36 true (1),
.cycle 1 34 true (1),
.cycle 5 20 true (1),
.cycle 1 32 true (1),
.last 25 (5,true),
.cycle 1 25 true (1),
.cycle 7 18 true (2),
.cycle 2 24 true (1),
.cycle 0 26 true (0),
.cycle 0 27 true (0),
.last 25 (5,true)
])
theorem kid10_part433_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part433) = true := by rfl

def kid10_part434 : Audit := .split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.cycle 0 26 true (0),
.cycle 24 22 true (3),
.last 29 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 60, 1, 60, 4096, 4096],4096⟩,
.cycle 0 26 true (0),
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 22, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 2, 1, 4, 4096, 128, 16, 2, 1, 318, 4096, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 60, 4096, 4096],4096⟩,
.cycle 0 24 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 16, 1, 60, 4096, 4096],4096⟩,
.last 23 (5,true),
.cycle 7 34 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 60, 4096, 4096],4096⟩,
.cycle 1 25 true (1),
.cycle 23 20 true (3),
.last 24 (5,true),
.cycle 21 2 true (5),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.cycle 8 17 true (2),
.last 23 (5,true)
])
theorem kid10_part434_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part434) = true := by rfl

def kid10_part435 : Audit := .cycle 1 23 true (1)
theorem kid10_part435_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part435) = true := by rfl

def kid10_part436 : Audit := .cycle 6 14 true (2)
theorem kid10_part436_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part436) = true := by rfl

def kid10_part437 : Audit := .cycle 1 21 true (1)
theorem kid10_part437_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part437) = true := by rfl

def kid10_part438 : Audit := .split 20 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 0 24 true (0),
.cycle 22 18 true (3),
.last 27 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 31, 32, 4, 64],[2, 16, 12, 1, 4, 64, 64],64⟩,
.cycle 0 24 true (0),
.cycle 1 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 2, 1, 4, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.last 21 (5,true),
.cycle 7 28 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 1 23 true (1),
.cycle 21 16 true (3),
.last 22 (5,true),
.cycle 20 2 true (5),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.cycle 30 12 true (7),
.last 21 (5,true)
])
theorem kid10_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part438) = true := by rfl

def kid10_part439 : Audit := .cycle 1 21 true (1)
theorem kid10_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part439) = true := by rfl

def kid10_part440 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 4, 64],[2, 16, 64, 1, 16, 64, 64],64⟩
theorem kid10_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part440) = true := by rfl

def kid10_part441 : Audit := .split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 9 29 true (2),
.cycle 3 25 true (1),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 1 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 2, 64],64⟩,
.last 21 (2,true),
.cycle 0 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 9 15 true (2),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 9 25 true (2),
.cycle 20 2 true (5),
.last 22 (2,true),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 12 true (6),
.cycle 9 22 true (2)
])
theorem kid10_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part441) = true := by rfl

def kid10_part442 : Audit := .cycle 7 20 true (2)
theorem kid10_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part442) = true := by rfl

def kid10_part443 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.last 24 (5,true),
.cycle 37 1 false (1),
.cycle 0 29 true (0),
.cycle 35 3 false (1),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 10 14 true (2),
.cycle 1 23 true (1),
.cycle 8 20 true (2),
.last 22 (5,true),
.cycle 6 26 true (2),
.cycle 18 4 true (4),
.cycle 5 38 true (1),
.cycle 1 29 true (1),
.cycle 35 3 false (1),
.last 22 (5,true),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.cycle 23 18 true (5),
.last 22 (5,true)
])
theorem kid10_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part443) = true := by rfl

def kid10_part444 : Audit := .cycle 5 16 true (1)
theorem kid10_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part444) = true := by rfl

def kid10_part445 : Audit := .cycle 4 26 true (1)
theorem kid10_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part445) = true := by rfl

def kid10_part446 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 2 38 true (1),
.last 26 (2,true),
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 4, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 26 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 4 32 true (1),
.cycle 20 2 true (4),
.last 23 (2,true),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 19 4 true (4),
.cycle 23 11 true (7)
])
theorem kid10_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part446) = true := by rfl

def kid10_part447 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (1),
.cycle 1 25 true (1),
.cycle 2 38 true (1),
.cycle 7 22 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4104, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 25 true (1),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 16, 1, 16, 4096, 128, 16, 16, 1, 4096, 4096, 4096],4096⟩,
.last 22 (5,true),
.cycle 7 26 true (2),
.cycle 18 6 true (4),
.cycle 5 18 true (1),
.cycle 4 32 true (1),
.last 23 (5,true),
.cycle 20 2 true (4),
.cycle 6 16 true (2),
.cycle 1 25 true (1),
.cycle 2 22 true (1),
.cycle 1 23 true (1),
.last 23 (5,true),
.last 22 (5,true)
])
theorem kid10_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part447) = true := by rfl

def kid10_part448 : Audit := .cycle 6 14 true (2)
theorem kid10_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part448) = true := by rfl

def kid10_part449 : Audit := .cycle 1 21 true (1)
theorem kid10_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part449) = true := by rfl

def kid10_part450 : Audit := .split 20 (2,true) (byMove [
.cycle 1 24 true (1),
.last 23 (5,true),
.last 29 (5,true),
.cycle 7 16 true (2),
.cycle 0 24 true (0),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 2 36 true (1),
.cycle 2 38 true (1),
.cycle 0 22 true (0),
.cycle 2 20 true (1),
.last 21 (5,true),
.cycle 2 22 true (1),
.cycle 2 24 true (1),
.cycle 5 18 true (1),
.cycle 5 16 true (1),
.cycle 19 2 true (5),
.last 21 (5,true),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 2 20 true (1),
.cycle 0 22 true (0),
.cycle 2 20 true (1),
.last 21 (5,true)
])
theorem kid10_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part450) = true := by rfl

def kid10_part451 : Audit := .cycle 1 21 true (1)
theorem kid10_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part451) = true := by rfl

def kid10_part452 : Audit := .cycle 20 12 true (6)
theorem kid10_part452_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part452) = true := by rfl

def kid10_part453 : Audit := .split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 1 23 true (1),
.last 21 (2,true),
.cycle 7 16 true (2),
.last 23 (2,true),
.cycle 33 9 true (4),
.cycle 1 21 true (1),
.cycle 36 9 true (10),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 21 9 true (7),
.cycle 9 13 true (2),
.cycle 21 9 true (5),
.cycle 24 9 true (6),
.last 21 (2,true),
.cycle 5 16 true (1),
.cycle 19 2 true (5),
.last 23 (2,true),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 21 9 true (7),
.cycle 22 9 true (7)
])
theorem kid10_part453_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part453) = true := by rfl

def kid10_part429 : Audit := .split 19 (4,true) (byMove [(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437),(kid10_part438),(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450),(kid10_part451),(kid10_part452),(kid10_part453)])

theorem kid10_part429_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part429) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) 19 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (4,true) (some mv)) (byMove [(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437),(kid10_part438),(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450),(kid10_part451),(kid10_part452),(kid10_part453)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part430_checked

  · exact kid10_part436_checked

  · exact kid10_part442_checked

  · exact kid10_part448_checked

  · exact kid10_part431_checked

  · exact kid10_part437_checked

  · exact kid10_part443_checked

  · exact kid10_part449_checked

  · exact kid10_part432_checked

  · exact kid10_part438_checked

  · exact kid10_part444_checked

  · exact kid10_part450_checked

  · exact kid10_part433_checked

  · exact kid10_part439_checked

  · exact kid10_part445_checked

  · exact kid10_part451_checked

  · exact kid10_part434_checked

  · exact kid10_part440_checked

  · exact kid10_part446_checked

  · exact kid10_part452_checked

  · exact kid10_part435_checked

  · exact kid10_part441_checked

  · exact kid10_part447_checked

  · exact kid10_part453_checked

def kid10_part455 : Audit := .split 20 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.cycle 0 32 true (0),
.cycle 0 22 true (0),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 0 29 true (0),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 0 29 true (0),
.cycle 6 15 true (2),
.cycle 0 23 true (0),
.cycle 0 29 true (0),
.cycle 1 22 true (1),
.cycle 19 4 true (4),
.last 21 (5,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 0 30 true (0),
.cycle 3 19 true (1)
])
theorem kid10_part455_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part455) = true := by rfl

def kid10_part456 : Audit := .cycle 0 21 true (0)
theorem kid10_part456_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part456) = true := by rfl

def kid10_part457 : Audit := .cycle 2 23 true (1)
theorem kid10_part457_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part457) = true := by rfl

def kid10_part458 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 42 1 false (2),
.cycle 0 24 true (0),
.cycle 0 25 true (0),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 1 33 true (1),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.cycle 1 33 true (1),
.cycle 6 17 true (2),
.cycle 1 27 true (1),
.cycle 5 21 true (1),
.cycle 1 24 true (1),
.cycle 7 19 true (2),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 1 34 true (1),
.cycle 3 21 true (1)
])
theorem kid10_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part458) = true := by rfl

def kid10_part459 : Audit := .cycle 0 21 true (0)
theorem kid10_part459_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part459) = true := by rfl

def kid10_part460 : Audit := .cycle 3 23 true (1)
theorem kid10_part460_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part460) = true := by rfl

def kid10_part461 : Audit := .cycle 1 18 true (1)
theorem kid10_part461_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part461) = true := by rfl

def kid10_part462 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 8, 64],[2, 16, 64, 1, 2, 64, 64],64⟩
theorem kid10_part462_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part462) = true := by rfl

def kid10_part463 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 10 18 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 10 18 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.last 30 (5,true),
.cycle 7 13 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 10 16 true (2),
.last 20 (5,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 10 19 true (2),
.cycle 3 17 true (1)
])
theorem kid10_part463_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part463) = true := by rfl

def kid10_part464 : Audit := .cycle 0 19 true (0)
theorem kid10_part464_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part464) = true := by rfl

def kid10_part465 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 8, 64],[2, 16, 64, 1, 16, 64, 64],64⟩
theorem kid10_part465_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part465) = true := by rfl

def kid10_part466 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 9 18 true (2),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 9 18 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 30 (2,true),
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 9 16 true (2),
.cycle 18 2 true (5),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 9 19 true (2),
.cycle 3 17 true (1)
])
theorem kid10_part466_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part466) = true := by rfl

def kid10_part467 : Audit := .cycle 7 15 true (2)
theorem kid10_part467_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part467) = true := by rfl

def kid10_part468 : Audit := .split 19 (2,true) (byMove [
.cycle 1 23 true (1),
.last 22 (5,true),
.cycle 35 1 false (1),
.cycle 7 15 true (2),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 1 37 true (1),
.cycle 10 12 true (2),
.cycle 0 21 true (0),
.cycle 8 15 true (2),
.last 20 (5,true),
.cycle 6 19 true (2),
.cycle 16 4 true (4),
.cycle 5 27 true (1),
.cycle 5 15 true (1),
.cycle 33 3 false (1),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 19 true (1),
.cycle 0 21 true (0),
.cycle 21 11 true (5),
.last 20 (5,true)
])
theorem kid10_part468_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part468) = true := by rfl

def kid10_part469 : Audit := .cycle 1 20 true (1)
theorem kid10_part469_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part469) = true := by rfl

def kid10_part470 : Audit := .cycle 4 19 true (1)
theorem kid10_part470_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part470) = true := by rfl

def kid10_part471 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 27 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 3 27 true (1),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 8, 64],[2, 16, 64, 1, 18, 2, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 8, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 7 19 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 23 true (1),
.cycle 18 2 true (4),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 17 4 true (4),
.cycle 3 19 true (1)
])
theorem kid10_part471_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part471) = true := by rfl

def kid10_part472 : Audit := .cycle 1 20 true (1)
theorem kid10_part472_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part472) = true := by rfl

def kid10_part473 : Audit := .cycle 1 18 true (1)
theorem kid10_part473_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part473) = true := by rfl

def kid10_part474 : Audit := .cycle 7 11 true (2)
theorem kid10_part474_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part474) = true := by rfl

def kid10_part475 : Audit := .split 18 (2,true) (byMove [
.cycle 1 19 true (1),
.last 34 (5,true),
.cycle 2 18 true (1),
.cycle 0 20 true (0),
.cycle 2 18 true (1),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 25 true (1),
.cycle 3 16 true (1),
.cycle 8 11 true (2),
.cycle 2 25 true (1),
.cycle 6 13 true (2),
.cycle 2 19 true (1),
.cycle 1 22 true (1),
.cycle 1 20 true (1),
.cycle 17 2 true (5),
.last 19 (5,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 26 true (1),
.cycle 3 17 true (1)
])
theorem kid10_part475_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part475) = true := by rfl

def kid10_part476 : Audit := .cycle 0 19 true (0)
theorem kid10_part476_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part476) = true := by rfl

def kid10_part477 : Audit := .cycle 18 9 true (6)
theorem kid10_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part477) = true := by rfl

def kid10_part478 : Audit := .split 18 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 34 true (1),
.last 19 (2,true),
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
.cycle 3 19 true (1),
.last 19 (2,true),
.cycle 1 20 true (1),
.cycle 17 2 true (5),
.cycle 1 22 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 26 true (1),
.cycle 3 17 true (1)
])
theorem kid10_part478_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part478) = true := by rfl

def kid10_part454 : Audit := .split 17 (4,true) (byMove [(kid10_part455),(kid10_part456),(kid10_part457),(kid10_part458),(kid10_part459),(kid10_part460),(kid10_part461),(kid10_part462),(kid10_part463),(kid10_part464),(kid10_part465),(kid10_part466),(kid10_part467),(kid10_part468),(kid10_part469),(kid10_part470),(kid10_part471),(kid10_part472),(kid10_part473),(kid10_part474),(kid10_part475),(kid10_part476),(kid10_part477),(kid10_part478)])

theorem kid10_part454_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part454) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) 17 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (4,true) (some mv)) (byMove [(kid10_part455),(kid10_part456),(kid10_part457),(kid10_part458),(kid10_part459),(kid10_part460),(kid10_part461),(kid10_part462),(kid10_part463),(kid10_part464),(kid10_part465),(kid10_part466),(kid10_part467),(kid10_part468),(kid10_part469),(kid10_part470),(kid10_part471),(kid10_part472),(kid10_part473),(kid10_part474),(kid10_part475),(kid10_part476),(kid10_part477),(kid10_part478)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part455_checked

  · exact kid10_part461_checked

  · exact kid10_part467_checked

  · exact kid10_part473_checked

  · exact kid10_part456_checked

  · exact kid10_part462_checked

  · exact kid10_part468_checked

  · exact kid10_part474_checked

  · exact kid10_part457_checked

  · exact kid10_part463_checked

  · exact kid10_part469_checked

  · exact kid10_part475_checked

  · exact kid10_part458_checked

  · exact kid10_part464_checked

  · exact kid10_part470_checked

  · exact kid10_part476_checked

  · exact kid10_part459_checked

  · exact kid10_part465_checked

  · exact kid10_part471_checked

  · exact kid10_part477_checked

  · exact kid10_part460_checked

  · exact kid10_part466_checked

  · exact kid10_part472_checked

  · exact kid10_part478_checked

def kid10_part479 : Audit := .cycle 8 2 true (4)
theorem kid10_part479_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part479) = true := by rfl

def kid10_part480 : Audit := .cycle 9 1 true (5)
theorem kid10_part480_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part480) = true := by rfl

def kid10_part481 : Audit := .cycle 7 4 true (3)
theorem kid10_part481_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part481) = true := by rfl

def kid10_part483 : Audit := .cycle 1 12 true (1)
theorem kid10_part483_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part483) = true := by rfl

def kid10_part484 : Audit := .cycle 7 5 true (3)
theorem kid10_part484_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part484) = true := by rfl

def kid10_part485 : Audit := .cycle 2 11 true (1)
theorem kid10_part485_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part485) = true := by rfl

def kid10_part486 : Audit := .cycle 0 13 true (0)
theorem kid10_part486_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part486) = true := by rfl

def kid10_part487 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 24 5 false (0),
.last 20 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 12 7 true (2),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 7 7 true (3),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.last 20 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.cycle 12 3 true (4)
])
theorem kid10_part487_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part487) = true := by rfl

def kid10_part488 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 18 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 7 7 true (3),
.last 17 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 12 2 true (3),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 5 true (4),
.last 15 (4,true)
])
theorem kid10_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part488) = true := by rfl

def kid10_part489 : Audit := .cycle 0 12 true (0)
theorem kid10_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part489) = true := by rfl

def kid10_part490 : Audit := .cycle 1 11 true (1)
theorem kid10_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part490) = true := by rfl

def kid10_part491 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 9 14 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 13 7 true (4),
.cycle 8 12 true (4),
.cycle 9 11 true (4),
.cycle 7 14 true (3),
.cycle 10 10 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 18 3 true (6)
])
theorem kid10_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part491) = true := by rfl

def kid10_part492 : Audit := .cycle 3 9 true (1)
theorem kid10_part492_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part492) = true := by rfl

def kid10_part493 : Audit := .cycle 8 4 true (4)
theorem kid10_part493_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part493) = true := by rfl

def kid10_part494 : Audit := .cycle 9 3 true (4)
theorem kid10_part494_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part494) = true := by rfl

def kid10_part495 : Audit := .cycle 6 6 true (2)
theorem kid10_part495_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part495) = true := by rfl

def kid10_part496 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 20 true (1),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 28 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 23 true (0),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 7 8 true (3),
.cycle 10 4 true (4),
.cycle 0 16 true (0),
.cycle 4 16 true (1),
.last 15 (5,true),
.cycle 28 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid10_part496_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part496) = true := by rfl

def kid10_part497 : Audit := .cycle 1 15 true (1)
theorem kid10_part497_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part497) = true := by rfl

def kid10_part498 : Audit := .cycle 1 13 true (1)
theorem kid10_part498_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part498) = true := by rfl

def kid10_part499 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (3),
.cycle 0 16 true (0),
.cycle 2 18 true (1),
.cycle 7 14 true (2),
.cycle 24 5 false (0),
.last 20 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true),
.cycle 7 10 true (3),
.cycle 25 3 false (1),
.cycle 1 15 true (1),
.cycle 4 14 true (1),
.last 14 (5,true),
.last 20 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.cycle 8 6 true (4),
.last 13 (5,true)
])
theorem kid10_part499_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part499) = true := by rfl

def kid10_part500 : Audit := .split 12 (5,true) (byMove [
.cycle 14 4 true (3),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 7 14 true (2),
.last 18 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 9 5 true (4),
.last 15 (4,true),
.last 17 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 12 2 true (3),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part500_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part500) = true := by rfl

def kid10_part501 : Audit := .cycle 0 12 true (0)
theorem kid10_part501_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part501) = true := by rfl

def kid10_part502 : Audit := .cycle 1 11 true (1)
theorem kid10_part502_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part502) = true := by rfl

def kid10_part503 : Audit := .cycle 2 10 true (1)
theorem kid10_part503_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part503) = true := by rfl

def kid10_part504 : Audit := .cycle 1 14 true (1)
theorem kid10_part504_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part504) = true := by rfl

def kid10_part505 : Audit := .cycle 8 4 true (4)
theorem kid10_part505_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part505) = true := by rfl

def kid10_part506 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (4),
.cycle 36 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 40 (5,true),
.cycle 13 7 true (4),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 7 9 true (3),
.cycle 10 5 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.last 21 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid10_part506_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part506) = true := by rfl

def kid10_part482 : Audit := .split 11 (2,true) (byMove [(kid10_part483),(kid10_part484),(kid10_part485),(kid10_part486),(kid10_part487),(kid10_part488),(kid10_part489),(kid10_part490),(kid10_part491),(kid10_part492),(kid10_part493),(kid10_part494),(kid10_part495),(kid10_part496),(kid10_part497),(kid10_part498),(kid10_part499),(kid10_part500),(kid10_part501),(kid10_part502),(kid10_part503),(kid10_part504),(kid10_part505),(kid10_part506)])

theorem kid10_part482_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part482) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid10_part483),(kid10_part484),(kid10_part485),(kid10_part486),(kid10_part487),(kid10_part488),(kid10_part489),(kid10_part490),(kid10_part491),(kid10_part492),(kid10_part493),(kid10_part494),(kid10_part495),(kid10_part496),(kid10_part497),(kid10_part498),(kid10_part499),(kid10_part500),(kid10_part501),(kid10_part502),(kid10_part503),(kid10_part504),(kid10_part505),(kid10_part506)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part483_checked

  · exact kid10_part489_checked

  · exact kid10_part495_checked

  · exact kid10_part501_checked

  · exact kid10_part484_checked

  · exact kid10_part490_checked

  · exact kid10_part496_checked

  · exact kid10_part502_checked

  · exact kid10_part485_checked

  · exact kid10_part491_checked

  · exact kid10_part497_checked

  · exact kid10_part503_checked

  · exact kid10_part486_checked

  · exact kid10_part492_checked

  · exact kid10_part498_checked

  · exact kid10_part504_checked

  · exact kid10_part487_checked

  · exact kid10_part493_checked

  · exact kid10_part499_checked

  · exact kid10_part505_checked

  · exact kid10_part488_checked

  · exact kid10_part494_checked

  · exact kid10_part500_checked

  · exact kid10_part506_checked

def kid10_part507 : Audit := .cycle 0 12 true (0)
theorem kid10_part507_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part507) = true := by rfl

def kid10_part508 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 4 14 true (1),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.split 25 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 10 18 true (2),
.cycle 3 23 true (1),
.cycle 8 18 true (2),
.cycle 4 23 true (1),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 22, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 17 9 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 22, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.cycle 18 9 true (3),
.cycle 7 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 22, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 28 true (0),
.cycle 10 16 true (2),
.last 27 (5,true),
.cycle 11 16 true (2),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 4 24 true (1),
.cycle 1 28 true (1)
]),
.cycle 10 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 16, 64, 64],64⟩,
.cycle 9 7 true (2),
.cycle 7 10 true (2),
.split 17 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 7 11 true (2),
.cycle 33 1 false (1),
.cycle 0 19 true (0),
.cycle 31 3 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 10 10 true (2),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 4 15 true (1),
.cycle 6 12 true (2),
.cycle 14 4 true (4),
.cycle 5 16 true (1),
.cycle 1 19 true (1),
.cycle 31 3 false (1),
.last 18 (5,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1),
.cycle 1 20 true (1)
]),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1),
.cycle 1 20 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 29 (2,true),
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 9 true (2),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 5 14 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 4 16 true (1),
.cycle 1 20 true (1)
]),
.cycle 5 12 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 4 14 true (1),
.cycle 1 18 true (1)
])
theorem kid10_part508_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part508) = true := by rfl

def kid10_part510 : Audit := .cycle 0 12 true (0)
theorem kid10_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part510) = true := by rfl

def kid10_part511 : Audit := .cycle 1 11 true (1)
theorem kid10_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part511) = true := by rfl

def kid10_part512 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 22 true (1),
.cycle 47 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 29 (2,true),
.cycle 13 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 16, 128, 256, 8, 128, 32, 16, 4096],[128, 16, 4096, 1, 16, 16, 128, 16, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 9 11 true (2),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 2 20 true (1),
.cycle 38 1 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 22 true (1),
.last 23 (2,true)
])
theorem kid10_part512_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part512) = true := by rfl

def kid10_part513 : Audit := .cycle 3 9 true (1)
theorem kid10_part513_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part513) = true := by rfl

def kid10_part514 : Audit := .cycle 8 4 true (4)
theorem kid10_part514_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part514) = true := by rfl

def kid10_part515 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 40 1 false (2),
.last 21 (2,true),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 1 17 true (1),
.cycle 35 3 false (3),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 35 3 false (3),
.cycle 23 3 false (1),
.cycle 18 14 true (1),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 35 1 false (1),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 12 7 true (2),
.cycle 22 3 false (0)
])
theorem kid10_part515_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part515) = true := by rfl

def kid10_part516 : Audit := .cycle 0 12 true (0)
theorem kid10_part516_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part516) = true := by rfl

def kid10_part517 : Audit := .cycle 1 11 true (1)
theorem kid10_part517_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part517) = true := by rfl

def kid10_part518 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.last 26 (2,true),
.last 26 (2,true),
.cycle 0 39 true (0),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 20, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 23 (2,true),
.cycle 7 22 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.last 24 (2,true),
.last 27 (2,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 22 (2,true),
.cycle 1 23 true (1),
.cycle 22 14 true (6),
.last 23 (2,true)
])
theorem kid10_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part518) = true := by rfl

def kid10_part519 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 37 1 false (1),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 24, 64],[2, 16, 64, 1, 2, 8, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 24, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 11 9 true (2),
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.cycle 0 23 true (0),
.cycle 5 29 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.cycle 3 18 true (1)
])
theorem kid10_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part519) = true := by rfl

def kid10_part520 : Audit := .cycle 8 4 true (4)
theorem kid10_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part520) = true := by rfl

def kid10_part521 : Audit := .cycle 9 3 true (4)
theorem kid10_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part521) = true := by rfl

def kid10_part522 : Audit := .cycle 7 6 true (3)
theorem kid10_part522_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part522) = true := by rfl

def kid10_part523 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.last 15 (4,true)
])
theorem kid10_part523_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part523) = true := by rfl

def kid10_part524 : Audit := .cycle 0 14 true (0)
theorem kid10_part524_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part524) = true := by rfl

def kid10_part525 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 4 18 true (1),
.cycle 40 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 12 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.cycle 9 9 true (2),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 4 16 true (1),
.cycle 33 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 4 18 true (1),
.cycle 1 22 true (1)
])
theorem kid10_part525_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part525) = true := by rfl

def kid10_part526 : Audit := .cycle 10 2 true (4)
theorem kid10_part526_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part526) = true := by rfl

def kid10_part527 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 54 1 false (4),
.last 21 (2,true),
.cycle 24 3 false (0),
.cycle 19 3 false (-1),
.cycle 0 20 true (0),
.cycle 49 3 false (9),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 49 3 false (9),
.cycle 23 3 false (1),
.cycle 18 20 true (2),
.last 18 (2,true),
.cycle 0 24 true (0),
.cycle 45 1 false (3),
.cycle 21 3 false (0),
.cycle 19 3 false (-1),
.cycle 0 20 true (0),
.cycle 7 12 true (2),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 17 8 true (3),
.cycle 22 3 false (0)
])
theorem kid10_part527_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part527) = true := by rfl

def kid10_part528 : Audit := .cycle 0 12 true (0)
theorem kid10_part528_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part528) = true := by rfl

def kid10_part529 : Audit := .cycle 1 11 true (1)
theorem kid10_part529_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part529) = true := by rfl

def kid10_part530 : Audit := .cycle 2 10 true (1)
theorem kid10_part530_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part530) = true := by rfl

def kid10_part531 : Audit := .cycle 1 14 true (1)
theorem kid10_part531_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part531) = true := by rfl

def kid10_part532 : Audit := .cycle 8 4 true (4)
theorem kid10_part532_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part532) = true := by rfl

def kid10_part533 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 27 true (1),
.cycle 10 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 21 5 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5),
.cycle 7 11 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 4 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 16 5 true (4),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 11 3 true (5)
])
theorem kid10_part533_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part533) = true := by rfl

def kid10_part509 : Audit := .split 11 (5,true) (byMove [(kid10_part510),(kid10_part511),(kid10_part512),(kid10_part513),(kid10_part514),(kid10_part515),(kid10_part516),(kid10_part517),(kid10_part518),(kid10_part519),(kid10_part520),(kid10_part521),(kid10_part522),(kid10_part523),(kid10_part524),(kid10_part525),(kid10_part526),(kid10_part527),(kid10_part528),(kid10_part529),(kid10_part530),(kid10_part531),(kid10_part532),(kid10_part533)])

theorem kid10_part509_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part509) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid10_part510),(kid10_part511),(kid10_part512),(kid10_part513),(kid10_part514),(kid10_part515),(kid10_part516),(kid10_part517),(kid10_part518),(kid10_part519),(kid10_part520),(kid10_part521),(kid10_part522),(kid10_part523),(kid10_part524),(kid10_part525),(kid10_part526),(kid10_part527),(kid10_part528),(kid10_part529),(kid10_part530),(kid10_part531),(kid10_part532),(kid10_part533)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part510_checked

  · exact kid10_part516_checked

  · exact kid10_part522_checked

  · exact kid10_part528_checked

  · exact kid10_part511_checked

  · exact kid10_part517_checked

  · exact kid10_part523_checked

  · exact kid10_part529_checked

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

def kid10_part535 : Audit := .split 15 (2,true) (byMove [
.cycle 1 22 true (1),
.cycle 7 15 true (1),
.cycle 20 1 false (0),
.last 19 (4,true),
.last 16 (4,true),
.cycle 1 21 true (1),
.cycle 6 10 true (1),
.last 17 (4,true),
.last 27 (4,true),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 0 27 true (0),
.last 18 (4,true),
.last 17 (4,true),
.last 23 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.cycle 14 4 true (1),
.cycle 14 10 true (2),
.last 17 (4,true),
.cycle 2 16 true (1),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 16 5 true (3)
])
theorem kid10_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part535) = true := by rfl

def kid10_part536 : Audit := .cycle 5 10 true (1)
theorem kid10_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part536) = true := by rfl

def kid10_part537 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 1 23 true (0),
.cycle 46 1 false (4),
.last 24 (2,true),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 0 38 true (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 18, 32, 18, 8192, 16384, 8, 128, 32, 18, 33554432, 67108864, 2097152, 128, 8388608, 1073741824, 33554432, 67108864, 2097152, 18, 8388608, 1073741824, 33554432, 67108864, 134217728, 301989888, 536870912, 1375731730, 1073741824],[128, 16, 1073741824, 1, 2, 18, 8192, 16, 1073741824, 1, 2, 1073741824, 33554432, 4194304, 1073741824, 262144, 524288, 1073741824, 33554432, 4194304, 1073741824, 262144, 524288, 18, 33554432, 268435456, 1073741824, 16777216, 33554432, 1375731712, 1073741824],2144284736⟩,
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 31 1 false (1),
.cycle 43 1 false (3),
.last 33 (2,true),
.last 21 (2,true),
.cycle 0 44 true (0),
.cycle 40 1 false (4),
.cycle 52 1 false (4),
.cycle 23 1 false (1),
.last 27 (2,true),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 1 21 true (0),
.last 26 (2,true),
.last 21 (2,true)
])
theorem kid10_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part537) = true := by rfl

def kid10_part538 : Audit := .split 17 (2,true) (byMove [
.cycle 1 24 true (0),
.cycle 38 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,true),
.last 18 (4,true),
.cycle 0 30 true (0),
.cycle 6 12 true (0),
.last 19 (4,true),
.last 29 (4,true),
.cycle 1 19 true (0),
.last 18 (4,true),
.last 30 (4,true),
.last 20 (4,true),
.last 19 (4,true),
.last 24 (4,true),
.last 21 (4,true),
.last 18 (4,true),
.last 22 (4,true),
.last 28 (4,true),
.last 19 (4,true),
.cycle 2 18 true (0),
.cycle 1 19 true (0),
.last 18 (4,true),
.cycle 7 14 true (0)
])
theorem kid10_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part538) = true := by rfl

def kid10_part539 : Audit := .cycle 18 1 false (0)
theorem kid10_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part539) = true := by rfl

def kid10_part540 : Audit := .cycle 15 1 false (-1)
theorem kid10_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part540) = true := by rfl

def kid10_part541 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 13 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 16, 1, 64],64⟩,
.cycle 9 7 true (2),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 18 true (0),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 1 18 true (1)
])
theorem kid10_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part541) = true := by rfl

def kid10_part542 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 52 1 false (6),
.cycle 0 28 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 15 true (1),
.cycle 33 1 false (9),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 33 1 false (9),
.cycle 1 15 true (1),
.cycle 7 12 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 43 1 false (5),
.cycle 41 1 false (9),
.cycle 21 1 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 6 true (5),
.cycle 1 15 true (1)
])
theorem kid10_part542_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part542) = true := by rfl

def kid10_part543 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.last 21 (4,true),
.last 28 (4,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 27 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 30 1 false (8),
.last 16 (4,true),
.last 17 (4,true),
.cycle 5 10 true (1),
.last 19 (4,true),
.last 33 (4,true),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid10_part543_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part543) = true := by rfl

def kid10_part544 : Audit := .cycle 5 8 true (1)
theorem kid10_part544_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part544) = true := by rfl

def kid10_part545 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 49 1 false (5),
.cycle 1 31 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 33 1 false (9),
.cycle 30 1 false (8),
.cycle 7 14 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 40 1 false (4),
.cycle 53 1 false (9),
.cycle 18 1 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 6 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part545_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part545) = true := by rfl

def kid10_part546 : Audit := .cycle 29 1 false (7)
theorem kid10_part546_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part546) = true := by rfl

def kid10_part547 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 2 28 true (1),
.last 20 (2,true),
.cycle 21 7 false (2),
.cycle 19 5 false (2),
.cycle 6 10 true (1),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 11 true (1),
.cycle 14 16 true (2),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 4 22 true (1),
.cycle 14 22 true (2),
.cycle 19 5 false (2),
.cycle 14 10 true (2),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 16 8 true (4),
.cycle 18 5 true (4)
])
theorem kid10_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part547) = true := by rfl

def kid10_part548 : Audit := .split 14 (2,true) (byMove [
.cycle 1 24 true (1),
.cycle 73 1 false (7),
.cycle 18 1 false (0),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 28 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 28 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.cycle 2 16 true (1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 17 (4,true)
])
theorem kid10_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part548) = true := by rfl

def kid10_part549 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 5 18 true (1),
.cycle 1 22 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 14 7 true (2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16, 32, 16, 8192, 16384, 8, 128, 32, 128, 33554432, 67108864, 2097152, 128, 8388608, 1073741824, 33554432, 67108864, 2097152, 16, 8388608, 1073741824, 33554432, 67108864, 134217728, 301989888, 536870912, 1375731712, 1073741824],[128, 16, 1073741824, 1, 16, 1, 8192, 16, 1073741824, 1, 16, 1073741824, 33554432, 4194304, 1073741824, 262144, 4194304, 1073741824, 33554432, 4194304, 1073741824, 262144, 4194304, 262144, 33554432, 268435456, 1073741824, 16777216, 268435456, 1090519040, 1073741824],2144284736⟩,
.cycle 9 9 true (1),
.last 25 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 0 22 true (0),
.cycle 5 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 5 18 true (1),
.cycle 1 22 true (1)
])
theorem kid10_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part549) = true := by rfl

def kid10_part550 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 1 21 true (0),
.cycle 43 1 false (3),
.last 22 (2,true),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 0 34 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 2, 18, 64],64⟩,
.last 18 (2,true),
.cycle 1 19 true (0),
.cycle 28 1 false (0),
.cycle 36 1 false (2),
.cycle 19 14 true (3),
.last 19 (2,true),
.cycle 0 40 true (0),
.cycle 37 1 false (3),
.cycle 43 1 false (3),
.cycle 20 1 false (0),
.cycle 1 29 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 1 19 true (0),
.cycle 18 18 true (4),
.cycle 34 7 true (4)
])
theorem kid10_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part550) = true := by rfl

def kid10_part551 : Audit := .cycle 12 2 true (1)
theorem kid10_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part551) = true := by rfl

def kid10_part552 : Audit := .cycle 15 1 false (-1)
theorem kid10_part552_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part552) = true := by rfl

def kid10_part553 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 13 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 16, 1, 64],64⟩,
.cycle 9 7 true (2),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 0 18 true (0),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 6 14 true (2),
.cycle 1 18 true (1)
])
theorem kid10_part553_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part553) = true := by rfl

def kid10_part554 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.last 19 (2,true),
.cycle 10 6 true (2),
.cycle 1 19 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 64, 1, 2, 2, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 1 15 true (1),
.cycle 7 12 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.cycle 7 10 true (2),
.cycle 11 4 true (2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 6 true (5),
.cycle 1 15 true (1)
])
theorem kid10_part554_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part554) = true := by rfl

def kid10_part555 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 57 1 false (11),
.last 32 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 1 17 true (1),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 25 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 2 19 true (1),
.last 16 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 12 2 true (2),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid10_part555_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part555) = true := by rfl

def kid10_part556 : Audit := .cycle 5 8 true (1)
theorem kid10_part556_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part556) = true := by rfl

def kid10_part557 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 34 8 true (4),
.last 14 (2,true),
.cycle 1 20 true (1),
.cycle 22 1 false (0),
.cycle 18 8 true (4),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 16 6 true (4),
.cycle 7 14 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 4 14 true (1),
.cycle 12 4 true (1),
.cycle 12 2 true (2),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 6 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part557_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part557) = true := by rfl

def kid10_part558 : Audit := .cycle 14 3 true (4)
theorem kid10_part558_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part558) = true := by rfl

def kid10_part534 : Audit := .split 12 (5,true) (byMove [(kid10_part535),(kid10_part536),(kid10_part537),(kid10_part538),(kid10_part539),(kid10_part540),(kid10_part541),(kid10_part542),(kid10_part543),(kid10_part544),(kid10_part545),(kid10_part546),(kid10_part547),(kid10_part548),(kid10_part549),(kid10_part550),(kid10_part551),(kid10_part552),(kid10_part553),(kid10_part554),(kid10_part555),(kid10_part556),(kid10_part557),(kid10_part558)])

theorem kid10_part534_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part534) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part535),(kid10_part536),(kid10_part537),(kid10_part538),(kid10_part539),(kid10_part540),(kid10_part541),(kid10_part542),(kid10_part543),(kid10_part544),(kid10_part545),(kid10_part546),(kid10_part547),(kid10_part548),(kid10_part549),(kid10_part550),(kid10_part551),(kid10_part552),(kid10_part553),(kid10_part554),(kid10_part555),(kid10_part556),(kid10_part557),(kid10_part558)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part535_checked

  · exact kid10_part541_checked

  · exact kid10_part547_checked

  · exact kid10_part553_checked

  · exact kid10_part536_checked

  · exact kid10_part542_checked

  · exact kid10_part548_checked

  · exact kid10_part554_checked

  · exact kid10_part537_checked

  · exact kid10_part543_checked

  · exact kid10_part549_checked

  · exact kid10_part555_checked

  · exact kid10_part538_checked

  · exact kid10_part544_checked

  · exact kid10_part550_checked

  · exact kid10_part556_checked

  · exact kid10_part539_checked

  · exact kid10_part545_checked

  · exact kid10_part551_checked

  · exact kid10_part557_checked

  · exact kid10_part540_checked

  · exact kid10_part546_checked

  · exact kid10_part552_checked

  · exact kid10_part558_checked

def kid10_part559 : Audit := .cycle 0 10 true (0)
theorem kid10_part559_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part559) = true := by rfl

def kid10_part560 : Audit := .cycle 1 9 true (1)
theorem kid10_part560_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part560) = true := by rfl

def kid10_part561 : Audit := .cycle 2 8 true (1)
theorem kid10_part561_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part561) = true := by rfl

def kid10_part562 : Audit := .cycle 1 12 true (1)
theorem kid10_part562_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part562) = true := by rfl

def kid10_part563 : Audit := .cycle 8 2 true (4)
theorem kid10_part563_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part563) = true := by rfl

def kid10_part564 : Audit := .cycle 9 1 true (5)
theorem kid10_part564_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part564) = true := by rfl

def kid10_part420 : Audit := .split 9 (5,false) (byMove [(kid10_part421),(kid10_part422),(kid10_part423),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part454),(kid10_part479),(kid10_part480),(kid10_part481),(kid10_part482),(kid10_part507),(kid10_part508),(kid10_part509),(kid10_part534),(kid10_part559),(kid10_part560),(kid10_part561),(kid10_part562),(kid10_part563),(kid10_part564)])

theorem kid10_part420_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid10_part420) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part421),(kid10_part422),(kid10_part423),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part454),(kid10_part479),(kid10_part480),(kid10_part481),(kid10_part482),(kid10_part507),(kid10_part508),(kid10_part509),(kid10_part534),(kid10_part559),(kid10_part560),(kid10_part561),(kid10_part562),(kid10_part563),(kid10_part564)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part421_checked

  · exact kid10_part427_checked

  · exact kid10_part481_checked

  · exact kid10_part559_checked

  · exact kid10_part422_checked

  · exact kid10_part428_checked

  · exact kid10_part482_checked

  · exact kid10_part560_checked

  · exact kid10_part423_checked

  · exact kid10_part429_checked

  · exact kid10_part507_checked

  · exact kid10_part561_checked

  · exact kid10_part424_checked

  · exact kid10_part454_checked

  · exact kid10_part508_checked

  · exact kid10_part562_checked

  · exact kid10_part425_checked

  · exact kid10_part479_checked

  · exact kid10_part509_checked

  · exact kid10_part563_checked

  · exact kid10_part426_checked

  · exact kid10_part480_checked

  · exact kid10_part534_checked

  · exact kid10_part564_checked

def kid10_part565 : Audit := .cycle 7 3 true (3)
theorem kid10_part565_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid10_part565) = true := by rfl

def kid10_part567 : Audit := .cycle 1 11 true (1)
theorem kid10_part567_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part567) = true := by rfl

def kid10_part568 : Audit := .cycle 7 4 true (3)
theorem kid10_part568_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part568) = true := by rfl

def kid10_part569 : Audit := .cycle 25 1 false (1)
theorem kid10_part569_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part569) = true := by rfl

def kid10_part570 : Audit := .cycle 0 12 true (0)
theorem kid10_part570_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part570) = true := by rfl

def kid10_part571 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 15 4 false (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,false),
.last 20 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.cycle 21 7 false (2),
.last 20 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 29 5 false (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (5,true),
.last 29 (5,true),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 4 true (3),
.cycle 12 1 true (4)
]),
.cycle 6 6 true (2),
.cycle 21 3 false (1),
.cycle 21 11 false (4),
.cycle 1 13 true (1),
.cycle 15 4 false (1),
.split 12 (5,true) (byMove [
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.last 20 (5,false),
.cycle 20 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.last 18 (5,false),
.last 24 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.last 14 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.cycle 1 15 true (1),
.last 18 (5,false),
.last 16 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (2),
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
.cycle 11 3 true (3),
.cycle 19 6 false (2),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 4 true (3),
.cycle 12 1 true (4)
])
])
theorem kid10_part571_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part571) = true := by rfl

def kid10_part573 : Audit := .cycle 1 12 true (1)
theorem kid10_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part573) = true := by rfl

def kid10_part574 : Audit := .cycle 1 16 true (1)
theorem kid10_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part574) = true := by rfl

def kid10_part575 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 25 1 false (-1),
.cycle 13 1 true (1),
.cycle 15 8 false (2),
.last 15 (4,true),
.cycle 0 28 true (-2),
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 13 1 true (1)
])
theorem kid10_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part575) = true := by rfl

def kid10_part576 : Audit := .cycle 0 13 true (0)
theorem kid10_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part576) = true := by rfl

def kid10_part577 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 12 7 true (0),
.cycle 20 4 false (2),
.last 13 (5,false),
.cycle 21 7 false (2),
.cycle 17 4 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (2),
.last 13 (5,false)
])
theorem kid10_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part577) = true := by rfl

def kid10_part578 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 18 13 false (1),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 18 5 false (0),
.cycle 13 1 true (1),
.cycle 15 8 false (2),
.last 15 (4,true),
.cycle 0 28 true (-2),
.cycle 1 15 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 13 1 true (1)
])
theorem kid10_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part578) = true := by rfl

def kid10_part579 : Audit := .cycle 0 12 true (0)
theorem kid10_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part579) = true := by rfl

def kid10_part580 : Audit := .cycle 1 11 true (1)
theorem kid10_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part580) = true := by rfl

def kid10_part581 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 44 1 false (2),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 30 (5,false),
.cycle 13 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4096, 128, 256, 8, 128, 16, 4096, 4096],[128, 16, 4096, 1, 16, 4, 128, 16, 8, 1, 16, 4, 4096],6176⟩,
.last 20 (5,false),
.cycle 7 14 true (2),
.cycle 9 11 true (2),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 1 29 true (1),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (4),
.last 20 (5,false)
])
theorem kid10_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part581) = true := by rfl

def kid10_part582 : Audit := .cycle 3 9 true (1)
theorem kid10_part582_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part582) = true := by rfl

def kid10_part583 : Audit := .cycle 8 4 true (3)
theorem kid10_part583_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part583) = true := by rfl

def kid10_part584 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (4,true),
.cycle 28 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 12 1 true (4)
])
theorem kid10_part584_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part584) = true := by rfl

def kid10_part585 : Audit := .cycle 6 6 true (2)
theorem kid10_part585_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part585) = true := by rfl

def kid10_part586 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (3),
.cycle 25 1 false (1),
.cycle 21 3 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,false),
.cycle 0 23 true (0),
.cycle 27 3 false (2),
.last 14 (5,false),
.cycle 7 8 true (2),
.cycle 22 3 false (1),
.cycle 0 16 true (0),
.cycle 30 1 false (2),
.cycle 21 3 false (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (2),
.last 14 (5,false)
])
theorem kid10_part586_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part586) = true := by rfl

def kid10_part587 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (0),
.last 34 (4,true),
.cycle 17 1 false (-1),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 22 1 false (0),
.cycle 7 8 true (1),
.cycle 0 19 true (0),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 14 14 true (-2),
.cycle 0 18 true (0),
.cycle 15 8 false (2),
.last 15 (4,true),
.cycle 14 10 true (-2),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 22 1 false (0),
.cycle 20 18 true (-2),
.cycle 24 5 false (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (4,true),
.cycle 16 14 true (-2)
])
theorem kid10_part587_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part587) = true := by rfl

def kid10_part588 : Audit := .cycle 1 13 true (1)
theorem kid10_part588_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part588) = true := by rfl

def kid10_part589 : Audit := .split 12 (4,true) (byMove [
.cycle 19 5 false (2),
.cycle 0 16 true (0),
.cycle 32 1 false (2),
.cycle 20 1 false (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 24 4 false (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 24 4 false (2),
.cycle 19 4 false (1),
.cycle 14 10 true (1),
.cycle 17 4 false (0),
.cycle 1 15 true (1),
.cycle 27 1 false (1),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 18 4 false (2),
.cycle 0 14 true (0),
.cycle 13 3 true (3),
.cycle 11 2 true (2)
])
theorem kid10_part589_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part589) = true := by rfl

def kid10_part590 : Audit := .split 13 (5,false) (byMove [
.cycle 15 6 false (2),
.last 25 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 6 8 true (1),
.last 15 (4,true),
.cycle 0 18 true (0),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 16 (4,true),
.last 15 (4,true),
.last 20 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 26 (4,true),
.last 15 (4,true),
.cycle 16 3 false (0),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid10_part590_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part590) = true := by rfl

def kid10_part591 : Audit := .cycle 0 12 true (0)
theorem kid10_part591_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part591) = true := by rfl

def kid10_part592 : Audit := .cycle 1 11 true (1)
theorem kid10_part592_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part592) = true := by rfl

def kid10_part593 : Audit := .cycle 2 10 true (1)
theorem kid10_part593_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part593) = true := by rfl

def kid10_part594 : Audit := .cycle 1 14 true (1)
theorem kid10_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part594) = true := by rfl

def kid10_part595 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 25 7 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (5,false),
.cycle 13 7 true (2),
.cycle 8 7 true (3),
.last 15 (5,false),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 25 7 false (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (3),
.last 15 (5,false)
])
theorem kid10_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part595) = true := by rfl

def kid10_part596 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 21 1 false (-1),
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
.last 14 (4,true),
.last 38 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 12 1 true (4)
])
theorem kid10_part596_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part596) = true := by rfl

def kid10_part572 : Audit := .split 11 (5,true) (byMove [(kid10_part573),(kid10_part574),(kid10_part575),(kid10_part576),(kid10_part577),(kid10_part578),(kid10_part579),(kid10_part580),(kid10_part581),(kid10_part582),(kid10_part583),(kid10_part584),(kid10_part585),(kid10_part586),(kid10_part587),(kid10_part588),(kid10_part589),(kid10_part590),(kid10_part591),(kid10_part592),(kid10_part593),(kid10_part594),(kid10_part595),(kid10_part596)])

theorem kid10_part572_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part572) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part573),(kid10_part574),(kid10_part575),(kid10_part576),(kid10_part577),(kid10_part578),(kid10_part579),(kid10_part580),(kid10_part581),(kid10_part582),(kid10_part583),(kid10_part584),(kid10_part585),(kid10_part586),(kid10_part587),(kid10_part588),(kid10_part589),(kid10_part590),(kid10_part591),(kid10_part592),(kid10_part593),(kid10_part594),(kid10_part595),(kid10_part596)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part573_checked

  · exact kid10_part579_checked

  · exact kid10_part585_checked

  · exact kid10_part591_checked

  · exact kid10_part574_checked

  · exact kid10_part580_checked

  · exact kid10_part586_checked

  · exact kid10_part592_checked

  · exact kid10_part575_checked

  · exact kid10_part581_checked

  · exact kid10_part587_checked

  · exact kid10_part593_checked

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

def kid10_part597 : Audit := .cycle 0 11 true (0)
theorem kid10_part597_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part597) = true := by rfl

def kid10_part598 : Audit := .cycle 1 10 true (1)
theorem kid10_part598_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part598) = true := by rfl

def kid10_part599 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 14 true (3),
.split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 45 1 false (3),
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
.cycle 9 14 true (3),
.cycle 1 37 true (1),
.cycle 1 21 true (1),
.cycle 20 26 true (-3),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (5),
.cycle 19 1 true (5)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
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
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 13 7 true (3),
.last 33 (5,true),
.last 22 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (5),
.cycle 19 1 true (7)
]),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.split 19 (5,false) (byMove [
.cycle 9 12 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 149, 4, 8, 128, 256, 8, 128, 5, 4, 4096],[128, 16, 4, 1, 5, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 23 true (0),
.cycle 7 15 true (3),
.cycle 0 39 true (-3),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 21 true (0),
.cycle 18 2 true (5),
.last 20 (5,true),
.cycle 16 4 true (4),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 68 1 false (12),
.cycle 5 15 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048596, 1048580, 1048580, 8192, 16384, 8, 128, 1048580, 1048580, 33554432, 67108864, 2097152, 128, 1048580, 1073741824, 33554432, 67108864, 2097152, 1048596, 67108864, 68157444, 33554432, 67108864, 134217728, 1443889156, 1141899268, 1141899268, 1073741824],[128, 16, 4, 1, 1048580, 1073741824, 8192, 16, 4, 1, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1141899268, 1073741824, 33554432, 268435456, 67108864, 16777216, 1141899268, 1073741824, 1073741824],2144219200⟩,
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.last 21 (5,true),
.last 20 (5,true)
]),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.split 19 (5,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 30 (5,true),
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
.cycle 17 3 true (5),
.last 32 (5,true),
.cycle 1 21 true (1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 17 4 true (5),
.cycle 19 1 true (7)
])
])
theorem kid10_part599_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part599) = true := by rfl

def kid10_part600 : Audit := .cycle 3 8 true (1)
theorem kid10_part600_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part600) = true := by rfl

def kid10_part601 : Audit := .cycle 8 3 true (3)
theorem kid10_part601_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part601) = true := by rfl

def kid10_part603 : Audit := .cycle 0 12 true (0)
theorem kid10_part603_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part603) = true := by rfl

def kid10_part604 : Audit := .cycle 1 11 true (1)
theorem kid10_part604_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part604) = true := by rfl

def kid10_part605 : Audit := .cycle 2 10 true (1)
theorem kid10_part605_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part605) = true := by rfl

def kid10_part606 : Audit := .cycle 1 14 true (1)
theorem kid10_part606_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part606) = true := by rfl

def kid10_part607 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 25 7 false (1),
.cycle 18 8 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 44 (5,true),
.cycle 13 7 true (2),
.cycle 8 7 true (3),
.cycle 8 8 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 21 (5,true),
.cycle 18 8 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (3),
.cycle 14 2 true (4)
])
theorem kid10_part607_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part607) = true := by rfl

def kid10_part608 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 20 1 false (0),
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
.last 15 (4,true),
.cycle 0 18 true (0),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 12 2 true (3)
])
theorem kid10_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part608) = true := by rfl

def kid10_part609 : Audit := .cycle 0 12 true (0)
theorem kid10_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part609) = true := by rfl

def kid10_part610 : Audit := .cycle 1 11 true (1)
theorem kid10_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part610) = true := by rfl

def kid10_part611 : Audit := .split 20 (4,true) (byMove [
.cycle 9 13 true (3),
.cycle 0 24 true (0),
.cycle 2 26 true (1),
.cycle 9 15 true (3),
.cycle 0 30 true (0),
.cycle 0 24 true (0),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 35 (5,true),
.cycle 0 22 true (0),
.cycle 8 14 true (3),
.last 21 (5,true),
.cycle 7 18 true (3),
.last 23 (5,true),
.cycle 1 23 true (1),
.cycle 4 22 true (1),
.last 27 (5,true),
.last 23 (5,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 10 11 true (3),
.cycle 0 22 true (0),
.cycle 21 3 true (7),
.last 21 (5,true)
])
theorem kid10_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part611) = true := by rfl

def kid10_part612 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 8 14 true (3),
.cycle 3 17 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 40 (5,true),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.last 28 (5,true),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 25 (5,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 17 3 true (5),
.cycle 3 17 true (1)
])
theorem kid10_part612_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part612) = true := by rfl

def kid10_part613 : Audit := .cycle 8 4 true (3)
theorem kid10_part613_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part613) = true := by rfl

def kid10_part614 : Audit := .cycle 11 1 true (5)
theorem kid10_part614_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part614) = true := by rfl

def kid10_part615 : Audit := .cycle 7 6 true (3)
theorem kid10_part615_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part615) = true := by rfl

def kid10_part616 : Audit := .cycle 9 3 true (3)
theorem kid10_part616_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part616) = true := by rfl

def kid10_part617 : Audit := .cycle 0 14 true (0)
theorem kid10_part617_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part617) = true := by rfl

def kid10_part618 : Audit := .cycle 4 8 true (1)
theorem kid10_part618_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part618) = true := by rfl

def kid10_part619 : Audit := .split 14 (4,true) (byMove [
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.cycle 9 9 true (2),
.cycle 25 7 false (1),
.last 23 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 20 (5,true),
.cycle 0 16 true (0),
.cycle 8 8 true (3),
.last 15 (5,true),
.cycle 7 12 true (3),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.last 21 (5,true),
.last 23 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (3),
.cycle 0 16 true (0),
.cycle 15 3 true (5),
.last 15 (5,true)
])
theorem kid10_part619_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part619) = true := by rfl

def kid10_part620 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 22 true (0),
.cycle 20 1 false (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 25 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 40 1 false (8),
.last 16 (4,true),
.last 15 (4,true),
.cycle 5 12 true (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 14 3 true (4)
])
theorem kid10_part620_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part620) = true := by rfl

def kid10_part621 : Audit := .cycle 0 12 true (0)
theorem kid10_part621_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part621) = true := by rfl

def kid10_part622 : Audit := .cycle 1 11 true (1)
theorem kid10_part622_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part622) = true := by rfl

def kid10_part623 : Audit := .cycle 2 10 true (1)
theorem kid10_part623_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part623) = true := by rfl

def kid10_part624 : Audit := .cycle 1 14 true (1)
theorem kid10_part624_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part624) = true := by rfl

def kid10_part625 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 21 true (1),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 26 (5,true),
.cycle 0 24 true (0),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 17 true (1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (5),
.cycle 11 4 true (5)
])
theorem kid10_part625_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part625) = true := by rfl

def kid10_part626 : Audit := .cycle 11 1 true (5)
theorem kid10_part626_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part626) = true := by rfl

def kid10_part602 : Audit := .split 11 (5,false) (byMove [(kid10_part603),(kid10_part604),(kid10_part605),(kid10_part606),(kid10_part607),(kid10_part608),(kid10_part609),(kid10_part610),(kid10_part611),(kid10_part612),(kid10_part613),(kid10_part614),(kid10_part615),(kid10_part616),(kid10_part617),(kid10_part618),(kid10_part619),(kid10_part620),(kid10_part621),(kid10_part622),(kid10_part623),(kid10_part624),(kid10_part625),(kid10_part626)])

theorem kid10_part602_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part602) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part603),(kid10_part604),(kid10_part605),(kid10_part606),(kid10_part607),(kid10_part608),(kid10_part609),(kid10_part610),(kid10_part611),(kid10_part612),(kid10_part613),(kid10_part614),(kid10_part615),(kid10_part616),(kid10_part617),(kid10_part618),(kid10_part619),(kid10_part620),(kid10_part621),(kid10_part622),(kid10_part623),(kid10_part624),(kid10_part625),(kid10_part626)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part603_checked

  · exact kid10_part609_checked

  · exact kid10_part615_checked

  · exact kid10_part621_checked

  · exact kid10_part604_checked

  · exact kid10_part610_checked

  · exact kid10_part616_checked

  · exact kid10_part622_checked

  · exact kid10_part605_checked

  · exact kid10_part611_checked

  · exact kid10_part617_checked

  · exact kid10_part623_checked

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

def kid10_part627 : Audit := .cycle 6 5 true (2)
theorem kid10_part627_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part627) = true := by rfl

def kid10_part628 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 22 5 false (1),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 1 20 true (1),
.cycle 27 1 false (-1),
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
.cycle 22 5 false (1),
.cycle 15 16 true (-2),
.cycle 1 15 true (1),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (3),
.cycle 13 1 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
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
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 11 7 true (2),
.last 19 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (3),
.cycle 13 1 true (5)
]),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 22 5 false (1),
.split 13 (5,false) (byMove [
.cycle 9 6 true (2),
.cycle 1 24 true (1),
.cycle 27 1 false (-1),
.cycle 7 9 true (2),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.last 14 (5,true),
.cycle 11 4 true (2),
.cycle 22 5 false (1),
.cycle 17 12 true (-2),
.cycle 5 9 true (1),
.cycle 16 6 false (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
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
.cycle 11 3 true (3),
.last 19 (5,true),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 4 true (3),
.cycle 13 1 true (5)
])
])
theorem kid10_part628_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part628) = true := by rfl

def kid10_part629 : Audit := .cycle 5 9 true (1)
theorem kid10_part629_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part629) = true := by rfl

def kid10_part630 : Audit := .cycle 1 12 true (1)
theorem kid10_part630_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part630) = true := by rfl

def kid10_part631 : Audit := .split 11 (4,true) (byMove [
.cycle 9 4 true (2),
.cycle 1 20 true (1),
.cycle 17 1 false (1),
.cycle 7 7 true (2),
.cycle 15 4 false (1),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.last 21 (5,false),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 7 7 true (2),
.last 16 (5,false),
.cycle 0 15 true (0),
.last 20 (5,false),
.last 17 (5,false),
.last 13 (5,false),
.cycle 21 7 false (2),
.last 20 (5,false),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 29 5 false (2),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 32 6 true (6),
.last 20 (5,false),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 29 5 false (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 7 9 true (2),
.cycle 21 3 false (1),
.cycle 0 23 true (0),
.cycle 5 7 true (1),
.cycle 15 4 false (1),
.split 12 (5,true) (byMove [
.cycle 19 5 false (2),
.cycle 1 16 true (1),
.last 20 (5,false),
.cycle 20 1 false (0),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.last 24 (5,false),
.cycle 1 14 true (1),
.last 14 (5,false),
.last 15 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.cycle 5 9 true (1),
.last 18 (5,false),
.last 16 (5,false),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.last 15 (5,false),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.last 15 (5,false)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (2),
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
.last 15 (5,false),
.cycle 19 6 false (2),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid10_part631_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part631) = true := by rfl

def kid10_part633 : Audit := .cycle 9 4 true (2)
theorem kid10_part633_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part633) = true := by rfl

def kid10_part634 : Audit := .cycle 1 20 true (1)
theorem kid10_part634_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part634) = true := by rfl

def kid10_part635 : Audit := .split 13 (5,false) (byMove [
.cycle 15 6 false (2),
.cycle 20 1 false (0),
.cycle 17 1 false (-1),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 9 6 true (1),
.last 25 (4,true),
.cycle 12 2 true (1),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 29 1 false (1),
.last 16 (4,true),
.last 15 (4,true),
.last 20 (4,true),
.cycle 23 1 false (-1),
.last 14 (4,true),
.cycle 16 1 false (0),
.cycle 29 1 false (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 18 1 false (0)
])
theorem kid10_part635_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part635) = true := by rfl

def kid10_part636 : Audit := .cycle 7 7 true (2)
theorem kid10_part636_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part636) = true := by rfl

def kid10_part637 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 21 4 false (2),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.cycle 20 4 false (2),
.last 13 (5,false),
.cycle 21 7 false (2),
.cycle 17 4 false (0),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 16 3 true (4),
.last 13 (5,false)
])
theorem kid10_part637_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part637) = true := by rfl

def kid10_part638 : Audit := .split 13 (5,false) (byMove [
.last 22 (4,true),
.last 27 (4,true),
.cycle 17 1 false (-1),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.last 21 (4,true),
.cycle 25 1 false (1),
.cycle 18 5 false (0),
.cycle 17 1 true (3),
.cycle 15 8 false (2),
.last 15 (4,true),
.cycle 21 8 true (-2),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 30 (4,true),
.cycle 0 17 true (0),
.last 20 (4,true),
.cycle 9 8 true (1),
.last 16 (4,true),
.cycle 21 1 true (-1)
])
theorem kid10_part638_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part638) = true := by rfl

def kid10_part639 : Audit := .cycle 1 12 true (1)
theorem kid10_part639_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part639) = true := by rfl

def kid10_part640 : Audit := .cycle 7 5 true (3)
theorem kid10_part640_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part640) = true := by rfl

def kid10_part641 : Audit := .split 13 (5,false) (byMove [
.cycle 9 6 true (2),
.cycle 1 24 true (1),
.cycle 19 1 false (-1),
.cycle 7 9 true (2),
.last 14 (4,true),
.cycle 0 17 true (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 22 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 20 1 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 22 (4,true)
])
theorem kid10_part641_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part641) = true := by rfl

def kid10_part642 : Audit := .cycle 0 13 true (0)
theorem kid10_part642_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part642) = true := by rfl

def kid10_part643 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 23 5 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 12 7 true (2),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 23 5 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.last 13 (5,false)
])
theorem kid10_part643_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part643) = true := by rfl

def kid10_part644 : Audit := .split 13 (5,false) (byMove [
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
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 11 7 true (3),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 13 1 true (5)
])
theorem kid10_part644_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part644) = true := by rfl

def kid10_part645 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 23 10 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (5,false),
.cycle 12 7 true (2),
.cycle 13 7 true (3),
.last 15 (5,false),
.cycle 7 9 true (2),
.cycle 9 6 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 23 10 false (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 3 true (3),
.last 15 (5,false)
])
theorem kid10_part645_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part645) = true := by rfl

def kid10_part646 : Audit := .split 13 (4,true) (byMove [
.cycle 9 6 true (2),
.cycle 0 17 true (0),
.cycle 42 1 false (4),
.cycle 25 1 false (1),
.cycle 21 3 false (0),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 49 3 false (10),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 35 3 false (6),
.cycle 26 3 false (2),
.cycle 7 11 true (2),
.cycle 22 3 false (1),
.cycle 1 16 true (1),
.cycle 35 1 false (3),
.cycle 21 3 false (0),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 24 3 false (2),
.cycle 0 15 true (0),
.cycle 14 3 true (4),
.last 17 (5,false)
])
theorem kid10_part646_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part646) = true := by rfl

def kid10_part647 : Audit := .split 13 (5,false) (byMove [
.cycle 15 6 false (2),
.last 23 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.cycle 12 2 true (1),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 5 11 true (1),
.last 16 (4,true),
.last 15 (4,true),
.last 20 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 15 (4,true),
.last 24 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 21 (4,true)
])
theorem kid10_part647_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part647) = true := by rfl

def kid10_part648 : Audit := .cycle 5 7 true (1)
theorem kid10_part648_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part648) = true := by rfl

def kid10_part649 : Audit := .split 12 (4,true) (byMove [
.cycle 19 5 false (2),
.cycle 1 16 true (1),
.cycle 39 1 false (3),
.cycle 20 1 false (0),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 30 4 false (6),
.cycle 19 4 false (1),
.cycle 14 13 true (2),
.cycle 17 4 false (0),
.cycle 5 9 true (1),
.cycle 32 1 false (2),
.cycle 16 4 false (0),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 18 4 false (2),
.cycle 1 14 true (1),
.cycle 14 3 true (4),
.cycle 11 2 true (2)
])
theorem kid10_part649_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part649) = true := by rfl

def kid10_part650 : Audit := .split 13 (5,false) (byMove [
.cycle 15 6 false (2),
.last 25 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 13 2 true (1),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 2 true (1),
.last 16 (4,true),
.last 15 (4,true),
.last 20 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 16 3 false (0),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 15 3 false (1)
])
theorem kid10_part650_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part650) = true := by rfl

def kid10_part651 : Audit := .cycle 1 12 true (1)
theorem kid10_part651_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part651) = true := by rfl

def kid10_part652 : Audit := .cycle 7 5 true (3)
theorem kid10_part652_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part652) = true := by rfl

def kid10_part653 : Audit := .cycle 10 2 true (3)
theorem kid10_part653_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part653) = true := by rfl

def kid10_part654 : Audit := .cycle 0 13 true (0)
theorem kid10_part654_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part654) = true := by rfl

def kid10_part655 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 17 6 false (1),
.last 17 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 17 (5,false),
.cycle 1 14 true (1),
.cycle 17 6 false (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.last 13 (5,false)
])
theorem kid10_part655_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part655) = true := by rfl

def kid10_part656 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
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
.last 15 (4,true),
.cycle 11 5 true (3),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 13 1 true (5)
])
theorem kid10_part656_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part656) = true := by rfl

def kid10_part632 : Audit := .split 11 (5,true) (byMove [(kid10_part633),(kid10_part634),(kid10_part635),(kid10_part636),(kid10_part637),(kid10_part638),(kid10_part639),(kid10_part640),(kid10_part641),(kid10_part642),(kid10_part643),(kid10_part644),(kid10_part645),(kid10_part646),(kid10_part647),(kid10_part648),(kid10_part649),(kid10_part650),(kid10_part651),(kid10_part652),(kid10_part653),(kid10_part654),(kid10_part655),(kid10_part656)])

theorem kid10_part632_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part632) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part633),(kid10_part634),(kid10_part635),(kid10_part636),(kid10_part637),(kid10_part638),(kid10_part639),(kid10_part640),(kid10_part641),(kid10_part642),(kid10_part643),(kid10_part644),(kid10_part645),(kid10_part646),(kid10_part647),(kid10_part648),(kid10_part649),(kid10_part650),(kid10_part651),(kid10_part652),(kid10_part653),(kid10_part654),(kid10_part655),(kid10_part656)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part633_checked

  · exact kid10_part639_checked

  · exact kid10_part645_checked

  · exact kid10_part651_checked

  · exact kid10_part634_checked

  · exact kid10_part640_checked

  · exact kid10_part646_checked

  · exact kid10_part652_checked

  · exact kid10_part635_checked

  · exact kid10_part641_checked

  · exact kid10_part647_checked

  · exact kid10_part653_checked

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

def kid10_part657 : Audit := .cycle 0 11 true (0)
theorem kid10_part657_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part657) = true := by rfl

def kid10_part658 : Audit := .cycle 1 10 true (1)
theorem kid10_part658_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part658) = true := by rfl

def kid10_part659 : Audit := .cycle 2 9 true (1)
theorem kid10_part659_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part659) = true := by rfl

def kid10_part660 : Audit := .cycle 1 13 true (1)
theorem kid10_part660_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part660) = true := by rfl

def kid10_part661 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 26 9 false (2),
.split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 49 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (3),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.cycle 14 1 true (4),
.cycle 6 9 true (2),
.cycle 27 9 false (2),
.last 17 (5,true),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (4)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 12 50 true (3),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (3),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 8 7 true (3),
.cycle 14 1 true (6),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 12 7 true (3),
.last 23 (5,true),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (6)
]),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 24 6 false (2),
.split 14 (5,false) (byMove [
.cycle 9 7 true (3),
.last 20 (5,true),
.cycle 39 1 false (1),
.cycle 7 10 true (3),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.cycle 13 2 true (4),
.last 15 (5,true),
.cycle 12 4 true (3),
.last 24 (5,true),
.last 17 (5,true),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.cycle 13 2 true (5),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (4),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.cycle 14 1 true (6),
.cycle 6 9 true (2),
.cycle 12 3 true (4),
.cycle 13 3 true (5),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (4),
.cycle 14 1 true (6)
])
])
theorem kid10_part661_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part661) = true := by rfl

def kid10_part663 : Audit := .cycle 1 12 true (1)
theorem kid10_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part663) = true := by rfl

def kid10_part664 : Audit := .cycle 7 5 true (3)
theorem kid10_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part664) = true := by rfl

def kid10_part665 : Audit := .cycle 10 2 true (4)
theorem kid10_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part665) = true := by rfl

def kid10_part666 : Audit := .cycle 0 13 true (0)
theorem kid10_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part666) = true := by rfl

def kid10_part667 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 37 1 false (1),
.cycle 0 14 true (0),
.cycle 17 6 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 44 (5,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 8 10 true (3),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 11 2 true (4)
])
theorem kid10_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part667) = true := by rfl

def kid10_part668 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 37 1 false (1),
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
.last 14 (4,true),
.cycle 12 2 true (3),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (4,true),
.cycle 11 2 true (4)
])
theorem kid10_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part668) = true := by rfl

def kid10_part669 : Audit := .cycle 0 12 true (0)
theorem kid10_part669_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part669) = true := by rfl

def kid10_part670 : Audit := .cycle 1 11 true (1)
theorem kid10_part670_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part670) = true := by rfl

def kid10_part671 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 15 true (3),
.cycle 11 9 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 19 true (4),
.cycle 13 7 true (4),
.cycle 8 12 true (3),
.last 31 (5,true),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 26 (5,true),
.cycle 10 11 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (6),
.cycle 11 9 true (4)
])
theorem kid10_part671_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part671) = true := by rfl

def kid10_part672 : Audit := .cycle 3 9 true (1)
theorem kid10_part672_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part672) = true := by rfl

def kid10_part673 : Audit := .cycle 8 4 true (3)
theorem kid10_part673_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part673) = true := by rfl

def kid10_part674 : Audit := .cycle 11 1 true (5)
theorem kid10_part674_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part674) = true := by rfl

def kid10_part675 : Audit := .cycle 6 6 true (2)
theorem kid10_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part675) = true := by rfl

def kid10_part676 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 27 9 false (2),
.cycle 26 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 39 (5,true),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.cycle 9 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 23 (5,true),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (4)
])
theorem kid10_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part676) = true := by rfl

def kid10_part677 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 24 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 12 2 true (4),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 26 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 11 3 true (4)
])
theorem kid10_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part677) = true := by rfl

def kid10_part678 : Audit := .cycle 1 13 true (1)
theorem kid10_part678_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part678) = true := by rfl

def kid10_part679 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 true (3),
.last 17 (5,true),
.cycle 58 1 false (4),
.cycle 7 8 true (3),
.cycle 17 6 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.last 13 (5,true),
.cycle 7 10 true (3),
.last 17 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 13 3 true (5),
.last 13 (5,true)
])
theorem kid10_part679_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part679) = true := by rfl

def kid10_part680 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 true (3),
.cycle 7 11 true (3),
.last 25 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 49 1 false (9),
.last 15 (4,true),
.last 14 (4,true),
.cycle 12 2 true (3),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 3 true (4)
])
theorem kid10_part680_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part680) = true := by rfl

def kid10_part681 : Audit := .cycle 0 12 true (0)
theorem kid10_part681_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part681) = true := by rfl

def kid10_part682 : Audit := .cycle 1 11 true (1)
theorem kid10_part682_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part682) = true := by rfl

def kid10_part683 : Audit := .cycle 2 10 true (1)
theorem kid10_part683_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part683) = true := by rfl

def kid10_part684 : Audit := .cycle 1 14 true (1)
theorem kid10_part684_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part684) = true := by rfl

def kid10_part685 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 31 13 false (3),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 14 true (4),
.cycle 13 7 true (4),
.cycle 8 7 true (3),
.cycle 11 4 true (5),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 27 (5,true),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (5),
.cycle 11 4 true (5)
])
theorem kid10_part685_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part685) = true := by rfl

def kid10_part686 : Audit := .cycle 11 1 true (5)
theorem kid10_part686_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part686) = true := by rfl

def kid10_part662 : Audit := .split 11 (5,false) (byMove [(kid10_part663),(kid10_part664),(kid10_part665),(kid10_part666),(kid10_part667),(kid10_part668),(kid10_part669),(kid10_part670),(kid10_part671),(kid10_part672),(kid10_part673),(kid10_part674),(kid10_part675),(kid10_part676),(kid10_part677),(kid10_part678),(kid10_part679),(kid10_part680),(kid10_part681),(kid10_part682),(kid10_part683),(kid10_part684),(kid10_part685),(kid10_part686)])

theorem kid10_part662_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part662) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part663),(kid10_part664),(kid10_part665),(kid10_part666),(kid10_part667),(kid10_part668),(kid10_part669),(kid10_part670),(kid10_part671),(kid10_part672),(kid10_part673),(kid10_part674),(kid10_part675),(kid10_part676),(kid10_part677),(kid10_part678),(kid10_part679),(kid10_part680),(kid10_part681),(kid10_part682),(kid10_part683),(kid10_part684),(kid10_part685),(kid10_part686)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part663_checked

  · exact kid10_part669_checked

  · exact kid10_part675_checked

  · exact kid10_part681_checked

  · exact kid10_part664_checked

  · exact kid10_part670_checked

  · exact kid10_part676_checked

  · exact kid10_part682_checked

  · exact kid10_part665_checked

  · exact kid10_part671_checked

  · exact kid10_part677_checked

  · exact kid10_part683_checked

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

def kid10_part566 : Audit := .split 10 (2,true) (byMove [(kid10_part567),(kid10_part568),(kid10_part569),(kid10_part570),(kid10_part571),(kid10_part572),(kid10_part597),(kid10_part598),(kid10_part599),(kid10_part600),(kid10_part601),(kid10_part602),(kid10_part627),(kid10_part628),(kid10_part629),(kid10_part630),(kid10_part631),(kid10_part632),(kid10_part657),(kid10_part658),(kid10_part659),(kid10_part660),(kid10_part661),(kid10_part662)])

theorem kid10_part566_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid10_part566) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid10_part567),(kid10_part568),(kid10_part569),(kid10_part570),(kid10_part571),(kid10_part572),(kid10_part597),(kid10_part598),(kid10_part599),(kid10_part600),(kid10_part601),(kid10_part602),(kid10_part627),(kid10_part628),(kid10_part629),(kid10_part630),(kid10_part631),(kid10_part632),(kid10_part657),(kid10_part658),(kid10_part659),(kid10_part660),(kid10_part661),(kid10_part662)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part567_checked

  · exact kid10_part597_checked

  · exact kid10_part627_checked

  · exact kid10_part657_checked

  · exact kid10_part568_checked

  · exact kid10_part598_checked

  · exact kid10_part628_checked

  · exact kid10_part658_checked

  · exact kid10_part569_checked

  · exact kid10_part599_checked

  · exact kid10_part629_checked

  · exact kid10_part659_checked

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

def kid10_part687 : Audit := .cycle 0 11 true (0)
theorem kid10_part687_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid10_part687) = true := by rfl

def kid10_part688 : Audit := .cycle 4 5 true (1)
theorem kid10_part688_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid10_part688) = true := by rfl

def kid10_part690 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.cycle 0 19 true (0),
.split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 24 1 false (0),
.cycle 18 1 false (0),
.cycle 0 21 true (0),
.cycle 0 25 true (0),
.last 17 (5,false),
.cycle 7 9 true (1),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 19 7 false (2),
.last 15 (5,false),
.cycle 21 9 false (2),
.cycle 0 21 true (0),
.last 29 (5,false),
.cycle 1 21 true (1),
.cycle 17 5 false (2),
.last 17 (5,false),
.cycle 12 9 true (2),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 12 6 true (1),
.last 15 (5,false)
]),
.cycle 1 14 true (1),
.cycle 0 24 true (0),
.cycle 0 35 true (0),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 20 (5,false),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 27 (5,false),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.last 15 (5,false),
.cycle 12 9 true (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 12 6 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 20 (5,false),
.last 15 (5,false)
]),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.split 14 (5,true) (byMove [
.cycle 12 4 true (1),
.cycle 24 1 false (0),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.cycle 1 20 true (0),
.last 17 (5,false),
.cycle 6 9 true (1),
.cycle 0 17 true (0),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 0 21 true (0),
.last 17 (5,false),
.cycle 0 25 true (0),
.cycle 10 6 true (1),
.last 51 (5,false),
.cycle 0 19 true (0),
.cycle 17 5 false (2),
.last 17 (5,false),
.cycle 12 9 true (2),
.cycle 0 17 true (0),
.cycle 13 2 true (2),
.cycle 1 16 true (1),
.cycle 1 21 true (1),
.last 17 (5,false)
]),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.split 14 (5,true) (byMove [
.cycle 1 15 true (1),
.cycle 12 8 true (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 19 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 12 7 true (2),
.last 15 (5,false),
.cycle 12 9 true (2),
.cycle 0 17 true (0),
.cycle 13 2 true (3),
.cycle 1 16 true (1),
.last 19 (5,false),
.last 19 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 20 (5,false),
.last 15 (5,false)
])
])
theorem kid10_part690_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part690) = true := by rfl

def kid10_part691 : Audit := .cycle 1 14 true (1)
theorem kid10_part691_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part691) = true := by rfl

def kid10_part692 : Audit := .cycle 35 1 false (3)
theorem kid10_part692_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part692) = true := by rfl

def kid10_part693 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.cycle 0 23 true (0),
.split 16 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 18 1 false (2),
.last 18 (5,false),
.cycle 0 23 true (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 7 11 true (0),
.cycle 1 43 true (0),
.cycle 0 19 true (0),
.cycle 1 25 true (0),
.cycle 20 1 false (0),
.last 17 (5,false),
.cycle 22 1 false (0),
.cycle 19 1 false (1),
.last 18 (5,false),
.cycle 1 23 true (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 1 28 true (0),
.cycle 1 19 true (0),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.cycle 1 25 true (0),
.last 17 (5,false)
]),
.cycle 1 16 true (0),
.cycle 3 67 true (0),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.cycle 1 19 true (0),
.split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 25 1 false (1),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 40 true (0),
.last 31 (5,false),
.cycle 1 26 true (0),
.last 30 (5,false),
.last 17 (5,false),
.cycle 1 28 true (0),
.last 19 (5,false),
.cycle 0 19 true (0),
.cycle 4 13 true (0),
.cycle 1 25 true (0),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.proven (BB6.Agent11Raw39Pumps.M728.table) (fun m hm => BB6.Agent11Raw39Pumps.M728.never m hm),
.cycle 1 19 true (0),
.last 24 (5,false),
.last 17 (5,false)
]),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.cycle 1 23 true (0),
.split 16 (5,true) (byMove [
.cycle 13 4 true (1),
.cycle 18 1 false (2),
.last 18 (5,false),
.cycle 1 23 true (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 6 11 true (0),
.cycle 27 1 false (1),
.last 18 (5,false),
.cycle 1 18 true (0),
.cycle 1 27 true (0),
.last 19 (5,false),
.cycle 1 31 true (0),
.cycle 19 1 false (1),
.last 18 (5,false),
.cycle 1 23 true (0),
.cycle 18 1 false (0),
.last 18 (5,false),
.cycle 1 28 true (0),
.cycle 1 21 true (0),
.cycle 15 2 true (2),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.last 19 (5,false)
]),
.cycle 1 16 true (0),
.cycle 1 26 true (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.split 16 (5,true) (byMove [
.cycle 1 17 true (0),
.cycle 1 27 true (0),
.last 18 (5,false),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.last 20 (5,false),
.cycle 0 17 true (0),
.cycle 3 40 true (0),
.cycle 1 27 true (0),
.cycle 3 14 true (0),
.cycle 1 26 true (0),
.last 17 (5,false),
.cycle 1 28 true (0),
.cycle 1 21 true (0),
.cycle 15 2 true (3),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.last 20 (5,false),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 1 19 true (0),
.cycle 7 14 true (0),
.last 17 (5,false)
])
])
theorem kid10_part693_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part693) = true := by rfl

def kid10_part694 : Audit := .cycle 13 1 false (-1)
theorem kid10_part694_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part694) = true := by rfl

def kid10_part696 : Audit := .cycle 1 16 true (0)
theorem kid10_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part696) = true := by rfl

def kid10_part697 : Audit := .cycle 13 1 false (1)
theorem kid10_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part697) = true := by rfl

def kid10_part698 : Audit := .split 12 (2,true) (byMove [
.cycle 14 35 true (0),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 0 29 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 42 1 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part698) = true := by rfl

def kid10_part699 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 21 (5,true),
.cycle 0 41 true (0),
.cycle 0 17 true (0),
.cycle 0 19 true (0),
.last 16 (5,true),
.cycle 0 21 true (0),
.cycle 0 27 true (0),
.cycle 0 25 true (0),
.cycle 5 11 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 20 (5,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid10_part699_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part699) = true := by rfl

def kid10_part700 : Audit := .cycle 14 1 false (-2)
theorem kid10_part700_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part700) = true := by rfl

def kid10_part701 : Audit := .split 12 (5,true) (byMove [
.cycle 14 35 true (0),
.cycle 23 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 40 1 false (2),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part701_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part701) = true := by rfl

def kid10_part702 : Audit := .cycle 0 16 true (0)
theorem kid10_part702_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part702) = true := by rfl

def kid10_part703 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (1),
.cycle 0 19 true (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 1 24 true (1),
.cycle 1 35 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 1 17 true (1),
.cycle 1 21 true (1),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid10_part703_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part703) = true := by rfl

def kid10_part704 : Audit := .cycle 1 14 true (1)
theorem kid10_part704_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part704) = true := by rfl

def kid10_part705 : Audit := .cycle 35 1 false (3)
theorem kid10_part705_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part705) = true := by rfl

def kid10_part706 : Audit := .cycle 16 1 false (0)
theorem kid10_part706_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part706) = true := by rfl

def kid10_part707 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 33 1 true (3),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 1 true (3),
.cycle 1 14 true (1),
.cycle 30 1 false (6),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (3),
.cycle 15 1 true (5),
.cycle 17 1 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 29 1 true (3),
.cycle 20 1 false (0),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 5 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part707) = true := by rfl

def kid10_part708 : Audit := .cycle 13 6 false (2)
theorem kid10_part708_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part708) = true := by rfl

def kid10_part709 : Audit := .split 16 (2,true) (byMove [
.cycle 1 70 false (5),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 1 22 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 1 20 true (-1),
.cycle 1 20 true (-1),
.cycle 10 14 true (-1),
.cycle 10 23 false (2),
.cycle 13 6 false (1),
.last 23 (5,true),
.cycle 13 8 false (1),
.cycle 12 5 false (1),
.cycle 1 24 true (-2),
.cycle 1 22 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 115 82 false (7),
.cycle 1 20 true (-1),
.cycle 2 62 false (5),
.cycle 0 23 true (-1),
.last 19 (5,true),
.cycle 10 9 false (2)
])
theorem kid10_part709_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part709) = true := by rfl

def kid10_part710 : Audit := .split 12 (2,true) (byMove [
.cycle 1 20 true (-1),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 16 true (-2),
.cycle 1 16 true (0),
.cycle 14 1 false (2),
.cycle 1 16 true (0),
.cycle 0 20 true (0),
.cycle 0 30 true (-1),
.last 13 (5,true),
.cycle 10 5 false (2),
.cycle 10 20 true (-2),
.cycle 1 29 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 16 true (-2),
.cycle 1 16 true (0),
.cycle 10 12 true (-2),
.cycle 1 16 true (0),
.cycle 0 20 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part710_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part710) = true := by rfl

def kid10_part711 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 21 (5,true),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.cycle 1 19 true (0),
.last 16 (5,true),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.last 17 (5,true),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 20 (5,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid10_part711_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part711) = true := by rfl

def kid10_part712 : Audit := .cycle 14 1 false (-2)
theorem kid10_part712_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part712) = true := by rfl

def kid10_part713 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 14 1 false (2),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (2),
.cycle 10 5 false (2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 17 1 false (-1),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 17 1 false (-1),
.cycle 17 3 true (3)
])
theorem kid10_part713_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part713) = true := by rfl

def kid10_part714 : Audit := .cycle 0 16 true (0)
theorem kid10_part714_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part714) = true := by rfl

def kid10_part715 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.last 18 (5,true),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 19 (5,true),
.cycle 1 35 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 1 17 true (1),
.cycle 1 21 true (1),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid10_part715_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part715) = true := by rfl

def kid10_part716 : Audit := .cycle 1 14 true (1)
theorem kid10_part716_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part716) = true := by rfl

def kid10_part717 : Audit := .cycle 1 20 true (1)
theorem kid10_part717_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part717) = true := by rfl

def kid10_part718 : Audit := .split 14 (5,true) (byMove [
.cycle 0 46 true (-1),
.cycle 10 12 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 32 3 false (4),
.last 16 (2,true),
.cycle 20 3 false (4),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 24 3 false (5),
.cycle 18 3 false (0),
.last 16 (2,true),
.cycle 38 3 false (4),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 19 13 true (1),
.last 16 (2,true),
.cycle 0 40 true (0),
.cycle 38 3 false (4),
.cycle 15 3 false (1),
.cycle 19 7 true (2)
])
theorem kid10_part718_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part718) = true := by rfl

def kid10_part719 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 10 16 true (-1),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 28 1 true (-2),
.cycle 28 1 true (-2),
.cycle 1 14 true (1),
.last 21 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 true (3),
.cycle 15 1 true (5),
.cycle 17 1 true (3),
.cycle 21 1 true (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 22 1 false (-2),
.cycle 15 3 false (1),
.cycle 1 14 true (1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 13 false (3),
.cycle 15 1 true (5)
])
theorem kid10_part719_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part719) = true := by rfl

def kid10_part695 : Audit := .split 11 (5,false) (byMove [(kid10_part696),(kid10_part697),(kid10_part698),(kid10_part699),(kid10_part700),(kid10_part701),(kid10_part702),(kid10_part703),(kid10_part704),(kid10_part705),(kid10_part706),(kid10_part707),(kid10_part708),(kid10_part709),(kid10_part710),(kid10_part711),(kid10_part712),(kid10_part713),(kid10_part714),(kid10_part715),(kid10_part716),(kid10_part717),(kid10_part718),(kid10_part719)])

theorem kid10_part695_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part695) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part696),(kid10_part697),(kid10_part698),(kid10_part699),(kid10_part700),(kid10_part701),(kid10_part702),(kid10_part703),(kid10_part704),(kid10_part705),(kid10_part706),(kid10_part707),(kid10_part708),(kid10_part709),(kid10_part710),(kid10_part711),(kid10_part712),(kid10_part713),(kid10_part714),(kid10_part715),(kid10_part716),(kid10_part717),(kid10_part718),(kid10_part719)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part699_checked

  · exact kid10_part705_checked

  · exact kid10_part711_checked

  · exact kid10_part717_checked

  · exact kid10_part700_checked

  · exact kid10_part706_checked

  · exact kid10_part712_checked

  · exact kid10_part718_checked

  · exact kid10_part701_checked

  · exact kid10_part707_checked

  · exact kid10_part713_checked

  · exact kid10_part719_checked

def kid10_part720 : Audit := .cycle 6 5 true (2)
theorem kid10_part720_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part720) = true := by rfl

def kid10_part721 : Audit := .cycle 1 12 true (1)
theorem kid10_part721_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part721) = true := by rfl

def kid10_part722 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 31 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 7 7 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 19 1 false (1),
.last 14 (5,true),
.cycle 21 7 false (2),
.last 15 (5,true),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 7 7 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 14 (5,true)
]),
.cycle 1 12 true (1),
.cycle 24 1 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 0 13 true (0),
.cycle 41 1 false (9),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.last 30 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 27 (5,false),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.last 13 (5,false),
.cycle 7 7 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.last 21 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 7 19 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 4, 64, 64],[2, 16, 4, 1, 4, 64, 64],96⟩,
.cycle 1 14 true (1),
.cycle 12 16 true (0),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 14 18 true (0),
.last 18 (5,true),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 53 1 false (9),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],4096⟩,
.last 13 (5,true),
.cycle 14 14 true (2),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 13 16 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 7 19 true (2),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 13 20 true (3),
.last 13 (5,true)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 29 3 true (7),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 10 13 true (0),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 31 (5,false),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid10_part722_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part722) = true := by rfl

def kid10_part723 : Audit := .cycle 1 12 true (1)
theorem kid10_part723_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part723) = true := by rfl

def kid10_part724 : Audit := .cycle 24 1 false (6)
theorem kid10_part724_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part724) = true := by rfl

def kid10_part726 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (5,false),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.last 15 (5,false),
.cycle 6 9 true (2),
.last 17 (5,false),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 13 4 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.last 15 (5,false)
])
theorem kid10_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part726) = true := by rfl

def kid10_part727 : Audit := .cycle 0 15 true (0)
theorem kid10_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part727) = true := by rfl

def kid10_part728 : Audit := .split 29 (5,false) (byMove [
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
.cycle 7 24 true (0),
.last 31 (2,true),
.cycle 0 32 true (0),
.cycle 23 7 true (1),
.cycle 35 1 false (3),
.cycle 34 1 false (2),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 10 48 true (0),
.cycle 1 32 true (0),
.cycle 13 22 true (0),
.cycle 29 1 true (5)
])
theorem kid10_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part728) = true := by rfl

def kid10_part729 : Audit := .cycle 21 1 false (1)
theorem kid10_part729_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part729) = true := by rfl

def kid10_part730 : Audit := .cycle 16 1 false (0)
theorem kid10_part730_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part730) = true := by rfl

def kid10_part731 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 21 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 19 1 false (1),
.cycle 15 1 true (3),
.cycle 21 7 false (2),
.last 14 (2,true),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.cycle 17 1 true (1)
])
theorem kid10_part731_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part731) = true := by rfl

def kid10_part732 : Audit := .cycle 1 12 true (1)
theorem kid10_part732_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part732) = true := by rfl

def kid10_part733 : Audit := .cycle 24 1 false (6)
theorem kid10_part733_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part733) = true := by rfl

def kid10_part734 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 22 true (0),
.last 20 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 4, 16777216, 128, 256, 32768, 128, 1048580, 16777216, 128, 256, 2097152, 65536, 4, 16777216, 128, 256, 8, 8388608, 4, 16777216, 16777216],[128, 16, 4, 1, 32, 4, 128, 65536, 16384, 4096, 131072, 16384, 128, 4194304, 1048576, 262144, 8388608, 1048576, 128, 16, 4, 1, 32, 4, 16777216],27412512⟩,
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.last 13 (5,false),
.cycle 7 7 true (2),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 10 20 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 41 true (0),
.last 13 (5,false)
])
theorem kid10_part734_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part734) = true := by rfl

def kid10_part735 : Audit := .cycle 0 13 true (0)
theorem kid10_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part735) = true := by rfl

def kid10_part736 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 33 1 false (5),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 48, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 41 1 false (9),
.cycle 28 1 false (8),
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 24 1 false (6),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 32 1 false (8),
.cycle 13 1 true (5)
])
theorem kid10_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part736) = true := by rfl

def kid10_part737 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (0),
.cycle 43 1 false (5),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 28 1 false (8),
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 11 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part737) = true := by rfl

def kid10_part738 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 9 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.cycle 33 13 false (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 10 15 true (2),
.cycle 7 19 true (2),
.cycle 10 14 true (2),
.cycle 15 1 true (5),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 13 7 true (2),
.cycle 7 18 true (2),
.cycle 10 11 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 13 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part738_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part738) = true := by rfl

def kid10_part739 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 23 1 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (2),
.last 15 (5,false),
.last 20 (5,false),
.cycle 1 14 true (1),
.last 24 (5,false),
.last 35 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 10 4 true (2),
.cycle 20 3 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 17 (5,false)
])
theorem kid10_part739_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part739) = true := by rfl

def kid10_part740 : Audit := .cycle 1 14 true (1)
theorem kid10_part740_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part740) = true := by rfl

def kid10_part741 : Audit := .split 25 (5,false) (byMove [
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
.cycle 7 20 true (0),
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 19 7 true (1),
.cycle 30 1 false (2),
.cycle 29 1 false (1),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 10 40 true (0),
.cycle 1 28 true (0),
.cycle 12 18 true (0),
.cycle 25 1 true (5)
])
theorem kid10_part741_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part741) = true := by rfl

def kid10_part742 : Audit := .cycle 16 1 false (0)
theorem kid10_part742_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part742) = true := by rfl

def kid10_part743 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 9 true (1),
.last 17 (2,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 44 1 false (8),
.cycle 11 2 true (2),
.cycle 7 16 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 7 true (1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 6 true (3),
.cycle 17 3 false (1)
])
theorem kid10_part743_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part743) = true := by rfl

def kid10_part744 : Audit := .cycle 1 12 true (1)
theorem kid10_part744_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part744) = true := by rfl

def kid10_part745 : Audit := .cycle 7 5 true (2)
theorem kid10_part745_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part745) = true := by rfl

def kid10_part746 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 1 false (2),
.last 22 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.last 13 (5,false)
])
theorem kid10_part746_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part746) = true := by rfl

def kid10_part747 : Audit := .cycle 0 13 true (0)
theorem kid10_part747_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part747) = true := by rfl

def kid10_part748 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 3 true (3),
.cycle 15 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 22 3 true (6),
.cycle 29 3 true (7),
.cycle 19 3 true (5),
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 9 5 true (2),
.cycle 16 3 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 3 true (5),
.cycle 13 1 true (5)
])
theorem kid10_part748_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part748) = true := by rfl

def kid10_part749 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
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
.last 18 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part749_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part749) = true := by rfl

def kid10_part725 : Audit := .split 11 (5,true) (byMove [(kid10_part726),(kid10_part727),(kid10_part728),(kid10_part729),(kid10_part730),(kid10_part731),(kid10_part732),(kid10_part733),(kid10_part734),(kid10_part735),(kid10_part736),(kid10_part737),(kid10_part738),(kid10_part739),(kid10_part740),(kid10_part741),(kid10_part742),(kid10_part743),(kid10_part744),(kid10_part745),(kid10_part746),(kid10_part747),(kid10_part748),(kid10_part749)])

theorem kid10_part725_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part725) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part726),(kid10_part727),(kid10_part728),(kid10_part729),(kid10_part730),(kid10_part731),(kid10_part732),(kid10_part733),(kid10_part734),(kid10_part735),(kid10_part736),(kid10_part737),(kid10_part738),(kid10_part739),(kid10_part740),(kid10_part741),(kid10_part742),(kid10_part743),(kid10_part744),(kid10_part745),(kid10_part746),(kid10_part747),(kid10_part748),(kid10_part749)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part726_checked

  · exact kid10_part732_checked

  · exact kid10_part738_checked

  · exact kid10_part744_checked

  · exact kid10_part727_checked

  · exact kid10_part733_checked

  · exact kid10_part739_checked

  · exact kid10_part745_checked

  · exact kid10_part728_checked

  · exact kid10_part734_checked

  · exact kid10_part740_checked

  · exact kid10_part746_checked

  · exact kid10_part729_checked

  · exact kid10_part735_checked

  · exact kid10_part741_checked

  · exact kid10_part747_checked

  · exact kid10_part730_checked

  · exact kid10_part736_checked

  · exact kid10_part742_checked

  · exact kid10_part748_checked

  · exact kid10_part731_checked

  · exact kid10_part737_checked

  · exact kid10_part743_checked

  · exact kid10_part749_checked

def kid10_part750 : Audit := .cycle 12 11 true (2)
theorem kid10_part750_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part750) = true := by rfl

def kid10_part751 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.cycle 15 3 false (1),
.split 13 (5,true) (byMove [
.cycle 1 18 true (0),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 0 25 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.cycle 20 1 false (0),
.last 14 (5,false),
.cycle 15 8 false (2),
.cycle 16 3 false (1),
.last 15 (5,false),
.cycle 1 25 true (0),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 1 24 true (1),
.cycle 17 5 false (1),
.last 14 (5,false)
]),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.cycle 10 13 true (1),
.split 13 (5,true) (byMove [
.last 17 (5,false),
.cycle 0 17 true (0),
.last 23 (5,false),
.last 19 (5,false),
.cycle 17 5 false (2),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 21 27 true (0),
.last 15 (5,false),
.cycle 0 15 true (0),
.last 17 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 1 16 true (1),
.last 21 (5,false),
.cycle 17 5 false (2),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.last 19 (5,false),
.last 15 (5,false)
]),
.cycle 10 19 true (1),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.cycle 15 3 false (1),
.split 13 (5,true) (byMove [
.cycle 11 4 true (0),
.cycle 15 1 false (1),
.last 15 (5,false),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 1 20 true (1),
.cycle 60 1 false (6),
.last 15 (5,false),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.last 17 (5,false),
.cycle 10 6 true (0),
.cycle 16 3 false (1),
.last 15 (5,false),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.last 15 (5,false),
.cycle 1 20 true (1),
.cycle 10 19 true (1),
.cycle 12 2 true (1),
.cycle 5 9 true (1),
.cycle 10 6 true (1),
.last 17 (5,false)
]),
.cycle 10 9 true (1),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.cycle 13 11 true (2),
.split 13 (5,true) (byMove [
.last 17 (5,false),
.cycle 19 7 false (2),
.last 15 (5,false),
.cycle 7 9 true (1),
.last 19 (5,false),
.last 17 (5,false),
.cycle 1 14 true (1),
.last 28 (5,false),
.last 15 (5,false),
.cycle 0 15 true (0),
.last 17 (5,false),
.last 15 (5,false),
.last 19 (5,false),
.last 23 (5,false),
.cycle 12 2 true (2),
.cycle 5 9 true (1),
.cycle 10 6 true (1),
.last 17 (5,false),
.cycle 1 14 true (1),
.cycle 10 9 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.last 19 (5,false),
.last 15 (5,false)
])
])
theorem kid10_part751_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part751) = true := by rfl

def kid10_part752 : Audit := .cycle 5 7 true (1)
theorem kid10_part752_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part752) = true := by rfl

def kid10_part753 : Audit := .cycle 28 1 false (2)
theorem kid10_part753_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part753) = true := by rfl

def kid10_part754 : Audit := .cycle 13 1 false (-1)
theorem kid10_part754_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part754) = true := by rfl

def kid10_part756 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 0 24 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 6 9 true (0),
.cycle 13 20 true (1),
.cycle 10 16 true (0),
.cycle 1 16 true (0),
.last 28 (5,true),
.last 15 (5,true),
.last 34 (5,true),
.cycle 10 6 true (0),
.cycle 13 35 true (-1),
.cycle 1 24 true (0),
.last 16 (5,true),
.last 15 (5,true),
.last 20 (5,true),
.cycle 1 20 true (0),
.cycle 2 15 true (0),
.cycle 1 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid10_part756_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part756) = true := by rfl

def kid10_part757 : Audit := .cycle 13 1 false (1)
theorem kid10_part757_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part757) = true := by rfl

def kid10_part758 : Audit := .split 12 (2,true) (byMove [
.cycle 10 19 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 30 1 false (2),
.cycle 10 36 true (0),
.cycle 22 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-1),
.cycle 36 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.last 28 (5,true),
.cycle 1 20 true (0),
.cycle 10 17 true (0),
.cycle 36 1 false (2),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part758) = true := by rfl

def kid10_part759 : Audit := .cycle 29 1 false (1)
theorem kid10_part759_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part759) = true := by rfl

def kid10_part760 : Audit := .cycle 14 1 false (-2)
theorem kid10_part760_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part760) = true := by rfl

def kid10_part761 : Audit := .split 12 (5,true) (byMove [
.cycle 10 23 true (-1),
.cycle 10 10 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 28 1 false (2),
.last 14 (2,true),
.cycle 20 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 18 1 false (-2),
.last 14 (2,true),
.cycle 34 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 11 true (2),
.last 14 (2,true),
.cycle 10 19 true (0),
.cycle 34 1 false (2),
.cycle 15 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid10_part761_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part761) = true := by rfl

def kid10_part762 : Audit := .cycle 1 16 true (1)
theorem kid10_part762_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part762) = true := by rfl

def kid10_part763 : Audit := .cycle 42 1 false (6)
theorem kid10_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part763) = true := by rfl

def kid10_part764 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.cycle 7 13 true (0),
.cycle 17 1 false (-1),
.cycle 1 16 true (1),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 20, 4, 4, 8192, 16384, 8, 128, 4, 4, 33554432, 67108864, 2097152, 128, 1073741824, 1048576, 33554432, 67108864, 2097152, 20, 1073741824, 1048576, 33554432, 67108864, 134217728, 1442840576, 1141899264, 67108864, 1073741824],[128, 16, 4, 1, 4, 1073741824, 8192, 16, 4, 1, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1048576, 1073741824, 33554432, 268435456, 67108864, 16777216, 1140850688, 1073741824, 1073741824],2135765056⟩,
.cycle 1 14 true (1),
.cycle 42 1 false (6),
.last 13 (5,true),
.last 28 (5,true),
.cycle 10 6 true (1),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.last 18 (5,true),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part764) = true := by rfl

def kid10_part765 : Audit := .cycle 5 7 true (1)
theorem kid10_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part765) = true := by rfl

def kid10_part766 : Audit := .cycle 10 2 true (1)
theorem kid10_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part766) = true := by rfl

def kid10_part767 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 17 (2,true),
.cycle 17 1 false (-1),
.cycle 19 1 true (3),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 42 1 false (6),
.cycle 15 1 true (5),
.cycle 10 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 17 1 false (-1),
.cycle 11 2 true (1),
.cycle 0 24 true (0),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 2 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part767) = true := by rfl

def kid10_part768 : Audit := .cycle 10 4 true (0)
theorem kid10_part768_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part768) = true := by rfl

def kid10_part769 : Audit := .split 16 (2,true) (byMove [
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 4672924418048, 1048576, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 65536, 274877906944, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 65536, 4398046511104, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 4398046511104],[128, 16, 1048576, 1, 274877906944, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 274877906944, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 274877906944, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],5514742202384⟩,
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 10 10 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 65536, 4398046576640, 4096, 524288, 1048576, 32768, 128, 65536, 33554432, 33554432, 67108864, 8, 65536, 65536, 1073741824, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 65536, 524288, 1048576, 32768, 128, 65536, 33554432, 33554432, 67108864, 8, 65536, 4398046511104, 1073741824, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 65536, 4398046511104],[128, 16, 1, 1, 33554432, 4398046511104, 524288, 65536, 4096, 4096, 4398046511104, 4398046511104, 33554432, 16, 1, 1, 65536, 4398046511104, 137438953472, 17179869184, 1073741824, 1073741824, 4398046511104, 4398046511104, 524288, 65536, 4096, 4096, 4398046511104, 4398046511104, 33554432, 16, 1, 1, 65536, 4398046511104, 137438953472, 17179869184, 1073741824, 1073741824, 4398046511104, 4398046511104, 4398046511104],5514742202384⟩,
.last 37 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 1048596, 1048580, 1048580, 8192, 16384, 8, 128, 1048580, 1048580, 33554432, 67108864, 2097152, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 1048596, 1073741824, 67108864, 33554432, 67108864, 134217728, 1443889156, 1141899268, 1141899268, 1073741824],[128, 16, 4, 1, 1048580, 1073741824, 8192, 16, 4, 1, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 1073741824, 1073741824, 33554432, 4194304, 1048576, 262144, 68157444, 1073741824, 33554432, 268435456, 67108864, 16777216, 1141899268, 1073741824, 1073741824],2144153664⟩,
.cycle 1 28 true (-1),
.cycle 10 7 false (2),
.last 17 (5,true),
.cycle 10 9 false (2),
.cycle 12 5 false (1),
.cycle 10 12 true (-2),
.cycle 10 10 true (-1),
.cycle 13 4 false (1),
.last 17 (5,true),
.cycle 10 15 false (3),
.cycle 10 11 false (2),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 274877906944, 4672924418048, 1048576, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 65536, 274877906944, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 524288, 1048576, 32768, 128, 274877906944, 274877906944, 33554432, 67108864, 8, 65536, 4398046511104, 274877906944, 137438953472, 274877906944, 8589934592, 33554432, 4398046511104, 274877906944, 4398046511104],[128, 16, 256, 1, 274877906944, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 67108864, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 524288, 65536, 1048576, 4096, 4398046511104, 4398046511104, 33554432, 16, 67108864, 1, 274877906944, 4398046511104, 137438953472, 17179869184, 274877906944, 1073741824, 4398046511104, 4398046511104, 4398046511104],5514742202384⟩,
.cycle 1 28 true (-1),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid10_part769_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part769) = true := by rfl

def kid10_part770 : Audit := .split 12 (2,true) (byMove [
.cycle 14 25 true (0),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.cycle 18 13 true (1),
.cycle 1 28 true (0),
.cycle 18 1 false (6),
.cycle 1 20 true (0),
.cycle 22 17 true (0),
.last 13 (5,true),
.cycle 10 5 false (2),
.cycle 10 12 true (-2),
.cycle 20 15 true (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 10 8 true (-2),
.last 28 (5,true),
.cycle 10 4 true (0),
.cycle 2 15 true (0),
.cycle 1 20 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part770_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part770) = true := by rfl

def kid10_part771 : Audit := .cycle 29 1 false (1)
theorem kid10_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part771) = true := by rfl

def kid10_part772 : Audit := .cycle 14 1 false (-2)
theorem kid10_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part772) = true := by rfl

def kid10_part773 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 28 1 false (2),
.cycle 15 1 false (1),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 14 1 false (0),
.cycle 17 1 false (5),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 34 1 false (2),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 17 11 true (1),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 12 2 true (0),
.cycle 15 3 true (3)
])
theorem kid10_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part773) = true := by rfl

def kid10_part774 : Audit := .cycle 1 16 true (1)
theorem kid10_part774_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part774) = true := by rfl

def kid10_part775 : Audit := .split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 54 1 false (0),
.last 23 (2,true),
.cycle 12 13 true (1),
.cycle 25 1 false (-1),
.cycle 10 23 true (-1),
.cycle 15 9 true (2),
.cycle 12 11 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 10 13 true (1),
.cycle 1 26 true (1),
.cycle 10 15 true (1),
.cycle 10 17 true (1),
.last 23 (2,true),
.cycle 12 13 true (1),
.cycle 25 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 2, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 15 9 true (2),
.cycle 12 11 true (2),
.last 23 (2,true),
.cycle 5 18 true (1),
.cycle 21 2 true (2),
.cycle 1 26 true (1)
])
theorem kid10_part775_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part775) = true := by rfl

def kid10_part776 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.last 22 (5,true),
.last 13 (5,true),
.last 28 (5,true),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.last 14 (5,true),
.last 13 (5,true),
.last 18 (5,true),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid10_part776_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part776) = true := by rfl

def kid10_part777 : Audit := .cycle 5 7 true (1)
theorem kid10_part777_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part777) = true := by rfl

def kid10_part778 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.cycle 14 6 false (0),
.cycle 1 20 true (1),
.cycle 60 1 false (6),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.cycle 14 8 true (2),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 37 1 false (1),
.cycle 18 1 false (-2),
.cycle 14 3 false (0),
.cycle 1 20 true (1),
.cycle 12 15 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 2 true (1),
.cycle 14 6 true (2)
])
theorem kid10_part778_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part778) = true := by rfl

def kid10_part779 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 20 1 false (0),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 15 1 false (-1),
.cycle 37 1 true (-3),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 10 13 true (1),
.cycle 15 1 true (5),
.cycle 10 21 true (1),
.cycle 10 4 true (1),
.last 13 (2,true),
.cycle 1 20 true (1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 24 true (0),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 12 2 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part779_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part779) = true := by rfl

def kid10_part755 : Audit := .split 11 (5,false) (byMove [(kid10_part756),(kid10_part757),(kid10_part758),(kid10_part759),(kid10_part760),(kid10_part761),(kid10_part762),(kid10_part763),(kid10_part764),(kid10_part765),(kid10_part766),(kid10_part767),(kid10_part768),(kid10_part769),(kid10_part770),(kid10_part771),(kid10_part772),(kid10_part773),(kid10_part774),(kid10_part775),(kid10_part776),(kid10_part777),(kid10_part778),(kid10_part779)])

theorem kid10_part755_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part755) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part756),(kid10_part757),(kid10_part758),(kid10_part759),(kid10_part760),(kid10_part761),(kid10_part762),(kid10_part763),(kid10_part764),(kid10_part765),(kid10_part766),(kid10_part767),(kid10_part768),(kid10_part769),(kid10_part770),(kid10_part771),(kid10_part772),(kid10_part773),(kid10_part774),(kid10_part775),(kid10_part776),(kid10_part777),(kid10_part778),(kid10_part779)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part756_checked

  · exact kid10_part762_checked

  · exact kid10_part768_checked

  · exact kid10_part774_checked

  · exact kid10_part757_checked

  · exact kid10_part763_checked

  · exact kid10_part769_checked

  · exact kid10_part775_checked

  · exact kid10_part758_checked

  · exact kid10_part764_checked

  · exact kid10_part770_checked

  · exact kid10_part776_checked

  · exact kid10_part759_checked

  · exact kid10_part765_checked

  · exact kid10_part771_checked

  · exact kid10_part777_checked

  · exact kid10_part760_checked

  · exact kid10_part766_checked

  · exact kid10_part772_checked

  · exact kid10_part778_checked

  · exact kid10_part761_checked

  · exact kid10_part767_checked

  · exact kid10_part773_checked

  · exact kid10_part779_checked

def kid10_part780 : Audit := .cycle 6 5 true (2)
theorem kid10_part780_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part780) = true := by rfl

def kid10_part781 : Audit := .cycle 1 12 true (1)
theorem kid10_part781_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part781) = true := by rfl

def kid10_part782 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 10 37 true (0),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 21 7 false (2),
.cycle 53 3 false (5),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
]),
.cycle 1 12 true (1),
.cycle 2 18 true (1),
.cycle 2 29 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,false),
.cycle 2 18 true (1),
.cycle 2 18 true (1),
.last 13 (5,false),
.cycle 7 7 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 2 13 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.split 12 (5,true) (byMove [
.cycle 14 4 true (1),
.cycle 1 16 true (1),
.cycle 10 37 true (0),
.cycle 44 1 false (2),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.last 14 (5,false),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.last 15 (5,false),
.cycle 2 19 true (1),
.cycle 18 3 false (2),
.cycle 5 9 true (1),
.cycle 10 31 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.cycle 2 15 true (1),
.last 15 (5,false)
]),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 19 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 15 (5,false),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,false),
.last 13 (5,false)
])
])
theorem kid10_part782_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part782) = true := by rfl

def kid10_part783 : Audit := .cycle 1 12 true (1)
theorem kid10_part783_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part783) = true := by rfl

def kid10_part784 : Audit := .cycle 11 3 true (3)
theorem kid10_part784_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part784) = true := by rfl

def kid10_part786 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,false),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 23 (5,false),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.last 15 (5,false),
.cycle 6 9 true (2),
.last 17 (5,false),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 18 true (1),
.last 15 (5,false)
])
theorem kid10_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part786) = true := by rfl

def kid10_part787 : Audit := .cycle 19 1 false (1)
theorem kid10_part787_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part787) = true := by rfl

def kid10_part788 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.last 21 (5,false),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 29 (5,false),
.cycle 19 1 false (1),
.last 13 (5,false),
.cycle 21 7 false (2),
.last 17 (5,false),
.cycle 7 9 true (1),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
])
theorem kid10_part788_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part788) = true := by rfl

def kid10_part789 : Audit := .cycle 7 7 true (2)
theorem kid10_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part789) = true := by rfl

def kid10_part790 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 23 1 false (1),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 12 2 true (2),
.cycle 21 1 false (-1),
.cycle 1 14 true (1),
.cycle 1 24 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 8 true (2),
.cycle 19 1 true (3),
.cycle 6 12 true (2),
.cycle 17 3 true (3),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 10 4 true (2),
.cycle 21 1 false (-1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 5 true (4),
.cycle 16 1 true (4)
])
theorem kid10_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part790) = true := by rfl

def kid10_part791 : Audit := .split 13 (5,false) (byMove [
.cycle 1 24 true (0),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 24 9 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 1 true (3),
.cycle 15 8 false (2),
.last 26 (2,true),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 20 true (1),
.last 18 (2,true),
.cycle 17 5 false (1),
.cycle 21 1 true (-1)
])
theorem kid10_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part791) = true := by rfl

def kid10_part792 : Audit := .cycle 1 12 true (1)
theorem kid10_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part792) = true := by rfl

def kid10_part793 : Audit := .split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.cycle 1 30 true (1),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 1 21 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 18 9 true (4),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.cycle 18 3 true (4),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 1 22 true (1),
.cycle 10 21 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6)
])
theorem kid10_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part793) = true := by rfl

def kid10_part794 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 24 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (5,false),
.last 20 (5,false),
.last 20 (5,false),
.last 13 (5,false),
.cycle 7 7 true (2),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 24 (5,false),
.last 13 (5,false)
])
theorem kid10_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part794) = true := by rfl

def kid10_part795 : Audit := .cycle 0 13 true (0)
theorem kid10_part795_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part795) = true := by rfl

def kid10_part796 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 8 14 true (2),
.last 14 (2,true),
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
.cycle 12 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 8 8 true (2),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part796_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part796) = true := by rfl

def kid10_part797 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 21 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 13 true (2),
.cycle 3 29 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 13 1 true (5),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part797_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part797) = true := by rfl

def kid10_part798 : Audit := .split 15 (5,false) (byMove [
.cycle 1 16 true (1),
.cycle 6 20 true (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 14 2 true (4),
.cycle 7 11 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 12 9 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.cycle 15 1 true (5),
.cycle 6 10 true (2),
.cycle 13 3 true (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 6 12 true (2),
.cycle 13 5 true (3),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 6 13 true (2),
.cycle 15 1 true (5)
])
theorem kid10_part798_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part798) = true := by rfl

def kid10_part799 : Audit := .split 17 (5,false) (byMove [
.cycle 1 18 true (1),
.cycle 42 1 false (6),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.last 20 (2,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 15 9 true (3),
.cycle 3 15 true (1),
.cycle 8 10 true (2),
.cycle 17 1 true (5),
.cycle 6 12 true (2),
.cycle 15 3 true (3),
.last 18 (2,true),
.cycle 1 19 true (1),
.cycle 13 5 true (3),
.last 20 (2,true),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 13 6 true (3),
.cycle 17 1 true (5)
])
theorem kid10_part799_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part799) = true := by rfl

def kid10_part800 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 1 16 true (1),
.last 29 (5,false),
.cycle 7 13 true (0),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048580, 4, 16777216, 128, 256, 32768, 128, 1048580, 16777216, 128, 256, 2097152, 65536, 4, 16777216, 128, 256, 8, 2048, 4, 16777216, 16777216],[128, 16, 4, 1, 2048, 1, 128, 65536, 16384, 4096, 2048, 1048580, 128, 4194304, 1048576, 262144, 2048, 262144, 128, 16, 4, 1, 2048, 1, 16777216],27412512⟩,
.cycle 1 14 true (1),
.last 17 (5,false),
.cycle 1 16 true (1),
.last 21 (5,false),
.cycle 10 6 true (1),
.cycle 5 9 true (1),
.last 25 (5,false),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 17 (5,false),
.cycle 11 2 true (2)
])
theorem kid10_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part800) = true := by rfl

def kid10_part801 : Audit := .cycle 5 7 true (1)
theorem kid10_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part801) = true := by rfl

def kid10_part802 : Audit := .cycle 10 2 true (2)
theorem kid10_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part802) = true := by rfl

def kid10_part803 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 27 true (0),
.cycle 13 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 10 4 true (1),
.cycle 12 2 true (1),
.cycle 10 6 true (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 1 27 true (0),
.cycle 18 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 16 5 false (2),
.cycle 15 3 false (1)
])
theorem kid10_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part803) = true := by rfl

def kid10_part804 : Audit := .cycle 1 12 true (1)
theorem kid10_part804_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part804) = true := by rfl

def kid10_part805 : Audit := .cycle 7 5 true (2)
theorem kid10_part805_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part805) = true := by rfl

def kid10_part806 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,false),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 15 (5,false),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.last 13 (5,false)
])
theorem kid10_part806_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part806) = true := by rfl

def kid10_part807 : Audit := .cycle 0 13 true (0)
theorem kid10_part807_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part807) = true := by rfl

def kid10_part808 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
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
.cycle 12 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 3 true (5),
.cycle 13 1 true (5)
])
theorem kid10_part808_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part808) = true := by rfl

def kid10_part809 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
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
.cycle 13 3 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 4 true (4),
.cycle 13 1 true (5)
])
theorem kid10_part809_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part809) = true := by rfl

def kid10_part785 : Audit := .split 11 (5,true) (byMove [(kid10_part786),(kid10_part787),(kid10_part788),(kid10_part789),(kid10_part790),(kid10_part791),(kid10_part792),(kid10_part793),(kid10_part794),(kid10_part795),(kid10_part796),(kid10_part797),(kid10_part798),(kid10_part799),(kid10_part800),(kid10_part801),(kid10_part802),(kid10_part803),(kid10_part804),(kid10_part805),(kid10_part806),(kid10_part807),(kid10_part808),(kid10_part809)])

theorem kid10_part785_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part785) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part786),(kid10_part787),(kid10_part788),(kid10_part789),(kid10_part790),(kid10_part791),(kid10_part792),(kid10_part793),(kid10_part794),(kid10_part795),(kid10_part796),(kid10_part797),(kid10_part798),(kid10_part799),(kid10_part800),(kid10_part801),(kid10_part802),(kid10_part803),(kid10_part804),(kid10_part805),(kid10_part806),(kid10_part807),(kid10_part808),(kid10_part809)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part786_checked

  · exact kid10_part792_checked

  · exact kid10_part798_checked

  · exact kid10_part804_checked

  · exact kid10_part787_checked

  · exact kid10_part793_checked

  · exact kid10_part799_checked

  · exact kid10_part805_checked

  · exact kid10_part788_checked

  · exact kid10_part794_checked

  · exact kid10_part800_checked

  · exact kid10_part806_checked

  · exact kid10_part789_checked

  · exact kid10_part795_checked

  · exact kid10_part801_checked

  · exact kid10_part807_checked

  · exact kid10_part790_checked

  · exact kid10_part796_checked

  · exact kid10_part802_checked

  · exact kid10_part808_checked

  · exact kid10_part791_checked

  · exact kid10_part797_checked

  · exact kid10_part803_checked

  · exact kid10_part809_checked

def kid10_part689 : Audit := .split 10 (4,true) (byMove [(kid10_part690),(kid10_part691),(kid10_part692),(kid10_part693),(kid10_part694),(kid10_part695),(kid10_part720),(kid10_part721),(kid10_part722),(kid10_part723),(kid10_part724),(kid10_part725),(kid10_part750),(kid10_part751),(kid10_part752),(kid10_part753),(kid10_part754),(kid10_part755),(kid10_part780),(kid10_part781),(kid10_part782),(kid10_part783),(kid10_part784),(kid10_part785)])

theorem kid10_part689_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid10_part689) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part690),(kid10_part691),(kid10_part692),(kid10_part693),(kid10_part694),(kid10_part695),(kid10_part720),(kid10_part721),(kid10_part722),(kid10_part723),(kid10_part724),(kid10_part725),(kid10_part750),(kid10_part751),(kid10_part752),(kid10_part753),(kid10_part754),(kid10_part755),(kid10_part780),(kid10_part781),(kid10_part782),(kid10_part783),(kid10_part784),(kid10_part785)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part690_checked

  · exact kid10_part720_checked

  · exact kid10_part750_checked

  · exact kid10_part780_checked

  · exact kid10_part691_checked

  · exact kid10_part721_checked

  · exact kid10_part751_checked

  · exact kid10_part781_checked

  · exact kid10_part692_checked

  · exact kid10_part722_checked

  · exact kid10_part752_checked

  · exact kid10_part782_checked

  · exact kid10_part693_checked

  · exact kid10_part723_checked

  · exact kid10_part753_checked

  · exact kid10_part783_checked

  · exact kid10_part694_checked

  · exact kid10_part724_checked

  · exact kid10_part754_checked

  · exact kid10_part784_checked

  · exact kid10_part695_checked

  · exact kid10_part725_checked

  · exact kid10_part755_checked

  · exact kid10_part785_checked

def kid10_part812 : Audit := .cycle 1 13 true (1)
theorem kid10_part812_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part812) = true := by rfl

def kid10_part813 : Audit := .cycle 7 6 true (2)
theorem kid10_part813_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part813) = true := by rfl

def kid10_part814 : Audit := .cycle 29 1 false (1)
theorem kid10_part814_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part814) = true := by rfl

def kid10_part815 : Audit := .cycle 0 14 true (0)
theorem kid10_part815_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part815) = true := by rfl

def kid10_part816 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.last 16 (5,true),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 8 24 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 6 8 true (2),
.cycle 23 3 false (1),
.last 16 (5,true),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 1 15 true (1)
])
theorem kid10_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part816) = true := by rfl

def kid10_part817 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 25 7 false (2),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 16 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (2),
.cycle 0 15 true (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 17 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 1 15 true (1)
])
theorem kid10_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part817) = true := by rfl

def kid10_part818 : Audit := .cycle 0 13 true (0)
theorem kid10_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part818) = true := by rfl

def kid10_part819 : Audit := .cycle 1 12 true (1)
theorem kid10_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part819) = true := by rfl

def kid10_part820 : Audit := .split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 22 (5,true),
.cycle 1 22 true (1),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 14 7 true (3),
.cycle 11 13 true (3),
.cycle 0 22 true (0),
.cycle 7 15 true (2),
.cycle 11 10 true (3),
.cycle 0 23 true (0),
.cycle 4 17 true (1),
.last 22 (5,true),
.cycle 9 12 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 22 (5,true),
.cycle 1 22 true (1)
])
theorem kid10_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part820) = true := by rfl

def kid10_part821 : Audit := .cycle 3 10 true (1)
theorem kid10_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part821) = true := by rfl

def kid10_part822 : Audit := .cycle 8 5 true (2)
theorem kid10_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part822) = true := by rfl

def kid10_part823 : Audit := .cycle 0 14 true (0)
theorem kid10_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part823) = true := by rfl

def kid10_part824 : Audit := .cycle 6 7 true (2)
theorem kid10_part824_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part824) = true := by rfl

def kid10_part825 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 1 16 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 13 7 true (2),
.cycle 11 7 true (3),
.cycle 0 16 true (0),
.cycle 7 9 true (2),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 9 6 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 1 16 true (1)
])
theorem kid10_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part825) = true := by rfl

def kid10_part826 : Audit := .cycle 5 11 true (1)
theorem kid10_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part826) = true := by rfl

def kid10_part827 : Audit := .cycle 1 14 true (1)
theorem kid10_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part827) = true := by rfl

def kid10_part828 : Audit := .split 13 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.last 16 (5,true),
.cycle 7 9 true (2),
.last 16 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 11 7 true (3),
.last 14 (5,true),
.cycle 7 11 true (2),
.cycle 23 3 false (1),
.last 16 (5,true),
.cycle 5 9 true (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid10_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part828) = true := by rfl

def kid10_part829 : Audit := .split 13 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 25 7 false (2),
.cycle 17 6 false (2),
.cycle 7 9 true (2),
.last 14 (4,true),
.last 24 (4,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 9 6 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 16 true (0),
.last 16 (4,true),
.last 15 (4,true),
.cycle 17 6 false (2),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 17 6 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 16 true (1)
])
theorem kid10_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part829) = true := by rfl

def kid10_part830 : Audit := .cycle 0 13 true (0)
theorem kid10_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part830) = true := by rfl

def kid10_part831 : Audit := .cycle 1 12 true (1)
theorem kid10_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part831) = true := by rfl

def kid10_part832 : Audit := .cycle 2 11 true (1)
theorem kid10_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part832) = true := by rfl

def kid10_part833 : Audit := .cycle 1 15 true (1)
theorem kid10_part833_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part833) = true := by rfl

def kid10_part834 : Audit := .split 14 (5,true) (byMove [
.cycle 10 5 true (2),
.last 21 (4,true),
.last 27 (4,true),
.cycle 7 10 true (2),
.last 15 (4,true),
.last 31 (4,true),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 0 17 true (0),
.last 17 (4,true),
.last 16 (4,true),
.last 16 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 1 17 true (1)
])
theorem kid10_part834_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part834) = true := by rfl

def kid10_part835 : Audit := .cycle 1 14 true (1)
theorem kid10_part835_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part835) = true := by rfl

def kid10_part811 : Audit := .split 12 (2,true) (byMove [(kid10_part812),(kid10_part813),(kid10_part814),(kid10_part815),(kid10_part816),(kid10_part817),(kid10_part818),(kid10_part819),(kid10_part820),(kid10_part821),(kid10_part822),(kid10_part823),(kid10_part824),(kid10_part825),(kid10_part826),(kid10_part827),(kid10_part828),(kid10_part829),(kid10_part830),(kid10_part831),(kid10_part832),(kid10_part833),(kid10_part834),(kid10_part835)])

theorem kid10_part811_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part811) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid10_part812),(kid10_part813),(kid10_part814),(kid10_part815),(kid10_part816),(kid10_part817),(kid10_part818),(kid10_part819),(kid10_part820),(kid10_part821),(kid10_part822),(kid10_part823),(kid10_part824),(kid10_part825),(kid10_part826),(kid10_part827),(kid10_part828),(kid10_part829),(kid10_part830),(kid10_part831),(kid10_part832),(kid10_part833),(kid10_part834),(kid10_part835)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part812_checked

  · exact kid10_part818_checked

  · exact kid10_part824_checked

  · exact kid10_part830_checked

  · exact kid10_part813_checked

  · exact kid10_part819_checked

  · exact kid10_part825_checked

  · exact kid10_part831_checked

  · exact kid10_part814_checked

  · exact kid10_part820_checked

  · exact kid10_part826_checked

  · exact kid10_part832_checked

  · exact kid10_part815_checked

  · exact kid10_part821_checked

  · exact kid10_part827_checked

  · exact kid10_part833_checked

  · exact kid10_part816_checked

  · exact kid10_part822_checked

  · exact kid10_part828_checked

  · exact kid10_part834_checked

  · exact kid10_part817_checked

  · exact kid10_part823_checked

  · exact kid10_part829_checked

  · exact kid10_part835_checked

def kid10_part836 : Audit := .cycle 1 16 true (1)
theorem kid10_part836_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part836) = true := by rfl

def kid10_part838 : Audit := .cycle 0 15 true (0)
theorem kid10_part838_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part838) = true := by rfl

def kid10_part839 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (5,true),
.cycle 1 20 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 1 28 true (1),
.cycle 13 7 true (1),
.cycle 12 9 true (1),
.cycle 13 9 true (1),
.cycle 43 1 false (1),
.cycle 7 14 true (1),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (5,true),
.cycle 9 10 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (5,true),
.cycle 1 20 true (1)
])
theorem kid10_part839_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part839) = true := by rfl

def kid10_part840 : Audit := .cycle 21 1 false (1)
theorem kid10_part840_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part840) = true := by rfl

def kid10_part841 : Audit := .cycle 0 17 true (0)
theorem kid10_part841_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part841) = true := by rfl

def kid10_part842 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 19 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 13 (4,true),
.cycle 16 1 false (2),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 20 1 false (-2),
.last 14 (4,true),
.last 17 (4,true),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part842_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part842) = true := by rfl

def kid10_part843 : Audit := .cycle 15 1 false (-1)
theorem kid10_part843_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part843) = true := by rfl

def kid10_part844 : Audit := .cycle 7 5 true (2)
theorem kid10_part844_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part844) = true := by rfl

def kid10_part845 : Audit := .cycle 1 12 true (1)
theorem kid10_part845_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part845) = true := by rfl

def kid10_part846 : Audit := .cycle 0 13 true (0)
theorem kid10_part846_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part846) = true := by rfl

def kid10_part847 : Audit := .split 17 (4,true) (byMove [
.cycle 3 18 true (0),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.cycle 3 20 true (0),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 1 18 true (0),
.cycle 11 11 true (0),
.cycle 11 9 true (0),
.cycle 0 19 true (0),
.cycle 11 11 true (0),
.last 18 (5,true),
.cycle 19 11 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (4),
.last 19 (5,true),
.cycle 20 1 false (2),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.cycle 0 37 true (0),
.cycle 0 19 true (0),
.last 20 (5,true),
.last 18 (5,true)
])
theorem kid10_part847_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part847) = true := by rfl

def kid10_part848 : Audit := .split 19 (4,true) (byMove [
.cycle 35 1 false (1),
.cycle 0 23 true (0),
.cycle 39 1 false (3),
.cycle 34 1 false (2),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 1 20 true (0),
.cycle 14 11 true (0),
.cycle 14 11 true (0),
.cycle 0 21 true (0),
.cycle 14 11 true (0),
.last 20 (5,true),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.cycle 1 22 true (0),
.cycle 35 1 false (3),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.cycle 8 13 true (0),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid10_part848_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part848) = true := by rfl

def kid10_part849 : Audit := .split 19 (4,true) (byMove [
.cycle 2 22 true (0),
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 2 24 true (0),
.last 21 (5,true),
.cycle 24 1 false (2),
.cycle 1 20 true (0),
.cycle 11 11 true (0),
.cycle 13 11 true (0),
.cycle 0 21 true (0),
.cycle 11 11 true (0),
.last 20 (5,true),
.cycle 21 13 true (2),
.last 22 (5,true),
.cycle 1 22 true (0),
.cycle 34 1 false (4),
.last 21 (5,true),
.cycle 24 1 false (2),
.cycle 1 20 true (0),
.cycle 7 13 true (0),
.last 42 (5,true),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid10_part849_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part849) = true := by rfl

def kid10_part850 : Audit := .cycle 17 5 false (2)
theorem kid10_part850_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part850) = true := by rfl

def kid10_part851 : Audit := .split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 22 true (1),
.cycle 29 1 false (1),
.cycle 0 21 true (0),
.last 16 (5,true),
.cycle 23 1 false (-1),
.cycle 7 9 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 0 23 true (0),
.cycle 18 11 true (0),
.last 24 (5,true),
.cycle 19 9 false (2),
.cycle 11 4 true (1),
.cycle 7 11 true (1),
.cycle 26 1 false (0),
.last 16 (5,true),
.cycle 23 1 false (-1),
.cycle 12 7 true (1),
.cycle 1 18 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 9 6 true (1)
])
theorem kid10_part851_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part851) = true := by rfl

def kid10_part852 : Audit := .cycle 7 7 true (1)
theorem kid10_part852_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part852) = true := by rfl

def kid10_part853 : Audit := .cycle 18 1 false (0)
theorem kid10_part853_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part853) = true := by rfl

def kid10_part854 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 19 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 21 1 false (-1),
.last 14 (4,true),
.cycle 17 1 false (-1),
.last 17 (4,true),
.last 13 (4,true),
.cycle 17 1 false (3),
.last 15 (4,true),
.last 15 (4,true),
.cycle 23 1 false (-1),
.cycle 13 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.last 18 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 17 (4,true),
.last 13 (4,true),
.last 17 (4,true)
])
theorem kid10_part854_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part854) = true := by rfl

def kid10_part855 : Audit := .cycle 15 1 false (-1)
theorem kid10_part855_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part855) = true := by rfl

def kid10_part856 : Audit := .cycle 7 5 true (2)
theorem kid10_part856_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part856) = true := by rfl

def kid10_part857 : Audit := .cycle 1 12 true (1)
theorem kid10_part857_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part857) = true := by rfl

def kid10_part858 : Audit := .cycle 0 13 true (0)
theorem kid10_part858_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part858) = true := by rfl

def kid10_part859 : Audit := .cycle 4 7 true (1)
theorem kid10_part859_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part859) = true := by rfl

def kid10_part860 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 18 1 false (-2),
.cycle 19 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.cycle 18 1 false (-2),
.cycle 19 1 false (-1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 13 5 true (3)
])
theorem kid10_part860_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part860) = true := by rfl

def kid10_part861 : Audit := .cycle 9 2 true (2)
theorem kid10_part861_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part861) = true := by rfl

def kid10_part837 : Audit := .split 10 (2,true) (byMove [(kid10_part838),(kid10_part839),(kid10_part840),(kid10_part841),(kid10_part842),(kid10_part843),(kid10_part844),(kid10_part845),(kid10_part846),(kid10_part847),(kid10_part848),(kid10_part849),(kid10_part850),(kid10_part851),(kid10_part852),(kid10_part853),(kid10_part854),(kid10_part855),(kid10_part856),(kid10_part857),(kid10_part858),(kid10_part859),(kid10_part860),(kid10_part861)])

theorem kid10_part837_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part837) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part838),(kid10_part839),(kid10_part840),(kid10_part841),(kid10_part842),(kid10_part843),(kid10_part844),(kid10_part845),(kid10_part846),(kid10_part847),(kid10_part848),(kid10_part849),(kid10_part850),(kid10_part851),(kid10_part852),(kid10_part853),(kid10_part854),(kid10_part855),(kid10_part856),(kid10_part857),(kid10_part858),(kid10_part859),(kid10_part860),(kid10_part861)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part838_checked

  · exact kid10_part844_checked

  · exact kid10_part850_checked

  · exact kid10_part856_checked

  · exact kid10_part839_checked

  · exact kid10_part845_checked

  · exact kid10_part851_checked

  · exact kid10_part857_checked

  · exact kid10_part840_checked

  · exact kid10_part846_checked

  · exact kid10_part852_checked

  · exact kid10_part858_checked

  · exact kid10_part841_checked

  · exact kid10_part847_checked

  · exact kid10_part853_checked

  · exact kid10_part859_checked

  · exact kid10_part842_checked

  · exact kid10_part848_checked

  · exact kid10_part854_checked

  · exact kid10_part860_checked

  · exact kid10_part843_checked

  · exact kid10_part849_checked

  · exact kid10_part855_checked

  · exact kid10_part861_checked

def kid10_part862 : Audit := .cycle 7 5 true (2)
theorem kid10_part862_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part862) = true := by rfl

def kid10_part864 : Audit := .cycle 0 15 true (0)
theorem kid10_part864_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part864) = true := by rfl

def kid10_part865 : Audit := .cycle 1 18 true (1)
theorem kid10_part865_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part865) = true := by rfl

def kid10_part866 : Audit := .cycle 21 1 false (1)
theorem kid10_part866_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part866) = true := by rfl

def kid10_part867 : Audit := .cycle 0 17 true (0)
theorem kid10_part867_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part867) = true := by rfl

def kid10_part868 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 14 2 false (2),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 17 true (0),
.cycle 17 2 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
])
theorem kid10_part868_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part868) = true := by rfl

def kid10_part869 : Audit := .cycle 13 2 false (-1)
theorem kid10_part869_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part869) = true := by rfl

def kid10_part870 : Audit := .cycle 7 5 true (2)
theorem kid10_part870_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part870) = true := by rfl

def kid10_part871 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 22 2 false (2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 128, 1073741824, 256, 128, 256, 2097152, 65536, 269320576, 1073741824, 128, 256, 134217728, 524288, 1073741824, 269320576, 128, 256, 2097152, 268435456, 269320576, 1073741824, 1073741824],[128, 16, 0, 1, 2, 1073741824, 128, 65536, 269320576, 4096, 8192, 1073741824, 128, 4194304, 65536, 262144, 524288, 1073741824, 128, 268435456, 524288, 16777216, 33554432, 1073741824, 128, 4194304, 268435456, 262144, 524288, 1073741824, 1073741824],1614939136⟩,
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 20 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 1 14 true (1)
])
theorem kid10_part871_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part871) = true := by rfl

def kid10_part872 : Audit := .cycle 0 13 true (0)
theorem kid10_part872_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part872) = true := by rfl

def kid10_part873 : Audit := .cycle 0 19 true (0)
theorem kid10_part873_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part873) = true := by rfl

def kid10_part874 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 30 31 false (7),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 16 2 false (2),
.last 15 (2,true),
.cycle 29 2 false (5),
.cycle 16 2 false (2),
.cycle 16 2 false (2),
.cycle 10 7 false (3),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 17 (2,true),
.cycle 19 2 false (1),
.last 15 (2,true),
.cycle 7 18 true (0),
.cycle 19 2 false (1),
.cycle 21 2 false (1)
])
theorem kid10_part874_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part874) = true := by rfl

def kid10_part875 : Audit := .cycle 15 2 false (1)
theorem kid10_part875_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part875) = true := by rfl

def kid10_part876 : Audit := .cycle 17 5 false (2)
theorem kid10_part876_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part876) = true := by rfl

def kid10_part877 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 3 18 true (1),
.cycle 17 5 false (2),
.last 15 (5,true),
.cycle 19 7 false (2),
.cycle 10 4 true (1),
.cycle 37 17 true (1),
.cycle 1 18 true (1),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 10 9 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 10 6 true (1)
])
theorem kid10_part877_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part877) = true := by rfl

def kid10_part878 : Audit := .cycle 7 7 true (1)
theorem kid10_part878_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part878) = true := by rfl

def kid10_part879 : Audit := .cycle 18 1 false (0)
theorem kid10_part879_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part879) = true := by rfl

def kid10_part880 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 18 2 false (0),
.cycle 15 2 false (1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 2 false (0),
.cycle 15 2 false (3),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 20 2 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 4 true (0),
.last 13 (2,true),
.last 16 (2,true),
.cycle 15 2 false (-1),
.cycle 19 2 false (-1)
])
theorem kid10_part880_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part880) = true := by rfl

def kid10_part881 : Audit := .cycle 13 2 false (-1)
theorem kid10_part881_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part881) = true := by rfl

def kid10_part882 : Audit := .cycle 7 5 true (2)
theorem kid10_part882_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part882) = true := by rfl

def kid10_part883 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 20 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 15 (5,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 1 14 true (1)
])
theorem kid10_part883_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part883) = true := by rfl

def kid10_part884 : Audit := .cycle 0 13 true (0)
theorem kid10_part884_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part884) = true := by rfl

def kid10_part885 : Audit := .cycle 4 7 true (1)
theorem kid10_part885_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part885) = true := by rfl

def kid10_part886 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.last 23 (2,true),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 7 true (2),
.cycle 40 2 false (8),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 3 true (4),
.cycle 25 2 false (3),
.cycle 20 5 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 5 34 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1),
.cycle 6 7 true (2),
.cycle 7 10 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 14 3 true (4),
.cycle 13 5 true (3)
])
theorem kid10_part886_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part886) = true := by rfl

def kid10_part887 : Audit := .cycle 9 2 true (2)
theorem kid10_part887_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part887) = true := by rfl

def kid10_part863 : Audit := .split 10 (4,true) (byMove [(kid10_part864),(kid10_part865),(kid10_part866),(kid10_part867),(kid10_part868),(kid10_part869),(kid10_part870),(kid10_part871),(kid10_part872),(kid10_part873),(kid10_part874),(kid10_part875),(kid10_part876),(kid10_part877),(kid10_part878),(kid10_part879),(kid10_part880),(kid10_part881),(kid10_part882),(kid10_part883),(kid10_part884),(kid10_part885),(kid10_part886),(kid10_part887)])

theorem kid10_part863_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part863) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part864),(kid10_part865),(kid10_part866),(kid10_part867),(kid10_part868),(kid10_part869),(kid10_part870),(kid10_part871),(kid10_part872),(kid10_part873),(kid10_part874),(kid10_part875),(kid10_part876),(kid10_part877),(kid10_part878),(kid10_part879),(kid10_part880),(kid10_part881),(kid10_part882),(kid10_part883),(kid10_part884),(kid10_part885),(kid10_part886),(kid10_part887)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part864_checked

  · exact kid10_part870_checked

  · exact kid10_part876_checked

  · exact kid10_part882_checked

  · exact kid10_part865_checked

  · exact kid10_part871_checked

  · exact kid10_part877_checked

  · exact kid10_part883_checked

  · exact kid10_part866_checked

  · exact kid10_part872_checked

  · exact kid10_part878_checked

  · exact kid10_part884_checked

  · exact kid10_part867_checked

  · exact kid10_part873_checked

  · exact kid10_part879_checked

  · exact kid10_part885_checked

  · exact kid10_part868_checked

  · exact kid10_part874_checked

  · exact kid10_part880_checked

  · exact kid10_part886_checked

  · exact kid10_part869_checked

  · exact kid10_part875_checked

  · exact kid10_part881_checked

  · exact kid10_part887_checked

def kid10_part888 : Audit := .split 10 (5,true) (byMove [
.cycle 0 15 true (0),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.cycle 1 20 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 28 (2,true),
.cycle 13 7 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 8, 128, 17, 16, 4096],[128, 16, 4096, 1, 16, 8, 128, 16, 4096, 1, 16, 16, 4096],4096⟩,
.cycle 1 22 true (1),
.cycle 74 1 false (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.cycle 1 24 true (1),
.cycle 9 10 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 0 24 true (0),
.cycle 1 20 true (1)
]),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 26 (4,true),
.last 21 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 1 15 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 35 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 0 23 true (0),
.cycle 1 14 true (1)
]),
.cycle 0 13 true (0),
.split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.last 22 (2,true),
.cycle 26 1 false (4),
.cycle 20 1 false (2),
.cycle 1 18 true (0),
.cycle 24 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 24 1 false (2),
.cycle 11 9 true (0),
.cycle 19 11 true (2),
.last 19 (2,true),
.cycle 1 20 true (0),
.cycle 30 1 false (4),
.cycle 26 1 false (4),
.cycle 20 1 false (2),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.cycle 0 37 true (0)
]),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 17 5 false (2),
.split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.last 13 (4,true),
.last 15 (4,true),
.cycle 7 7 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 18 (4,true),
.last 17 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.last 36 (4,true),
.cycle 1 18 true (1),
.last 13 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (4,true),
.last 16 (4,true)
]),
.cycle 7 7 true (1),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 1 15 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 7 7 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 1 14 true (1)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 24 1 false (0),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 20 1 false (-2),
.cycle 10 4 true (2),
.cycle 1 14 true (1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 14 6 true (4),
.cycle 7 11 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 1 false (-2),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 3 true (4),
.cycle 14 5 true (4)
]),
.cycle 9 2 true (2)
])
theorem kid10_part888_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part888) = true := by rfl

def kid10_part889 : Audit := .cycle 1 10 true (1)
theorem kid10_part889_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part889) = true := by rfl

def kid10_part890 : Audit := .cycle 7 3 true (3)
theorem kid10_part890_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part890) = true := by rfl

def kid10_part892 : Audit := .cycle 0 11 true (0)
theorem kid10_part892_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part892) = true := by rfl

def kid10_part893 : Audit := .cycle 1 10 true (1)
theorem kid10_part893_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part893) = true := by rfl

def kid10_part894 : Audit := .cycle 2 9 true (1)
theorem kid10_part894_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part894) = true := by rfl

def kid10_part895 : Audit := .cycle 1 13 true (1)
theorem kid10_part895_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part895) = true := by rfl

def kid10_part896 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 0 16 true (0),
.last 19 (4,true),
.last 18 (4,true),
.cycle 15 3 false (-1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 26 3 false (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 22 (4,true)
])
theorem kid10_part896_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part896) = true := by rfl

def kid10_part897 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 11 9 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 11 true (3),
.cycle 13 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 8, 1, 16, 4096, 128, 16, 4096, 1, 16, 4096, 4096],5120⟩,
.last 31 (5,true),
.cycle 7 14 true (2),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 11 9 true (2)
])
theorem kid10_part897_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part897) = true := by rfl

def kid10_part898 : Audit := .cycle 0 11 true (0)
theorem kid10_part898_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part898) = true := by rfl

def kid10_part899 : Audit := .cycle 1 10 true (1)
theorem kid10_part899_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part899) = true := by rfl

def kid10_part900 : Audit := .split 19 (4,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 1 35 true (1),
.last 21 (5,true),
.cycle 0 23 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 2, 4096, 128, 16, 4, 1, 2, 4096, 4096],5120⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 21 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 16, 4096, 128, 16, 4, 1, 16, 4096, 4096],5120⟩,
.last 20 (5,true),
.cycle 7 17 true (2),
.cycle 10 12 true (2),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.last 21 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],5120⟩,
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.last 22 (5,true),
.last 20 (5,true)
])
theorem kid10_part900_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part900) = true := by rfl

def kid10_part901 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 19 (5,true),
.cycle 11 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 19 9 true (3),
.cycle 11 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 8, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 8, 1, 16, 4096, 128, 16, 8, 1, 16, 4096, 4096],5120⟩,
.last 29 (5,true),
.cycle 7 12 true (2),
.cycle 3 17 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 9 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 19 (5,true),
.cycle 11 9 true (2)
])
theorem kid10_part901_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part901) = true := by rfl

def kid10_part902 : Audit := .cycle 8 3 true (3)
theorem kid10_part902_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part902) = true := by rfl

def kid10_part903 : Audit := .split 21 (4,true) (byMove [
.last 25 (5,true),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.last 27 (5,true),
.last 23 (5,true),
.cycle 1 25 true (1),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 23 (5,true),
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 32, 1, 16, 4096, 128, 16, 32, 1, 16, 4096, 4096],5120⟩,
.last 22 (5,true),
.cycle 7 22 true (2),
.last 24 (5,true),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.last 23 (5,true),
.last 24 (5,true),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.last 23 (5,true),
.cycle 1 23 true (1),
.last 25 (5,true),
.last 22 (5,true)
])
theorem kid10_part903_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part903) = true := by rfl

def kid10_part904 : Audit := .cycle 7 5 true (3)
theorem kid10_part904_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part904) = true := by rfl

def kid10_part905 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 13 9 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 13 7 true (2),
.cycle 8 7 true (3),
.last 26 (5,true),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 13 9 true (3)
])
theorem kid10_part905_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part905) = true := by rfl

def kid10_part906 : Audit := .cycle 0 13 true (0)
theorem kid10_part906_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part906) = true := by rfl

def kid10_part907 : Audit := .cycle 4 7 true (1)
theorem kid10_part907_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part907) = true := by rfl

def kid10_part908 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 1 16 true (1),
.last 19 (4,true),
.last 18 (4,true),
.cycle 15 3 false (-1),
.cycle 1 16 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 27 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 5 9 true (1),
.last 17 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 23 (4,true)
])
theorem kid10_part908_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part908) = true := by rfl

def kid10_part909 : Audit := .cycle 9 2 true (3)
theorem kid10_part909_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part909) = true := by rfl

def kid10_part910 : Audit := .cycle 0 11 true (0)
theorem kid10_part910_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part910) = true := by rfl

def kid10_part911 : Audit := .cycle 1 10 true (1)
theorem kid10_part911_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part911) = true := by rfl

def kid10_part912 : Audit := .cycle 2 9 true (1)
theorem kid10_part912_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part912) = true := by rfl

def kid10_part913 : Audit := .cycle 1 13 true (1)
theorem kid10_part913_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part913) = true := by rfl

def kid10_part914 : Audit := .split 12 (5,true) (byMove [
.cycle 14 5 true (4),
.cycle 0 16 true (0),
.last 19 (4,true),
.cycle 7 15 true (2),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 25 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 15 true (1),
.last 17 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 22 (4,true)
])
theorem kid10_part914_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part914) = true := by rfl

def kid10_part915 : Audit := .split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 11 9 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 19 true (4),
.cycle 13 7 true (4),
.cycle 8 12 true (3),
.last 31 (5,true),
.cycle 7 14 true (3),
.cycle 10 11 true (4),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 9 11 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.last 21 (5,true),
.cycle 11 9 true (4)
])
theorem kid10_part915_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part915) = true := by rfl

def kid10_part891 : Audit := .split 10 (2,true) (byMove [(kid10_part892),(kid10_part893),(kid10_part894),(kid10_part895),(kid10_part896),(kid10_part897),(kid10_part898),(kid10_part899),(kid10_part900),(kid10_part901),(kid10_part902),(kid10_part903),(kid10_part904),(kid10_part905),(kid10_part906),(kid10_part907),(kid10_part908),(kid10_part909),(kid10_part910),(kid10_part911),(kid10_part912),(kid10_part913),(kid10_part914),(kid10_part915)])

theorem kid10_part891_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part891) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid10_part892),(kid10_part893),(kid10_part894),(kid10_part895),(kid10_part896),(kid10_part897),(kid10_part898),(kid10_part899),(kid10_part900),(kid10_part901),(kid10_part902),(kid10_part903),(kid10_part904),(kid10_part905),(kid10_part906),(kid10_part907),(kid10_part908),(kid10_part909),(kid10_part910),(kid10_part911),(kid10_part912),(kid10_part913),(kid10_part914),(kid10_part915)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part892_checked

  · exact kid10_part898_checked

  · exact kid10_part904_checked

  · exact kid10_part910_checked

  · exact kid10_part893_checked

  · exact kid10_part899_checked

  · exact kid10_part905_checked

  · exact kid10_part911_checked

  · exact kid10_part894_checked

  · exact kid10_part900_checked

  · exact kid10_part906_checked

  · exact kid10_part912_checked

  · exact kid10_part895_checked

  · exact kid10_part901_checked

  · exact kid10_part907_checked

  · exact kid10_part913_checked

  · exact kid10_part896_checked

  · exact kid10_part902_checked

  · exact kid10_part908_checked

  · exact kid10_part914_checked

  · exact kid10_part897_checked

  · exact kid10_part903_checked

  · exact kid10_part909_checked

  · exact kid10_part915_checked

def kid10_part916 : Audit := .cycle 0 11 true (0)
theorem kid10_part916_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part916) = true := by rfl

def kid10_part917 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.last 17 (2,true),
.cycle 15 3 false (-1),
.cycle 20 3 false (0),
.cycle 1 13 true (1),
.cycle 26 3 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 3 false (1),
.cycle 31 3 false (3),
.cycle 19 5 false (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 8 7 true (2)
]),
.cycle 8 4 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 18 true (2),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],5120⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 12 9 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 16, 1, 4, 4096, 128, 16, 16, 1, 4, 4096, 4096],5120⟩,
.last 38 (5,true),
.cycle 7 15 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (2),
.cycle 19 4 true (4),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4096, 1, 4, 4096, 4096],5120⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.last 22 (5,true),
.cycle 8 14 true (2)
]),
.cycle 10 7 true (2),
.cycle 8 3 true (3),
.cycle 8 4 true (3),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 8 6 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 8 6 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 23 1 false (1),
.last 17 (2,true),
.cycle 15 3 false (-1),
.cycle 20 3 false (0),
.cycle 6 7 true (2),
.cycle 24 3 false (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 19 3 false (1),
.cycle 40 3 false (8),
.cycle 19 5 false (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 20 1 false (0),
.cycle 15 3 false (-1),
.cycle 17 3 false (0),
.cycle 6 7 true (2),
.cycle 10 4 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 3 false (0),
.cycle 8 8 true (2)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 10 9 true (2),
.last 17 (2,true),
.cycle 15 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 7 true (3),
.cycle 10 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 7 true (2),
.cycle 23 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 8 7 true (3)
]),
.cycle 8 4 true (3)
])
theorem kid10_part917_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part917) = true := by rfl

def kid10_part918 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 14 3 false (0),
.cycle 11 1 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.last 22 (2,true),
.last 36 (2,true),
.cycle 1 20 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 4, 32, 128, 256, 8, 128, 4096, 32, 4096],[128, 16, 4096, 1, 2, 4, 128, 16, 4096, 1, 2, 4, 4096],5120⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 32, 128, 256, 8, 128, 4096, 32, 4096],[128, 16, 4096, 1, 16, 4, 128, 16, 4096, 1, 16, 4, 4096],5120⟩,
.last 32 (2,true),
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.last 22 (2,true),
.last 22 (2,true),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 23 (2,true),
.cycle 29 1 true (9)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 0 21 true (0),
.cycle 18 1 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 9, 32, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 18 1 true (6),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 1 21 true (1),
.cycle 9 9 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 0 21 true (0),
.cycle 18 1 true (6)
]),
.cycle 8 3 true (3),
.cycle 11 1 true (5),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.cycle 13 1 true (5)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 14 3 false (0),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 19 7 false (1),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 31 (2,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 14 1 true (6),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 20 5 false (1),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 14 1 true (6)
]),
.cycle 11 1 true (5)
])
theorem kid10_part918_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part918) = true := by rfl

def kid10_part919 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.last 19 (2,true),
.cycle 15 7 false (1),
.cycle 17 10 false (2),
.cycle 1 15 true (1),
.cycle 11 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 19 8 false (2),
.cycle 7 11 true (2),
.cycle 21 5 false (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 22 1 false (0),
.cycle 15 7 false (1),
.cycle 17 6 false (2),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 16 9 false (2),
.cycle 6 11 true (2)
]),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 18 true (2),
.cycle 3 20 true (1),
.cycle 8 15 true (2),
.cycle 7 18 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 14 9 true (2),
.cycle 11 15 true (2),
.cycle 7 18 true (2),
.cycle 7 17 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 16, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 25 true (0),
.cycle 10 16 true (2),
.cycle 19 6 true (3),
.cycle 11 14 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.last 24 (5,true),
.cycle 6 18 true (2)
]),
.cycle 10 7 true (2),
.cycle 11 5 true (3),
.cycle 7 8 true (2),
.cycle 7 7 true (2),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 25 3 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 10 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.cycle 7 10 true (2),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 25 3 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 6 10 true (2)
]),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 25 1 false (1),
.last 19 (2,true),
.cycle 15 7 false (1),
.cycle 17 10 false (2),
.cycle 6 9 true (2),
.cycle 29 9 false (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 19 8 false (2),
.cycle 7 12 true (2),
.cycle 21 5 false (2),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 22 1 false (0),
.cycle 15 7 false (1),
.cycle 17 6 false (2),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 16 9 false (2),
.cycle 6 12 true (2)
]),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 10 9 true (2),
.last 19 (2,true),
.cycle 15 9 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 7 11 true (2),
.cycle 11 5 true (3),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 10 7 true (2),
.cycle 27 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 6 11 true (2)
]),
.cycle 6 8 true (2)
])
theorem kid10_part919_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part919) = true := by rfl

def kid10_part921 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 23 true (0),
.cycle 3 12 true (1),
.cycle 8 7 true (2),
.cycle 13 3 true (3),
.cycle 6 9 true (2),
.cycle 0 17 true (0),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 13 4 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.cycle 0 18 true (0)
])
theorem kid10_part921_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part921) = true := by rfl

def kid10_part922 : Audit := .cycle 0 15 true (0)
theorem kid10_part922_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part922) = true := by rfl

def kid10_part923 : Audit := .cycle 38 1 false (4)
theorem kid10_part923_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part923) = true := by rfl

def kid10_part924 : Audit := .cycle 21 1 false (1)
theorem kid10_part924_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part924) = true := by rfl

def kid10_part925 : Audit := .split 19 (2,true) (byMove [
.cycle 0 44 true (-2),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.cycle 12 11 false (2),
.cycle 15 5 false (1),
.last 20 (5,true),
.last 34 (5,true),
.last 32 (5,true),
.cycle 0 36 true (-2),
.last 36 (5,true),
.last 22 (5,true),
.last 20 (5,true),
.last 24 (5,true),
.cycle 14 6 false (1),
.cycle 12 13 false (2),
.cycle 12 11 false (2),
.cycle 15 5 false (1),
.last 20 (5,true),
.last 30 (5,true),
.last 26 (5,true),
.cycle 0 36 true (-2),
.last 32 (5,true),
.cycle 15 7 false (1),
.last 20 (5,true)
])
theorem kid10_part925_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part925) = true := by rfl

def kid10_part926 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 7 9 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 3 24 true (1),
.cycle 19 7 false (1),
.last 18 (5,true),
.cycle 21 9 false (1),
.cycle 18 5 false (1),
.cycle 1 50 true (-1),
.cycle 1 20 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 75 39 false (5),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 18 9 false (2)
])
theorem kid10_part926_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part926) = true := by rfl

def kid10_part927 : Audit := .cycle 1 12 true (1)
theorem kid10_part927_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part927) = true := by rfl

def kid10_part928 : Audit := .split 16 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 47 5 false (10),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 18, 411, 411, 128, 256, 8, 128, 4096, 2, 4096],[128, 16, 18, 1, 2, 4096, 128, 16, 411, 1, 2, 4096, 4096],5120⟩,
.cycle 7 12 true (2),
.cycle 1 20 true (1),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 10 15 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 17 (5,true),
.cycle 1 19 true (1),
.cycle 10 7 true (2),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.cycle 1 19 true (1),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 17 (5,true)
])
theorem kid10_part928_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part928) = true := by rfl

def kid10_part929 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 13 18 true (0),
.cycle 40 1 false (4),
.cycle 0 20 true (0),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 24 true (0),
.cycle 10 15 true (2),
.cycle 12 3 true (4),
.cycle 7 7 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 15 true (0),
.cycle 13 16 true (0),
.last 20 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.last 29 (5,true)
])
theorem kid10_part929_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part929) = true := by rfl

def kid10_part930 : Audit := .cycle 0 13 true (0)
theorem kid10_part930_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part930) = true := by rfl

def kid10_part931 : Audit := .split 16 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 36 5 false (6),
.cycle 33 1 false (1),
.cycle 7 12 true (2),
.cycle 35 5 false (6),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 13 5 true (3),
.cycle 10 15 true (2),
.cycle 0 18 true (0),
.cycle 12 5 true (3),
.last 17 (5,true),
.cycle 12 7 true (3),
.cycle 10 7 true (2),
.cycle 5 14 true (1),
.cycle 5 12 true (1),
.cycle 11 7 true (3),
.last 17 (5,true),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 8 10 true (2),
.last 17 (5,true)
])
theorem kid10_part931_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part931) = true := by rfl

def kid10_part932 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 33 (2,true),
.last 22 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (2,true),
.cycle 0 24 true (0),
.last 16 (2,true),
.last 15 (2,true),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 29 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 18 (2,true),
.last 18 (2,true)
])
theorem kid10_part932_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part932) = true := by rfl

def kid10_part933 : Audit := .cycle 7 9 true (2)
theorem kid10_part933_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part933) = true := by rfl

def kid10_part934 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 24 5 false (1),
.cycle 29 1 false (1),
.cycle 7 9 true (2),
.cycle 19 3 false (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 10 12 true (2),
.cycle 0 15 true (0),
.cycle 8 9 true (2),
.last 14 (5,true),
.cycle 6 13 true (2),
.cycle 10 4 true (2),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 19 3 false (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 20 (5,true),
.last 14 (5,true)
])
theorem kid10_part934_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part934) = true := by rfl

def kid10_part935 : Audit := .cycle 1 14 true (1)
theorem kid10_part935_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part935) = true := by rfl

def kid10_part936 : Audit := .cycle 31 1 false (3)
theorem kid10_part936_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part936) = true := by rfl

def kid10_part937 : Audit := .split 19 (2,true) (byMove [
.last 52 (5,true),
.cycle 16 5 false (0),
.cycle 22 1 false (-2),
.last 25 (5,true),
.cycle 15 5 false (1),
.last 20 (5,true),
.last 24 (5,true),
.cycle 10 10 false (3),
.last 39 (5,true),
.last 25 (5,true),
.last 22 (5,true),
.last 20 (5,true),
.last 24 (5,true),
.cycle 14 6 false (1),
.last 27 (5,true),
.last 25 (5,true),
.cycle 15 5 false (1),
.last 20 (5,true),
.last 24 (5,true),
.last 23 (5,true),
.last 40 (5,true),
.last 25 (5,true),
.cycle 15 7 false (1),
.last 20 (5,true)
])
theorem kid10_part937_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part937) = true := by rfl

def kid10_part938 : Audit := .split 14 (2,true) (byMove [
.cycle 1 21 true (1),
.cycle 20 5 false (0),
.cycle 18 1 false (0),
.cycle 9 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 6 9 true (1),
.cycle 17 5 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],5120⟩,
.cycle 1 16 true (1),
.cycle 18 7 false (2),
.last 15 (5,true),
.cycle 19 9 false (2),
.cycle 18 5 false (1),
.cycle 15 12 true (-1),
.cycle 9 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 19 15 false (4),
.cycle 18 11 false (3),
.cycle 2 15 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid10_part938_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part938) = true := by rfl

def kid10_part939 : Audit := .cycle 1 12 true (1)
theorem kid10_part939_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part939) = true := by rfl

def kid10_part940 : Audit := .cycle 7 5 true (2)
theorem kid10_part940_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part940) = true := by rfl

def kid10_part941 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 28 5 false (2),
.cycle 58 1 false (4),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 19 true (1),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.cycle 12 3 true (4),
.cycle 6 7 true (2),
.cycle 2 13 true (1),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 2 14 true (1)
])
theorem kid10_part941_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part941) = true := by rfl

def kid10_part942 : Audit := .cycle 0 13 true (0)
theorem kid10_part942_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part942) = true := by rfl

def kid10_part943 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.last 19 (2,true),
.last 15 (2,true),
.cycle 7 10 true (2),
.last 31 (2,true),
.last 18 (2,true),
.cycle 1 15 true (1),
.last 19 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.last 18 (2,true),
.cycle 16 5 true (4),
.cycle 10 5 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 11 5 true (3),
.last 18 (2,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 12 6 true (4)
])
theorem kid10_part943_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part943) = true := by rfl

def kid10_part944 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.last 17 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 3 true (3),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 3 true (5),
.cycle 3 10 true (1),
.cycle 8 5 true (2),
.last 15 (2,true),
.cycle 6 7 true (2),
.cycle 13 3 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 15 3 true (5),
.cycle 13 3 true (4)
])
theorem kid10_part944_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part944) = true := by rfl

def kid10_part920 : Audit := .split 11 (4,true) (byMove [(kid10_part921),(kid10_part922),(kid10_part923),(kid10_part924),(kid10_part925),(kid10_part926),(kid10_part927),(kid10_part928),(kid10_part929),(kid10_part930),(kid10_part931),(kid10_part932),(kid10_part933),(kid10_part934),(kid10_part935),(kid10_part936),(kid10_part937),(kid10_part938),(kid10_part939),(kid10_part940),(kid10_part941),(kid10_part942),(kid10_part943),(kid10_part944)])

theorem kid10_part920_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part920) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (4,true) (some mv)) (byMove [(kid10_part921),(kid10_part922),(kid10_part923),(kid10_part924),(kid10_part925),(kid10_part926),(kid10_part927),(kid10_part928),(kid10_part929),(kid10_part930),(kid10_part931),(kid10_part932),(kid10_part933),(kid10_part934),(kid10_part935),(kid10_part936),(kid10_part937),(kid10_part938),(kid10_part939),(kid10_part940),(kid10_part941),(kid10_part942),(kid10_part943),(kid10_part944)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part921_checked

  · exact kid10_part927_checked

  · exact kid10_part933_checked

  · exact kid10_part939_checked

  · exact kid10_part922_checked

  · exact kid10_part928_checked

  · exact kid10_part934_checked

  · exact kid10_part940_checked

  · exact kid10_part923_checked

  · exact kid10_part929_checked

  · exact kid10_part935_checked

  · exact kid10_part941_checked

  · exact kid10_part924_checked

  · exact kid10_part930_checked

  · exact kid10_part936_checked

  · exact kid10_part942_checked

  · exact kid10_part925_checked

  · exact kid10_part931_checked

  · exact kid10_part937_checked

  · exact kid10_part943_checked

  · exact kid10_part926_checked

  · exact kid10_part932_checked

  · exact kid10_part938_checked

  · exact kid10_part944_checked

def kid10_part946 : Audit := .cycle 1 17 true (1)
theorem kid10_part946_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part946) = true := by rfl

def kid10_part947 : Audit := .cycle 1 14 true (1)
theorem kid10_part947_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part947) = true := by rfl

def kid10_part948 : Audit := .split 17 (4,true) (byMove [
.cycle 25 1 false (1),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.cycle 26 1 false (2),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 1 23 true (0),
.cycle 12 18 true (0),
.cycle 0 19 true (0),
.cycle 1 23 true (0),
.last 18 (5,true),
.cycle 29 1 false (1),
.cycle 23 1 false (1),
.cycle 1 20 true (0),
.cycle 31 1 false (3),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.cycle 30 1 false (2),
.cycle 0 19 true (0),
.last 20 (5,true),
.last 18 (5,true)
])
theorem kid10_part948_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part948) = true := by rfl

def kid10_part949 : Audit := .cycle 7 11 true (0)
theorem kid10_part949_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part949) = true := by rfl

def kid10_part950 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 28 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 1 22 true (-2),
.last 16 (4,true),
.last 13 (4,true),
.last 29 (4,true),
.last 15 (4,true),
.last 15 (4,true),
.last 18 (4,true),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 28 (4,true),
.last 16 (4,true),
.last 24 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part950_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part950) = true := by rfl

def kid10_part951 : Audit := .split 26 (4,true) (byMove [
.last 30 (5,true),
.cycle 1 30 true (-2),
.cycle 39 15 true (1),
.last 32 (5,true),
.last 28 (5,true),
.cycle 11 16 true (-2),
.cycle 0 38 true (-2),
.cycle 27 16 true (3),
.cycle 0 55 true (-2),
.cycle 1 28 true (-2),
.cycle 1 33 true (-2),
.last 27 (5,true),
.last 38 (5,true),
.last 29 (5,true),
.cycle 0 42 true (-2),
.cycle 35 13 true (1),
.last 28 (5,true),
.cycle 19 8 true (-2),
.last 32 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 144, 128, 1, 8192, 16384, 8, 144, 16777216, 17, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 4727808, 17301504, 21233664, 16777216],[128, 16, 128, 1, 128, 16777216, 8192, 16, 16777216, 1, 8192, 16777216, 524288, 1024, 16777216, 64, 524288, 16777216, 524288, 4194304, 17301504, 262144, 524288, 16777216, 16777216],33502272⟩,
.last 28 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 657, 640, 1, 8192, 16384, 8, 144, 16777216, 17, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 7119936, 19398656, 21233664, 16777216],[128, 16, 640, 1, 512, 16777216, 8192, 16, 16777216, 1, 32768, 16777216, 524288, 1024, 16777216, 64, 2097152, 16777216, 524288, 4194304, 19398656, 262144, 2097152, 16777216, 16777216],33502272⟩,
.last 30 (5,true),
.last 27 (5,true)
])
theorem kid10_part951_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part951) = true := by rfl

def kid10_part952 : Audit := .cycle 6 5 true (2)
theorem kid10_part952_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part952) = true := by rfl

def kid10_part953 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 1 22 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 22, 132, 1, 128, 256, 8, 128, 4096, 16, 4096],[128, 16, 2, 1, 4, 4096, 128, 16, 2, 1, 4, 4096, 4096],5120⟩,
.cycle 1 23 true (0),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 5 11 true (1),
.cycle 1 16 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 1 20 true (1)
])
theorem kid10_part953_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part953) = true := by rfl

def kid10_part954 : Audit := .split 23 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 1 51 true (0),
.cycle 57 1 false (9),
.cycle 1 71 true (0),
.last 25 (5,true),
.cycle 37 1 false (9),
.cycle 0 27 true (0),
.cycle 1 31 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 132, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 0 50 true (0),
.cycle 1 31 true (0),
.last 24 (5,true),
.cycle 25 23 true (3),
.cycle 10 16 true (0),
.cycle 0 31 true (0),
.cycle 49 1 false (9),
.last 25 (5,true),
.cycle 32 1 false (8),
.cycle 0 27 true (0),
.cycle 7 19 true (0),
.cycle 10 71 true (0),
.cycle 5 19 true (0),
.last 28 (5,true),
.last 24 (5,true)
])
theorem kid10_part954_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part954) = true := by rfl

def kid10_part955 : Audit := .cycle 1 12 true (1)
theorem kid10_part955_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part955) = true := by rfl

def kid10_part956 : Audit := .split 11 (4,true) (byMove [
.cycle 8 7 true (2),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.last 28 (5,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 0 13 true (0),
.cycle 1 17 true (1),
.last 12 (5,true),
.cycle 7 9 true (2),
.cycle 8 9 true (2),
.cycle 1 14 true (1),
.cycle 31 1 false (3),
.last 24 (5,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part956_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part956) = true := by rfl

def kid10_part957 : Audit := .split 11 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 1 26 true (-2),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 16 true (0),
.last 14 (4,true),
.cycle 0 20 true (0),
.cycle 1 14 true (1),
.last 17 (4,true),
.last 22 (4,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (4)
])
theorem kid10_part957_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part957) = true := by rfl

def kid10_part958 : Audit := .split 13 (4,true) (byMove [
.cycle 12 11 true (2),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.cycle 12 13 true (1),
.last 15 (5,true),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 1 19 true (1),
.cycle 7 9 true (1),
.cycle 0 15 true (0),
.cycle 1 19 true (1),
.last 14 (5,true),
.cycle 12 11 true (2),
.cycle 12 15 true (2),
.cycle 1 16 true (1),
.cycle 4 15 true (1),
.last 15 (5,true),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.cycle 6 9 true (1),
.cycle 0 15 true (0),
.last 16 (5,true),
.last 14 (5,true)
])
theorem kid10_part958_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part958) = true := by rfl

def kid10_part959 : Audit := .split 14 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 1 18 true (1),
.cycle 43 1 false (3),
.cycle 1 31 true (0),
.last 16 (5,true),
.cycle 13 24 true (-2),
.cycle 6 9 true (1),
.cycle 1 16 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 132, 1, 128, 256, 8, 128, 4096, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 1 16 true (1),
.cycle 1 21 true (1),
.last 15 (5,true),
.cycle 12 13 true (1),
.cycle 11 4 true (1),
.cycle 5 11 true (1),
.cycle 36 1 false (2),
.last 16 (5,true),
.cycle 13 12 true (-2),
.cycle 12 7 true (1),
.cycle 1 16 true (1),
.cycle 2 19 true (1),
.cycle 1 16 true (1),
.last 18 (5,true),
.last 15 (5,true)
])
theorem kid10_part959_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part959) = true := by rfl

def kid10_part960 : Audit := .cycle 5 7 true (1)
theorem kid10_part960_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part960) = true := by rfl

def kid10_part961 : Audit := .split 15 (4,true) (byMove [
.cycle 1 20 true (0),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.cycle 1 22 true (0),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 1 21 true (0),
.cycle 11 16 true (0),
.cycle 0 17 true (0),
.cycle 1 21 true (0),
.last 16 (5,true),
.cycle 17 9 true (2),
.cycle 5 13 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (2),
.last 17 (5,true),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 7 9 true (0),
.cycle 1 18 true (0),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 16 (5,true)
])
theorem kid10_part961_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part961) = true := by rfl

def kid10_part962 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.last 18 (4,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 20 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 20 true (0),
.last 15 (4,true),
.last 15 (4,true),
.last 17 (4,true),
.cycle 13 1 false (-1),
.last 19 (4,true),
.last 18 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 19 (4,true)
])
theorem kid10_part962_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part962) = true := by rfl

def kid10_part963 : Audit := .split 18 (4,true) (byMove [
.last 22 (5,true),
.cycle 1 22 true (-2),
.cycle 29 15 true (1),
.last 24 (5,true),
.last 20 (5,true),
.cycle 11 16 true (-2),
.cycle 0 30 true (-2),
.cycle 19 16 true (3),
.cycle 1 47 true (-2),
.cycle 1 20 true (-2),
.cycle 1 25 true (-2),
.last 19 (5,true),
.last 30 (5,true),
.last 21 (5,true),
.cycle 0 34 true (-2),
.cycle 25 13 true (1),
.last 20 (5,true),
.cycle 11 8 true (-2),
.last 24 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 144, 128, 1, 8192, 16384, 8, 144, 16777216, 17, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 4727808, 17301504, 21233664, 16777216],[128, 16, 128, 1, 128, 16777216, 8192, 16, 16777216, 1, 8192, 16777216, 524288, 1024, 16777216, 64, 524288, 16777216, 524288, 4194304, 17301504, 262144, 524288, 16777216, 16777216],33502272⟩,
.last 20 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 657, 640, 1, 8192, 16384, 8, 144, 16777216, 17, 524288, 1048576, 512, 128, 16777216, 16777216, 524288, 1048576, 2097152, 7119936, 19398656, 21233664, 16777216],[128, 16, 640, 1, 512, 16777216, 8192, 16, 16777216, 1, 32768, 16777216, 524288, 1024, 16777216, 64, 2097152, 16777216, 524288, 4194304, 19398656, 262144, 2097152, 16777216, 16777216],33502272⟩,
.last 22 (5,true),
.last 19 (5,true)
])
theorem kid10_part963_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part963) = true := by rfl

def kid10_part964 : Audit := .cycle 6 5 true (2)
theorem kid10_part964_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part964) = true := by rfl

def kid10_part965 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 22 true (1),
.cycle 11 7 true (2),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 7 7 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 7 8 true (2)
])
theorem kid10_part965_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part965) = true := by rfl

def kid10_part966 : Audit := .cycle 2 11 true (1)
theorem kid10_part966_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part966) = true := by rfl

def kid10_part967 : Audit := .cycle 1 12 true (1)
theorem kid10_part967_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part967) = true := by rfl

def kid10_part968 : Audit := .split 11 (4,true) (byMove [
.last 16 (5,true),
.cycle 5 11 true (1),
.last 14 (5,true),
.cycle 7 7 true (2),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 17 true (1),
.last 12 (5,true),
.cycle 7 9 true (2),
.last 22 (5,true),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part968_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part968) = true := by rfl

def kid10_part969 : Audit := .split 11 (5,true) (byMove [
.cycle 1 18 true (1),
.cycle 5 11 true (1),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 28 (4,true),
.cycle 1 12 true (1),
.cycle 1 17 true (1),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 16 true (0),
.last 14 (4,true),
.last 13 (4,true),
.cycle 10 2 true (2),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 22 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 14 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 12 3 true (4)
])
theorem kid10_part969_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part969) = true := by rfl

def kid10_part945 : Audit := .split 10 (2,true) (byMove [(kid10_part946),(kid10_part947),(kid10_part948),(kid10_part949),(kid10_part950),(kid10_part951),(kid10_part952),(kid10_part953),(kid10_part954),(kid10_part955),(kid10_part956),(kid10_part957),(kid10_part958),(kid10_part959),(kid10_part960),(kid10_part961),(kid10_part962),(kid10_part963),(kid10_part964),(kid10_part965),(kid10_part966),(kid10_part967),(kid10_part968),(kid10_part969)])

theorem kid10_part945_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part945) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part946),(kid10_part947),(kid10_part948),(kid10_part949),(kid10_part950),(kid10_part951),(kid10_part952),(kid10_part953),(kid10_part954),(kid10_part955),(kid10_part956),(kid10_part957),(kid10_part958),(kid10_part959),(kid10_part960),(kid10_part961),(kid10_part962),(kid10_part963),(kid10_part964),(kid10_part965),(kid10_part966),(kid10_part967),(kid10_part968),(kid10_part969)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part946_checked

  · exact kid10_part952_checked

  · exact kid10_part958_checked

  · exact kid10_part964_checked

  · exact kid10_part947_checked

  · exact kid10_part953_checked

  · exact kid10_part959_checked

  · exact kid10_part965_checked

  · exact kid10_part948_checked

  · exact kid10_part954_checked

  · exact kid10_part960_checked

  · exact kid10_part966_checked

  · exact kid10_part949_checked

  · exact kid10_part955_checked

  · exact kid10_part961_checked

  · exact kid10_part967_checked

  · exact kid10_part950_checked

  · exact kid10_part956_checked

  · exact kid10_part962_checked

  · exact kid10_part968_checked

  · exact kid10_part951_checked

  · exact kid10_part957_checked

  · exact kid10_part963_checked

  · exact kid10_part969_checked

def kid10_part970 : Audit := .cycle 5 5 true (1)
theorem kid10_part970_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part970) = true := by rfl

def kid10_part972 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.cycle 0 19 true (0),
.last 14 (5,true),
.cycle 1 14 true (1),
.last 18 (5,true),
.cycle 0 35 true (0),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 10 45 true (-1),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true)
])
theorem kid10_part972_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part972) = true := by rfl

def kid10_part973 : Audit := .cycle 1 14 true (1)
theorem kid10_part973_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part973) = true := by rfl

def kid10_part974 : Audit := .cycle 35 1 false (3)
theorem kid10_part974_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part974) = true := by rfl

def kid10_part975 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.cycle 0 23 true (0),
.last 16 (5,true),
.cycle 1 16 true (0),
.last 20 (5,true),
.cycle 1 41 true (0),
.cycle 0 17 true (0),
.cycle 1 19 true (0),
.last 16 (5,true),
.cycle 1 21 true (0),
.cycle 1 27 true (0),
.cycle 1 25 true (0),
.cycle 5 11 true (0),
.cycle 1 23 true (0),
.last 16 (5,true),
.cycle 1 16 true (0),
.cycle 1 26 true (0),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true)
])
theorem kid10_part975_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part975) = true := by rfl

def kid10_part976 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 14 2 false (2),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 14 2 false (0),
.cycle 14 2 false (2),
.cycle 10 5 false (2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 17 2 false (-1),
.last 13 (2,true),
.cycle 0 20 true (0),
.cycle 15 2 false (-1),
.cycle 17 2 false (-1)
])
theorem kid10_part976_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part976) = true := by rfl

def kid10_part977 : Audit := .cycle 13 2 false (-1)
theorem kid10_part977_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part977) = true := by rfl

def kid10_part978 : Audit := .cycle 6 5 true (2)
theorem kid10_part978_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part978) = true := by rfl

def kid10_part979 : Audit := .cycle 1 12 true (1)
theorem kid10_part979_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part979) = true := by rfl

def kid10_part980 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 13 18 true (0),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.last 18 (5,true),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668544, 1074790400, 1074790400, 2, 4, 32768, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 65536, 1048580, 1073741824, 128, 256, 2097152, 1048576, 1074790404, 1074790404, 2, 4, 32768, 128, 1073741824, 1048576, 1073741824],[128, 16, 4, 1, 4, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 33554432, 4194304, 1048576, 262144, 1048576, 1073741824, 128, 4194304, 1048576, 262144, 1048576, 1073741824, 2, 65536, 16384, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 0 13 true (0),
.cycle 41 1 false (9),
.last 12 (5,true),
.cycle 7 19 true (2),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 4, 3, 1, 2, 0],[128, 256, 8, 34668548, 1074790404, 1074790404, 2, 4, 32768, 128, 1073741824, 1048580, 33554432, 67108864, 2097152, 65536, 1048580, 1073741824, 128, 256, 2097152, 1048580, 1074790404, 1074790404, 2, 4, 32768, 128, 1073741824, 1048580, 1073741824],[128, 16, 1048580, 1, 4, 1073741824, 2, 65536, 1048580, 4096, 16384, 1073741824, 33554432, 4194304, 1048580, 262144, 1048576, 1073741824, 128, 4194304, 1048580, 262144, 1048576, 1073741824, 2, 65536, 1048576, 4096, 16384, 1073741824, 1073741824],1354892336⟩,
.cycle 1 14 true (1),
.cycle 12 16 true (0),
.cycle 16 2 false (0),
.last 14 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 32 (5,true),
.last 12 (5,true)
])
theorem kid10_part980_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part980) = true := by rfl

def kid10_part981 : Audit := .cycle 1 12 true (1)
theorem kid10_part981_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part981) = true := by rfl

def kid10_part982 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 52 2 false (8),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.cycle 24 2 false (6),
.last 19 (2,true),
.cycle 33 2 false (7),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.last 20 (2,true),
.cycle 10 13 true (-1),
.cycle 19 1 false (-1),
.cycle 19 2 false (-1),
.cycle 19 2 false (-1),
.cycle 10 11 true (0),
.cycle 37 2 false (7),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 17, 18, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 37 2 false (7),
.cycle 20 10 true (2)
])
theorem kid10_part982_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part982) = true := by rfl

def kid10_part983 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 35 1 false (3),
.cycle 21 1 false (1),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 1 12 true (1),
.cycle 24 2 false (6),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 24 2 false (6),
.cycle 24 2 false (6),
.cycle 7 18 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 30 1 false (2),
.cycle 16 2 false (0),
.cycle 15 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 8 true (3),
.cycle 12 3 true (4)
])
theorem kid10_part983_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part983) = true := by rfl

def kid10_part984 : Audit := .cycle 12 11 true (2)
theorem kid10_part984_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part984) = true := by rfl

def kid10_part985 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 20 2 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 6 7 true (1),
.cycle 1 16 true (1),
.cycle 10 14 true (1),
.cycle 1 14 true (1),
.cycle 10 13 true (1),
.last 13 (5,true),
.cycle 10 19 true (1),
.cycle 10 4 true (1),
.cycle 22 19 true (0),
.cycle 1 20 true (1),
.cycle 15 3 false (1),
.last 13 (5,true),
.cycle 10 9 true (1),
.cycle 1 16 true (1),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 24 (5,true),
.last 13 (5,true)
])
theorem kid10_part985_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part985) = true := by rfl

def kid10_part986 : Audit := .cycle 5 7 true (1)
theorem kid10_part986_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part986) = true := by rfl

def kid10_part987 : Audit := .cycle 28 1 false (2)
theorem kid10_part987_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part987) = true := by rfl

def kid10_part988 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 1 24 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 28 2 false (2),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 14 2 false (0),
.cycle 17 2 false (5),
.cycle 10 5 false (2),
.last 14 (2,true),
.cycle 34 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 31 2 false (-1),
.cycle 10 4 true (0),
.last 13 (2,true),
.cycle 1 20 true (0),
.cycle 15 2 false (-1),
.cycle 23 2 false (-1)
])
theorem kid10_part988_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part988) = true := by rfl

def kid10_part989 : Audit := .cycle 13 2 false (-1)
theorem kid10_part989_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part989) = true := by rfl

def kid10_part990 : Audit := .cycle 6 5 true (2)
theorem kid10_part990_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part990) = true := by rfl

def kid10_part991 : Audit := .cycle 1 12 true (1)
theorem kid10_part991_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part991) = true := by rfl

def kid10_part992 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 16 (5,true),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 1 12 true (1),
.last 16 (5,true),
.cycle 2 29 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 2 13 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true)
])
theorem kid10_part992_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part992) = true := by rfl

def kid10_part993 : Audit := .cycle 1 12 true (1)
theorem kid10_part993_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part993) = true := by rfl

def kid10_part994 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 10 9 true (2),
.last 15 (2,true),
.cycle 7 10 true (2),
.cycle 23 2 false (-1),
.cycle 23 2 false (-1),
.cycle 1 15 true (1),
.cycle 11 10 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 10 10 true (2),
.cycle 16 5 true (4),
.cycle 11 5 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 10 5 true (2),
.cycle 31 2 false (-1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 12 3 true (4),
.cycle 11 6 true (3)
])
theorem kid10_part994_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part994) = true := by rfl

def kid10_part995 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 24 45 true (-2),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 9 4 true (2),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 8 true (2),
.cycle 61 2 false (9),
.cycle 6 12 true (2),
.cycle 13 5 true (3),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 10 2 true (2),
.cycle 17 2 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 6 true (3),
.cycle 12 3 true (4)
])
theorem kid10_part995_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part995) = true := by rfl

def kid10_part971 : Audit := .split 10 (4,true) (byMove [(kid10_part972),(kid10_part973),(kid10_part974),(kid10_part975),(kid10_part976),(kid10_part977),(kid10_part978),(kid10_part979),(kid10_part980),(kid10_part981),(kid10_part982),(kid10_part983),(kid10_part984),(kid10_part985),(kid10_part986),(kid10_part987),(kid10_part988),(kid10_part989),(kid10_part990),(kid10_part991),(kid10_part992),(kid10_part993),(kid10_part994),(kid10_part995)])

theorem kid10_part971_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part971) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part972),(kid10_part973),(kid10_part974),(kid10_part975),(kid10_part976),(kid10_part977),(kid10_part978),(kid10_part979),(kid10_part980),(kid10_part981),(kid10_part982),(kid10_part983),(kid10_part984),(kid10_part985),(kid10_part986),(kid10_part987),(kid10_part988),(kid10_part989),(kid10_part990),(kid10_part991),(kid10_part992),(kid10_part993),(kid10_part994),(kid10_part995)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part972_checked

  · exact kid10_part978_checked

  · exact kid10_part984_checked

  · exact kid10_part990_checked

  · exact kid10_part973_checked

  · exact kid10_part979_checked

  · exact kid10_part985_checked

  · exact kid10_part991_checked

  · exact kid10_part974_checked

  · exact kid10_part980_checked

  · exact kid10_part986_checked

  · exact kid10_part992_checked

  · exact kid10_part975_checked

  · exact kid10_part981_checked

  · exact kid10_part987_checked

  · exact kid10_part993_checked

  · exact kid10_part976_checked

  · exact kid10_part982_checked

  · exact kid10_part988_checked

  · exact kid10_part994_checked

  · exact kid10_part977_checked

  · exact kid10_part983_checked

  · exact kid10_part989_checked

  · exact kid10_part995_checked

def kid10_part997 : Audit := .split 13 (2,true) (byMove [
.cycle 1 17 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 7 9 true (1),
.last 14 (4,true),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.last 23 (4,true),
.last 23 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 0 15 true (0),
.last 16 (4,true),
.last 15 (4,true),
.last 21 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.cycle 12 4 true (1),
.cycle 1 14 true (1),
.cycle 12 7 true (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1)
])
theorem kid10_part997_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part997) = true := by rfl

def kid10_part998 : Audit := .cycle 1 14 true (1)
theorem kid10_part998_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part998) = true := by rfl

def kid10_part999 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 35 1 false (3),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 25 1 false (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 25 1 false (1),
.cycle 32 1 false (2),
.last 26 (2,true),
.last 19 (2,true),
.cycle 1 20 true (0),
.cycle 31 1 false (3),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 1 18 true (0),
.cycle 7 11 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.last 21 (2,true),
.last 19 (2,true)
])
theorem kid10_part999_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part999) = true := by rfl

def kid10_part1000 : Audit := .split 15 (2,true) (byMove [
.cycle 1 19 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 7 11 true (0),
.last 16 (4,true),
.cycle 0 23 true (0),
.cycle 1 16 true (0),
.last 24 (4,true),
.last 25 (4,true),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 1 19 true (0),
.last 18 (4,true),
.last 17 (4,true),
.last 22 (4,true),
.cycle 5 11 true (0),
.last 16 (4,true),
.last 20 (4,true),
.cycle 1 16 true (0),
.last 23 (4,true),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0)
])
theorem kid10_part1000_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part1000) = true := by rfl

def kid10_part1001 : Audit := .cycle 14 1 false (-2)
theorem kid10_part1001_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part1001) = true := by rfl

def kid10_part1002 : Audit := .cycle 13 1 false (-1)
theorem kid10_part1002_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part1002) = true := by rfl

def kid10_part1003 : Audit := .cycle 6 5 true (2)
theorem kid10_part1003_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part1003) = true := by rfl

def kid10_part1004 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 41 1 false (5),
.cycle 1 22 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 1 23 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 27 10 true (5),
.cycle 25 37 true (3)
])
theorem kid10_part1004_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part1004) = true := by rfl

def kid10_part1005 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (4,true),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.last 21 (4,true),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 23 (4,true),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (1),
.last 17 (4,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 20 (4,true)
])
theorem kid10_part1005_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part1005) = true := by rfl

def kid10_part1006 : Audit := .cycle 1 12 true (1)
theorem kid10_part1006_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part1006) = true := by rfl

def kid10_part1007 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 38 1 false (4),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 37 1 false (9),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (6),
.cycle 7 9 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 31 1 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 8 5 true (2)
])
theorem kid10_part1007_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part1007) = true := by rfl

def kid10_part1008 : Audit := .cycle 24 1 false (6)
theorem kid10_part1008_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part1008) = true := by rfl

def kid10_part1009 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 2 19 true (1),
.last 18 (2,true),
.cycle 17 5 false (2),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 18, 18, 64],[2, 16, 64, 1, 2, 16, 64],64⟩,
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 7 9 true (1),
.cycle 12 11 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 4 15 true (1),
.cycle 17 5 false (2),
.cycle 17 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 5 true (4),
.cycle 6 9 true (1)
])
theorem kid10_part1009_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part1009) = true := by rfl

def kid10_part1010 : Audit := .split 12 (2,true) (byMove [
.cycle 1 19 true (1),
.cycle 21 1 false (-1),
.cycle 16 1 false (0),
.last 16 (4,true),
.last 13 (4,true),
.last 15 (4,true),
.cycle 6 7 true (1),
.last 14 (4,true),
.last 24 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 23 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.last 15 (4,true),
.last 19 (4,true),
.last 14 (4,true),
.cycle 2 13 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid10_part1010_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part1010) = true := by rfl

def kid10_part1011 : Audit := .cycle 5 7 true (1)
theorem kid10_part1011_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part1011) = true := by rfl

def kid10_part1012 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 32 1 false (2),
.last 20 (2,true),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 22 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 1 false (1),
.cycle 17 9 true (2),
.last 17 (2,true),
.cycle 1 18 true (0),
.cycle 28 1 false (2),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 1 16 true (0),
.cycle 7 9 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 5 30 true (0),
.cycle 1 18 true (0)
])
theorem kid10_part1012_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part1012) = true := by rfl

def kid10_part1013 : Audit := .cycle 14 1 false (-2)
theorem kid10_part1013_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part1013) = true := by rfl

def kid10_part1014 : Audit := .cycle 13 1 false (-1)
theorem kid10_part1014_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part1014) = true := by rfl

def kid10_part1015 : Audit := .cycle 6 5 true (2)
theorem kid10_part1015_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part1015) = true := by rfl

def kid10_part1016 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 1 19 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 10 4 true (2),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 7 8 true (2)
])
theorem kid10_part1016_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part1016) = true := by rfl

def kid10_part1017 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 1 12 true (1),
.last 19 (4,true),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.last 14 (4,true),
.last 13 (4,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1)
])
theorem kid10_part1017_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part1017) = true := by rfl

def kid10_part1018 : Audit := .cycle 1 12 true (1)
theorem kid10_part1018_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part1018) = true := by rfl

def kid10_part1019 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 20 1 false (0),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 18 1 false (-2),
.cycle 10 4 true (2),
.cycle 1 12 true (1),
.cycle 1 19 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 8 true (2),
.cycle 7 9 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 18 1 false (-2),
.cycle 10 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (4),
.cycle 14 3 true (4)
])
theorem kid10_part1019_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part1019) = true := by rfl

def kid10_part1020 : Audit := .cycle 11 3 true (3)
theorem kid10_part1020_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part1020) = true := by rfl

def kid10_part996 : Audit := .split 10 (5,true) (byMove [(kid10_part997),(kid10_part998),(kid10_part999),(kid10_part1000),(kid10_part1001),(kid10_part1002),(kid10_part1003),(kid10_part1004),(kid10_part1005),(kid10_part1006),(kid10_part1007),(kid10_part1008),(kid10_part1009),(kid10_part1010),(kid10_part1011),(kid10_part1012),(kid10_part1013),(kid10_part1014),(kid10_part1015),(kid10_part1016),(kid10_part1017),(kid10_part1018),(kid10_part1019),(kid10_part1020)])

theorem kid10_part996_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part996) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part997),(kid10_part998),(kid10_part999),(kid10_part1000),(kid10_part1001),(kid10_part1002),(kid10_part1003),(kid10_part1004),(kid10_part1005),(kid10_part1006),(kid10_part1007),(kid10_part1008),(kid10_part1009),(kid10_part1010),(kid10_part1011),(kid10_part1012),(kid10_part1013),(kid10_part1014),(kid10_part1015),(kid10_part1016),(kid10_part1017),(kid10_part1018),(kid10_part1019),(kid10_part1020)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part997_checked

  · exact kid10_part1003_checked

  · exact kid10_part1009_checked

  · exact kid10_part1015_checked

  · exact kid10_part998_checked

  · exact kid10_part1004_checked

  · exact kid10_part1010_checked

  · exact kid10_part1016_checked

  · exact kid10_part999_checked

  · exact kid10_part1005_checked

  · exact kid10_part1011_checked

  · exact kid10_part1017_checked

  · exact kid10_part1000_checked

  · exact kid10_part1006_checked

  · exact kid10_part1012_checked

  · exact kid10_part1018_checked

  · exact kid10_part1001_checked

  · exact kid10_part1007_checked

  · exact kid10_part1013_checked

  · exact kid10_part1019_checked

  · exact kid10_part1002_checked

  · exact kid10_part1008_checked

  · exact kid10_part1014_checked

  · exact kid10_part1020_checked

def kid10_part1021 : Audit := .cycle 1 10 true (1)
theorem kid10_part1021_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part1021) = true := by rfl

def kid10_part1022 : Audit := .cycle 7 3 true (3)
theorem kid10_part1022_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part1022) = true := by rfl

def kid10_part1024 : Audit := .cycle 1 11 true (1)
theorem kid10_part1024_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part1024) = true := by rfl

def kid10_part1025 : Audit := .cycle 7 4 true (3)
theorem kid10_part1025_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part1025) = true := by rfl

def kid10_part1026 : Audit := .cycle 25 1 false (1)
theorem kid10_part1026_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part1026) = true := by rfl

def kid10_part1027 : Audit := .cycle 0 12 true (0)
theorem kid10_part1027_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part1027) = true := by rfl

def kid10_part1028 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 14 (5,true),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 21 3 false (1),
.last 14 (5,true),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.cycle 2 11 true (1)
])
theorem kid10_part1028_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part1028) = true := by rfl

def kid10_part1029 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 0 16 true (0),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 2 11 true (1)
])
theorem kid10_part1029_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part1029) = true := by rfl

def kid10_part1030 : Audit := .cycle 0 11 true (0)
theorem kid10_part1030_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part1030) = true := by rfl

def kid10_part1031 : Audit := .cycle 1 10 true (1)
theorem kid10_part1031_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part1031) = true := by rfl

def kid10_part1032 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (5,true),
.cycle 2 18 true (1),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.cycle 2 18 true (1),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 20 (5,true),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 20 (5,true),
.cycle 2 18 true (1)
])
theorem kid10_part1032_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part1032) = true := by rfl

def kid10_part1033 : Audit := .cycle 3 8 true (1)
theorem kid10_part1033_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part1033) = true := by rfl

def kid10_part1034 : Audit := .cycle 8 3 true (3)
theorem kid10_part1034_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part1034) = true := by rfl

def kid10_part1035 : Audit := .cycle 2 10 true (1)
theorem kid10_part1035_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part1035) = true := by rfl

def kid10_part1036 : Audit := .cycle 6 5 true (2)
theorem kid10_part1036_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part1036) = true := by rfl

def kid10_part1037 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],5120⟩,
.cycle 11 7 true (2),
.cycle 8 5 true (3),
.cycle 2 12 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 2 12 true (1)
])
theorem kid10_part1037_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part1037) = true := by rfl

def kid10_part1038 : Audit := .cycle 5 9 true (1)
theorem kid10_part1038_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part1038) = true := by rfl

def kid10_part1039 : Audit := .cycle 1 12 true (1)
theorem kid10_part1039_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part1039) = true := by rfl

def kid10_part1040 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.last 14 (5,true),
.cycle 7 7 true (2),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.last 12 (5,true),
.cycle 7 9 true (2),
.cycle 21 3 false (1),
.last 14 (5,true),
.cycle 5 7 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 14 (5,true),
.last 12 (5,true)
])
theorem kid10_part1040_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part1040) = true := by rfl

def kid10_part1041 : Audit := .split 11 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 1 20 true (1),
.cycle 21 1 false (-1),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 20 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 12 true (1),
.last 14 (4,true),
.last 13 (4,true),
.last 24 (4,true),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 12 true (1)
])
theorem kid10_part1041_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part1041) = true := by rfl

def kid10_part1042 : Audit := .cycle 0 11 true (0)
theorem kid10_part1042_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part1042) = true := by rfl

def kid10_part1043 : Audit := .cycle 1 10 true (1)
theorem kid10_part1043_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part1043) = true := by rfl

def kid10_part1044 : Audit := .cycle 2 9 true (1)
theorem kid10_part1044_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part1044) = true := by rfl

def kid10_part1045 : Audit := .cycle 1 13 true (1)
theorem kid10_part1045_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part1045) = true := by rfl

def kid10_part1046 : Audit := .split 12 (5,true) (byMove [
.cycle 10 5 true (3),
.last 17 (4,true),
.last 25 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.last 25 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 2 13 true (1)
])
theorem kid10_part1046_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part1046) = true := by rfl

def kid10_part1047 : Audit := .cycle 2 10 true (1)
theorem kid10_part1047_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part1047) = true := by rfl

def kid10_part1023 : Audit := .split 10 (2,true) (byMove [(kid10_part1024),(kid10_part1025),(kid10_part1026),(kid10_part1027),(kid10_part1028),(kid10_part1029),(kid10_part1030),(kid10_part1031),(kid10_part1032),(kid10_part1033),(kid10_part1034),(kid10_part1035),(kid10_part1036),(kid10_part1037),(kid10_part1038),(kid10_part1039),(kid10_part1040),(kid10_part1041),(kid10_part1042),(kid10_part1043),(kid10_part1044),(kid10_part1045),(kid10_part1046),(kid10_part1047)])

theorem kid10_part1023_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part1023) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid10_part1024),(kid10_part1025),(kid10_part1026),(kid10_part1027),(kid10_part1028),(kid10_part1029),(kid10_part1030),(kid10_part1031),(kid10_part1032),(kid10_part1033),(kid10_part1034),(kid10_part1035),(kid10_part1036),(kid10_part1037),(kid10_part1038),(kid10_part1039),(kid10_part1040),(kid10_part1041),(kid10_part1042),(kid10_part1043),(kid10_part1044),(kid10_part1045),(kid10_part1046),(kid10_part1047)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1024_checked

  · exact kid10_part1030_checked

  · exact kid10_part1036_checked

  · exact kid10_part1042_checked

  · exact kid10_part1025_checked

  · exact kid10_part1031_checked

  · exact kid10_part1037_checked

  · exact kid10_part1043_checked

  · exact kid10_part1026_checked

  · exact kid10_part1032_checked

  · exact kid10_part1038_checked

  · exact kid10_part1044_checked

  · exact kid10_part1027_checked

  · exact kid10_part1033_checked

  · exact kid10_part1039_checked

  · exact kid10_part1045_checked

  · exact kid10_part1028_checked

  · exact kid10_part1034_checked

  · exact kid10_part1040_checked

  · exact kid10_part1046_checked

  · exact kid10_part1029_checked

  · exact kid10_part1035_checked

  · exact kid10_part1041_checked

  · exact kid10_part1047_checked

def kid10_part1048 : Audit := .cycle 0 11 true (0)
theorem kid10_part1048_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part1048) = true := by rfl

def kid10_part1050 : Audit := .cycle 1 11 true (1)
theorem kid10_part1050_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part1050) = true := by rfl

def kid10_part1051 : Audit := .cycle 7 4 true (3)
theorem kid10_part1051_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part1051) = true := by rfl

def kid10_part1052 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 35 1 false (3),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 32 1 false (2),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 13 (5,true),
.last 14 (5,true)
])
theorem kid10_part1052_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part1052) = true := by rfl

def kid10_part1053 : Audit := .cycle 0 12 true (0)
theorem kid10_part1053_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part1053) = true := by rfl

def kid10_part1054 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 13 3 false (1),
.cycle 1 15 true (0),
.cycle 16 4 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 13 4 true (0),
.cycle 12 5 false (2),
.last 16 (2,true),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.cycle 1 15 true (0),
.cycle 19 4 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 13 4 true (0)
])
theorem kid10_part1054_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part1054) = true := by rfl

def kid10_part1055 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 19 4 false (-1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 11 4 true (3),
.cycle 6 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 19 4 false (-1),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.cycle 11 4 true (3)
])
theorem kid10_part1055_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part1055) = true := by rfl

def kid10_part1056 : Audit := .cycle 0 11 true (0)
theorem kid10_part1056_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part1056) = true := by rfl

def kid10_part1057 : Audit := .cycle 1 10 true (1)
theorem kid10_part1057_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part1057) = true := by rfl

def kid10_part1058 : Audit := .split 28 (2,true) (byMove [
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 11 18 true (3),
.cycle 3 26 true (1),
.cycle 8 21 true (3),
.last 31 (5,true),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 1024, 128, 256, 8, 128, 4096, 1024, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],7200⟩,
.cycle 20 9 true (4),
.cycle 8 21 true (3),
.last 31 (5,true),
.cycle 7 23 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 1024, 128, 256, 8, 128, 4096, 1024, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],7200⟩,
.cycle 0 31 true (0),
.cycle 13 16 true (3),
.last 34 (5,true),
.cycle 9 20 true (3),
.cycle 0 29 true (0),
.cycle 1 28 true (1),
.cycle 2 27 true (1),
.cycle 1 31 true (1),
.last 30 (5,true),
.last 31 (5,true)
])
theorem kid10_part1058_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part1058) = true := by rfl

def kid10_part1059 : Audit := .cycle 3 8 true (1)
theorem kid10_part1059_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part1059) = true := by rfl

def kid10_part1060 : Audit := .cycle 8 3 true (3)
theorem kid10_part1060_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part1060) = true := by rfl

def kid10_part1061 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 20 true (3),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 22 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5),
.cycle 10 6 true (4),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 14 16 true (3),
.cycle 25 6 false (1),
.cycle 9 8 true (3),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5)
])
theorem kid10_part1061_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part1061) = true := by rfl

def kid10_part1062 : Audit := .cycle 6 5 true (2)
theorem kid10_part1062_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part1062) = true := by rfl

def kid10_part1063 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 25 3 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (3),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.last 17 (5,true),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.cycle 25 3 false (1),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 16 (5,true),
.last 17 (5,true)
])
theorem kid10_part1063_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part1063) = true := by rfl

def kid10_part1064 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.cycle 7 9 true (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 1 24 true (1),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 12 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.cycle 5 9 true (1),
.last 12 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true)
])
theorem kid10_part1064_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part1064) = true := by rfl

def kid10_part1065 : Audit := .cycle 1 12 true (1)
theorem kid10_part1065_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part1065) = true := by rfl

def kid10_part1066 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 1 26 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 13 3 false (1),
.cycle 30 4 false (4),
.cycle 16 4 false (2),
.last 15 (2,true),
.cycle 1 22 true (0),
.cycle 15 4 false (1),
.cycle 17 4 true (3),
.cycle 12 5 false (2),
.last 16 (2,true),
.cycle 36 4 false (4),
.cycle 15 1 false (-1),
.cycle 15 4 false (-1),
.cycle 15 4 false (0),
.cycle 33 4 false (1),
.cycle 12 4 true (0),
.last 15 (2,true),
.cycle 1 22 true (0),
.cycle 15 4 false (1),
.cycle 17 4 true (3)
])
theorem kid10_part1066_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part1066) = true := by rfl

def kid10_part1067 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 17 4 false (0),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 11 4 true (3),
.cycle 9 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 17 4 false (0),
.cycle 16 3 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 11 4 true (3)
])
theorem kid10_part1067_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part1067) = true := by rfl

def kid10_part1068 : Audit := .cycle 0 11 true (0)
theorem kid10_part1068_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part1068) = true := by rfl

def kid10_part1069 : Audit := .cycle 1 10 true (1)
theorem kid10_part1069_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part1069) = true := by rfl

def kid10_part1070 : Audit := .cycle 2 9 true (1)
theorem kid10_part1070_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part1070) = true := by rfl

def kid10_part1071 : Audit := .cycle 1 13 true (1)
theorem kid10_part1071_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part1071) = true := by rfl

def kid10_part1072 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 10 7 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 19 8 false (1),
.cycle 18 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 4 true (4),
.cycle 14 5 true (4),
.cycle 10 5 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 10 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 3 true (4),
.cycle 11 4 true (4)
])
theorem kid10_part1072_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part1072) = true := by rfl

def kid10_part1073 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 7 12 true (3),
.last 14 (2,true),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 20 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5),
.cycle 10 6 true (4),
.cycle 10 8 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 13 2 true (4),
.cycle 20 5 false (2),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 11 4 true (5)
])
theorem kid10_part1073_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part1073) = true := by rfl

def kid10_part1049 : Audit := .split 10 (4,true) (byMove [(kid10_part1050),(kid10_part1051),(kid10_part1052),(kid10_part1053),(kid10_part1054),(kid10_part1055),(kid10_part1056),(kid10_part1057),(kid10_part1058),(kid10_part1059),(kid10_part1060),(kid10_part1061),(kid10_part1062),(kid10_part1063),(kid10_part1064),(kid10_part1065),(kid10_part1066),(kid10_part1067),(kid10_part1068),(kid10_part1069),(kid10_part1070),(kid10_part1071),(kid10_part1072),(kid10_part1073)])

theorem kid10_part1049_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part1049) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid10_part1050),(kid10_part1051),(kid10_part1052),(kid10_part1053),(kid10_part1054),(kid10_part1055),(kid10_part1056),(kid10_part1057),(kid10_part1058),(kid10_part1059),(kid10_part1060),(kid10_part1061),(kid10_part1062),(kid10_part1063),(kid10_part1064),(kid10_part1065),(kid10_part1066),(kid10_part1067),(kid10_part1068),(kid10_part1069),(kid10_part1070),(kid10_part1071),(kid10_part1072),(kid10_part1073)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part1053_checked

  · exact kid10_part1059_checked

  · exact kid10_part1065_checked

  · exact kid10_part1071_checked

  · exact kid10_part1054_checked

  · exact kid10_part1060_checked

  · exact kid10_part1066_checked

  · exact kid10_part1072_checked

  · exact kid10_part1055_checked

  · exact kid10_part1061_checked

  · exact kid10_part1067_checked

  · exact kid10_part1073_checked

def kid10_part1075 : Audit := .cycle 1 11 true (1)
theorem kid10_part1075_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part1075) = true := by rfl

def kid10_part1076 : Audit := .cycle 7 4 true (3)
theorem kid10_part1076_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part1076) = true := by rfl

def kid10_part1077 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 19 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 23 (4,true),
.cycle 12 1 true (4)
])
theorem kid10_part1077_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part1077) = true := by rfl

def kid10_part1078 : Audit := .cycle 0 12 true (0)
theorem kid10_part1078_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part1078) = true := by rfl

def kid10_part1079 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 4 false (-1),
.cycle 32 1 true (-6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 4 false (-1),
.cycle 16 3 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 17 6 false (1),
.cycle 12 1 true (4)
])
theorem kid10_part1079_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part1079) = true := by rfl

def kid10_part1080 : Audit := .cycle 13 1 true (1)
theorem kid10_part1080_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part1080) = true := by rfl

def kid10_part1081 : Audit := .cycle 0 11 true (0)
theorem kid10_part1081_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part1081) = true := by rfl

def kid10_part1082 : Audit := .cycle 1 10 true (1)
theorem kid10_part1082_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part1082) = true := by rfl

def kid10_part1083 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 21 (2,true),
.cycle 19 1 true (5),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 28 (2,true),
.cycle 12 7 true (3),
.cycle 8 11 true (3),
.cycle 19 1 true (7),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 4 15 true (1),
.last 21 (2,true),
.cycle 9 10 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.last 21 (2,true),
.cycle 19 1 true (7)
])
theorem kid10_part1083_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part1083) = true := by rfl

def kid10_part1084 : Audit := .cycle 3 8 true (1)
theorem kid10_part1084_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part1084) = true := by rfl

def kid10_part1085 : Audit := .cycle 8 3 true (3)
theorem kid10_part1085_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part1085) = true := by rfl

def kid10_part1086 : Audit := .cycle 11 1 true (5)
theorem kid10_part1086_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part1086) = true := by rfl

def kid10_part1087 : Audit := .cycle 6 5 true (2)
theorem kid10_part1087_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part1087) = true := by rfl

def kid10_part1088 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (2,true),
.cycle 13 1 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (2,true),
.cycle 11 7 true (2),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (2,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (2,true),
.cycle 13 1 true (5)
])
theorem kid10_part1088_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part1088) = true := by rfl

def kid10_part1089 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 13 (4,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3)
])
theorem kid10_part1089_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part1089) = true := by rfl

def kid10_part1090 : Audit := .cycle 1 12 true (1)
theorem kid10_part1090_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part1090) = true := by rfl

def kid10_part1091 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 1 20 true (1),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 15 4 false (-1),
.cycle 14 9 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (3),
.cycle 16 5 false (0),
.cycle 7 9 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 15 4 false (-1),
.cycle 16 3 false (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 5 true (3),
.cycle 10 2 true (3)
])
theorem kid10_part1091_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part1091) = true := by rfl

def kid10_part1092 : Audit := .cycle 15 3 false (1)
theorem kid10_part1092_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part1092) = true := by rfl

def kid10_part1093 : Audit := .cycle 0 11 true (0)
theorem kid10_part1093_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part1093) = true := by rfl

def kid10_part1094 : Audit := .cycle 1 10 true (1)
theorem kid10_part1094_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part1094) = true := by rfl

def kid10_part1095 : Audit := .cycle 2 9 true (1)
theorem kid10_part1095_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part1095) = true := by rfl

def kid10_part1096 : Audit := .cycle 1 13 true (1)
theorem kid10_part1096_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part1096) = true := by rfl

def kid10_part1097 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 19 8 false (1),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 31 (2,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 14 1 true (6),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 19 6 false (1),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 14 1 true (6)
])
theorem kid10_part1097_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part1097) = true := by rfl

def kid10_part1098 : Audit := .cycle 11 1 true (5)
theorem kid10_part1098_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part1098) = true := by rfl

def kid10_part1074 : Audit := .split 10 (5,true) (byMove [(kid10_part1075),(kid10_part1076),(kid10_part1077),(kid10_part1078),(kid10_part1079),(kid10_part1080),(kid10_part1081),(kid10_part1082),(kid10_part1083),(kid10_part1084),(kid10_part1085),(kid10_part1086),(kid10_part1087),(kid10_part1088),(kid10_part1089),(kid10_part1090),(kid10_part1091),(kid10_part1092),(kid10_part1093),(kid10_part1094),(kid10_part1095),(kid10_part1096),(kid10_part1097),(kid10_part1098)])

theorem kid10_part1074_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part1074) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid10_part1075),(kid10_part1076),(kid10_part1077),(kid10_part1078),(kid10_part1079),(kid10_part1080),(kid10_part1081),(kid10_part1082),(kid10_part1083),(kid10_part1084),(kid10_part1085),(kid10_part1086),(kid10_part1087),(kid10_part1088),(kid10_part1089),(kid10_part1090),(kid10_part1091),(kid10_part1092),(kid10_part1093),(kid10_part1094),(kid10_part1095),(kid10_part1096),(kid10_part1097),(kid10_part1098)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part1080_checked

  · exact kid10_part1086_checked

  · exact kid10_part1092_checked

  · exact kid10_part1098_checked

def kid10_part810 : Audit := .split 9 (5,false) (byMove [(kid10_part811),(kid10_part836),(kid10_part837),(kid10_part862),(kid10_part863),(kid10_part888),(kid10_part889),(kid10_part890),(kid10_part891),(kid10_part916),(kid10_part917),(kid10_part918),(kid10_part919),(kid10_part920),(kid10_part945),(kid10_part970),(kid10_part971),(kid10_part996),(kid10_part1021),(kid10_part1022),(kid10_part1023),(kid10_part1048),(kid10_part1049),(kid10_part1074)])

theorem kid10_part810_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid10_part810) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part811),(kid10_part836),(kid10_part837),(kid10_part862),(kid10_part863),(kid10_part888),(kid10_part889),(kid10_part890),(kid10_part891),(kid10_part916),(kid10_part917),(kid10_part918),(kid10_part919),(kid10_part920),(kid10_part945),(kid10_part970),(kid10_part971),(kid10_part996),(kid10_part1021),(kid10_part1022),(kid10_part1023),(kid10_part1048),(kid10_part1049),(kid10_part1074)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part811_checked

  · exact kid10_part889_checked

  · exact kid10_part919_checked

  · exact kid10_part1021_checked

  · exact kid10_part836_checked

  · exact kid10_part890_checked

  · exact kid10_part920_checked

  · exact kid10_part1022_checked

  · exact kid10_part837_checked

  · exact kid10_part891_checked

  · exact kid10_part945_checked

  · exact kid10_part1023_checked

  · exact kid10_part862_checked

  · exact kid10_part916_checked

  · exact kid10_part970_checked

  · exact kid10_part1048_checked

  · exact kid10_part863_checked

  · exact kid10_part917_checked

  · exact kid10_part971_checked

  · exact kid10_part1049_checked

  · exact kid10_part888_checked

  · exact kid10_part918_checked

  · exact kid10_part996_checked

  · exact kid10_part1074_checked

def kid10_part1099 : Audit := .cycle 0 9 true (0)
theorem kid10_part1099_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid10_part1099) = true := by rfl

def kid10_part1100 : Audit := .cycle 1 8 true (1)
theorem kid10_part1100_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid10_part1100) = true := by rfl

def kid10_part1101 : Audit := .cycle 2 7 true (1)
theorem kid10_part1101_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid10_part1101) = true := by rfl

def kid10_part1102 : Audit := .cycle 1 11 true (1)
theorem kid10_part1102_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid10_part1102) = true := by rfl

def kid10_part1103 : Audit := .cycle 8 1 true (4)
theorem kid10_part1103_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid10_part1103) = true := by rfl

def kid10_part1105 : Audit := .cycle 1 10 true (1)
theorem kid10_part1105_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part1105) = true := by rfl

def kid10_part1106 : Audit := .cycle 7 3 true (3)
theorem kid10_part1106_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part1106) = true := by rfl

def kid10_part1107 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 33 1 false (3),
.cycle 14 7 true (0),
.cycle 25 3 false (2),
.cycle 14 9 true (0),
.cycle 25 9 false (3),
.cycle 19 3 false (1),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.last 16 (5,true),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (2),
.cycle 21 3 false (1)
]),
.cycle 17 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.cycle 0 31 true (0),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.cycle 1 35 true (1),
.cycle 0 25 true (0),
.cycle 35 1 false (3),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 26, 64],[2, 16, 4, 1, 2, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 30, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 26, 64],[2, 16, 4, 1, 16, 64, 64],64⟩,
.last 20 (5,true),
.cycle 7 17 true (2),
.cycle 10 12 true (2),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.last 21 (5,true),
.cycle 1 24 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.cycle 2 27 true (1),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.last 20 (5,true)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 18 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 19 9 true (3),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 8, 1, 16, 64, 64],64⟩,
.cycle 11 9 true (2),
.cycle 7 12 true (2),
.cycle 3 17 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 18 true (1),
.cycle 9 9 true (2)
]),
.cycle 8 3 true (4),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 22 true (1),
.cycle 36 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 20 11 true (3),
.cycle 13 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 18, 64],[2, 16, 32, 1, 16, 64, 64],64⟩,
.cycle 11 9 true (2),
.cycle 7 14 true (2),
.cycle 2 21 true (1),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 36 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 2 22 true (1),
.cycle 9 11 true (2)
]),
.cycle 7 5 true (3),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 29 7 false (1),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 30, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 13 7 true (2),
.cycle 8 7 true (3),
.cycle 13 9 true (2),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 9 6 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.last 15 (4,true)
]),
.cycle 17 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1107_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part1107) = true := by rfl

def kid10_part1108 : Audit := .cycle 0 11 true (0)
theorem kid10_part1108_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part1108) = true := by rfl

def kid10_part1109 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 18 3 false (0),
.cycle 13 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 18 true (2),
.cycle 3 18 true (1),
.cycle 8 13 true (2),
.cycle 10 22 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 12 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.last 36 (5,true),
.cycle 7 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 8, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 23 true (0),
.cycle 10 16 true (2),
.last 22 (5,true),
.cycle 0 27 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 21 true (2),
.last 34 (5,true)
]),
.cycle 10 7 true (2),
.cycle 8 3 true (4),
.cycle 8 4 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 10 8 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 7 true (3),
.cycle 10 6 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 0, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 22 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 0, 64],[2, 16, 64, 1, 32, 32, 64],64⟩
]),
.cycle 13 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1109_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part1109) = true := by rfl

def kid10_part1110 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 14 (4,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 29 1 false (1),
.cycle 1 17 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 24 (2,true),
.cycle 14 7 true (0),
.cycle 25 3 false (2),
.cycle 17 3 false (1),
.cycle 25 9 false (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 26 1 false (0),
.cycle 18 3 false (0),
.cycle 15 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (2),
.cycle 21 3 false (1)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 2 25 true (1),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 35 1 false (3),
.cycle 1 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 62, 64],[2, 16, 64, 1, 2, 4, 64],64⟩,
.last 20 (2,true),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 62, 64],[2, 16, 64, 1, 16, 4, 64],64⟩,
.last 32 (2,true),
.cycle 7 17 true (2),
.last 21 (2,true),
.cycle 1 22 true (1),
.cycle 4 21 true (1),
.last 22 (2,true),
.cycle 1 24 true (1),
.cycle 1 20 true (1),
.cycle 7 13 true (2),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 20 11 true (6),
.cycle 9 20 true (2)
]),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 18 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 62, 64],[2, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 21 9 true (0),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.cycle 3 17 true (1),
.cycle 30 1 false (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 3 18 true (1),
.cycle 9 9 true (2)
]),
.cycle 8 3 true (4),
.cycle 19 1 false (1),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (4,true),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 17 (4,true),
.cycle 6 7 true (2),
.last 14 (4,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.last 16 (4,true)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 21 true (0),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 17 6 false (1),
.cycle 22 1 false (-2),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 10 4 true (3),
.cycle 7 11 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 18 3 false (0),
.cycle 22 1 false (-2),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 5 true (3),
.cycle 12 2 true (3)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part1110_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part1110) = true := by rfl

def kid10_part1111 : Audit := .cycle 0 10 true (0)
theorem kid10_part1111_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part1111) = true := by rfl

def kid10_part1112 : Audit := .cycle 1 9 true (1)
theorem kid10_part1112_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part1112) = true := by rfl

def kid10_part1113 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (4),
.cycle 9 9 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 27 (2,true) (byMove [
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 10 18 true (4),
.cycle 3 25 true (1),
.cycle 8 20 true (4),
.cycle 18 11 true (5),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 19 9 true (5),
.cycle 8 20 true (4),
.last 41 (5,true),
.cycle 7 22 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 30 true (0),
.cycle 12 16 true (4),
.last 29 (5,true),
.cycle 27 2 true (8),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.cycle 8 20 true (4),
.cycle 9 19 true (4)
]),
.cycle 11 7 true (4),
.cycle 8 10 true (4),
.split 29 (5,true) (byMove [
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 10 29 true (4),
.cycle 0 38 true (0),
.last 32 (2,true),
.cycle 0 33 true (0),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 16 15 true (5),
.last 31 (2,true),
.cycle 1 32 true (1),
.cycle 12 25 true (4),
.cycle 28 4 true (8),
.last 31 (2,true),
.cycle 1 30 true (1),
.cycle 7 23 true (3),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 8 34 true (4),
.cycle 9 22 true (4)
]),
.cycle 7 12 true (3),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 47 1 false (1),
.cycle 0 21 true (0),
.cycle 41 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.cycle 8 12 true (4),
.last 32 (5,true),
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.cycle 5 18 true (1),
.cycle 1 21 true (1),
.cycle 41 3 false (1),
.last 20 (5,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4)
]),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.split 19 (5,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 32 3 false (0),
.cycle 52 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.cycle 8 12 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 16, 64, 1, 32, 32, 64],64⟩,
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.cycle 32 3 false (0),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4)
]),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2048, 4, 128, 256, 8, 128, 2048, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 11 9 true (4),
.cycle 8 12 true (4),
.last 33 (5,true),
.cycle 7 14 true (3),
.cycle 16 6 true (6),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.last 21 (5,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 8 12 true (4),
.cycle 9 11 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 8 10 true (4),
.cycle 9 9 true (4)
])
theorem kid10_part1113_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part1113) = true := by rfl

def kid10_part1114 : Audit := .cycle 3 7 true (1)
theorem kid10_part1114_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part1114) = true := by rfl

def kid10_part1115 : Audit := .cycle 8 2 true (4)
theorem kid10_part1115_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part1115) = true := by rfl

def kid10_part1116 : Audit := .cycle 9 1 true (5)
theorem kid10_part1116_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part1116) = true := by rfl

def kid10_part1117 : Audit := .cycle 6 4 true (2)
theorem kid10_part1117_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part1117) = true := by rfl

def kid10_part1118 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 9 14 true (3),
.cycle 3 12 true (1),
.cycle 8 7 true (3),
.cycle 12 3 true (3),
.cycle 6 9 true (2),
.cycle 26 5 false (1),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 35 13 false (3),
.cycle 30 9 false (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 22 (2,true) (byMove [
.cycle 1 26 true (1),
.cycle 0 26 true (0),
.cycle 24 18 true (3),
.last 29 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 31, 32, 12, 64],[2, 16, 12, 1, 4, 64, 64],64⟩,
.last 26 (5,true),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 6, 64],[2, 16, 2, 1, 4, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 20, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.last 23 (5,true),
.cycle 7 30 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 4, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 1 25 true (1),
.cycle 23 16 true (3),
.last 24 (5,true),
.last 26 (5,true),
.cycle 1 23 true (1),
.cycle 7 16 true (2),
.cycle 2 22 true (1),
.cycle 0 24 true (0),
.cycle 30 14 true (7),
.last 23 (5,true)
]),
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 26 true (1),
.cycle 0 16 true (0),
.cycle 11 4 true (5),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (4),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 12 3 true (5),
.cycle 6 9 true (2),
.cycle 10 5 true (4),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4)
]),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 27 3 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 12 3 true (4),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.cycle 27 3 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4)
]),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 3 false (0),
.last 29 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.last 16 (2,true),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 22 3 false (0),
.last 29 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4)
]),
.split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 17 (5,true),
.cycle 33 1 false (1),
.cycle 7 10 true (3),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2048, 4, 128, 256, 8, 128, 2048, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 16 true (0),
.cycle 28 7 false (2),
.last 15 (5,true),
.cycle 31 9 false (2),
.cycle 26 5 false (1),
.cycle 15 12 true (1),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1118_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part1118) = true := by rfl

def kid10_part1120 : Audit := .cycle 1 14 true (1)
theorem kid10_part1120_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part1120) = true := by rfl

def kid10_part1121 : Audit := .cycle 0 14 true (0)
theorem kid10_part1121_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part1121) = true := by rfl

def kid10_part1122 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 35 1 false (1),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 12 18 true (2),
.cycle 12 7 true (2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 16, 2048, 1, 8192, 16384, 8, 128, 131072, 16, 128, 256, 8, 128, 2048, 262144, 262144],[128, 16, 16, 1, 16, 262144, 8192, 16, 2048, 1, 16, 262144, 128, 16, 16, 1, 16, 262144, 262144],394240⟩,
.cycle 0 21 true (0),
.cycle 7 12 true (2),
.cycle 35 1 false (1),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 19 (5,true),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 29 (5,true),
.cycle 9 9 true (2)
])
theorem kid10_part1122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part1122) = true := by rfl

def kid10_part1123 : Audit := .cycle 0 17 true (0)
theorem kid10_part1123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part1123) = true := by rfl

def kid10_part1124 : Audit := .split 14 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 0 26 true (0),
.last 22 (5,true),
.cycle 1 21 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 18 true (0),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 1 23 true (0),
.last 16 (5,true),
.cycle 5 12 true (1),
.last 18 (5,true),
.cycle 19 3 false (1),
.cycle 0 22 true (0),
.last 20 (5,true),
.last 16 (5,true),
.cycle 15 3 false (1),
.cycle 0 18 true (0),
.cycle 1 20 true (1),
.cycle 1 17 true (1),
.cycle 1 22 true (1),
.last 16 (5,true),
.cycle 21 3 false (1)
])
theorem kid10_part1124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part1124) = true := by rfl

def kid10_part1125 : Audit := .split 21 (5,true) (byMove [
.cycle 0 26 true (-2),
.last 31 (4,true),
.cycle 11 20 true (-2),
.cycle 0 28 true (-2),
.last 22 (4,true),
.cycle 11 20 true (-2),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262160, 2048, 1, 8192, 16384, 8, 1168, 131072, 17, 8192, 16384, 512, 8320, 131072, 1105, 262144],[128, 16, 2176, 1, 262144, 1, 8192, 16, 141440, 1, 262144, 1, 8192, 1024, 8320, 64, 262144, 64, 262144],262414⟩,
.cycle 24 19 true (4),
.cycle 0 24 true (-2),
.last 27 (4,true),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262160, 2048, 1, 8192, 16384, 8, 1168, 131072, 17, 8192, 16384, 512, 8320, 131072, 1040, 262144],[128, 16, 2176, 1, 262144, 16, 8192, 16, 133120, 1, 262144, 16, 8192, 1024, 133120, 64, 262144, 1024, 262144],262414⟩,
.cycle 1 25 true (-2),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 262160, 2048, 1, 8192, 16384, 8, 1168, 131072, 1041, 8192, 16384, 512, 8320, 131072, 1040, 262144],[128, 16, 133248, 1, 262144, 1040, 8192, 16, 133120, 1, 262144, 1040, 8192, 1024, 133120, 64, 262144, 1024, 262144],262414⟩,
.last 23 (4,true),
.cycle 12 10 true (-2),
.cycle 1 28 true (-2),
.last 22 (4,true),
.last 30 (4,true),
.cycle 18 32 true (0),
.cycle 24 35 true (3),
.cycle 0 24 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 16777232, 2048, 1, 8192, 16384, 8, 144, 131072, 32785, 524288, 1048576, 512, 128, 8388608, 16810000, 524288, 1048576, 2097152, 21505024, 8388608, 23364624, 16777216],[128, 16, 2176, 1, 16777216, 512, 8192, 16, 16779408, 1, 16777216, 32768, 524288, 1024, 128, 64, 16777216, 2097152, 524288, 4194304, 30026880, 262144, 16777216, 2097152, 16777216],33502542⟩,
.cycle 21 6 true (3),
.proven (BB6.Agent11Raw39Pumps.M828.table) (fun m hm => BB6.Agent11Raw39Pumps.M828.never m hm)
])
theorem kid10_part1125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part1125) = true := by rfl

def kid10_part1126 : Audit := .cycle 1 11 true (1)
theorem kid10_part1126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part1126) = true := by rfl

def kid10_part1127 : Audit := .cycle 7 4 true (3)
theorem kid10_part1127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part1127) = true := by rfl

def kid10_part1128 : Audit := .split 21 (4,true) (byMove [
.cycle 0 46 true (0),
.cycle 1 25 true (1),
.cycle 2 34 true (1),
.cycle 1 52 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2048, 1, 128, 256, 8, 128, 2048, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 2076, 4096, 4096],4096⟩,
.cycle 1 27 true (1),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 5, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 1 23 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 5, 64],[2, 16, 4, 1, 16, 64, 64],64⟩,
.last 22 (5,true),
.cycle 7 22 true (2),
.cycle 10 14 true (2),
.cycle 5 18 true (1),
.cycle 4 28 true (1),
.last 23 (5,true),
.cycle 53 1 false (11),
.cycle 6 16 true (2),
.cycle 1 23 true (1),
.cycle 2 40 true (1),
.cycle 1 23 true (1),
.cycle 22 14 true (6),
.last 22 (5,true)
])
theorem kid10_part1128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part1128) = true := by rfl

def kid10_part1129 : Audit := .cycle 0 12 true (0)
theorem kid10_part1129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part1129) = true := by rfl

def kid10_part1130 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 5, 64],[2, 16, 16, 1, 4, 64, 64],64⟩,
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part1130) = true := by rfl

def kid10_part1131 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.last 19 (4,true),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part1131) = true := by rfl

def kid10_part1132 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (3),
.cycle 27 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (3),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 7 8 true (3),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 27 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (4),
.cycle 9 5 true (3)
])
theorem kid10_part1132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part1132) = true := by rfl

def kid10_part1133 : Audit := .split 14 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 2 20 true (1),
.cycle 1 24 true (1),
.cycle 29 7 false (1),
.last 33 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 22, 32, 5, 64],[2, 16, 4, 1, 4, 64, 64],64⟩,
.cycle 0 16 true (0),
.cycle 8 8 true (3),
.last 15 (5,true),
.cycle 7 12 true (3),
.cycle 11 4 true (3),
.cycle 1 17 true (1),
.cycle 4 16 true (1),
.last 16 (5,true),
.cycle 19 12 true (-2),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.cycle 12 6 true (3),
.last 15 (5,true)
])
theorem kid10_part1133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part1133) = true := by rfl

def kid10_part1134 : Audit := .cycle 1 13 true (1)
theorem kid10_part1134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part1134) = true := by rfl

def kid10_part1135 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 11 16 true (2),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 17, 64],[2, 16, 18, 1, 16, 64, 64],64⟩,
.cycle 0 19 true (0),
.cycle 7 10 true (2),
.cycle 1 19 true (1),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.last 17 (5,true),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 5 14 true (1),
.cycle 9 7 true (2)
])
theorem kid10_part1135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part1135) = true := by rfl

def kid10_part1136 : Audit := .split 12 (5,true) (byMove [
.last 16 (4,true),
.cycle 7 9 true (3),
.last 14 (4,true),
.cycle 7 8 true (3),
.last 13 (4,true),
.last 26 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 17 true (0),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 25 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid10_part1136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part1136) = true := by rfl

def kid10_part1137 : Audit := .split 20 (4,true) (byMove [
.last 24 (5,true),
.cycle 0 40 true (-2),
.cycle 31 24 true (1),
.last 26 (5,true),
.last 24 (5,true),
.last 29 (5,true),
.cycle 0 24 true (-2),
.cycle 21 20 true (3),
.cycle 1 41 true (-2),
.cycle 0 36 true (-2),
.cycle 22 20 true (4),
.last 21 (5,true),
.last 37 (5,true),
.last 23 (5,true),
.cycle 0 28 true (-2),
.cycle 27 20 true (1),
.last 22 (5,true),
.cycle 13 8 true (-2),
.last 39 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 144, 2048, 1, 8192, 16384, 8, 144, 131072, 17, 524288, 1048576, 512, 128, 8388608, 16777216, 524288, 1048576, 2097152, 4727808, 8388608, 21233664, 16777216],[128, 16, 128, 1, 128, 16777216, 8192, 16, 16777216, 1, 8192, 16777216, 524288, 1024, 16777216, 64, 524288, 16777216, 524288, 4194304, 17301504, 262144, 524288, 16777216, 16777216],33502272⟩,
.last 22 (5,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 657, 2048, 1, 8192, 16384, 8, 144, 131072, 17, 524288, 1048576, 512, 128, 8388608, 16777216, 524288, 1048576, 2097152, 7119936, 8388608, 21233664, 16777216],[128, 16, 640, 1, 512, 16777216, 8192, 16, 16777216, 1, 32768, 16777216, 524288, 1024, 16777216, 64, 2097152, 16777216, 524288, 4194304, 19398656, 262144, 2097152, 16777216, 16777216],33502272⟩,
.last 27 (5,true),
.last 21 (5,true)
])
theorem kid10_part1137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part1137) = true := by rfl

def kid10_part1138 : Audit := .cycle 1 11 true (1)
theorem kid10_part1138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part1138) = true := by rfl

def kid10_part1139 : Audit := .cycle 7 4 true (3)
theorem kid10_part1139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part1139) = true := by rfl

def kid10_part1140 : Audit := .cycle 2 10 true (1)
theorem kid10_part1140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part1140) = true := by rfl

def kid10_part1141 : Audit := .cycle 0 12 true (0)
theorem kid10_part1141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part1141) = true := by rfl

def kid10_part1142 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (4),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 22 true (4),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 8 8 true (4),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 14 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part1142) = true := by rfl

def kid10_part1143 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 24 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 26 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part1143) = true := by rfl

def kid10_part1119 : Audit := .split 10 (2,true) (byMove [(kid10_part1120),(kid10_part1121),(kid10_part1122),(kid10_part1123),(kid10_part1124),(kid10_part1125),(kid10_part1126),(kid10_part1127),(kid10_part1128),(kid10_part1129),(kid10_part1130),(kid10_part1131),(kid10_part1132),(kid10_part1133),(kid10_part1134),(kid10_part1135),(kid10_part1136),(kid10_part1137),(kid10_part1138),(kid10_part1139),(kid10_part1140),(kid10_part1141),(kid10_part1142),(kid10_part1143)])

theorem kid10_part1119_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part1119) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part1120),(kid10_part1121),(kid10_part1122),(kid10_part1123),(kid10_part1124),(kid10_part1125),(kid10_part1126),(kid10_part1127),(kid10_part1128),(kid10_part1129),(kid10_part1130),(kid10_part1131),(kid10_part1132),(kid10_part1133),(kid10_part1134),(kid10_part1135),(kid10_part1136),(kid10_part1137),(kid10_part1138),(kid10_part1139),(kid10_part1140),(kid10_part1141),(kid10_part1142),(kid10_part1143)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1120_checked

  · exact kid10_part1126_checked

  · exact kid10_part1132_checked

  · exact kid10_part1138_checked

  · exact kid10_part1121_checked

  · exact kid10_part1127_checked

  · exact kid10_part1133_checked

  · exact kid10_part1139_checked

  · exact kid10_part1122_checked

  · exact kid10_part1128_checked

  · exact kid10_part1134_checked

  · exact kid10_part1140_checked

  · exact kid10_part1123_checked

  · exact kid10_part1129_checked

  · exact kid10_part1135_checked

  · exact kid10_part1141_checked

  · exact kid10_part1124_checked

  · exact kid10_part1130_checked

  · exact kid10_part1136_checked

  · exact kid10_part1142_checked

  · exact kid10_part1125_checked

  · exact kid10_part1131_checked

  · exact kid10_part1137_checked

  · exact kid10_part1143_checked

def kid10_part1144 : Audit := .cycle 1 11 true (1)
theorem kid10_part1144_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part1144) = true := by rfl

def kid10_part1146 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.last 16 (5,true),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 22 true (0),
.cycle 1 15 true (1),
.cycle 12 4 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (4),
.cycle 12 5 true (4)
])
theorem kid10_part1146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid10_part1146) = true := by rfl

def kid10_part1147 : Audit := .cycle 0 14 true (0)
theorem kid10_part1147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid10_part1147) = true := by rfl

def kid10_part1148 : Audit := .cycle 2 16 true (1)
theorem kid10_part1148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid10_part1148) = true := by rfl

def kid10_part1149 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.cycle 1 28 true (0),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 1 26 true (1),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.last 18 (5,true),
.cycle 6 10 true (2),
.cycle 1 20 true (1),
.cycle 5 14 true (1),
.cycle 1 17 true (1),
.cycle 7 12 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 14 true (2),
.cycle 7 13 true (2)
])
theorem kid10_part1149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid10_part1149) = true := by rfl

def kid10_part1150 : Audit := .cycle 18 3 false (0)
theorem kid10_part1150_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid10_part1150) = true := by rfl

def kid10_part1151 : Audit := .split 17 (5,true) (byMove [
.cycle 0 58 true (-2),
.cycle 13 7 false (1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 32, 17, 64],[2, 16, 64, 1, 34, 1, 64],64⟩,
.last 19 (2,true),
.cycle 0 39 true (-2),
.cycle 12 11 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 29 3 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 16, 64, 1, 32, 16, 64],64⟩,
.cycle 14 5 false (0),
.last 18 (2,true),
.last 21 (2,true),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.cycle 17 32 true (-1),
.last 19 (2,true),
.cycle 0 50 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2705, 2048, 512, 128, 256, 8, 128, 2048, 528, 4096],[128, 16, 4096, 1, 2176, 512, 128, 16, 4096, 1, 128, 512, 4096],4096⟩,
.cycle 21 6 true (3),
.cycle 13 8 false (1)
])
theorem kid10_part1151_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid10_part1151) = true := by rfl

def kid10_part1152 : Audit := .cycle 1 11 true (1)
theorem kid10_part1152_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid10_part1152) = true := by rfl

def kid10_part1153 : Audit := .cycle 7 4 true (3)
theorem kid10_part1153_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid10_part1153) = true := by rfl

def kid10_part1154 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 18 true (2),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2048, 4096, 128, 256, 8, 128, 2048, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],4128⟩,
.cycle 10 9 true (2),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 7 6 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 2048, 4096, 128, 256, 8, 128, 2048, 4, 4096],[128, 16, 4, 1, 4, 4096, 128, 16, 4, 1, 4, 4096, 4096],4128⟩,
.cycle 0 14 true (0),
.cycle 10 16 true (2),
.last 13 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1154_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid10_part1154) = true := by rfl

def kid10_part1155 : Audit := .cycle 0 12 true (0)
theorem kid10_part1155_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid10_part1155) = true := by rfl

def kid10_part1156 : Audit := .cycle 8 4 true (4)
theorem kid10_part1156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid10_part1156) = true := by rfl

def kid10_part1157 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 10 9 true (2),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 1 22 true (1),
.cycle 10 4 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid10_part1157) = true := by rfl

def kid10_part1158 : Audit := .cycle 7 8 true (3)
theorem kid10_part1158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid10_part1158) = true := by rfl

def kid10_part1159 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 12 true (3),
.cycle 0 14 true (0),
.cycle 8 8 true (3),
.last 13 (5,true),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.cycle 5 20 true (1),
.cycle 5 8 true (1),
.cycle 23 3 false (1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 10 12 true (3),
.last 13 (5,true)
])
theorem kid10_part1159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid10_part1159) = true := by rfl

def kid10_part1160 : Audit := .cycle 1 13 true (1)
theorem kid10_part1160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid10_part1160) = true := by rfl

def kid10_part1161 : Audit := .cycle 4 12 true (1)
theorem kid10_part1161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid10_part1161) = true := by rfl

def kid10_part1162 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 7 9 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 8 true (3),
.cycle 13 3 true (5),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 20 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 32, 64],[2, 16, 64, 1, 32, 32, 64],64⟩
])
theorem kid10_part1162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid10_part1162) = true := by rfl

def kid10_part1163 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 28 13 true (2),
.last 18 (2,true),
.cycle 12 9 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.cycle 10 10 false (4),
.cycle 34 12 true (2),
.last 18 (2,true),
.cycle 30 20 true (0),
.cycle 12 6 false (2),
.cycle 23 3 true (5),
.cycle 12 8 false (2),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 12 9 false (2),
.cycle 14 4 false (0),
.cycle 15 4 false (-1),
.cycle 17 6 true (-1),
.cycle 12 12 false (2),
.last 18 (2,true),
.cycle 10 20 false (4),
.cycle 17 2 true (-1),
.cycle 21 5 true (3)
])
theorem kid10_part1163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid10_part1163) = true := by rfl

def kid10_part1164 : Audit := .cycle 1 11 true (1)
theorem kid10_part1164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid10_part1164) = true := by rfl

def kid10_part1165 : Audit := .cycle 7 4 true (3)
theorem kid10_part1165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid10_part1165) = true := by rfl

def kid10_part1166 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (5,true),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid10_part1166) = true := by rfl

def kid10_part1167 : Audit := .cycle 0 12 true (0)
theorem kid10_part1167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid10_part1167) = true := by rfl

def kid10_part1168 : Audit := .cycle 8 4 true (4)
theorem kid10_part1168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid10_part1168) = true := by rfl

def kid10_part1169 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
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
.cycle 9 5 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.cycle 19 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid10_part1169) = true := by rfl

def kid10_part1145 : Audit := .split 10 (4,true) (byMove [(kid10_part1146),(kid10_part1147),(kid10_part1148),(kid10_part1149),(kid10_part1150),(kid10_part1151),(kid10_part1152),(kid10_part1153),(kid10_part1154),(kid10_part1155),(kid10_part1156),(kid10_part1157),(kid10_part1158),(kid10_part1159),(kid10_part1160),(kid10_part1161),(kid10_part1162),(kid10_part1163),(kid10_part1164),(kid10_part1165),(kid10_part1166),(kid10_part1167),(kid10_part1168),(kid10_part1169)])

theorem kid10_part1145_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part1145) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid10_part1146),(kid10_part1147),(kid10_part1148),(kid10_part1149),(kid10_part1150),(kid10_part1151),(kid10_part1152),(kid10_part1153),(kid10_part1154),(kid10_part1155),(kid10_part1156),(kid10_part1157),(kid10_part1158),(kid10_part1159),(kid10_part1160),(kid10_part1161),(kid10_part1162),(kid10_part1163),(kid10_part1164),(kid10_part1165),(kid10_part1166),(kid10_part1167),(kid10_part1168),(kid10_part1169)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1146_checked

  · exact kid10_part1152_checked

  · exact kid10_part1158_checked

  · exact kid10_part1164_checked

  · exact kid10_part1147_checked

  · exact kid10_part1153_checked

  · exact kid10_part1159_checked

  · exact kid10_part1165_checked

  · exact kid10_part1148_checked

  · exact kid10_part1154_checked

  · exact kid10_part1160_checked

  · exact kid10_part1166_checked

  · exact kid10_part1149_checked

  · exact kid10_part1155_checked

  · exact kid10_part1161_checked

  · exact kid10_part1167_checked

  · exact kid10_part1150_checked

  · exact kid10_part1156_checked

  · exact kid10_part1162_checked

  · exact kid10_part1168_checked

  · exact kid10_part1151_checked

  · exact kid10_part1157_checked

  · exact kid10_part1163_checked

  · exact kid10_part1169_checked

def kid10_part1171 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (4,true),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 0 21 true (0),
.cycle 6 8 true (2),
.last 15 (4,true),
.last 21 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 12 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (4),
.cycle 12 5 true (4)
])
theorem kid10_part1171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part1171) = true := by rfl

def kid10_part1172 : Audit := .cycle 0 14 true (0)
theorem kid10_part1172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part1172) = true := by rfl

def kid10_part1173 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 21 (2,true),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 27 (2,true),
.cycle 12 7 true (2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 16, 2048, 262160, 8192, 16384, 8, 128, 131072, 16, 8192, 16384, 8, 128, 131072, 262144, 262144],[128, 16, 262144, 1, 16, 16, 8192, 16, 262144, 1, 16, 262144, 8192, 16, 262144, 1, 16, 262144, 262144],459808⟩,
.cycle 62 1 false (4),
.cycle 7 12 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 4 14 true (1),
.last 20 (2,true),
.cycle 31 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.last 21 (2,true),
.cycle 9 9 true (2)
])
theorem kid10_part1173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part1173) = true := by rfl

def kid10_part1174 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 7 9 true (2),
.last 25 (4,true),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 23 (4,true),
.cycle 3 13 true (1),
.cycle 8 8 true (2),
.last 22 (4,true),
.cycle 6 10 true (2),
.last 17 (4,true),
.cycle 5 14 true (1),
.cycle 1 17 true (1),
.last 16 (4,true),
.cycle 7 12 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 7 14 true (2),
.cycle 7 13 true (2)
])
theorem kid10_part1174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part1174) = true := by rfl

def kid10_part1175 : Audit := .split 14 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 0 26 true (0),
.cycle 47 1 false (3),
.cycle 1 21 true (0),
.cycle 19 3 false (0),
.cycle 15 3 false (1),
.cycle 0 18 true (0),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 1 23 true (0),
.cycle 52 3 false (7),
.cycle 17 3 false (1),
.cycle 16 19 true (2),
.last 16 (2,true),
.cycle 0 22 true (0),
.cycle 40 1 false (2),
.cycle 18 3 false (0),
.cycle 15 3 false (1),
.cycle 0 18 true (0),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 1 22 true (1),
.cycle 16 7 true (3),
.cycle 21 3 false (1)
])
theorem kid10_part1175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part1175) = true := by rfl

def kid10_part1176 : Audit := .cycle 15 1 false (-1)
theorem kid10_part1176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part1176) = true := by rfl

def kid10_part1177 : Audit := .cycle 1 11 true (1)
theorem kid10_part1177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part1177) = true := by rfl

def kid10_part1178 : Audit := .cycle 7 4 true (3)
theorem kid10_part1178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part1178) = true := by rfl

def kid10_part1179 : Audit := .split 11 (2,true) (byMove [
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
.last 33 (4,true),
.cycle 7 6 true (3),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 17 (4,true),
.last 21 (4,true),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part1179) = true := by rfl

def kid10_part1180 : Audit := .cycle 0 12 true (0)
theorem kid10_part1180_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part1180) = true := by rfl

def kid10_part1181 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 8 4 true (4),
.cycle 44 1 false (10),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 14 true (1),
.cycle 8 6 true (4),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1181_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part1181) = true := by rfl

def kid10_part1182 : Audit := .cycle 36 1 false (8)
theorem kid10_part1182_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part1182) = true := by rfl

def kid10_part1183 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (3),
.cycle 27 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 12 7 true (3),
.cycle 8 6 true (3),
.cycle 19 11 true (3),
.cycle 7 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 6 10 true (2),
.cycle 27 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 6 true (4),
.cycle 9 5 true (3)
])
theorem kid10_part1183_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part1183) = true := by rfl

def kid10_part1184 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 17 (4,true),
.cycle 29 1 false (1),
.cycle 7 8 true (3),
.last 13 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 20 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.last 19 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 15 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid10_part1184_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part1184) = true := by rfl

def kid10_part1185 : Audit := .cycle 1 13 true (1)
theorem kid10_part1185_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part1185) = true := by rfl

def kid10_part1186 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 5 14 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 25 (2,true),
.cycle 11 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 32, 16, 64],[2, 16, 64, 1, 16, 18, 64],64⟩,
.cycle 51 1 false (3),
.cycle 7 10 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (1),
.cycle 1 19 true (1),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 5 14 true (1),
.cycle 9 7 true (2)
])
theorem kid10_part1186_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part1186) = true := by rfl

def kid10_part1187 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 1 21 true (1),
.last 14 (2,true),
.cycle 1 20 true (1),
.cycle 17 6 false (1),
.cycle 22 1 false (-2),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 10 4 true (3),
.cycle 7 14 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 4 14 true (1),
.cycle 18 3 false (0),
.cycle 22 1 false (-2),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 6 true (3),
.cycle 12 2 true (3)
])
theorem kid10_part1187_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part1187) = true := by rfl

def kid10_part1188 : Audit := .cycle 15 1 false (-1)
theorem kid10_part1188_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part1188) = true := by rfl

def kid10_part1189 : Audit := .cycle 1 11 true (1)
theorem kid10_part1189_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part1189) = true := by rfl

def kid10_part1190 : Audit := .cycle 7 4 true (3)
theorem kid10_part1190_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part1190) = true := by rfl

def kid10_part1191 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (4,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 2 15 true (1),
.cycle 6 6 true (2),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1191_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part1191) = true := by rfl

def kid10_part1192 : Audit := .cycle 0 12 true (0)
theorem kid10_part1192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part1192) = true := by rfl

def kid10_part1193 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 23 5 false (1),
.cycle 8 5 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 29 (2,true),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 8 9 true (4),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 22 5 false (2),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part1193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part1193) = true := by rfl

def kid10_part1194 : Audit := .cycle 9 3 true (4)
theorem kid10_part1194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part1194) = true := by rfl

def kid10_part1170 : Audit := .split 10 (5,true) (byMove [(kid10_part1171),(kid10_part1172),(kid10_part1173),(kid10_part1174),(kid10_part1175),(kid10_part1176),(kid10_part1177),(kid10_part1178),(kid10_part1179),(kid10_part1180),(kid10_part1181),(kid10_part1182),(kid10_part1183),(kid10_part1184),(kid10_part1185),(kid10_part1186),(kid10_part1187),(kid10_part1188),(kid10_part1189),(kid10_part1190),(kid10_part1191),(kid10_part1192),(kid10_part1193),(kid10_part1194)])

theorem kid10_part1170_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part1170) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part1171),(kid10_part1172),(kid10_part1173),(kid10_part1174),(kid10_part1175),(kid10_part1176),(kid10_part1177),(kid10_part1178),(kid10_part1179),(kid10_part1180),(kid10_part1181),(kid10_part1182),(kid10_part1183),(kid10_part1184),(kid10_part1185),(kid10_part1186),(kid10_part1187),(kid10_part1188),(kid10_part1189),(kid10_part1190),(kid10_part1191),(kid10_part1192),(kid10_part1193),(kid10_part1194)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1171_checked

  · exact kid10_part1177_checked

  · exact kid10_part1183_checked

  · exact kid10_part1189_checked

  · exact kid10_part1172_checked

  · exact kid10_part1178_checked

  · exact kid10_part1184_checked

  · exact kid10_part1190_checked

  · exact kid10_part1173_checked

  · exact kid10_part1179_checked

  · exact kid10_part1185_checked

  · exact kid10_part1191_checked

  · exact kid10_part1174_checked

  · exact kid10_part1180_checked

  · exact kid10_part1186_checked

  · exact kid10_part1192_checked

  · exact kid10_part1175_checked

  · exact kid10_part1181_checked

  · exact kid10_part1187_checked

  · exact kid10_part1193_checked

  · exact kid10_part1176_checked

  · exact kid10_part1182_checked

  · exact kid10_part1188_checked

  · exact kid10_part1194_checked

def kid10_part1195 : Audit := .cycle 0 10 true (0)
theorem kid10_part1195_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part1195) = true := by rfl

def kid10_part1196 : Audit := .cycle 1 9 true (1)
theorem kid10_part1196_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part1196) = true := by rfl

def kid10_part1197 : Audit := .cycle 2 8 true (1)
theorem kid10_part1197_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part1197) = true := by rfl

def kid10_part1198 : Audit := .cycle 1 12 true (1)
theorem kid10_part1198_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part1198) = true := by rfl

def kid10_part1199 : Audit := .cycle 8 2 true (4)
theorem kid10_part1199_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part1199) = true := by rfl

def kid10_part1200 : Audit := .cycle 9 1 true (5)
theorem kid10_part1200_checked : zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part1200) = true := by rfl

def kid10_part1104 : Audit := .split 9 (5,false) (byMove [(kid10_part1105),(kid10_part1106),(kid10_part1107),(kid10_part1108),(kid10_part1109),(kid10_part1110),(kid10_part1111),(kid10_part1112),(kid10_part1113),(kid10_part1114),(kid10_part1115),(kid10_part1116),(kid10_part1117),(kid10_part1118),(kid10_part1119),(kid10_part1144),(kid10_part1145),(kid10_part1170),(kid10_part1195),(kid10_part1196),(kid10_part1197),(kid10_part1198),(kid10_part1199),(kid10_part1200)])

theorem kid10_part1104_checked : zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid10_part1104) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part1105),(kid10_part1106),(kid10_part1107),(kid10_part1108),(kid10_part1109),(kid10_part1110),(kid10_part1111),(kid10_part1112),(kid10_part1113),(kid10_part1114),(kid10_part1115),(kid10_part1116),(kid10_part1117),(kid10_part1118),(kid10_part1119),(kid10_part1144),(kid10_part1145),(kid10_part1170),(kid10_part1195),(kid10_part1196),(kid10_part1197),(kid10_part1198),(kid10_part1199),(kid10_part1200)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1105_checked

  · exact kid10_part1111_checked

  · exact kid10_part1117_checked

  · exact kid10_part1195_checked

  · exact kid10_part1106_checked

  · exact kid10_part1112_checked

  · exact kid10_part1118_checked

  · exact kid10_part1196_checked

  · exact kid10_part1107_checked

  · exact kid10_part1113_checked

  · exact kid10_part1119_checked

  · exact kid10_part1197_checked

  · exact kid10_part1108_checked

  · exact kid10_part1114_checked

  · exact kid10_part1144_checked

  · exact kid10_part1198_checked

  · exact kid10_part1109_checked

  · exact kid10_part1115_checked

  · exact kid10_part1145_checked

  · exact kid10_part1199_checked

  · exact kid10_part1110_checked

  · exact kid10_part1116_checked

  · exact kid10_part1170_checked

  · exact kid10_part1200_checked

def kid10 : Audit := .split 8 (4,false) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part54),(kid10_part247),(kid10_part248),(kid10_part249),(kid10_part370),(kid10_part419),(kid10_part420),(kid10_part565),(kid10_part566),(kid10_part687),(kid10_part688),(kid10_part689),(kid10_part810),(kid10_part1099),(kid10_part1100),(kid10_part1101),(kid10_part1102),(kid10_part1103),(kid10_part1104)])

theorem check10 : zipCheck 175 (child39 ⟨false,true,4⟩) (kid10) = true := by

  change (zipQueryOK 175 (child39 ⟨false,true,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨false,true,4⟩) (4,false) (some mv)) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part54),(kid10_part247),(kid10_part248),(kid10_part249),(kid10_part370),(kid10_part419),(kid10_part420),(kid10_part565),(kid10_part566),(kid10_part687),(kid10_part688),(kid10_part689),(kid10_part810),(kid10_part1099),(kid10_part1100),(kid10_part1101),(kid10_part1102),(kid10_part1103),(kid10_part1104)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1_checked

  · exact kid10_part247_checked

  · exact kid10_part565_checked

  · exact kid10_part1099_checked

  · exact kid10_part2_checked

  · exact kid10_part248_checked

  · exact kid10_part566_checked

  · exact kid10_part1100_checked

  · exact kid10_part3_checked

  · exact kid10_part249_checked

  · exact kid10_part687_checked

  · exact kid10_part1101_checked

  · exact kid10_part4_checked

  · exact kid10_part370_checked

  · exact kid10_part688_checked

  · exact kid10_part1102_checked

  · exact kid10_part5_checked

  · exact kid10_part419_checked

  · exact kid10_part689_checked

  · exact kid10_part1103_checked

  · exact kid10_part54_checked

  · exact kid10_part420_checked

  · exact kid10_part810_checked

  · exact kid10_part1104_checked

end BB6.Agent11Raw39
