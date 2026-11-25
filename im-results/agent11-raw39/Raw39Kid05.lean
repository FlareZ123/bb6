import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid05_part1 : Audit := .cycle 0 9 true (0)
theorem kid05_part1_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,0⟩)) (kid05_part1) = true := by rfl

def kid05_part2 : Audit := .cycle 1 8 true (1)
theorem kid05_part2_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,1⟩)) (kid05_part2) = true := by rfl

def kid05_part3 : Audit := .cycle 17 1 false (1)
theorem kid05_part3_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,2⟩)) (kid05_part3) = true := by rfl

def kid05_part4 : Audit := .cycle 1 11 true (0)
theorem kid05_part4_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,3⟩)) (kid05_part4) = true := by rfl

def kid05_part6 : Audit := .cycle 1 10 true (0)
theorem kid05_part6_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part6) = true := by rfl

def kid05_part7 : Audit := .split 11 (5,false) (byMove [
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
.cycle 13 9 false (-1),
.split 13 (2,true) (byMove [
.cycle 1 14 false (3),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 0 15 false (3),
.last 14 (4,true),
.cycle 14 9 false (-2),
.cycle 7 24 false (3),
.cycle 1 22 false (3),
.cycle 16 9 false (0),
.cycle 14 9 false (0),
.cycle 1 14 false (3),
.cycle 11 3 true (-2),
.cycle 14 9 false (-1),
.cycle 10 4 false (0),
.cycle 1 17 false (3),
.cycle 1 15 false (3),
.last 14 (4,true),
.cycle 14 9 false (-2),
.last 26 (4,true),
.cycle 23 9 false (-1),
.cycle 2 12 false (3),
.cycle 4 28 false (3),
.cycle 15 9 false (-1),
.cycle 15 9 false (-1)
]),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.split 37 (2,true) (byMove [
.cycle 1 50 false (3),
.cycle 1 40 false (3),
.cycle 42 9 false (-4),
.last 51 (4,true),
.last 38 (4,true),
.last 39 (4,true),
.last 50 (4,true),
.cycle 1 58 false (3),
.cycle 19 21 false (3),
.cycle 19 19 false (3),
.cycle 1 50 false (3),
.cycle 1 42 false (3),
.last 41 (4,true),
.cycle 1 40 false (3),
.cycle 1 54 false (3),
.last 51 (4,true),
.last 38 (4,true),
.last 39 (4,true),
.last 50 (4,true),
.last 49 (4,true),
.cycle 1 48 false (3),
.last 52 (4,true),
.last 41 (4,true),
.last 39 (4,true)
]),
.cycle 11 1 false (-1),
.cycle 22 9 false (0),
.cycle 1 11 false (3),
.cycle 12 9 false (1),
.cycle 1 14 true (-1),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
])
theorem kid05_part7_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part7) = true := by rfl

def kid05_part8 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 false (3),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
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
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.cycle 26 1 false (-2),
.cycle 1 11 false (3),
.cycle 21 1 false (-1),
.cycle 1 14 true (-1),
.cycle 9 3 false (1),
.cycle 11 1 true (-1)
]),
.cycle 0 11 true (0),
.cycle 21 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 13 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 22 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 22 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 14 1 false (2),
.cycle 11 1 true (1),
.cycle 17 1 false (-1),
.cycle 10 3 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 11 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 21 1 false (1),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
]),
.cycle 16 1 false (-2),
.split 14 (5,false) (byMove [
.cycle 16 19 true (-2),
.cycle 25 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 17 1 false (-3),
.cycle 14 1 false (-2),
.cycle 20 1 false (-2),
.cycle 11 4 true (-2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 20 1 false (-4),
.cycle 11 4 false (0),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 17 1 false (-3),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 21 1 false (-3),
.cycle 0 17 true (-2),
.cycle 22 1 false (-2),
.cycle 9 6 false (1),
.last 17 (4,true)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 12 true (-1),
.cycle 24 1 false (0),
.cycle 10 2 true (-1),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.cycle 26 1 false (-2),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 0 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 20 1 false (0),
.cycle 1 13 true (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 24 1 false (-2),
.cycle 10 2 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 30 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 22 1 false (0),
.cycle 11 1 true (1),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.last 14 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid05_part8_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part8) = true := by rfl

def kid05_part9 : Audit := .cycle 0 11 true (0)
theorem kid05_part9_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part9) = true := by rfl

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
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 24 1 false (-2),
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
.last 13 (2,true),
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
.split 12 (2,true) (byMove [
.cycle 1 13 false (3),
.last 14 (5,false),
.cycle 15 1 false (-1),
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
.last 14 (5,false),
.cycle 1 16 true (-2),
.cycle 1 14 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 26 1 false (-2),
.last 24 (5,false),
.cycle 2 11 false (3),
.cycle 1 15 true (-1),
.last 16 (5,false),
.last 13 (5,false)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 1 false (-1),
.split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 1 12 true (-1),
.cycle 22 1 false (0),
.last 12 (2,true),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 24 1 false (-2),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 0 13 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 18 1 false (0),
.cycle 1 13 true (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 22 1 false (-2),
.last 12 (2,true),
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
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 10 4 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.cycle 11 1 true (1)
])
])
theorem kid05_part10_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part10) = true := by rfl

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
.cycle 10 5 false (0),
.split 14 (2,true) (byMove [
.cycle 1 15 false (3),
.cycle 12 4 false (-2),
.cycle 17 1 false (-3),
.cycle 0 16 false (3),
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 8 17 false (2),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.cycle 10 12 false (0),
.cycle 10 10 false (0),
.cycle 12 6 false (-1),
.cycle 12 3 true (-3),
.cycle 10 7 false (0),
.cycle 12 4 false (-2),
.cycle 1 18 false (3),
.cycle 1 16 false (3),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 26 (4,true),
.last 25 (4,true),
.cycle 2 13 false (3),
.cycle 8 19 false (2),
.last 17 (4,true),
.cycle 10 7 false (0)
]),
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
.cycle 10 17 false (2),
.last 26 (2,true),
.cycle 0 27 false (3),
.cycle 25 1 false (-3),
.cycle 23 6 false (-1),
.cycle 14 13 false (2),
.cycle 13 12 true (-2),
.cycle 1 24 false (3),
.cycle 10 21 false (2),
.cycle 1 27 false (3),
.cycle 9 16 false (2),
.cycle 12 13 true (-2)
]),
.cycle 1 12 false (3),
.cycle 10 9 false (0),
.cycle 1 15 false (3),
.cycle 9 4 false (1),
.cycle 12 1 true (-2)
])
theorem kid05_part11_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part11) = true := by rfl

def kid05_part12 : Audit := .cycle 0 10 true (0)
theorem kid05_part12_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part12) = true := by rfl

def kid05_part13 : Audit := .cycle 1 9 true (1)
theorem kid05_part13_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part13) = true := by rfl

def kid05_part14 : Audit := .cycle 20 1 false (2)
theorem kid05_part14_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part14) = true := by rfl

def kid05_part15 : Audit := .cycle 17 1 false (1)
theorem kid05_part15_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part15) = true := by rfl

def kid05_part16 : Audit := .cycle 9 1 true (1)
theorem kid05_part16_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part16) = true := by rfl

def kid05_part17 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 9 2 true (1),
.cycle 14 1 false (0),
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
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 16 5 false (0),
.cycle 15 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 5 false (2),
.cycle 1 17 true (0),
.cycle 9 6 true (0),
.cycle 17 5 false (1)
]),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 16 4 false (0),
.cycle 16 1 false (0),
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
.cycle 16 4 false (0),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (1),
.last 16 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 8 4 true (1),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (1),
.cycle 10 1 true (2)
])
theorem kid05_part17_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part17) = true := by rfl

def kid05_part18 : Audit := .cycle 11 4 false (1)
theorem kid05_part18_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part18) = true := by rfl

def kid05_part20 : Audit := .cycle 0 16 true (-2)
theorem kid05_part20_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part20) = true := by rfl

def kid05_part21 : Audit := .split 22 (2,true) (byMove [
.cycle 1 23 false (3),
.cycle 10 13 false (0),
.cycle 25 1 false (-3),
.far true 3 ⟨0,[0, 1, 2, 1, 0, 1],[131120, 130, 512, 512, 128, 2, 16, 130, 130, 512, 128, 8192, 131104, 131104, 512, 512, 128, 2, 262144],[131120, 32, 8, 130, 262144, 16, 16, 131072, 32768, 130, 262144, 65536, 131104, 32, 8, 128, 262144, 16, 262144],262144⟩,
.last 23 (4,true),
.cycle 19 4 false (-1),
.cycle 7 31 false (5),
.cycle 88 11 true (2),
.cycle 14 11 false (0),
.cycle 14 9 false (0),
.last 29 (4,true),
.cycle 1 23 false (3),
.cycle 17 6 false (0),
.cycle 10 13 false (0),
.cycle 31 49 false (5),
.far true 3 ⟨0,[0, 1, 2, 1, 0, 1],[131120, 130, 512, 512, 128, 2, 16, 130, 130, 512, 128, 8192, 131104, 131104, 512, 512, 128, 2, 262144],[131120, 32, 512, 130, 262144, 16, 16, 131072, 512, 130, 262144, 65536, 131104, 32, 512, 128, 262144, 16, 262144],262144⟩,
.last 23 (4,true),
.cycle 19 4 false (-1),
.last 38 (4,true),
.last 49 (4,true),
.cycle 2 21 false (3),
.cycle 7 35 false (5),
.cycle 18 6 false (0),
.cycle 18 6 false (0)
])
theorem kid05_part21_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part21) = true := by rfl

def kid05_part22 : Audit := .cycle 13 1 false (-1)
theorem kid05_part22_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part22) = true := by rfl

def kid05_part23 : Audit := .cycle 12 1 false (-2)
theorem kid05_part23_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part23) = true := by rfl

def kid05_part24 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 false (3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.last 59 (4,true),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 33 (4,true),
.cycle 12 11 false (0),
.cycle 12 9 false (-1),
.last 21 (4,true),
.cycle 9 7 false (1),
.cycle 12 6 false (-2),
.cycle 10 5 false (0),
.cycle 23 41 false (5),
.last 59 (4,true),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 33 (4,true),
.cycle 2 13 false (3),
.last 34 (4,true),
.cycle 12 6 false (-1),
.last 16 (4,true)
])
theorem kid05_part24_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part24) = true := by rfl

def kid05_part25 : Audit := .cycle 11 1 false (-1)
theorem kid05_part25_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part25) = true := by rfl

def kid05_part26 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 false (3),
.cycle 0 20 false (3),
.cycle 20 1 false (-2),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 14 4 false (0),
.cycle 7 24 false (3),
.cycle 13 11 true (-2),
.cycle 13 11 false (1),
.cycle 13 9 false (1),
.cycle 15 3 true (-2),
.cycle 0 19 true (-2),
.cycle 13 6 false (1),
.cycle 10 8 false (1),
.cycle 1 21 false (3),
.cycle 1 19 false (3),
.last 18 (4,true),
.cycle 14 4 false (0),
.last 30 (4,true),
.last 64 (4,true),
.cycle 2 16 false (3),
.cycle 7 26 false (3),
.cycle 13 6 false (1),
.cycle 30 10 false (2)
])
theorem kid05_part26_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part26) = true := by rfl

def kid05_part27 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (-1),
.cycle 12 13 false (2),
.cycle 16 1 false (0),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 12 4 false (1),
.cycle 0 14 true (-1),
.cycle 12 11 true (0),
.cycle 12 11 false (3),
.cycle 12 9 false (2),
.cycle 12 3 true (0),
.cycle 12 12 true (0),
.cycle 12 6 false (1),
.cycle 10 4 true (-1),
.cycle 1 17 true (-1),
.cycle 1 15 true (-1),
.last 14 (4,true),
.cycle 12 4 false (1),
.last 26 (4,true),
.cycle 0 31 true (-2),
.cycle 2 12 true (-1),
.cycle 1 16 true (-1),
.cycle 12 6 false (2),
.cycle 12 12 true (0)
])
theorem kid05_part27_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part27) = true := by rfl

def kid05_part28 : Audit := .cycle 0 14 true (-1)
theorem kid05_part28_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part28) = true := by rfl

def kid05_part29 : Audit := .cycle 12 1 false (0)
theorem kid05_part29_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part29) = true := by rfl

def kid05_part30 : Audit := .split 14 (2,true) (byMove [
.cycle 1 33 false (3),
.cycle 10 5 false (0),
.cycle 17 1 false (-1),
.cycle 0 23 false (3),
.last 15 (4,true),
.cycle 12 4 false (0),
.cycle 1 15 true (-1),
.cycle 17 11 true (0),
.cycle 18 11 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 12 6 false (0),
.cycle 10 5 false (0),
.cycle 1 27 false (3),
.cycle 1 23 false (3),
.last 15 (4,true),
.cycle 12 4 false (0),
.last 27 (4,true),
.last 17 (4,true),
.cycle 2 27 false (3),
.cycle 0 16 true (-1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part30_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part30) = true := by rfl

def kid05_part31 : Audit := .split 16 (2,true) (byMove [
.cycle 1 17 false (3),
.cycle 18 1 true (-2),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 0 17 true (-1),
.cycle 13 11 true (-1),
.cycle 13 11 false (2),
.cycle 13 9 false (1),
.cycle 14 3 true (-1),
.cycle 17 1 true (1),
.cycle 13 6 false (1),
.cycle 10 7 false (1),
.cycle 1 20 true (-2),
.cycle 1 18 true (-1),
.last 17 (4,true),
.cycle 13 4 false (1),
.last 29 (4,true),
.last 65 (4,true),
.cycle 2 15 false (3),
.cycle 1 19 true (-1),
.cycle 13 6 false (1),
.cycle 17 1 true (1)
])
theorem kid05_part31_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part31) = true := by rfl

def kid05_part32 : Audit := .split 17 (2,true) (byMove [
.cycle 1 18 false (3),
.cycle 10 8 false (0),
.cycle 20 1 false (-4),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 14 4 false (-2),
.last 37 (4,true),
.last 47 (4,true),
.cycle 13 11 false (-1),
.cycle 13 9 false (-1),
.last 27 (4,true),
.last 22 (4,true),
.cycle 13 6 false (-1),
.cycle 10 8 false (0),
.cycle 1 21 false (3),
.cycle 1 19 false (3),
.last 18 (4,true),
.cycle 14 4 false (-2),
.last 37 (4,true),
.last 49 (4,true),
.cycle 2 16 false (3),
.last 39 (4,true),
.cycle 13 6 false (-1),
.last 22 (4,true)
])
theorem kid05_part32_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part32) = true := by rfl

def kid05_part33 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 128, 8192, 16384, 8, 128, 128, 128, 33554432, 67108864, 2097152, 128, 16777216, 16777216, 33554432, 67108864, 134217728, 2097152, 1327497216, 1327497216, 33554432, 67108864, 134217728, 1327497216, 1327497216, 1327497216, 1073741824],[128, 16384, 1327513600, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 16384, 16777216, 1073741824, 33554432, 33554432, 1327497216, 1327497216, 16777216, 1073741824, 1327497216, 1073741824],2145333582⟩,
.last 14 (4,true),
.cycle 12 4 false (-1),
.cycle 7 8 false (3),
.cycle 14 11 true (0),
.cycle 0 16 true (-2),
.cycle 12 9 false (0),
.last 17 (4,true),
.last 34 (4,true),
.cycle 12 6 false (-1),
.cycle 10 4 false (0),
.cycle 1 33 false (3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 128, 8192, 16384, 8, 128, 128, 128, 33554432, 67108864, 2097152, 128, 16777216, 16777216, 33554432, 67108864, 134217728, 2097152, 1325400064, 1325400064, 33554432, 67108864, 134217728, 1325400064, 1325400064, 1325400064, 1073741824],[128, 16384, 1327497216, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 2097152, 16777216, 1073741824, 33554432, 33554432, 1325400064, 1325400064, 16777216, 1073741824, 1325400064, 1073741824],2145333582⟩,
.last 14 (4,true),
.cycle 12 4 false (-1),
.last 17 (4,true),
.last 27 (4,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.cycle 12 6 false (0),
.cycle 12 6 false (0)
])
theorem kid05_part33_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part33) = true := by rfl

def kid05_part34 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 false (3),
.cycle 0 24 false (3),
.cycle 22 1 false (-2),
.cycle 0 21 false (3),
.last 20 (4,true),
.cycle 16 4 false (0),
.cycle 18 16 true (-2),
.cycle 15 11 true (-2),
.cycle 15 11 false (1),
.cycle 15 9 false (1),
.cycle 17 3 true (-2),
.cycle 0 23 true (-2),
.cycle 15 6 false (1),
.cycle 10 10 false (1),
.cycle 1 23 false (3),
.cycle 1 21 false (3),
.last 20 (4,true),
.cycle 16 4 false (0),
.last 32 (4,true),
.last 68 (4,true),
.cycle 2 18 false (3),
.cycle 7 30 false (3),
.cycle 15 6 false (1),
.last 23 (4,true)
])
theorem kid05_part34_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part34) = true := by rfl

def kid05_part35 : Audit := .cycle 12 1 false (-2)
theorem kid05_part35_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part35) = true := by rfl

def kid05_part36 : Audit := .split 14 (2,true) (byMove [
.last 37 (4,true),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.cycle 0 23 false (3),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 17 (4,true),
.cycle 0 18 true (-3),
.cycle 3 19 false (3),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 12 6 false (-2),
.cycle 10 5 false (0),
.cycle 1 27 false (3),
.cycle 1 23 false (3),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 17 (4,true),
.last 33 (4,true),
.last 44 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part36_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part36) = true := by rfl

def kid05_part37 : Audit := .cycle 11 1 false (-1)
theorem kid05_part37_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part37) = true := by rfl

def kid05_part38 : Audit := .split 15 (4,true) (byMove [
.cycle 0 16 false (3),
.last 26 (2,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (2,true),
.last 31 (2,true),
.cycle 0 16 true (-1),
.last 26 (2,true),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 18 (2,true),
.last 31 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 18 (2,true),
.last 31 (2,true),
.last 30 (2,true),
.cycle 1 15 false (3),
.last 25 (2,true),
.cycle 1 18 true (-1),
.cycle 9 7 false (1),
.cycle 11 19 true (-1)
])
theorem kid05_part38_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part38) = true := by rfl

def kid05_part39 : Audit := .split 13 (2,true) (byMove [
.cycle 1 29 false (3),
.cycle 1 20 false (3),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 12 11 true (0),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 12 3 true (0),
.cycle 1 14 true (-1),
.last 17 (4,true),
.cycle 10 9 false (1),
.cycle 1 27 false (3),
.cycle 1 15 true (-1),
.last 14 (4,true),
.last 15 (4,true),
.last 26 (4,true),
.last 25 (4,true),
.cycle 2 25 false (3),
.cycle 1 16 true (-1),
.last 17 (4,true),
.last 26 (4,true)
])
theorem kid05_part39_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part39) = true := by rfl

def kid05_part40 : Audit := .cycle 0 14 true (-1)
theorem kid05_part40_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part40) = true := by rfl

def kid05_part41 : Audit := .split 19 (2,true) (byMove [
.cycle 1 20 false (3),
.cycle 1 24 false (3),
.cycle 22 1 false (-2),
.cycle 0 21 false (3),
.last 20 (4,true),
.cycle 16 4 false (0),
.cycle 4 28 false (3),
.cycle 12 11 true (-2),
.cycle 12 11 false (1),
.cycle 12 9 false (1),
.cycle 17 3 true (-2),
.cycle 1 23 true (-2),
.cycle 14 6 false (1),
.cycle 10 10 false (1),
.cycle 1 23 false (3),
.cycle 1 21 false (3),
.last 20 (4,true),
.cycle 16 4 false (0),
.last 32 (4,true),
.last 68 (4,true),
.cycle 2 18 false (3),
.cycle 4 30 false (3),
.cycle 15 6 false (1),
.cycle 34 12 false (2)
])
theorem kid05_part41_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part41) = true := by rfl

def kid05_part42 : Audit := .cycle 9 3 false (1)
theorem kid05_part42_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part42) = true := by rfl

def kid05_part43 : Audit := .split 14 (4,true) (byMove [
.cycle 1 15 false (3),
.cycle 16 1 true (-2),
.last 15 (2,true),
.cycle 0 16 true (-1),
.last 18 (2,true),
.last 18 (2,true),
.cycle 0 15 true (-1),
.last 25 (2,true),
.last 25 (2,true),
.last 23 (2,true),
.last 17 (2,true),
.cycle 15 1 true (1),
.last 20 (2,true),
.cycle 10 5 false (1),
.last 15 (2,true),
.cycle 1 16 true (-1),
.last 18 (2,true),
.last 18 (2,true),
.last 30 (2,true),
.last 28 (2,true),
.cycle 2 13 false (3),
.cycle 1 17 true (-1),
.last 20 (2,true),
.cycle 15 1 true (1)
])
theorem kid05_part43_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part43) = true := by rfl

def kid05_part19 : Audit := .split 11 (5,false) (byMove [(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28),(kid05_part29),(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42),(kid05_part43)])

theorem kid05_part19_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part19) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some mv)) (byMove [(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28),(kid05_part29),(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42),(kid05_part43)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part25_checked

  · exact kid05_part31_checked

  · exact kid05_part37_checked

  · exact kid05_part43_checked

def kid05_part45 : Audit := .cycle 12 14 true (-1)
theorem kid05_part45_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part45) = true := by rfl

def kid05_part46 : Audit := .cycle 0 14 true (-1)
theorem kid05_part46_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part46) = true := by rfl

def kid05_part47 : Audit := .cycle 12 1 false (0)
theorem kid05_part47_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part47) = true := by rfl

def kid05_part48 : Audit := .cycle 11 1 false (-1)
theorem kid05_part48_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part48) = true := by rfl

def kid05_part49 : Audit := .cycle 0 20 true (-2)
theorem kid05_part49_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part49) = true := by rfl

def kid05_part50 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.last 27 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 19 (4,true),
.cycle 11 1 false (-1),
.cycle 0 18 true (-2),
.cycle 0 18 true (-2),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 1 15 true (-1),
.cycle 0 17 true (-1),
.last 37 (4,true),
.last 37 (4,true),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.last 19 (4,true),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 0 14 true (-1),
.cycle 0 20 true (-2),
.cycle 9 3 false (1),
.last 14 (4,true)
])
theorem kid05_part50_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part50) = true := by rfl

def kid05_part51 : Audit := .cycle 1 11 true (0)
theorem kid05_part51_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part51) = true := by rfl

def kid05_part52 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 false (3),
.cycle 0 24 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-2),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 16 true (0),
.cycle 12 1 true (0),
.cycle 0 19 false (3),
.cycle 0 26 true (-1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 1 16 true (-2),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 true (-1),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid05_part52_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part52) = true := by rfl

def kid05_part53 : Audit := .cycle 13 1 false (3)
theorem kid05_part53_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part53) = true := by rfl

def kid05_part54 : Audit := .cycle 0 12 true (0)
theorem kid05_part54_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part54) = true := by rfl

def kid05_part55 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 15 true (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 0 18 true (-2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 1 15 true (-1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid05_part55_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part55) = true := by rfl

def kid05_part56 : Audit := .cycle 0 15 true (-1)
theorem kid05_part56_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part56) = true := by rfl

def kid05_part57 : Audit := .split 23 (4,true) (byMove [
.cycle 0 24 false (3),
.cycle 0 35 false (3),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 0 27 false (3),
.last 24 (5,false),
.cycle 0 24 true (-3),
.cycle 0 35 true (-3),
.cycle 25 1 false (1),
.cycle 24 1 false (0),
.cycle 0 27 true (-3),
.last 24 (5,false),
.cycle 0 30 false (3),
.cycle 0 32 false (3),
.cycle 0 26 true (-3),
.cycle 24 1 false (-2),
.cycle 1 27 false (3),
.last 24 (5,false),
.cycle 12 24 true (-3),
.cycle 1 23 false (3),
.cycle 0 34 true (-3),
.cycle 1 26 true (-3),
.cycle 9 15 false (1),
.last 24 (5,false)
])
theorem kid05_part57_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part57) = true := by rfl

def kid05_part58 : Audit := .split 14 (5,false) (byMove [
.cycle 16 19 true (-2),
.cycle 21 8 true (-4),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 15 8 true (-4),
.cycle 14 1 false (-2),
.cycle 16 8 true (-3),
.cycle 11 4 true (-2),
.cycle 1 17 true (-2),
.cycle 15 1 false (-1),
.cycle 0 24 true (-2),
.cycle 0 26 true (-2),
.last 43 (4,true),
.cycle 11 4 false (0),
.cycle 18 8 true (-3),
.cycle 15 1 false (-3),
.cycle 19 8 true (-4),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 15 8 true (-4),
.cycle 1 17 true (-2),
.cycle 18 8 true (-3),
.cycle 9 6 false (1),
.last 17 (4,true)
])
theorem kid05_part58_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part58) = true := by rfl

def kid05_part59 : Audit := .cycle 1 13 true (-1)
theorem kid05_part59_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part59) = true := by rfl

def kid05_part60 : Audit := .cycle 11 1 false (-1)
theorem kid05_part60_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part60) = true := by rfl

def kid05_part61 : Audit := .cycle 0 20 true (-2)
theorem kid05_part61_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part61) = true := by rfl

def kid05_part62 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 25 (4,true),
.cycle 11 1 false (-1),
.cycle 0 18 true (-2),
.cycle 0 26 true (-2),
.cycle 10 2 true (-1),
.cycle 1 13 true (-1),
.last 12 (4,true),
.cycle 0 22 true (-2),
.last 22 (4,true),
.last 28 (4,true),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.last 25 (4,true),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 21 (4,true),
.last 27 (4,true),
.cycle 1 13 true (-1),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part62_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part62) = true := by rfl

def kid05_part63 : Audit := .cycle 1 11 true (0)
theorem kid05_part63_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part63) = true := by rfl

def kid05_part64 : Audit := .cycle 0 16 true (-2)
theorem kid05_part64_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part64) = true := by rfl

def kid05_part65 : Audit := .cycle 2 10 true (0)
theorem kid05_part65_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part65) = true := by rfl

def kid05_part66 : Audit := .cycle 0 12 true (0)
theorem kid05_part66_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part66) = true := by rfl

def kid05_part67 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 9 4 true (0),
.cycle 0 13 true (0),
.cycle 0 16 true (-2),
.cycle 0 16 true (-2),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 9 58 true (-1),
.cycle 0 21 true (-1),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 0 18 true (-2),
.last 13 (5,false),
.cycle 10 2 true (0),
.cycle 1 13 true (0),
.cycle 0 22 true (-2),
.cycle 0 22 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid05_part67_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part67) = true := by rfl

def kid05_part68 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 0 24 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 16 true (0),
.last 13 (5,false),
.cycle 0 19 false (3),
.last 15 (5,false),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 1 16 true (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 true (-1),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid05_part68_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part68) = true := by rfl

def kid05_part44 : Audit := .split 10 (2,true) (byMove [(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66),(kid05_part67),(kid05_part68)])

theorem kid05_part44_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part44) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66),(kid05_part67),(kid05_part68)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part50_checked

  · exact kid05_part56_checked

  · exact kid05_part62_checked

  · exact kid05_part68_checked

def kid05_part69 : Audit := .cycle 1 11 true (0)
theorem kid05_part69_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part69) = true := by rfl

def kid05_part71 : Audit := .split 13 (2,true) (byMove [
.cycle 12 14 true (-1),
.cycle 16 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 1 15 false (3),
.cycle 0 16 false (3),
.cycle 0 14 true (-1),
.last 29 (5,false),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 12 21 true (-1),
.last 14 (5,false),
.cycle 0 18 false (3),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.cycle 1 15 true (-1),
.cycle 12 4 true (-1),
.cycle 0 20 true (-2),
.cycle 12 14 true (0),
.cycle 12 13 true (0),
.cycle 12 12 true (-1),
.cycle 1 16 true (-1),
.cycle 12 5 true (0),
.last 14 (5,false)
])
theorem kid05_part71_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part71) = true := by rfl

def kid05_part72 : Audit := .cycle 0 14 true (-1)
theorem kid05_part72_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part72) = true := by rfl

def kid05_part73 : Audit := .cycle 12 1 false (0)
theorem kid05_part73_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part73) = true := by rfl

def kid05_part74 : Audit := .cycle 11 1 false (-1)
theorem kid05_part74_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part74) = true := by rfl

def kid05_part75 : Audit := .cycle 11 1 false (-1)
theorem kid05_part75_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part75) = true := by rfl

def kid05_part76 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 29 1 false (-3),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.cycle 16 1 false (-2)
])
theorem kid05_part76_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part76) = true := by rfl

def kid05_part77 : Audit := .cycle 1 11 true (0)
theorem kid05_part77_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part77) = true := by rfl

def kid05_part78 : Audit := .split 12 (5,false) (byMove [
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
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (0),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 12 1 true (0)
])
theorem kid05_part78_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part78) = true := by rfl

def kid05_part79 : Audit := .split 11 (2,true) (byMove [
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
])
theorem kid05_part79_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part79) = true := by rfl

def kid05_part80 : Audit := .cycle 0 12 true (0)
theorem kid05_part80_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part80) = true := by rfl

def kid05_part81 : Audit := .cycle 12 1 false (2)
theorem kid05_part81_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part81) = true := by rfl

def kid05_part82 : Audit := .cycle 12 1 false (0)
theorem kid05_part82_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part82) = true := by rfl

def kid05_part83 : Audit := .cycle 14 1 false (-2)
theorem kid05_part83_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part83) = true := by rfl

def kid05_part84 : Audit := .split 12 (2,true) (byMove [
.last 28 (5,false),
.last 14 (5,false),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 1 13 true (-1),
.last 14 (5,false),
.cycle 23 1 false (-1),
.cycle 0 14 true (-1),
.last 20 (5,false),
.cycle 8 5 false (2),
.cycle 16 1 false (-2),
.last 14 (5,false),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 26 1 false (-2),
.last 29 (5,false),
.last 24 (5,false),
.cycle 0 14 true (-1),
.cycle 16 1 false (-2),
.last 16 (5,false)
])
theorem kid05_part84_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part84) = true := by rfl

def kid05_part85 : Audit := .cycle 1 13 true (-1)
theorem kid05_part85_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part85) = true := by rfl

def kid05_part86 : Audit := .cycle 11 1 false (-1)
theorem kid05_part86_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part86) = true := by rfl

def kid05_part87 : Audit := .cycle 11 1 false (-1)
theorem kid05_part87_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part87) = true := by rfl

def kid05_part88 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (-1),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 29 1 false (-3),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 1 13 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
])
theorem kid05_part88_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part88) = true := by rfl

def kid05_part89 : Audit := .cycle 1 11 true (0)
theorem kid05_part89_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part89) = true := by rfl

def kid05_part90 : Audit := .cycle 13 1 false (-1)
theorem kid05_part90_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part90) = true := by rfl

def kid05_part91 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.last 25 (5,false),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 12 12 true (0),
.last 12 (5,false),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 1 15 true (-1),
.cycle 1 13 true (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 9 3 true (0),
.last 12 (5,false)
])
theorem kid05_part91_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part91) = true := by rfl

def kid05_part92 : Audit := .cycle 0 12 true (0)
theorem kid05_part92_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part92) = true := by rfl

def kid05_part93 : Audit := .cycle 9 3 true (0)
theorem kid05_part93_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part93) = true := by rfl

def kid05_part94 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 24 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 13 16 true (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 12 8 true (0),
.cycle 13 1 true (1),
.cycle 17 1 false (-1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 10 4 true (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 9 5 true (0),
.cycle 13 1 true (1)
])
theorem kid05_part94_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part94) = true := by rfl

def kid05_part70 : Audit := .split 10 (4,true) (byMove [(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91),(kid05_part92),(kid05_part93),(kid05_part94)])

theorem kid05_part70_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part70) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91),(kid05_part92),(kid05_part93),(kid05_part94)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part75_checked

  · exact kid05_part81_checked

  · exact kid05_part87_checked

  · exact kid05_part93_checked

  · exact kid05_part76_checked

  · exact kid05_part82_checked

  · exact kid05_part88_checked

  · exact kid05_part94_checked

def kid05_part96 : Audit := .split 15 (2,true) (byMove [
.cycle 14 20 true (-2),
.cycle 10 7 false (0),
.cycle 19 1 false (-3),
.proven (BB6.Agent11Raw39Pumps.M210.table) (fun m hm => BB6.Agent11Raw39Pumps.M210.never m hm),
.last 16 (4,true),
.last 17 (4,true),
.last 21 (4,true),
.cycle 16 13 true (0),
.cycle 0 18 true (-3),
.cycle 3 13 false (3),
.last 21 (4,true),
.last 32 (4,true),
.last 19 (4,true),
.cycle 10 7 false (0),
.cycle 10 12 false (0),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[1099511627776, 131072, 35184372088832, 32768, 131072, 1, 281492425016320, 282592481905664, 281476201448000, 134217728, 536870912, 64, 16, 8388608, 1073741824, 35184372088832, 140737488355328, 68719476736, 268436480, 8388608, 68736254016, 134217728, 536870912, 1073741824, 282591936644096, 282592481905664, 281544920924736, 512, 2048, 16777216, 17179869184, 282591936644096, 512, 2097152, 8388608, 64, 17179869184, 17179869184, 134217728, 2097152, 8388608, 16777216, 268435456, 131072, 1073741824, 134217728, 536870912, 16777216, 281474976710656],[1099511627776, 32, 32768, 8388608, 281474976710656, 16, 281492425016320, 2048, 134217728, 281475521972224, 281474976710656, 1024, 16, 2199023255552, 35184372088832, 8388608, 281474976710656, 1099511627776, 268436480, 34359738368, 134217728, 8388608, 281474976710656, 17179869184, 282591936644096, 536870912, 512, 281475521972224, 281474976710656, 268435456, 17179869184, 2048, 2097152, 536872960, 281474976710656, 1024, 17179869184, 536870912, 2097152, 131072, 281474976710656, 268435456, 268435456, 536870912, 134217728, 131072, 281474976710656, 268435456, 281474976710656],499215714553280⟩,
.last 16 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 28 (4,true),
.cycle 14 18 true (-2),
.last 23 (4,true),
.last 18 (4,true),
.last 32 (4,true)
])
theorem kid05_part96_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part96) = true := by rfl

def kid05_part97 : Audit := .far true 5 ⟨0,[0, 1, 2, 3, 1, 1, 4, 4, 4, 4],[65536, 2048, 2097152, 512, 2048, 2, 65552, 1619003392, 2105344, 2097152, 8388608, 8192, 1342242816, 2048, 134217728, 512, 2048, 128, 1024, 1073741824, 1107304448, 134217728, 536870912, 33554432, 1342242816, 1619003392, 1241522176, 134217728, 536870912, 33554432, 1073741824],[65536, 32, 1073741824, 2048, 1073741824, 16, 65552, 131072, 1073741824, 1610614784, 1073741824, 65536, 1342242816, 2048, 1073741824, 2048, 1073741824, 1024, 1024, 536870912, 1073741824, 2048, 1073741824, 268435456, 1342242816, 536870912, 1073741824, 1619003392, 1073741824, 268435456, 1073741824],2011042944⟩
theorem kid05_part97_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part97) = true := by rfl

def kid05_part98 : Audit := .cycle 14 1 false (-2)
theorem kid05_part98_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part98) = true := by rfl

def kid05_part99 : Audit := .cycle 13 1 false (-3)
theorem kid05_part99_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part99) = true := by rfl

def kid05_part100 : Audit := .cycle 11 2 false (-1)
theorem kid05_part100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part100) = true := by rfl

def kid05_part101 : Audit := .cycle 12 1 false (-2)
theorem kid05_part101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part101) = true := by rfl

def kid05_part102 : Audit := .split 15 (2,true) (byMove [
.last 27 (4,true),
.cycle 1 20 false (3),
.cycle 19 1 false (-1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 1, 8192, 16384, 8, 128, 128, 1, 33554432, 67108864, 2097152, 128, 1073741824, 262144, 33554432, 67108864, 134217728, 2097152, 33554432, 16777216, 33554432, 67108864, 134217728, 1327497216, 1327497216, 16777216, 1073741824],[128, 128, 1327513600, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 16384, 16777216, 1073741824, 1073741824, 33554432, 1327497216, 1327497216, 16777216, 1073741824, 1327497216, 1073741824],2145333582⟩,
.last 16 (4,true),
.last 17 (4,true),
.last 29 (4,true),
.last 39 (4,true),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.last 31 (4,true),
.cycle 0 17 true (-2),
.last 19 (4,true),
.last 44 (4,true),
.cycle 1 25 false (3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 1, 8192, 16384, 8, 128, 128, 1, 33554432, 67108864, 2097152, 128, 1073741824, 262144, 33554432, 67108864, 134217728, 2097152, 33554432, 16777216, 33554432, 67108864, 134217728, 1325400064, 1325400064, 16777216, 1073741824],[128, 128, 1327497216, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 2097152, 16777216, 1073741824, 1073741824, 33554432, 1325400064, 1325400064, 16777216, 1073741824, 1325400064, 1073741824],2145333582⟩,
.last 16 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 26 (4,true),
.last 25 (4,true),
.last 31 (4,true),
.last 18 (4,true),
.last 30 (4,true)
])
theorem kid05_part102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part102) = true := by rfl

def kid05_part103 : Audit := .cycle 0 18 true (-2)
theorem kid05_part103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part103) = true := by rfl

def kid05_part104 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 16 1 false (0),
.cycle 0 20 true (-2),
.cycle 15 11 true (1),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.last 17 (4,true),
.cycle 18 1 false (4),
.cycle 10 6 false (0),
.cycle 0 32 true (-3),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 17 (4,true),
.last 26 (4,true),
.cycle 0 16 true (-2),
.cycle 1 24 true (-2),
.cycle 9 5 false (1),
.cycle 0 31 true (-2)
])
theorem kid05_part104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part104) = true := by rfl

def kid05_part105 : Audit := .cycle 0 20 true (-2)
theorem kid05_part105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part105) = true := by rfl

def kid05_part106 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 11 4 true (-2),
.cycle 0 20 true (-2),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (0),
.cycle 17 3 true (1),
.cycle 14 4 true (0),
.cycle 10 6 false (0),
.last 15 (2,true),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.cycle 13 16 true (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 1 24 true (-2),
.cycle 9 5 false (1),
.cycle 14 4 true (0)
])
theorem kid05_part106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part106) = true := by rfl

def kid05_part107 : Audit := .cycle 10 3 false (0)
theorem kid05_part107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part107) = true := by rfl

def kid05_part108 : Audit := .cycle 10 5 false (0)
theorem kid05_part108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part108) = true := by rfl

def kid05_part109 : Audit := .split 14 (2,true) (byMove [
.last 37 (4,true),
.cycle 12 4 false (-2),
.cycle 17 1 false (-3),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 31 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.cycle 0 18 true (-3),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 10, 32, 64, 16, 64],64⟩,
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 10 7 false (0),
.cycle 12 4 false (-2),
.cycle 10 10 false (0),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 29 (4,true),
.last 17 (4,true),
.last 33 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part109) = true := by rfl

def kid05_part110 : Audit := .split 17 (2,true) (byMove [
.last 29 (4,true),
.cycle 1 24 false (3),
.cycle 21 1 false (-1),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 17025, 1, 8192, 16384, 8, 17024, 17025, 17025, 524288, 1048576, 512, 128, 16777216, 17024, 524288, 1048576, 2097152, 20734593, 20734593, 20734593, 16777216],[128, 17024, 17024, 1, 16777216, 17024, 8192, 17024, 16512, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20734593, 20734593, 262144, 16777216, 20734593, 16777216],33370176⟩,
.last 18 (4,true),
.last 19 (4,true),
.last 31 (4,true),
.cycle 16 21 true (-2),
.cycle 3 17 false (3),
.cycle 3 15 false (3),
.last 21 (4,true),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 641, 2176, 1, 8192, 16384, 8, 640, 2176, 16385, 524288, 1048576, 512, 128, 16777216, 16385, 524288, 1048576, 2097152, 19668992, 25690112, 18087936, 16777216],[128, 640, 32, 1, 16777216, 16385, 8192, 640, 32, 1, 16777216, 16777216, 524288, 16777216, 2048, 64, 16777216, 16777216, 524288, 19398656, 8388608, 262144, 16777216, 18087936, 16777216],33370176⟩,
.last 21 (4,true),
.far true 2 ⟨0,[0, 1, 0, 1],[176, 2464, 512, 512, 2048, 256, 16, 32, 256, 512, 2048, 256, 4096],[176, 32, 128, 2336, 4096, 16, 16, 32, 128, 2336, 4096, 16, 4096],4096⟩,
.cycle 1 29 false (3),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 17025, 1, 8192, 16384, 8, 17024, 17025, 17025, 524288, 1048576, 512, 128, 16777216, 17025, 524288, 1048576, 2097152, 20734593, 20734593, 20734593, 16777216],[128, 17024, 17025, 1, 16777216, 17024, 8192, 17024, 17024, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20734593, 20734593, 262144, 16777216, 20734593, 16777216],33370176⟩,
.last 18 (4,true),
.last 19 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.last 27 (4,true),
.last 33 (4,true),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid05_part110_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part110) = true := by rfl

def kid05_part111 : Audit := .cycle 13 1 false (-3)
theorem kid05_part111_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part111) = true := by rfl

def kid05_part112 : Audit := .cycle 11 2 false (-1)
theorem kid05_part112_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part112) = true := by rfl

def kid05_part113 : Audit := .cycle 12 1 false (-2)
theorem kid05_part113_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part113) = true := by rfl

def kid05_part114 : Audit := .split 15 (2,true) (byMove [
.last 27 (4,true),
.last 18 (4,true),
.cycle 20 1 false (-2),
.last 30 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.last 29 (4,true),
.last 37 (4,true),
.last 26 (4,true),
.last 24 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.last 19 (4,true),
.last 18 (4,true),
.proven (BB6.Agent11Raw39Pumps.M221.table) (fun m hm => BB6.Agent11Raw39Pumps.M221.never m hm),
.last 30 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.last 26 (4,true),
.last 25 (4,true),
.last 31 (4,true),
.last 18 (4,true),
.last 28 (4,true)
])
theorem kid05_part114_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part114) = true := by rfl

def kid05_part115 : Audit := .cycle 10 4 false (0)
theorem kid05_part115_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part115) = true := by rfl

def kid05_part116 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 12 false (0),
.cycle 16 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 256, 8192, 16384, 8, 128, 128, 16384, 33554432, 67108864, 2097152, 128, 1073741824, 67108864, 33554432, 67108864, 134217728, 2097152, 1327497216, 67108864, 33554432, 67108864, 134217728, 1327497216, 1327497216, 67108864, 1073741824],[128, 2097160, 1327513600, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 134217728, 16384, 16777216, 1073741824, 1073741824, 33554432, 1327497216, 1327497216, 16777216, 1073741824, 1327497216, 1073741824],2145333614⟩,
.last 14 (4,true),
.cycle 10 4 false (0),
.cycle 7 8 false (3),
.cycle 15 11 true (1),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.last 17 (4,true),
.cycle 14 11 true (0),
.cycle 10 6 false (0),
.cycle 19 17 false (1),
.cycle 1 33 false (3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 128, 256, 8192, 16384, 8, 128, 128, 16384, 33554432, 67108864, 2097152, 128, 1073741824, 67108864, 33554432, 67108864, 134217728, 2097152, 1325400064, 67108864, 33554432, 67108864, 134217728, 1325400064, 1325400064, 67108864, 1073741824],[128, 2097160, 1327497216, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 134217728, 2097152, 16777216, 1073741824, 1073741824, 33554432, 1325400064, 1325400064, 16777216, 1073741824, 1325400064, 1073741824],2145333614⟩,
.last 14 (4,true),
.cycle 10 4 false (0),
.last 17 (4,true),
.last 26 (4,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.last 16 (4,true),
.last 26 (4,true)
])
theorem kid05_part116_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part116) = true := by rfl

def kid05_part117 : Audit := .cycle 7 8 false (3)
theorem kid05_part117_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part117) = true := by rfl

def kid05_part118 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (-2),
.cycle 9 7 false (1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.cycle 7 8 false (3),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 10 9 false (0),
.cycle 17 3 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 10 6 false (0),
.cycle 9 7 false (1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.cycle 13 16 true (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.cycle 9 8 false (1),
.cycle 13 6 true (-1)
])
theorem kid05_part118_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part118) = true := by rfl

def kid05_part119 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 10 12 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 28 1 true (-6),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 11 4 true (-2),
.cycle 19 1 true (1),
.cycle 10 7 false (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 12 3 false (-1),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 10 11 false (0),
.last 19 (2,true),
.cycle 9 6 false (1),
.cycle 19 1 true (1)
])
theorem kid05_part119_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part119) = true := by rfl

def kid05_part95 : Audit := .split 12 (5,false) (byMove [(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116),(kid05_part117),(kid05_part118),(kid05_part119)])

theorem kid05_part95_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part95) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116),(kid05_part117),(kid05_part118),(kid05_part119)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part101_checked

  · exact kid05_part107_checked

  · exact kid05_part113_checked

  · exact kid05_part119_checked

def kid05_part120 : Audit := .cycle 0 10 true (0)
theorem kid05_part120_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part120) = true := by rfl

def kid05_part121 : Audit := .cycle 1 9 true (1)
theorem kid05_part121_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part121) = true := by rfl

def kid05_part122 : Audit := .cycle 2 8 true (1)
theorem kid05_part122_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part122) = true := by rfl

def kid05_part123 : Audit := .cycle 1 12 true (1)
theorem kid05_part123_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part123) = true := by rfl

def kid05_part124 : Audit := .cycle 9 1 true (1)
theorem kid05_part124_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part124) = true := by rfl

def kid05_part126 : Audit := .cycle 1 11 true (1)
theorem kid05_part126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part126) = true := by rfl

def kid05_part127 : Audit := .cycle 11 12 false (1)
theorem kid05_part127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part127) = true := by rfl

def kid05_part128 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 18 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 25 1 false (1),
.cycle 13 6 false (1),
.cycle 15 1 false (-1),
.cycle 1 15 true (-1),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 18 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid05_part128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part128) = true := by rfl

def kid05_part129 : Audit := .cycle 0 12 true (0)
theorem kid05_part129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part129) = true := by rfl

def kid05_part130 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 11 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 9 4 true (1),
.cycle 13 6 false (1),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 12 3 false (0),
.cycle 13 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (1),
.cycle 10 2 true (1)
])
theorem kid05_part130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part130) = true := by rfl

def kid05_part131 : Audit := .split 12 (4,true) (byMove [
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
.cycle 15 3 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 3 false (1),
.cycle 1 15 true (0),
.cycle 9 4 true (0),
.cycle 13 3 false (1)
])
theorem kid05_part131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part131) = true := by rfl

def kid05_part132 : Audit := .cycle 0 11 true (0)
theorem kid05_part132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part132) = true := by rfl

def kid05_part133 : Audit := .cycle 1 10 true (1)
theorem kid05_part133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part133) = true := by rfl

def kid05_part134 : Audit := .cycle 0 23 true (0)
theorem kid05_part134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part134) = true := by rfl

def kid05_part135 : Audit := .cycle 3 8 true (1)
theorem kid05_part135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part135) = true := by rfl

def kid05_part136 : Audit := .cycle 9 2 true (1)
theorem kid05_part136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part136) = true := by rfl

def kid05_part137 : Audit := .cycle 10 1 true (2)
theorem kid05_part137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part137) = true := by rfl

def kid05_part138 : Audit := .split 14 (4,true) (byMove [
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
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 17 5 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 19 5 false (2),
.cycle 1 17 true (0),
.cycle 9 6 true (0),
.cycle 15 5 false (1)
])
theorem kid05_part138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part138) = true := by rfl

def kid05_part139 : Audit := .split 18 (2,true) (byMove [
.cycle 10 19 false (2),
.cycle 15 4 false (-1),
.cycle 21 1 false (-3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 2048, 128, 8192, 16384, 8, 128, 131072, 128, 33554432, 67108864, 2097152, 128, 536870912, 128, 33554432, 67108864, 2097152, 16512, 536870912, 1327775872, 33554432, 67108864, 134217728, 1327775872, 536870912, 1327775872, 1073741824],[128, 16384, 2113536, 1, 1073741824, 128, 8192, 16384, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 1327775872, 2113536, 262144, 1073741824, 1327775872, 33554432, 1327775872, 1327775872, 16777216, 1073741824, 1327775872, 1073741824],2144153664⟩,
.last 19 (4,true),
.cycle 12 7 false (0),
.cycle 7 13 false (3),
.far true 2 ⟨0,[0, 1, 0, 1],[16, 32, 512, 512, 32, 128, 16, 32, 128, 512, 4096, 128, 4096],[16, 32, 128, 32, 4096, 16, 16, 32, 128, 32, 4096, 16, 4096],5120⟩,
.cycle 0 32 true (-3),
.cycle 11 12 false (1),
.last 21 (4,true),
.last 27 (4,true),
.cycle 11 9 false (1),
.cycle 15 4 false (-1),
.cycle 11 19 false (1),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 2048, 128, 8192, 16384, 8, 128, 131072, 128, 33554432, 67108864, 2097152, 128, 536870912, 128, 33554432, 67108864, 2097152, 16512, 536870912, 1327775872, 33554432, 67108864, 134217728, 1327775872, 536870912, 1327775872, 1073741824],[128, 16384, 16512, 1, 1073741824, 128, 8192, 16384, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 1327775872, 16512, 262144, 1073741824, 1327775872, 33554432, 1327775872, 1327775872, 16777216, 1073741824, 1327775872, 1073741824],2144153664⟩,
.last 19 (4,true),
.cycle 12 7 false (0),
.last 22 (4,true),
.last 35 (4,true),
.cycle 10 17 false (2),
.cycle 4 15 false (3),
.last 21 (4,true),
.cycle 10 9 false (2)
])
theorem kid05_part139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part139) = true := by rfl

def kid05_part140 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 27 true (-2),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 1 12 true (1),
.cycle 0 19 true (-1),
.cycle 1 28 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 11 12 false (1),
.cycle 1 23 true (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 9 false (0),
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part140) = true := by rfl

def kid05_part141 : Audit := .cycle 1 12 true (1)
theorem kid05_part141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part141) = true := by rfl

def kid05_part142 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 77 36 false (0),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.cycle 15 4 false (-1),
.cycle 1 12 true (1),
.cycle 13 16 true (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.cycle 15 4 false (-1),
.cycle 1 12 true (1),
.cycle 1 14 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (1),
.cycle 10 4 true (1)
])
theorem kid05_part142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part142) = true := by rfl

def kid05_part143 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 3 false (3),
.cycle 13 1 false (1),
.cycle 15 3 false (-1),
.last 14 (2,true),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 3 false (1),
.cycle 9 7 true (0),
.cycle 13 3 false (1)
])
theorem kid05_part143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part143) = true := by rfl

def kid05_part144 : Audit := .cycle 0 11 true (0)
theorem kid05_part144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part144) = true := by rfl

def kid05_part145 : Audit := .cycle 1 10 true (1)
theorem kid05_part145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part145) = true := by rfl

def kid05_part146 : Audit := .cycle 2 9 true (1)
theorem kid05_part146_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part146) = true := by rfl

def kid05_part147 : Audit := .cycle 1 13 true (1)
theorem kid05_part147_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part147) = true := by rfl

def kid05_part148 : Audit := .cycle 9 2 true (1)
theorem kid05_part148_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part148) = true := by rfl

def kid05_part149 : Audit := .cycle 10 1 true (2)
theorem kid05_part149_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part149) = true := by rfl

def kid05_part125 : Audit := .split 10 (5,false) (byMove [(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)])

theorem kid05_part125_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part125) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part126_checked

  · exact kid05_part132_checked

  · exact kid05_part138_checked

  · exact kid05_part144_checked

  · exact kid05_part127_checked

  · exact kid05_part133_checked

  · exact kid05_part139_checked

  · exact kid05_part145_checked

  · exact kid05_part128_checked

  · exact kid05_part134_checked

  · exact kid05_part140_checked

  · exact kid05_part146_checked

  · exact kid05_part129_checked

  · exact kid05_part135_checked

  · exact kid05_part141_checked

  · exact kid05_part147_checked

  · exact kid05_part130_checked

  · exact kid05_part136_checked

  · exact kid05_part142_checked

  · exact kid05_part148_checked

  · exact kid05_part131_checked

  · exact kid05_part137_checked

  · exact kid05_part143_checked

  · exact kid05_part149_checked

def kid05_part5 : Audit := .split 9 (4,false) (byMove [(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part19),(kid05_part44),(kid05_part69),(kid05_part70),(kid05_part95),(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125)])

theorem kid05_part5_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (kid05_part5) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part19),(kid05_part44),(kid05_part69),(kid05_part70),(kid05_part95),(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125)] mv))) = true

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

  · exact kid05_part120_checked

  · exact kid05_part7_checked

  · exact kid05_part13_checked

  · exact kid05_part19_checked

  · exact kid05_part121_checked

  · exact kid05_part8_checked

  · exact kid05_part14_checked

  · exact kid05_part44_checked

  · exact kid05_part122_checked

  · exact kid05_part9_checked

  · exact kid05_part15_checked

  · exact kid05_part69_checked

  · exact kid05_part123_checked

  · exact kid05_part10_checked

  · exact kid05_part16_checked

  · exact kid05_part70_checked

  · exact kid05_part124_checked

  · exact kid05_part11_checked

  · exact kid05_part17_checked

  · exact kid05_part95_checked

  · exact kid05_part125_checked

def kid05_part151 : Audit := .cycle 1 10 true (0)
theorem kid05_part151_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part151) = true := by rfl

def kid05_part152 : Audit := .cycle 11 9 false (0)
theorem kid05_part152_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part152) = true := by rfl

def kid05_part153 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 false (3),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
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
.cycle 17 1 false (-3),
.last 14 (4,true),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 23 (4,true),
.cycle 1 11 false (3),
.cycle 21 1 false (-1),
.cycle 1 14 true (-1),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 21 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 22 1 false (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 22 1 false (2),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 14 1 false (2),
.cycle 17 1 false (-1),
.cycle 10 3 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 21 1 false (1),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 12 true (-1),
.cycle 15 1 false (-1),
.cycle 10 2 true (-1),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-3),
.last 14 (4,true),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 23 (4,true),
.cycle 16 1 false (-2),
.last 13 (4,true),
.cycle 0 13 true (-1),
.last 12 (4,true),
.cycle 16 1 false (-2)
]),
.cycle 13 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 20 1 false (0),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 15 1 false (-1),
.cycle 10 2 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 30 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 11 1 true (1),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 13 (4,true),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
]),
.cycle 9 2 true (0)
])
theorem kid05_part153_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part153) = true := by rfl

def kid05_part154 : Audit := .cycle 0 11 true (0)
theorem kid05_part154_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part154) = true := by rfl

def kid05_part156 : Audit := .cycle 0 11 false (3)
theorem kid05_part156_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part156) = true := by rfl

def kid05_part157 : Audit := .split 20 (4,false) (byMove [
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
.last 22 (2,true),
.cycle 0 23 false (3),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 19 14 false (2),
.cycle 1 20 false (3),
.cycle 12 9 false (1),
.cycle 1 23 false (3),
.cycle 20 1 true (-2),
.cycle 9 12 false (1)
])
theorem kid05_part157_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part157) = true := by rfl

def kid05_part158 : Audit := .cycle 12 1 false (0)
theorem kid05_part158_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part158) = true := by rfl

def kid05_part159 : Audit := .cycle 11 1 false (-1)
theorem kid05_part159_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part159) = true := by rfl

def kid05_part160 : Audit := .split 11 (4,false) (byMove [
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
.last 13 (2,true),
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
theorem kid05_part160_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part160) = true := by rfl

def kid05_part161 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (2,true),
.cycle 0 15 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 14 false (2),
.cycle 1 12 false (3),
.cycle 11 9 false (0),
.cycle 1 15 false (3),
.cycle 12 1 true (-2),
.cycle 9 4 false (1)
])
theorem kid05_part161_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part161) = true := by rfl

def kid05_part162 : Audit := .cycle 0 11 true (0)
theorem kid05_part162_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part162) = true := by rfl

def kid05_part163 : Audit := .split 20 (4,false) (byMove [
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
.last 22 (2,true),
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
theorem kid05_part163_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part163) = true := by rfl

def kid05_part164 : Audit := .cycle 12 1 false (2)
theorem kid05_part164_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part164) = true := by rfl

def kid05_part165 : Audit := .cycle 11 1 false (1)
theorem kid05_part165_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part165) = true := by rfl

def kid05_part166 : Audit := .split 11 (4,false) (byMove [
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
.last 13 (2,true),
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
theorem kid05_part166_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part166) = true := by rfl

def kid05_part167 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (2,true),
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
theorem kid05_part167_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part167) = true := by rfl

def kid05_part168 : Audit := .split 15 (4,false) (byMove [
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
.last 17 (2,true),
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
theorem kid05_part168_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part168) = true := by rfl

def kid05_part169 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 false (3),
.last 15 (4,false),
.cycle 15 1 false (-1),
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
.last 15 (4,false),
.cycle 1 16 true (-2),
.cycle 1 14 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 27 (4,false),
.last 25 (4,false),
.cycle 2 11 false (3),
.cycle 1 15 true (-1),
.last 13 (4,false),
.last 17 (4,false)
])
theorem kid05_part169_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part169) = true := by rfl

def kid05_part170 : Audit := .cycle 0 13 true (-1)
theorem kid05_part170_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part170) = true := by rfl

def kid05_part171 : Audit := .cycle 11 1 false (-1)
theorem kid05_part171_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part171) = true := by rfl

def kid05_part172 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 12 true (-1),
.cycle 13 10 true (-2),
.last 12 (2,true),
.cycle 0 13 true (-1),
.cycle 10 2 true (-1),
.cycle 13 2 true (-2),
.cycle 11 5 false (-1),
.last 13 (2,true),
.cycle 1 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 13 19 false (3),
.cycle 1 15 false (3),
.last 12 (2,true),
.cycle 0 13 true (-1),
.cycle 10 3 false (0),
.cycle 9 7 false (1)
])
theorem kid05_part172_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part172) = true := by rfl

def kid05_part173 : Audit := .split 12 (4,false) (byMove [
.cycle 14 17 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 18 false (3),
.last 14 (2,true),
.cycle 0 15 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 14 (2,true),
.cycle 0 22 false (3),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 35 (2,true),
.last 14 (2,true),
.cycle 0 15 true (-2),
.cycle 1 22 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 0, 16, 64],64⟩,
.cycle 9 4 false (1)
])
theorem kid05_part173_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part173) = true := by rfl

def kid05_part174 : Audit := .cycle 0 11 true (0)
theorem kid05_part174_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part174) = true := by rfl

def kid05_part175 : Audit := .cycle 1 10 true (0)
theorem kid05_part175_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part175) = true := by rfl

def kid05_part176 : Audit := .split 19 (4,false) (byMove [
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
.last 21 (2,true),
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
theorem kid05_part176_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part176) = true := by rfl

def kid05_part177 : Audit := .cycle 1 13 true (0)
theorem kid05_part177_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part177) = true := by rfl

def kid05_part178 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 10 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 11 10 true (1),
.cycle 23 1 false (1),
.cycle 20 1 false (0),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 10 3 true (0),
.cycle 13 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid05_part178_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part178) = true := by rfl

def kid05_part179 : Audit := .cycle 9 2 true (0)
theorem kid05_part179_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part179) = true := by rfl

def kid05_part155 : Audit := .split 10 (4,true) (byMove [(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173),(kid05_part174),(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179)])

theorem kid05_part155_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part155) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173),(kid05_part174),(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part156_checked

  · exact kid05_part162_checked

  · exact kid05_part168_checked

  · exact kid05_part174_checked

  · exact kid05_part157_checked

  · exact kid05_part163_checked

  · exact kid05_part169_checked

  · exact kid05_part175_checked

  · exact kid05_part158_checked

  · exact kid05_part164_checked

  · exact kid05_part170_checked

  · exact kid05_part176_checked

  · exact kid05_part159_checked

  · exact kid05_part165_checked

  · exact kid05_part171_checked

  · exact kid05_part177_checked

  · exact kid05_part160_checked

  · exact kid05_part166_checked

  · exact kid05_part172_checked

  · exact kid05_part178_checked

  · exact kid05_part161_checked

  · exact kid05_part167_checked

  · exact kid05_part173_checked

  · exact kid05_part179_checked

def kid05_part180 : Audit := .cycle 11 1 false (-1)
theorem kid05_part180_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part180) = true := by rfl

def kid05_part181 : Audit := .cycle 0 10 true (0)
theorem kid05_part181_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part181) = true := by rfl

def kid05_part182 : Audit := .cycle 1 9 true (1)
theorem kid05_part182_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part182) = true := by rfl

def kid05_part183 : Audit := .cycle 20 1 false (2)
theorem kid05_part183_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part183) = true := by rfl

def kid05_part184 : Audit := .cycle 17 1 false (1)
theorem kid05_part184_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part184) = true := by rfl

def kid05_part185 : Audit := .split 10 (4,false) (byMove [
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
.last 14 (2,true),
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
.cycle 14 5 false (0),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 15 5 false (0),
.cycle 16 1 false (0),
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
.cycle 15 5 false (0),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 16 7 false (1),
.cycle 9 4 true (1)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.cycle 16 1 false (0)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 16 3 false (0),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 10 3 true (1),
.cycle 9 4 true (1),
.cycle 16 7 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 16 3 false (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 9 4 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid05_part185_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part185) = true := by rfl

def kid05_part186 : Audit := .cycle 9 1 true (1)
theorem kid05_part186_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part186) = true := by rfl

def kid05_part187 : Audit := .cycle 11 4 false (1)
theorem kid05_part187_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part187) = true := by rfl

def kid05_part188 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 15, 64],80⟩,
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 128, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 1, 393, 128, 393, 128, 1, 1, 393, 4096],5136⟩,
.cycle 0 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 11 4 true (-2),
.cycle 11 7 false (-1),
.cycle 12 3 false (-1),
.last 22 (4,false),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 197 60 false (-5),
.cycle 0 18 true (-2),
.cycle 11 11 false (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 128, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 512, 393, 128, 393, 128, 1, 512, 393, 4096],5136⟩,
.last 15 (4,false),
.cycle 9 6 false (1)
]),
.cycle 11 4 false (-1),
.cycle 7 8 false (3),
.cycle 14 11 true (0),
.cycle 0 16 true (-2),
.cycle 11 9 false (0),
.split 14 (4,false) (byMove [
.cycle 197 60 false (-5),
.cycle 0 18 true (-2),
.cycle 11 11 false (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 360833, 295296, 65536, 128, 256, 32768, 128, 128, 98561, 128, 256, 8, 33024, 256, 65536, 262144],[128, 256, 16, 1, 262144, 256, 128, 33024, 65536, 4096, 262144, 33024, 128, 33152, 16, 1, 262144, 33152, 262144],278556⟩,
.last 16 (4,true),
.cycle 9 6 false (1),
.cycle 1 15 true (-2),
.cycle 16 12 true (-1),
.cycle 0 43 true (-3),
.cycle 0 16 true (-2),
.last 15 (4,true),
.cycle 16 4 true (-1),
.cycle 11 8 false (0),
.last 17 (4,true),
.cycle 1 17 true (-2),
.cycle 11 9 false (0),
.last 16 (4,true),
.cycle 9 6 false (1),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 292481, 64, 1040, 8192, 16384, 8, 29312, 4096, 9216, 8192, 16384, 512, 8320, 4096, 30337, 262144],[128, 20544, 16, 1, 262144, 20544, 8192, 29312, 16, 1, 262144, 29312, 8192, 29312, 1024, 64, 262144, 29312, 262144],262414⟩,
.cycle 7 8 false (3),
.cycle 15 11 true (1),
.cycle 27 12 false (1),
.last 15 (4,true),
.cycle 8 8 false (2)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 64, 32, 64],[2, 32, 32, 1, 64, 32, 64],80⟩,
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 1 33 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 15, 64],80⟩,
.split 14 (4,true) (byMove [
.cycle 16 4 true (-3),
.cycle 21 17 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 128, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 1, 393, 128, 393, 128, 1, 1, 393, 4096],5136⟩,
.cycle 10 5 false (0),
.last 16 (4,false),
.cycle 0 24 true (-2),
.last 16 (4,false),
.cycle 11 5 false (-1),
.cycle 11 7 false (-1),
.cycle 12 3 false (-1),
.last 22 (4,false),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 197 60 false (-5),
.cycle 11 6 false (-1),
.cycle 13 2 true (-2),
.cycle 7 10 false (3),
.last 16 (4,false),
.cycle 11 6 false (-1)
]),
.cycle 11 4 false (-1),
.cycle 16 46 false (3),
.cycle 171 52 false (-5),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.split 14 (4,false) (byMove [
.cycle 197 60 false (-5),
.cycle 11 6 false (0),
.cycle 13 2 true (-1),
.cycle 7 10 false (3),
.last 15 (4,true),
.cycle 11 6 false (0),
.cycle 26 10 false (0),
.cycle 23 12 true (-1),
.cycle 0 31 true (-2),
.cycle 0 16 true (-2),
.last 15 (4,true),
.last 26 (4,true),
.cycle 11 8 false (0),
.cycle 11 6 false (0),
.last 16 (4,true),
.cycle 5 10 false (3),
.last 15 (4,true),
.cycle 11 6 false (0),
.cycle 16 60 false (7),
.cycle 16 46 false (3),
.cycle 171 52 false (-5),
.cycle 57 12 false (-1),
.last 15 (4,true),
.cycle 17 8 false (-1)
]),
.cycle 11 6 false (0)
])
theorem kid05_part188_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part188) = true := by rfl

def kid05_part189 : Audit := .split 10 (2,true) (byMove [
.cycle 12 14 true (-1),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.last 26 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 18 (4,true),
.cycle 0 18 true (-2),
.last 14 (4,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 1 15 true (-1),
.proven (BB6.Agent11Raw39Pumps.M238.table) (fun m hm => BB6.Agent11Raw39Pumps.M238.never m hm),
.last 14 (4,true),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 18 (4,true),
.cycle 0 19 false (3),
.last 14 (4,true),
.cycle 0 14 true (-1),
.cycle 0 20 true (-2),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 0 20 true (-2),
.cycle 1 11 true (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (3),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 0 15 true (-1),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 0 18 true (-2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 1 15 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 0 15 true (-1),
.cycle 0 27 false (3),
.cycle 18 8 true (-3),
.cycle 1 13 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 24 (4,true),
.cycle 0 18 true (-2),
.cycle 0 22 true (-2),
.cycle 10 2 true (-1),
.cycle 1 13 true (-1),
.last 12 (4,true),
.cycle 0 22 true (-2),
.last 21 (4,true),
.last 14 (4,true),
.cycle 0 20 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 24 (4,true),
.cycle 0 19 false (3),
.last 20 (4,true),
.last 13 (4,true),
.cycle 1 13 true (-1),
.last 12 (4,true),
.last 20 (4,true)
]),
.cycle 0 20 true (-2),
.cycle 1 11 true (0),
.cycle 0 16 true (-2),
.cycle 2 10 true (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 0 16 true (-2),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 0 16 true (-2),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.last 26 (4,false),
.cycle 0 21 true (-1),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 0 18 true (-2),
.cycle 0 22 true (-2),
.cycle 10 2 true (0),
.cycle 1 13 true (0),
.last 13 (4,false),
.cycle 0 22 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 1 14 true (0),
.last 12 (4,false),
.cycle 9 3 true (0)
]),
.cycle 0 16 true (-2)
])
theorem kid05_part189_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part189) = true := by rfl

def kid05_part190 : Audit := .cycle 1 11 true (0)
theorem kid05_part190_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part190) = true := by rfl

def kid05_part192 : Audit := .split 13 (2,true) (byMove [
.cycle 12 14 true (-1),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 1 15 false (3),
.last 17 (4,false),
.cycle 0 14 true (-1),
.last 23 (4,false),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.last 14 (4,false),
.last 15 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.last 22 (4,false),
.cycle 1 15 true (-1),
.cycle 12 4 true (-1),
.last 17 (4,false),
.cycle 12 14 true (0),
.cycle 12 13 true (0),
.cycle 12 12 true (-1),
.cycle 1 16 true (-1),
.last 14 (4,false),
.cycle 12 5 true (0)
])
theorem kid05_part192_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part192) = true := by rfl

def kid05_part193 : Audit := .cycle 0 14 true (-1)
theorem kid05_part193_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part193) = true := by rfl

def kid05_part194 : Audit := .cycle 12 1 false (0)
theorem kid05_part194_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part194) = true := by rfl

def kid05_part195 : Audit := .cycle 11 1 false (-1)
theorem kid05_part195_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part195) = true := by rfl

def kid05_part196 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (-2),
.last 27 (2,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 17 false (3),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 12 1 false (0),
.cycle 14 1 true (0),
.cycle 12 3 false (0),
.cycle 11 5 false (-1),
.last 13 (2,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 33 (2,true),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 4 28 false (3),
.cycle 16 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid05_part196_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part196) = true := by rfl

def kid05_part197 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.last 29 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (2,true),
.cycle 11 3 false (-1),
.last 13 (2,true),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.cycle 11 5 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (2,true),
.cycle 11 4 false (-1),
.last 13 (2,true),
.cycle 7 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part197_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part197) = true := by rfl

def kid05_part198 : Audit := .cycle 1 11 true (0)
theorem kid05_part198_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part198) = true := by rfl

def kid05_part199 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 1 14 true (-1),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 11 true (-1),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.last 15 (2,true),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 9 17 false (3),
.cycle 12 4 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 11 true (-1),
.cycle 12 4 false (0)
])
theorem kid05_part199_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part199) = true := by rfl

def kid05_part200 : Audit := .split 11 (2,true) (byMove [
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
.last 16 (4,false),
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
theorem kid05_part200_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part200) = true := by rfl

def kid05_part201 : Audit := .cycle 0 12 true (0)
theorem kid05_part201_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part201) = true := by rfl

def kid05_part202 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 0 26 true (-1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 21 3 false (3),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.cycle 12 1 true (2),
.cycle 13 3 false (3),
.cycle 12 5 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 22 (2,true),
.cycle 1 15 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid05_part202_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part202) = true := by rfl

def kid05_part203 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 1 14 true (-1),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 3 true (-1),
.cycle 11 3 false (1),
.cycle 11 5 false (1),
.last 15 (2,true),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 8 17 false (3),
.cycle 11 4 false (1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 3 true (-1),
.cycle 11 4 false (1)
])
theorem kid05_part203_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part203) = true := by rfl

def kid05_part204 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 47 (2,true),
.cycle 14 3 false (-2),
.last 16 (2,true),
.last 19 (2,true),
.cycle 10 6 false (0),
.cycle 13 3 false (-1),
.cycle 11 5 false (0),
.last 17 (2,true),
.last 51 (2,true),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.last 64 (2,true),
.cycle 12 4 false (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 12 6 false (0),
.cycle 13 4 false (-1)
])
theorem kid05_part204_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part204) = true := by rfl

def kid05_part205 : Audit := .split 12 (2,true) (byMove [
.last 29 (4,false),
.last 15 (4,false),
.cycle 15 1 false (-1),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 1 13 true (-1),
.cycle 9 5 false (1),
.last 24 (4,false),
.cycle 0 14 true (-1),
.last 16 (4,false),
.cycle 8 5 false (2),
.last 17 (4,false),
.last 15 (4,false),
.last 20 (4,false),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 27 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.cycle 0 14 true (-1),
.last 17 (4,false),
.last 17 (4,false)
])
theorem kid05_part205_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part205) = true := by rfl

def kid05_part206 : Audit := .cycle 1 13 true (-1)
theorem kid05_part206_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part206) = true := by rfl

def kid05_part207 : Audit := .cycle 11 1 false (-1)
theorem kid05_part207_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part207) = true := by rfl

def kid05_part208 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 1 15 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 1 17 false (3),
.cycle 11 3 false (0),
.last 12 (2,true),
.cycle 1 13 true (-1),
.cycle 10 2 true (-1),
.cycle 11 3 false (0),
.cycle 11 5 false (-1),
.last 13 (2,true),
.cycle 1 21 false (3),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 10 19 false (1),
.cycle 11 4 false (0),
.last 12 (2,true),
.cycle 1 13 true (-1),
.cycle 10 3 false (0),
.cycle 11 4 false (0)
])
theorem kid05_part208_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part208) = true := by rfl

def kid05_part209 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.last 29 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 45 (2,true),
.cycle 11 3 false (-1),
.last 13 (2,true),
.cycle 0 20 true (-2),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.cycle 11 5 false (-1),
.last 14 (2,true),
.last 39 (2,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 35 (2,true),
.cycle 11 4 false (-1),
.last 13 (2,true),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part209_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part209) = true := by rfl

def kid05_part210 : Audit := .cycle 1 11 true (0)
theorem kid05_part210_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part210) = true := by rfl

def kid05_part211 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 41 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 15 false (3),
.cycle 13 3 false (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 1 15 false (3),
.cycle 12 3 false (0),
.cycle 11 5 false (1),
.last 16 (2,true),
.cycle 1 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 16 false (2),
.cycle 11 4 false (1),
.last 15 (2,true),
.cycle 7 20 false (3),
.cycle 12 16 false (2),
.cycle 12 4 false (0)
])
theorem kid05_part211_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part211) = true := by rfl

def kid05_part212 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 21 (4,false),
.last 14 (4,false),
.cycle 0 12 true (0),
.last 21 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.last 12 (4,false),
.last 13 (4,false),
.last 16 (4,false),
.last 14 (4,false),
.cycle 1 15 true (-1),
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
theorem kid05_part212_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part212) = true := by rfl

def kid05_part213 : Audit := .cycle 0 12 true (0)
theorem kid05_part213_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part213) = true := by rfl

def kid05_part214 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (0),
.last 45 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 9 15 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 12 1 true (2),
.cycle 8 7 true (0),
.cycle 16 5 false (0),
.last 18 (2,true),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 10 3 true (0),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 12 1 true (2),
.cycle 9 4 true (0)
])
theorem kid05_part214_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part214) = true := by rfl

def kid05_part215 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 41 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 1 15 false (3),
.cycle 13 3 false (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 9 7 false (1),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.last 16 (2,true),
.cycle 1 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 16 false (2),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 8 20 false (3),
.cycle 11 8 false (1),
.cycle 11 4 false (1)
])
theorem kid05_part215_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part215) = true := by rfl

def kid05_part191 : Audit := .split 10 (4,true) (byMove [(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212),(kid05_part213),(kid05_part214),(kid05_part215)])

theorem kid05_part191_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part191) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212),(kid05_part213),(kid05_part214),(kid05_part215)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part192_checked

  · exact kid05_part198_checked

  · exact kid05_part204_checked

  · exact kid05_part210_checked

  · exact kid05_part193_checked

  · exact kid05_part199_checked

  · exact kid05_part205_checked

  · exact kid05_part211_checked

  · exact kid05_part194_checked

  · exact kid05_part200_checked

  · exact kid05_part206_checked

  · exact kid05_part212_checked

  · exact kid05_part195_checked

  · exact kid05_part201_checked

  · exact kid05_part207_checked

  · exact kid05_part213_checked

  · exact kid05_part196_checked

  · exact kid05_part202_checked

  · exact kid05_part208_checked

  · exact kid05_part214_checked

  · exact kid05_part197_checked

  · exact kid05_part203_checked

  · exact kid05_part209_checked

  · exact kid05_part215_checked

def kid05_part216 : Audit := .cycle 11 1 false (-1)
theorem kid05_part216_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part216) = true := by rfl

def kid05_part217 : Audit := .cycle 0 10 true (0)
theorem kid05_part217_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part217) = true := by rfl

def kid05_part218 : Audit := .cycle 1 9 true (1)
theorem kid05_part218_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part218) = true := by rfl

def kid05_part219 : Audit := .cycle 2 8 true (1)
theorem kid05_part219_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part219) = true := by rfl

def kid05_part220 : Audit := .cycle 1 12 true (1)
theorem kid05_part220_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part220) = true := by rfl

def kid05_part221 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 13 3 false (0),
.split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 9 3 true (1),
.cycle 13 6 false (1),
.cycle 11 6 false (1),
.cycle 1 15 true (-1),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (1),
.cycle 9 3 true (1)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 9 3 true (1),
.cycle 13 6 false (1),
.last 17 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.cycle 11 6 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
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
.cycle 13 3 false (0),
.split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 28 true (-2),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 9 4 true (1),
.cycle 1 28 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 11 6 false (1),
.cycle 1 23 true (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 5 false (1)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 28 true (-2),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 9 4 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 17 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 11 6 false (1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 3 true (1),
.cycle 13 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (2),
.cycle 9 2 true (1)
])
theorem kid05_part221_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part221) = true := by rfl

def kid05_part222 : Audit := .cycle 9 1 true (1)
theorem kid05_part222_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part222) = true := by rfl

def kid05_part150 : Audit := .split 9 (5,false) (byMove [(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187),(kid05_part188),(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222)])

theorem kid05_part150_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (kid05_part150) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187),(kid05_part188),(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part151_checked

  · exact kid05_part181_checked

  · exact kid05_part187_checked

  · exact kid05_part217_checked

  · exact kid05_part152_checked

  · exact kid05_part182_checked

  · exact kid05_part188_checked

  · exact kid05_part218_checked

  · exact kid05_part153_checked

  · exact kid05_part183_checked

  · exact kid05_part189_checked

  · exact kid05_part219_checked

  · exact kid05_part154_checked

  · exact kid05_part184_checked

  · exact kid05_part190_checked

  · exact kid05_part220_checked

  · exact kid05_part155_checked

  · exact kid05_part185_checked

  · exact kid05_part191_checked

  · exact kid05_part221_checked

  · exact kid05_part180_checked

  · exact kid05_part186_checked

  · exact kid05_part216_checked

  · exact kid05_part222_checked

def kid05_part223 : Audit := .cycle 0 9 true (0)
theorem kid05_part223_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,0⟩)) (kid05_part223) = true := by rfl

def kid05_part224 : Audit := .cycle 1 8 true (1)
theorem kid05_part224_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,1⟩)) (kid05_part224) = true := by rfl

def kid05_part225 : Audit := .cycle 1 20 true (0)
theorem kid05_part225_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,2⟩)) (kid05_part225) = true := by rfl

def kid05_part226 : Audit := .cycle 16 1 false (2)
theorem kid05_part226_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,3⟩)) (kid05_part226) = true := by rfl

def kid05_part228 : Audit := .cycle 0 10 true (0)
theorem kid05_part228_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part228) = true := by rfl

def kid05_part229 : Audit := .cycle 1 9 true (1)
theorem kid05_part229_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part229) = true := by rfl

def kid05_part230 : Audit := .cycle 20 1 false (2)
theorem kid05_part230_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part230) = true := by rfl

def kid05_part231 : Audit := .cycle 17 1 false (1)
theorem kid05_part231_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part231) = true := by rfl

def kid05_part232 : Audit := .split 12 (4,true) (byMove [
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
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 28 1 false (0),
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
.last 15 (2,true),
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
.split 14 (2,true) (byMove [
.cycle 1 15 false (3),
.last 16 (5,false),
.cycle 17 1 false (-1),
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
.last 16 (5,false),
.cycle 1 18 true (-2),
.cycle 1 16 true (-1),
.cycle 12 3 false (0),
.cycle 12 4 true (-1),
.cycle 30 1 false (0),
.last 28 (5,false),
.cycle 2 13 false (3),
.cycle 1 17 true (-1),
.last 18 (5,false),
.last 15 (5,false)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 1 14 true (-1),
.cycle 24 1 false (2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 2 true (-1),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.last 15 (2,true),
.cycle 1 16 true (-2),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 16 true (-1),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 12 4 true (-1),
.cycle 10 5 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 1 15 true (0),
.cycle 11 2 true (0),
.split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 24 1 false (0),
.last 14 (2,true),
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
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 10 6 true (0),
.cycle 12 3 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 11 3 true (0),
.cycle 13 1 true (1)
])
])
theorem kid05_part232_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part232) = true := by rfl

def kid05_part233 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 2 false (1),
.cycle 14 1 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 9 2 true (2),
.cycle 10 1 true (2),
.cycle 17 5 false (1),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 16 4 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 5 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 18 6 false (1),
.cycle 10 3 true (1),
.cycle 19 7 false (-1),
.cycle 16 4 false (0),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 20 8 false (1),
.cycle 19 7 false (0)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 2 false (1),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 1 14 true (0),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.cycle 18 1 false (0),
.last 15 (2,true),
.cycle 1 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 1 14 true (0),
.cycle 17 1 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 16 3 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 4 true (2),
.cycle 10 1 true (2)
])
theorem kid05_part233_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part233) = true := by rfl

def kid05_part234 : Audit := .cycle 0 10 true (0)
theorem kid05_part234_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part234) = true := by rfl

def kid05_part235 : Audit := .cycle 1 9 true (1)
theorem kid05_part235_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part235) = true := by rfl

def kid05_part237 : Audit := .cycle 1 28 true (0)
theorem kid05_part237_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part237) = true := by rfl

def kid05_part238 : Audit := .cycle 1 25 true (0)
theorem kid05_part238_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part238) = true := by rfl

def kid05_part239 : Audit := .cycle 23 1 false (3)
theorem kid05_part239_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part239) = true := by rfl

def kid05_part240 : Audit := .cycle 22 1 false (2)
theorem kid05_part240_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part240) = true := by rfl

def kid05_part241 : Audit := .cycle 1 25 true (0)
theorem kid05_part241_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part241) = true := by rfl

def kid05_part242 : Audit := .split 22 (5,false) (byMove [
.cycle 1 27 true (0),
.cycle 55 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 0 29 true (0),
.cycle 39 1 false (9),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 31 1 false (7),
.last 25 (4,true),
.cycle 1 29 true (0),
.cycle 1 29 true (0),
.cycle 0 33 true (0),
.cycle 23 1 false (1),
.cycle 20 3 false (3),
.cycle 22 1 false (2),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 1 25 true (0),
.cycle 1 33 true (0),
.cycle 26 12 true (4),
.last 25 (4,true)
])
theorem kid05_part242_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part242) = true := by rfl

def kid05_part243 : Audit := .cycle 27 1 false (7)
theorem kid05_part243_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part243) = true := by rfl

def kid05_part244 : Audit := .split 23 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 44 1 false (10),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 false (7),
.cycle 26 28 true (4),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 36 1 false (10),
.cycle 28 1 false (8),
.cycle 0 30 true (0),
.cycle 24 40 true (2),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.last 58 (4,true),
.cycle 23 1 false (3),
.cycle 0 41 true (0),
.cycle 1 53 true (0),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.cycle 20 31 true (2),
.cycle 39 1 true (7)
])
theorem kid05_part244_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part244) = true := by rfl

def kid05_part245 : Audit := .cycle 25 1 false (7)
theorem kid05_part245_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part245) = true := by rfl

def kid05_part246 : Audit := .cycle 1 23 true (0)
theorem kid05_part246_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part246) = true := by rfl

def kid05_part247 : Audit := .split 22 (4,true) (byMove [
.cycle 0 39 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.last 23 (5,false),
.cycle 1 23 true (0),
.last 24 (5,false),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.cycle 26 1 false (8),
.cycle 30 1 false (8),
.cycle 24 15 true (4),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 30 1 false (8),
.last 23 (5,false),
.cycle 1 23 true (0),
.cycle 27 1 false (7),
.cycle 46 1 false (12),
.cycle 0 24 true (0),
.cycle 22 30 true (4),
.last 37 (5,false)
])
theorem kid05_part247_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part247) = true := by rfl

def kid05_part248 : Audit := .split 23 (4,true) (byMove [
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
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 26 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 33 1 false (9),
.cycle 1 26 true (0),
.last 35 (5,false),
.last 24 (5,false)
])
theorem kid05_part248_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part248) = true := by rfl

def kid05_part249 : Audit := .cycle 37 1 false (7)
theorem kid05_part249_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part249) = true := by rfl

def kid05_part250 : Audit := .split 25 (5,false) (byMove [
.cycle 0 68 true (0),
.cycle 14 14 true (0),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 49 1 false (7),
.cycle 22 4 true (1),
.cycle 33 1 false (7),
.cycle 26 1 false (2),
.cycle 20 6 true (1),
.last 28 (4,true),
.cycle 37 1 false (7),
.cycle 22 4 false (3),
.cycle 55 1 false (7),
.cycle 26 1 false (0),
.cycle 20 6 false (3),
.cycle 25 1 false (1),
.cycle 27 28 true (2),
.cycle 18 10 true (1),
.cycle 0 62 true (0),
.cycle 55 1 false (7),
.cycle 18 12 true (1),
.last 28 (4,true)
])
theorem kid05_part250_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part250) = true := by rfl

def kid05_part251 : Audit := .cycle 29 1 false (7)
theorem kid05_part251_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part251) = true := by rfl

def kid05_part252 : Audit := .cycle 22 1 false (2)
theorem kid05_part252_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part252) = true := by rfl

def kid05_part253 : Audit := .cycle 20 2 true (2)
theorem kid05_part253_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part253) = true := by rfl

def kid05_part254 : Audit := .split 22 (5,false) (byMove [
.last 27 (4,true),
.cycle 0 56 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.cycle 1 29 true (0),
.last 28 (4,true),
.cycle 21 2 true (2),
.cycle 29 1 false (7),
.last 23 (4,true),
.last 24 (4,true),
.cycle 18 6 true (1),
.last 26 (4,true),
.cycle 1 33 true (0),
.cycle 23 1 false (1),
.cycle 20 3 false (3),
.cycle 22 1 false (2),
.cycle 1 29 true (0),
.cycle 37 1 false (7),
.last 25 (4,true),
.cycle 5 18 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid05_part254_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part254) = true := by rfl

def kid05_part255 : Audit := .cycle 1 37 true (0)
theorem kid05_part255_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part255) = true := by rfl

def kid05_part256 : Audit := .cycle 1 25 true (0)
theorem kid05_part256_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part256) = true := by rfl

def kid05_part257 : Audit := .cycle 2 22 true (0)
theorem kid05_part257_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part257) = true := by rfl

def kid05_part258 : Audit := .cycle 1 23 true (0)
theorem kid05_part258_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part258) = true := by rfl

def kid05_part259 : Audit := .split 22 (4,true) (byMove [
.cycle 25 11 true (5),
.last 24 (5,false),
.cycle 24 11 true (4),
.cycle 29 1 false (7),
.cycle 26 1 false (4),
.cycle 23 11 true (3),
.cycle 1 23 true (0),
.last 24 (5,false),
.cycle 23 11 true (5),
.cycle 0 24 true (0),
.cycle 9 15 true (0),
.cycle 8 15 true (0),
.cycle 23 11 true (3),
.last 24 (5,false),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.cycle 20 4 true (2),
.last 25 (5,false),
.cycle 1 23 true (0),
.cycle 1 37 true (0),
.cycle 23 11 true (5),
.cycle 0 24 true (0),
.cycle 24 11 true (5),
.last 37 (5,false)
])
theorem kid05_part259_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part259) = true := by rfl

def kid05_part260 : Audit := .split 23 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 33 1 false (7),
.cycle 1 26 true (0),
.last 35 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.last 50 (5,false),
.cycle 24 13 true (3),
.last 33 (5,false),
.cycle 9 15 true (0),
.last 24 (5,false),
.cycle 26 13 true (3),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.last 26 (5,false),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.last 48 (5,false),
.cycle 1 26 true (0),
.last 35 (5,false),
.last 24 (5,false)
])
theorem kid05_part260_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part260) = true := by rfl

def kid05_part236 : Audit := .split 21 (2,true) (byMove [(kid05_part237),(kid05_part238),(kid05_part239),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part250),(kid05_part251),(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260)])

theorem kid05_part236_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part236) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) 21 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part237),(kid05_part238),(kid05_part239),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part250),(kid05_part251),(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part237_checked

  · exact kid05_part243_checked

  · exact kid05_part249_checked

  · exact kid05_part255_checked

  · exact kid05_part238_checked

  · exact kid05_part244_checked

  · exact kid05_part250_checked

  · exact kid05_part256_checked

  · exact kid05_part239_checked

  · exact kid05_part245_checked

  · exact kid05_part251_checked

  · exact kid05_part257_checked

  · exact kid05_part240_checked

  · exact kid05_part246_checked

  · exact kid05_part252_checked

  · exact kid05_part258_checked

  · exact kid05_part241_checked

  · exact kid05_part247_checked

  · exact kid05_part253_checked

  · exact kid05_part259_checked

  · exact kid05_part242_checked

  · exact kid05_part248_checked

  · exact kid05_part254_checked

  · exact kid05_part260_checked

def kid05_part261 : Audit := .cycle 1 20 true (0)
theorem kid05_part261_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part261) = true := by rfl

def kid05_part262 : Audit := .cycle 9 1 true (3)
theorem kid05_part262_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part262) = true := by rfl

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
.cycle 29 1 false (5),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 28 1 false (6),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 33 1 false (7),
.cycle 1 25 true (0),
.cycle 35 1 false (7),
.last 24 (2,true)
]),
.cycle 22 1 false (4),
.cycle 9 2 true (3),
.cycle 16 1 false (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 24 (4,true) (byMove [
.last 27 (2,true),
.cycle 1 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.last 27 (2,true),
.cycle 1 28 true (0),
.cycle 31 1 false (9),
.cycle 0 29 true (0),
.last 25 (2,true),
.cycle 1 26 true (0),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.cycle 37 1 false (9),
.last 26 (2,true),
.cycle 33 1 false (9),
.cycle 25 1 false (3),
.cycle 36 1 false (10),
.last 26 (2,true),
.cycle 1 43 true (0),
.cycle 32 1 false (10),
.last 25 (2,true),
.cycle 1 26 true (0),
.cycle 26 14 true (6),
.cycle 59 16 true (11)
]),
.split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 1 23 true (0),
.cycle 25 1 false (5),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 26 1 false (8),
.cycle 26 1 false (8),
.cycle 30 1 false (8),
.last 24 (2,true),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 30 1 false (8),
.cycle 1 25 true (0),
.cycle 1 23 true (0),
.cycle 27 1 false (7),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 30 true (4),
.cycle 46 1 false (12)
]),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 20 4 false (2),
.cycle 30 1 false (4),
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
.cycle 24 4 false (6),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 8 9 true (2)
]),
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
.cycle 26 1 false (4),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 30 1 false (6),
.cycle 1 23 true (0),
.cycle 30 1 false (6),
.cycle 1 23 true (0)
]),
.cycle 8 4 true (2),
.split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 0 60 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 22 1 false (6),
.cycle 17 1 false (1),
.last 16 (2,true),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 20 1 false (6),
.cycle 28 1 false (6),
.last 17 (2,true),
.cycle 24 1 false (6),
.cycle 16 1 false (0),
.cycle 28 1 false (6),
.cycle 16 1 false (0),
.cycle 0 35 true (0),
.cycle 1 20 true (0),
.last 16 (2,true),
.cycle 5 11 true (0),
.cycle 17 6 true (3),
.cycle 25 3 true (5)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part263_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part263) = true := by rfl

def kid05_part264 : Audit := .cycle 7 4 true (2)
theorem kid05_part264_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part264) = true := by rfl

def kid05_part266 : Audit := .cycle 1 12 true (1)
theorem kid05_part266_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part266) = true := by rfl

def kid05_part267 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 14 13 false (0),
.cycle 29 1 false (-1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 19 5 false (1),
.cycle 13 1 true (1),
.cycle 15 8 false (1),
.cycle 14 4 false (0),
.cycle 0 18 true (-1),
.cycle 1 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 20 3 false (0),
.cycle 13 1 true (1)
])
theorem kid05_part267_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part267) = true := by rfl

def kid05_part268 : Audit := .cycle 25 1 false (1)
theorem kid05_part268_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part268) = true := by rfl

def kid05_part269 : Audit := .cycle 0 13 true (0)
theorem kid05_part269_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part269) = true := by rfl

def kid05_part270 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.last 13 (5,false),
.cycle 21 7 false (1),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid05_part270_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part270) = true := by rfl

def kid05_part271 : Audit := .cycle 8 4 true (2)
theorem kid05_part271_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part271) = true := by rfl

def kid05_part272 : Audit := .cycle 0 12 true (0)
theorem kid05_part272_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part272) = true := by rfl

def kid05_part273 : Audit := .cycle 1 11 true (1)
theorem kid05_part273_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part273) = true := by rfl

def kid05_part274 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 4096, 128, 256, 8, 128, 4100, 4096, 4096],[128, 4096, 4, 1, 4096, 16, 128, 4, 4, 1, 4096, 16, 4096],7200⟩
theorem kid05_part274_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part274) = true := by rfl

def kid05_part275 : Audit := .cycle 3 9 true (1)
theorem kid05_part275_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part275) = true := by rfl

def kid05_part276 : Audit := .cycle 9 3 true (2)
theorem kid05_part276_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part276) = true := by rfl

def kid05_part277 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (4,true),
.cycle 8 15 true (2),
.cycle 9 4 true (2),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (4,true),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 23 (4,true),
.cycle 12 1 true (4)
])
theorem kid05_part277_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part277) = true := by rfl

def kid05_part278 : Audit := .cycle 6 6 true (2)
theorem kid05_part278_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part278) = true := by rfl

def kid05_part279 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.cycle 20 1 false (-2),
.cycle 25 1 false (-1),
.last 14 (4,true),
.cycle 19 1 false (-1),
.cycle 7 8 true (1),
.cycle 10 4 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 19 5 false (1),
.cycle 8 7 true (1),
.cycle 15 8 false (1),
.cycle 14 4 false (0),
.cycle 15 10 true (-3),
.cycle 25 1 false (-1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 20 13 false (2),
.cycle 19 9 false (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 20 3 false (0),
.last 38 (4,true)
])
theorem kid05_part279_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part279) = true := by rfl

def kid05_part280 : Audit := .cycle 1 15 true (1)
theorem kid05_part280_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part280) = true := by rfl

def kid05_part281 : Audit := .cycle 1 13 true (1)
theorem kid05_part281_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part281) = true := by rfl

def kid05_part282 : Audit := .split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 15 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.last 14 (5,false),
.last 21 (5,false),
.cycle 0 14 true (0),
.cycle 9 5 true (2),
.cycle 8 5 true (2),
.cycle 21 7 false (1),
.last 17 (5,false),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 12 9 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part282_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part282) = true := by rfl

def kid05_part283 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 21 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 30 (5,false),
.cycle 1 28 true (0),
.cycle 9 5 true (2),
.last 14 (5,false),
.cycle 7 8 true (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 21 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,false),
.last 14 (5,false)
])
theorem kid05_part283_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part283) = true := by rfl

def kid05_part284 : Audit := .cycle 0 12 true (0)
theorem kid05_part284_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part284) = true := by rfl

def kid05_part285 : Audit := .cycle 1 11 true (1)
theorem kid05_part285_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part285) = true := by rfl

def kid05_part286 : Audit := .cycle 2 10 true (1)
theorem kid05_part286_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part286) = true := by rfl

def kid05_part287 : Audit := .cycle 1 14 true (1)
theorem kid05_part287_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part287) = true := by rfl

def kid05_part288 : Audit := .split 18 (4,true) (byMove [
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 11 8 true (2),
.cycle 0 20 true (0),
.last 23 (5,false),
.cycle 8 11 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 13 12 true (2),
.cycle 3 16 true (1),
.cycle 9 10 true (2),
.last 19 (5,false),
.cycle 6 13 true (2),
.cycle 13 6 true (2),
.cycle 17 2 true (3),
.cycle 1 20 true (1),
.last 23 (5,false),
.last 21 (5,false),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 12 7 true (2),
.last 19 (5,false)
])
theorem kid05_part288_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part288) = true := by rfl

def kid05_part289 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
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
.cycle 8 10 true (2),
.cycle 8 6 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 11 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part289_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part289) = true := by rfl

def kid05_part265 : Audit := .split 11 (2,true) (byMove [(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273),(kid05_part274),(kid05_part275),(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288),(kid05_part289)])

theorem kid05_part265_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part265) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273),(kid05_part274),(kid05_part275),(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288),(kid05_part289)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part271_checked

  · exact kid05_part277_checked

  · exact kid05_part283_checked

  · exact kid05_part289_checked

def kid05_part290 : Audit := .cycle 0 12 true (0)
theorem kid05_part290_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part290) = true := by rfl

def kid05_part291 : Audit := .cycle 17 1 false (1)
theorem kid05_part291_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part291) = true := by rfl

def kid05_part293 : Audit := .split 15 (2,true) (byMove [
.cycle 14 22 true (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 7 11 false (3),
.cycle 1 21 true (-1),
.cycle 10 7 false (2),
.cycle 14 10 true (-1),
.last 17 (5,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 4, 1, 256, 16, 128, 4, 4, 1, 256, 16, 4096],6176⟩,
.cycle 1 17 true (-1),
.cycle 14 27 true (0),
.cycle 0 18 true (-1),
.cycle 10 9 false (2),
.cycle 18 1 false (0),
.cycle 23 1 false (1),
.cycle 5 11 false (3),
.cycle 14 4 true (-1),
.cycle 14 28 true (0),
.cycle 14 25 true (0),
.cycle 14 8 true (-1),
.cycle 14 16 true (0),
.cycle 1 17 true (-1),
.cycle 16 5 true (1),
.cycle 14 18 true (0)
])
theorem kid05_part293_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part293) = true := by rfl

def kid05_part294 : Audit := .cycle 9 11 false (3)
theorem kid05_part294_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part294) = true := by rfl

def kid05_part295 : Audit := .cycle 14 1 false (0)
theorem kid05_part295_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part295) = true := by rfl

def kid05_part296 : Audit := .cycle 13 1 false (-1)
theorem kid05_part296_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part296) = true := by rfl

def kid05_part297 : Audit := .cycle 13 1 false (-1)
theorem kid05_part297_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part297) = true := by rfl

def kid05_part298 : Audit := .split 13 (5,false) (byMove [
.cycle 27 1 false (-1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 15 (2,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 20 1 false (4),
.cycle 17 1 false (-1),
.last 15 (2,true),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.last 15 (2,true),
.cycle 9 11 false (3),
.cycle 19 1 false (1),
.cycle 11 3 false (1),
.cycle 28 1 false (0)
])
theorem kid05_part298_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part298) = true := by rfl

def kid05_part299 : Audit := .cycle 16 1 false (2)
theorem kid05_part299_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part299) = true := by rfl

def kid05_part300 : Audit := .split 14 (5,false) (byMove [
.cycle 1 19 true (-1),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 18 1 false (2),
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 26 1 false (6),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 20 1 false (2),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 10 8 true (0),
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 20 1 false (2),
.cycle 11 4 true (0),
.cycle 36 7 true (4)
])
theorem kid05_part300_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part300) = true := by rfl

def kid05_part301 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (0),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (3),
.last 15 (5,false),
.cycle 17 1 false (5),
.cycle 1 15 true (0),
.cycle 16 1 false (4),
.cycle 17 1 false (5),
.cycle 17 1 false (1),
.last 17 (5,false),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.last 14 (5,false),
.cycle 1 21 true (0),
.cycle 16 1 false (2),
.cycle 2 14 true (0),
.cycle 1 15 true (0),
.cycle 14 3 true (2),
.cycle 25 1 false (3)
])
theorem kid05_part301_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part301) = true := by rfl

def kid05_part302 : Audit := .cycle 17 1 false (3)
theorem kid05_part302_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part302) = true := by rfl

def kid05_part303 : Audit := .cycle 16 1 false (4)
theorem kid05_part303_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part303) = true := by rfl

def kid05_part304 : Audit := .cycle 16 1 false (4)
theorem kid05_part304_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part304) = true := by rfl

def kid05_part305 : Audit := .cycle 16 1 false (0)
theorem kid05_part305_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part305) = true := by rfl

def kid05_part306 : Audit := .split 14 (2,true) (byMove [
.proven (BB6.Agent11Raw39Pumps.M241.table) (fun m hm => BB6.Agent11Raw39Pumps.M241.never m hm),
.last 16 (5,false),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 12 3 false (0),
.cycle 16 1 false (0),
.cycle 6 9 false (3),
.last 16 (5,false),
.cycle 29 1 false (1),
.cycle 9 11 false (3),
.cycle 59 1 false (-1),
.cycle 8 11 true (-1),
.cycle 18 1 false (0),
.last 16 (5,false),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 12 3 false (0),
.cycle 12 4 true (-1),
.last 22 (5,false),
.cycle 10 7 false (2),
.far true 10 ⟨0,[0, 1, 2, 3, 4, 5, 6, 7, 4, 4, 4, 4, 6, 4, 8, 1, 6, 9, 5, 4],[128, 70368744177664, 2097152, 512, 1024, 1152921504606846976, 4194304, 128, 4194432, 2097152, 4194304, 1152921504606846976, 131072, 8796093153280, 35184372088832, 8589934592, 17179869184, 1152921504606846976, 70368744177664, 131072, 70369012613248, 35184372088832, 70368744177664, 1152921504606846976, 1162010068565755008, 1162010068565755008, 1162010068699972736, 134217728, 268435456, 1152921504606846976, 1162010068565755008, 9077568032473216, 134218752, 134217728, 268435456, 1152921504606846976, 1162010068565755008, 1162010068565755008, 134218240, 134217728, 268435456, 1152921504606846976, 268436480, 70368744177664, 1024, 512, 1024, 1152921504606846976, 128, 524288, 2097152, 144115188075855872, 288230376151711744, 1152921504606846976, 268436480, 2199023255552, 70369012613120, 134217728, 268435456, 1152921504606846976, 1152921504606846976],[128, 32, 70368744177664, 128, 128, 4194304, 4194304, 131072, 128, 272629888, 524288, 128, 131072, 536870912, 8796093153280, 70368744177664, 2147483648, 70368744177664, 70368744177664, 2199023255552, 131072, 70368744177664, 8796093022208, 131072, 1162010068565755008, 536870912, 1162010068565755008, 1162010068565755008, 33554432, 1162010068565755008, 1162010068565755008, 536870912, 9077568032473216, 1152921504879476736, 33554432, 9077568300908672, 1162010068565755008, 2199023255552, 1162010068565755008, 1162010068565755008, 33554432, 268436480, 268436480, 9007199254740992, 70368744177664, 1024, 128, 70368744177664, 128, 2199023255552, 524288, 272629760, 36028797018963968, 4194304, 268436480, 34359738368, 2199023255552, 128, 33554432, 2199023255552, 1152921504606846976],1775124384051771424⟩,
.last 24 (5,false),
.cycle 18 1 false (0),
.cycle 49 1 false (-1)
])
theorem kid05_part306_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part306) = true := by rfl

def kid05_part307 : Audit := .cycle 18 1 false (2)
theorem kid05_part307_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part307) = true := by rfl

def kid05_part308 : Audit := .cycle 13 1 false (-1)
theorem kid05_part308_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part308) = true := by rfl

def kid05_part309 : Audit := .cycle 13 1 false (-1)
theorem kid05_part309_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part309) = true := by rfl

def kid05_part310 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 9 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 17 1 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 18 1 false (2),
.cycle 12 2 true (-1),
.cycle 24 1 false (4),
.cycle 17 1 false (-1),
.last 15 (2,true),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 10 7 false (2),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 12 4 true (-1),
.cycle 14 13 true (0)
])
theorem kid05_part310_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part310) = true := by rfl

def kid05_part311 : Audit := .cycle 10 6 true (0)
theorem kid05_part311_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part311) = true := by rfl

def kid05_part312 : Audit := .cycle 15 1 false (1)
theorem kid05_part312_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part312) = true := by rfl

def kid05_part313 : Audit := .split 13 (2,true) (byMove [
.cycle 1 20 true (0),
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 18 1 false (2),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 6 8 true (0),
.last 15 (5,false),
.cycle 26 1 false (2),
.cycle 1 15 true (0),
.cycle 18 16 true (2),
.cycle 8 25 true (0),
.cycle 17 1 false (1),
.last 15 (5,false),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.cycle 29 1 false (5),
.cycle 1 21 true (0),
.cycle 10 6 true (0),
.cycle 2 14 true (0),
.cycle 1 15 true (0),
.cycle 14 3 true (2),
.last 32 (5,false)
])
theorem kid05_part313_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part313) = true := by rfl

def kid05_part314 : Audit := .cycle 5 8 true (0)
theorem kid05_part314_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part314) = true := by rfl

def kid05_part315 : Audit := .cycle 14 3 true (2)
theorem kid05_part315_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part315) = true := by rfl

def kid05_part316 : Audit := .split 21 (5,false) (byMove [
.cycle 1 22 true (0),
.cycle 36 1 false (0),
.last 22 (2,true),
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
.last 29 (2,true),
.last 22 (2,true),
.cycle 1 23 true (0),
.cycle 14 8 true (2),
.cycle 19 3 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 24 true (0),
.cycle 14 9 true (2),
.cycle 21 1 true (5)
])
theorem kid05_part316_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part316) = true := by rfl

def kid05_part292 : Audit := .split 12 (4,true) (byMove [(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316)])

theorem kid05_part292_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part292) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316)] mv))) = true

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

def kid05_part318 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 8, 4, 1, 4096, 16, 128, 4, 4, 1, 4096, 16, 4096],5120⟩,
.cycle 3 11 true (1),
.cycle 12 5 true (2),
.cycle 0 15 true (0),
.cycle 12 8 true (1),
.cycle 19 7 false (2),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 1 15 true (1)
])
theorem kid05_part318_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part318) = true := by rfl

def kid05_part319 : Audit := .cycle 0 14 true (0)
theorem kid05_part319_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part319) = true := by rfl

def kid05_part320 : Audit := .cycle 21 1 false (1)
theorem kid05_part320_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part320) = true := by rfl

def kid05_part321 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 395, 395, 395, 128, 256, 8, 128, 4096, 128, 4096],[128, 395, 2, 1, 4096, 16, 128, 395, 2, 1, 4096, 16, 4096],5120⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 5, 392, 128, 256, 8, 128, 4096, 128, 4096],[128, 397, 4, 1, 4096, 16, 128, 5, 4, 1, 4096, 16, 4096],5120⟩,
.cycle 3 13 true (0),
.cycle 7 13 true (0),
.cycle 1 19 true (0),
.cycle 27 1 false (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 18 (4,true),
.cycle 0 18 true (0)
])
theorem kid05_part321_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part321) = true := by rfl

def kid05_part322 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 22 2 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 17 2 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.cycle 17 2 false (1),
.last 15 (2,true),
.cycle 19 2 false (3),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 13 6 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 19 2 false (3),
.cycle 17 3 true (3),
.cycle 13 2 true (1)
])
theorem kid05_part322_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part322) = true := by rfl

def kid05_part323 : Audit := .cycle 14 1 false (0)
theorem kid05_part323_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part323) = true := by rfl

def kid05_part324 : Audit := .cycle 1 11 true (1)
theorem kid05_part324_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part324) = true := by rfl

def kid05_part325 : Audit := .cycle 1 12 true (1)
theorem kid05_part325_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part325) = true := by rfl

def kid05_part326 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 17 (4,true),
.cycle 1 28 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 1 24 true (0),
.cycle 9 3 true (2),
.last 28 (4,true),
.cycle 7 6 true (2),
.cycle 0 18 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 17 (4,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 8 16 true (2)
])
theorem kid05_part326_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part326) = true := by rfl

def kid05_part327 : Audit := .cycle 0 12 true (0)
theorem kid05_part327_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part327) = true := by rfl

def kid05_part328 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 17 3 false (1),
.cycle 9 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 9 3 true (2),
.cycle 9 4 true (2),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 17 3 false (1),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 9 4 true (2)
])
theorem kid05_part328_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part328) = true := by rfl

def kid05_part329 : Audit := .cycle 8 3 true (2)
theorem kid05_part329_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part329) = true := by rfl

def kid05_part330 : Audit := .cycle 17 5 false (1)
theorem kid05_part330_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part330) = true := by rfl

def kid05_part331 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 16 4 false (0),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.cycle 17 5 false (-1),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 258, 256, 2, 128, 256, 8, 128, 4096, 2, 4096],[128, 256, 2, 1, 4096, 16, 128, 256, 2, 1, 4096, 16, 4096],5120⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 132, 132, 4, 128, 256, 8, 128, 4096, 133, 4096],[128, 392, 4, 1, 4096, 16, 128, 132, 4, 1, 4096, 16, 4096],5120⟩,
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 19 7 false (-1),
.cycle 16 4 false (0),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 23 14 false (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 32 (4,true)
])
theorem kid05_part331_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part331) = true := by rfl

def kid05_part332 : Audit := .cycle 1 13 true (1)
theorem kid05_part332_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part332) = true := by rfl

def kid05_part333 : Audit := .cycle 18 1 false (0)
theorem kid05_part333_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part333) = true := by rfl

def kid05_part334 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 17 2 false (3),
.cycle 15 2 false (1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 16 2 false (4),
.cycle 16 2 false (4),
.cycle 17 2 false (1),
.last 15 (2,true),
.cycle 19 2 false (3),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 13 6 true (1),
.cycle 16 2 false (2),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 15 3 true (3),
.cycle 13 8 true (1)
])
theorem kid05_part334_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part334) = true := by rfl

def kid05_part335 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 18 1 false (2),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.cycle 18 1 false (0),
.last 15 (2,true),
.cycle 20 1 false (2),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 1 21 true (0),
.cycle 17 1 false (1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 15 3 true (3),
.cycle 14 3 true (2)
])
theorem kid05_part335_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part335) = true := by rfl

def kid05_part336 : Audit := .cycle 1 11 true (1)
theorem kid05_part336_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part336) = true := by rfl

def kid05_part337 : Audit := .cycle 7 4 true (2)
theorem kid05_part337_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part337) = true := by rfl

def kid05_part338 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 2 12 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 256, 128, 256, 8, 128, 4096, 256, 4096],[128, 8, 4, 1, 4096, 16, 128, 4, 4, 1, 4096, 16, 4096],5120⟩,
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.cycle 2 11 true (1)
])
theorem kid05_part338_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part338) = true := by rfl

def kid05_part339 : Audit := .cycle 0 12 true (0)
theorem kid05_part339_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part339) = true := by rfl

def kid05_part340 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 1 16 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 4 false (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 9 3 true (2),
.cycle 11 4 true (3),
.cycle 6 6 true (2),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 4 false (1),
.cycle 10 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 11 4 true (3)
])
theorem kid05_part340_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part340) = true := by rfl

def kid05_part341 : Audit := .cycle 8 3 true (2)
theorem kid05_part341_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part341) = true := by rfl

def kid05_part317 : Audit := .split 10 (5,false) (byMove [(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336),(kid05_part337),(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341)])

theorem kid05_part317_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part317) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336),(kid05_part337),(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341)] mv))) = true

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
theorem kid05_part342_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part342) = true := by rfl

def kid05_part343 : Audit := .cycle 1 9 true (1)
theorem kid05_part343_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part343) = true := by rfl

def kid05_part344 : Audit := .cycle 2 8 true (1)
theorem kid05_part344_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part344) = true := by rfl

def kid05_part345 : Audit := .cycle 1 12 true (1)
theorem kid05_part345_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part345) = true := by rfl

def kid05_part346 : Audit := .cycle 9 1 true (3)
theorem kid05_part346_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part346) = true := by rfl

def kid05_part347 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 1 12 true (1),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 36 1 false (4),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 9 3 true (3),
.last 24 (4,true),
.cycle 7 6 true (2),
.cycle 22 1 false (-2),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 8 5 true (2),
.cycle 29 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
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
.last 25 (2,true),
.cycle 22 12 true (2),
.cycle 9 3 true (3),
.cycle 9 4 true (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 31 1 false (3),
.cycle 8 5 true (2),
.cycle 17 4 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
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
.split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 19 4 false (1),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.last 15 (4,true),
.cycle 19 7 false (1),
.cycle 7 9 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 327680, 2048, 32768, 128, 256, 32768, 128, 2048, 65536, 128, 256, 8, 2048, 2048, 32768, 262144],[128, 2048, 8, 1, 262144, 16, 128, 2048, 32768, 4096, 262144, 65536, 128, 2048, 8, 1, 262144, 16, 262144],278540⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 396304, 2048, 1040, 8192, 16384, 8, 133248, 131072, 1040, 8192, 16384, 512, 8320, 131072, 1040, 262144],[128, 133120, 16, 1, 262144, 16, 8192, 133120, 16, 1, 262144, 16, 8192, 133120, 1024, 64, 262144, 1024, 262144],262414⟩,
.cycle 8 10 true (1),
.cycle 21 9 false (1),
.cycle 27 4 false (1),
.cycle 13 42 true (-1),
.cycle 1 20 true (1),
.last 15 (4,true),
.last 16 (4,true),
.last 53 (4,true),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 396304, 2048, 65536, 8192, 16384, 8, 133248, 131072, 66560, 8192, 16384, 512, 8320, 131072, 1040, 262144],[128, 131072, 1024, 1, 262144, 16, 8192, 133120, 65536, 1, 262144, 16, 8192, 133120, 65536, 64, 262144, 1024, 262144],262414⟩,
.last 20 (4,true)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 22 (4,true),
.cycle 21 1 false (1),
.last 18 (4,true),
.cycle 7 9 true (1),
.cycle 1 12 true (1),
.cycle 0 16 true (0),
.last 26 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 30 (4,true),
.cycle 1 14 true (1),
.last 20 (4,true),
.last 14 (4,true),
.cycle 5 9 true (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 34 1 false (4),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 1 12 true (1),
.cycle 8 7 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 29 1 false (3),
.cycle 8 8 true (2),
.cycle 19 6 false (1),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
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
.last 27 (2,true),
.cycle 0 26 true (0),
.cycle 9 4 true (3),
.cycle 24 1 false (6),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 32 1 false (4),
.cycle 8 6 true (2),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part347_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part347) = true := by rfl

def kid05_part227 : Audit := .split 9 (4,false) (byMove [(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part265),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part317),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347)])

theorem kid05_part227_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (kid05_part227) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part265),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part317),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part228_checked

  · exact kid05_part234_checked

  · exact kid05_part264_checked

  · exact kid05_part342_checked

  · exact kid05_part229_checked

  · exact kid05_part235_checked

  · exact kid05_part265_checked

  · exact kid05_part343_checked

  · exact kid05_part230_checked

  · exact kid05_part236_checked

  · exact kid05_part290_checked

  · exact kid05_part344_checked

  · exact kid05_part231_checked

  · exact kid05_part261_checked

  · exact kid05_part291_checked

  · exact kid05_part345_checked

  · exact kid05_part232_checked

  · exact kid05_part262_checked

  · exact kid05_part292_checked

  · exact kid05_part346_checked

  · exact kid05_part233_checked

  · exact kid05_part263_checked

  · exact kid05_part317_checked

  · exact kid05_part347_checked

def kid05_part349 : Audit := .cycle 0 10 true (0)
theorem kid05_part349_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part349) = true := by rfl

def kid05_part350 : Audit := .cycle 1 9 true (1)
theorem kid05_part350_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part350) = true := by rfl

def kid05_part351 : Audit := .cycle 20 1 false (2)
theorem kid05_part351_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part351) = true := by rfl

def kid05_part352 : Audit := .cycle 17 1 false (1)
theorem kid05_part352_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part352) = true := by rfl

def kid05_part353 : Audit := .split 10 (4,false) (byMove [
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
.last 14 (2,true),
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
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 2 false (2),
.cycle 1 15 true (0),
.cycle 15 2 false (1),
.cycle 11 2 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 10 1 true (2),
.cycle 9 2 true (2),
.cycle 17 5 false (1),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 15 5 false (1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 5 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 10 3 true (1),
.cycle 17 7 false (1),
.cycle 19 7 false (-1),
.cycle 15 5 false (1),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 6 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 19 7 false (-1),
.last 14 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 1 19 true (0),
.cycle 16 1 false (0),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 13 3 true (1),
.cycle 8 6 true (0)
]),
.split 12 (4,true) (byMove [
.cycle 0 17 true (-1),
.cycle 21 2 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 16 2 false (0),
.last 14 (2,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 20 2 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 2 false (2),
.cycle 17 2 false (3),
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
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 0, 64],[2, 0, 64, 1, 32, 32, 64],64⟩,
.cycle 13 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 3 true (2),
.cycle 11 2 true (2)
])
])
theorem kid05_part353_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part353) = true := by rfl

def kid05_part354 : Audit := .cycle 13 1 false (1)
theorem kid05_part354_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part354) = true := by rfl

def kid05_part355 : Audit := .cycle 0 10 true (0)
theorem kid05_part355_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part355) = true := by rfl

def kid05_part356 : Audit := .cycle 1 9 true (1)
theorem kid05_part356_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part356) = true := by rfl

def kid05_part357 : Audit := .split 21 (2,true) (byMove [
.cycle 1 28 true (0),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.cycle 1 27 true (0),
.cycle 55 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.last 24 (4,true),
.cycle 31 1 false (7),
.cycle 1 29 true (0),
.last 25 (4,true),
.cycle 0 33 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 20 3 false (3),
.cycle 0 29 true (0),
.last 25 (4,true),
.cycle 1 25 true (0),
.cycle 1 33 true (0),
.last 24 (4,true),
.cycle 26 12 true (4)
]),
.cycle 1 25 true (0),
.cycle 27 1 false (7),
.cycle 0 26 true (0),
.cycle 25 1 false (7),
.cycle 1 23 true (0),
.split 22 (4,true) (byMove [
.last 26 (4,false),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 0 26 true (0),
.cycle 1 23 true (0),
.cycle 26 1 false (6),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 24 (4,false),
.cycle 26 1 false (8),
.last 28 (4,false),
.last 28 (4,false),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.last 23 (4,false),
.last 28 (4,false),
.cycle 1 23 true (0),
.cycle 27 1 false (7),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 48 (4,false)
]),
.cycle 26 1 false (8),
.cycle 37 1 false (7),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.last 26 (4,true),
.cycle 0 56 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 31 1 false (7),
.cycle 1 29 true (0),
.cycle 1 27 true (0),
.cycle 21 2 true (2),
.cycle 29 1 false (7),
.last 23 (4,true),
.cycle 28 1 false (8),
.cycle 18 6 true (1),
.last 25 (4,true),
.cycle 1 33 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 20 3 false (3),
.cycle 1 29 true (0),
.cycle 37 1 false (7),
.last 24 (4,true),
.cycle 5 18 true (0),
.last 23 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 2048, 4, 128, 256, 8, 128, 2048, 4, 4096],[128, 8, 32, 1, 4096, 32, 128, 4, 4096, 1, 4096, 32, 4096],4096⟩
]),
.cycle 20 2 true (2),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.cycle 2 22 true (0),
.cycle 1 23 true (0),
.split 22 (4,true) (byMove [
.last 26 (4,false),
.cycle 26 1 false (4),
.last 24 (4,false),
.cycle 29 1 false (7),
.last 24 (4,false),
.last 26 (4,false),
.cycle 1 23 true (0),
.last 35 (4,false),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 24 (4,false),
.cycle 8 15 true (0),
.last 28 (4,false),
.cycle 1 27 true (0),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.last 24 (4,false),
.cycle 28 1 false (8),
.cycle 1 23 true (0),
.cycle 1 37 true (0),
.last 24 (4,false),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 48 (4,false)
]),
.cycle 8 15 true (0)
])
theorem kid05_part357_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part357) = true := by rfl

def kid05_part358 : Audit := .cycle 1 20 true (0)
theorem kid05_part358_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part358) = true := by rfl

def kid05_part360 : Audit := .cycle 0 11 true (0)
theorem kid05_part360_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part360) = true := by rfl

def kid05_part361 : Audit := .cycle 1 10 true (1)
theorem kid05_part361_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part361) = true := by rfl

def kid05_part362 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (3),
.cycle 1 22 true (0),
.cycle 26 1 false (4),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.cycle 26 1 false (6),
.cycle 33 1 false (5),
.last 23 (2,true),
.cycle 1 24 true (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 20 2 true (2),
.cycle 1 22 true (0),
.cycle 27 1 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.last 24 (2,true),
.cycle 47 1 false (9)
])
theorem kid05_part362_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part362) = true := by rfl

def kid05_part363 : Audit := .split 19 (4,true) (byMove [
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
.last 21 (2,true),
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
theorem kid05_part363_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part363) = true := by rfl

def kid05_part364 : Audit := .split 14 (4,true) (byMove [
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
.last 16 (2,true),
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
theorem kid05_part364_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part364) = true := by rfl

def kid05_part365 : Audit := .cycle 9 2 true (3)
theorem kid05_part365_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part365) = true := by rfl

def kid05_part366 : Audit := .cycle 0 11 true (0)
theorem kid05_part366_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part366) = true := by rfl

def kid05_part367 : Audit := .cycle 1 10 true (1)
theorem kid05_part367_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part367) = true := by rfl

def kid05_part368 : Audit := .split 23 (4,true) (byMove [
.last 26 (2,true),
.cycle 1 91 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.last 26 (2,true),
.cycle 0 29 true (0),
.last 27 (2,true),
.last 24 (2,true),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.cycle 30 1 false (10),
.cycle 45 1 false (9),
.last 25 (2,true),
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.last 25 (2,true),
.cycle 22 2 true (2),
.cycle 0 29 true (0),
.cycle 33 1 false (9),
.last 24 (2,true),
.cycle 5 19 true (0),
.cycle 26 11 true (6),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2096, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 4, 4096, 1, 2048, 32, 128, 16, 4096, 1, 2048, 32, 4096],4096⟩
])
theorem kid05_part368_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part368) = true := by rfl

def kid05_part369 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 1 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 1 25 true (0),
.cycle 27 1 false (7),
.cycle 0 26 true (0),
.last 22 (2,true),
.cycle 1 23 true (0),
.cycle 25 1 false (7),
.cycle 26 1 false (8),
.cycle 37 1 false (7),
.last 23 (2,true),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 29 1 false (7),
.cycle 20 2 true (2),
.cycle 1 37 true (0),
.cycle 1 25 true (0),
.last 22 (2,true),
.cycle 1 23 true (0),
.cycle 3 22 true (0),
.cycle 8 15 true (0)
])
theorem kid05_part369_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part369) = true := by rfl

def kid05_part370 : Audit := .cycle 10 1 true (4)
theorem kid05_part370_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part370) = true := by rfl

def kid05_part371 : Audit := .cycle 9 2 true (3)
theorem kid05_part371_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part371) = true := by rfl

def kid05_part372 : Audit := .cycle 7 5 true (2)
theorem kid05_part372_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part372) = true := by rfl

def kid05_part373 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 25 5 false (2),
.last 23 (4,true),
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
.last 26 (4,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 9 4 true (3)
])
theorem kid05_part373_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part373) = true := by rfl

def kid05_part374 : Audit := .cycle 0 13 true (0)
theorem kid05_part374_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part374) = true := by rfl

def kid05_part375 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 1 20 true (0),
.cycle 23 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 23 1 false (5),
.cycle 30 1 false (4),
.last 21 (2,true),
.cycle 1 22 true (0),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 1 20 true (0),
.cycle 24 1 false (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 1 23 true (0),
.cycle 40 1 false (8)
])
theorem kid05_part375_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part375) = true := by rfl

def kid05_part376 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 1 20 true (0),
.cycle 17 1 false (1),
.last 15 (2,true),
.cycle 21 1 false (5),
.cycle 19 1 false (5),
.cycle 20 1 false (6),
.cycle 39 1 false (5),
.last 16 (2,true),
.cycle 1 24 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 1 20 true (0),
.cycle 1 22 true (0),
.last 15 (2,true),
.cycle 1 23 true (0),
.cycle 17 3 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 48, 64, 1, 32, 32, 64],64⟩
])
theorem kid05_part376_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part376) = true := by rfl

def kid05_part377 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 23 3 false (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 26 (2,true),
.cycle 1 25 true (0),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 26 3 false (6),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3)
])
theorem kid05_part377_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part377) = true := by rfl

def kid05_part378 : Audit := .cycle 0 11 true (0)
theorem kid05_part378_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part378) = true := by rfl

def kid05_part379 : Audit := .cycle 1 10 true (1)
theorem kid05_part379_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part379) = true := by rfl

def kid05_part380 : Audit := .cycle 2 9 true (1)
theorem kid05_part380_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part380) = true := by rfl

def kid05_part381 : Audit := .cycle 1 13 true (1)
theorem kid05_part381_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part381) = true := by rfl

def kid05_part382 : Audit := .cycle 10 1 true (4)
theorem kid05_part382_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part382) = true := by rfl

def kid05_part383 : Audit := .cycle 9 2 true (3)
theorem kid05_part383_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part383) = true := by rfl

def kid05_part359 : Audit := .split 10 (4,false) (byMove [(kid05_part360),(kid05_part361),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371),(kid05_part372),(kid05_part373),(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part377),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383)])

theorem kid05_part359_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part359) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part360),(kid05_part361),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371),(kid05_part372),(kid05_part373),(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part377),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part360_checked

  · exact kid05_part366_checked

  · exact kid05_part372_checked

  · exact kid05_part378_checked

  · exact kid05_part361_checked

  · exact kid05_part367_checked

  · exact kid05_part373_checked

  · exact kid05_part379_checked

  · exact kid05_part362_checked

  · exact kid05_part368_checked

  · exact kid05_part374_checked

  · exact kid05_part380_checked

  · exact kid05_part363_checked

  · exact kid05_part369_checked

  · exact kid05_part375_checked

  · exact kid05_part381_checked

  · exact kid05_part364_checked

  · exact kid05_part370_checked

  · exact kid05_part376_checked

  · exact kid05_part382_checked

  · exact kid05_part365_checked

  · exact kid05_part371_checked

  · exact kid05_part377_checked

  · exact kid05_part383_checked

def kid05_part384 : Audit := .cycle 9 1 true (3)
theorem kid05_part384_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part384) = true := by rfl

def kid05_part385 : Audit := .cycle 7 4 true (2)
theorem kid05_part385_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part385) = true := by rfl

def kid05_part386 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 14 4 false (0),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 15 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 9 4 true (2),
.cycle 21 7 false (1),
.cycle 18 3 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 15 6 false (1)
]),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 4, 1, 64, 32, 64],80⟩,
.cycle 3 9 true (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 12 1 true (4),
.cycle 9 4 true (2),
.cycle 7 7 true (2),
.cycle 10 3 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 15 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 27 (4,true)
]),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.cycle 14 4 false (0),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 14 4 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 13 (4,false),
.cycle 15 4 false (-1),
.cycle 1 13 true (1),
.cycle 20 5 false (0),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (2),
.cycle 21 7 false (1),
.cycle 18 3 false (-1),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 15 4 false (-1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (2)
]),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
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
.last 18 (4,true),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 19 (4,true)
]),
.cycle 8 10 true (2)
])
theorem kid05_part386_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part386) = true := by rfl

def kid05_part387 : Audit := .cycle 0 12 true (0)
theorem kid05_part387_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part387) = true := by rfl

def kid05_part388 : Audit := .cycle 17 1 false (1)
theorem kid05_part388_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part388) = true := by rfl

def kid05_part390 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 4104, 4, 1, 4096, 32, 128, 4, 4, 1, 4096, 32, 4096],6144⟩,
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 12 5 true (2),
.cycle 12 8 true (1),
.cycle 19 7 false (2),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 8 7 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 15 (4,true)
])
theorem kid05_part390_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part390) = true := by rfl

def kid05_part391 : Audit := .cycle 0 14 true (0)
theorem kid05_part391_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part391) = true := by rfl

def kid05_part392 : Audit := .cycle 21 1 false (1)
theorem kid05_part392_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part392) = true := by rfl

def kid05_part393 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.proven (BB6.Agent11Raw39Pumps.M259.table) (fun m hm => BB6.Agent11Raw39Pumps.M259.never m hm),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 392, 5, 128, 256, 8, 128, 128, 4096, 4096],[128, 4232, 4, 1, 4096, 32, 128, 5, 4, 1, 4096, 32, 4096],6144⟩,
.cycle 3 13 true (0),
.cycle 1 19 true (0),
.cycle 7 13 true (0),
.cycle 27 1 false (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.last 16 (4,true),
.cycle 8 9 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 0 18 true (0),
.last 17 (4,true)
])
theorem kid05_part393_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part393) = true := by rfl

def kid05_part394 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 22 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 17 (2,true),
.cycle 11 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid05_part394_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part394) = true := by rfl

def kid05_part395 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 24 2 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 14 2 false (0),
.last 13 (2,true),
.cycle 17 2 false (3),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.cycle 16 2 false (0),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.last 15 (2,true),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 7 8 true (0),
.cycle 19 2 false (1),
.cycle 17 2 false (1)
])
theorem kid05_part395_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part395) = true := by rfl

def kid05_part396 : Audit := .cycle 1 11 true (1)
theorem kid05_part396_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part396) = true := by rfl

def kid05_part397 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 19 (2,true),
.cycle 17 3 false (-1),
.cycle 1 17 true (0),
.cycle 17 3 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 27 3 false (5),
.cycle 18 3 false (2),
.cycle 20 3 false (0),
.last 18 (2,true),
.cycle 1 19 true (-1),
.cycle 17 1 false (-1),
.cycle 17 3 false (0),
.cycle 17 3 false (-1),
.cycle 1 17 true (0),
.cycle 19 3 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 9 21 true (0),
.cycle 12 6 true (0)
])
theorem kid05_part397_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part397) = true := by rfl

def kid05_part398 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 28 true (0),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 1 24 true (0),
.last 27 (4,true),
.cycle 9 3 true (2),
.cycle 7 6 true (2),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 24 (4,true),
.last 13 (4,true)
])
theorem kid05_part398_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part398) = true := by rfl

def kid05_part399 : Audit := .cycle 0 12 true (0)
theorem kid05_part399_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part399) = true := by rfl

def kid05_part400 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 10 2 true (2),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 8 6 true (2)
])
theorem kid05_part400_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part400) = true := by rfl

def kid05_part401 : Audit := .cycle 8 3 true (2)
theorem kid05_part401_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part401) = true := by rfl

def kid05_part402 : Audit := .cycle 17 5 false (1)
theorem kid05_part402_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part402) = true := by rfl

def kid05_part403 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 15 5 false (1),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.cycle 17 5 false (-1),
.cycle 1 13 true (1),
.last 15 (4,true),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 4, 16384, 4, 524288, 1048576, 32768, 128, 4402341478401, 4398046511104, 33554432, 67108864, 8, 4, 4294967296, 4398046511236, 137438953472, 274877906944, 8589934592, 33554432, 4, 4398046511104, 524288, 1048576, 32768, 128, 4398046511104, 4398046511104, 33554432, 67108864, 8, 4, 4294967296, 4398046511108, 137438953472, 274877906944, 8589934592, 33554432, 4398046511108, 4398046511104, 4398046511104],[128, 4398047559688, 4, 1, 4398046511104, 32, 524288, 4, 16384, 4096, 4398046511104, 131072, 33554432, 4398046511104, 4, 1, 4398046511104, 32, 137438953472, 4398046511236, 4294967296, 1073741824, 4398046511104, 34359738368, 524288, 4, 16384, 4096, 4398046511104, 131072, 33554432, 4398046511104, 4, 1, 4398046511104, 32, 137438953472, 4398046511108, 4294967296, 1073741824, 4398046511104, 34359738368, 4398046511104],7731754961920⟩,
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 19 7 false (-1),
.cycle 15 5 false (1),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 8 7 true (1),
.cycle 1 13 true (1),
.cycle 19 9 false (1),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 38 16 true (2)
])
theorem kid05_part403_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part403) = true := by rfl

def kid05_part404 : Audit := .cycle 1 13 true (1)
theorem kid05_part404_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part404) = true := by rfl

def kid05_part405 : Audit := .cycle 18 1 false (0)
theorem kid05_part405_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part405) = true := by rfl

def kid05_part406 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 10 11 false (3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 18 1 false (2),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.last 13 (2,true),
.cycle 5 8 true (0),
.cycle 14 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid05_part406_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part406) = true := by rfl

def kid05_part407 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 28 2 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 16 2 false (2),
.cycle 14 2 false (0),
.last 13 (2,true),
.cycle 17 2 false (3),
.cycle 16 2 false (4),
.cycle 16 2 false (4),
.cycle 16 2 false (0),
.last 14 (2,true),
.cycle 18 2 false (2),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 22 2 false (4),
.cycle 15 2 false (1),
.last 13 (2,true),
.cycle 5 8 true (0),
.cycle 8 10 true (0),
.cycle 25 2 false (5)
])
theorem kid05_part407_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part407) = true := by rfl

def kid05_part408 : Audit := .cycle 1 11 true (1)
theorem kid05_part408_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part408) = true := by rfl

def kid05_part409 : Audit := .cycle 7 4 true (2)
theorem kid05_part409_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part409) = true := by rfl

def kid05_part410 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 256, 4, 128, 256, 8, 128, 256, 4096, 4096],[128, 4104, 4, 1, 4096, 32, 128, 4, 4, 1, 4096, 32, 4096],6144⟩,
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 13 (4,true)
])
theorem kid05_part410_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part410) = true := by rfl

def kid05_part411 : Audit := .cycle 0 12 true (0)
theorem kid05_part411_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part411) = true := by rfl

def kid05_part412 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 18 true (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 3 false (1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 8 6 true (2)
])
theorem kid05_part412_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part412) = true := by rfl

def kid05_part413 : Audit := .cycle 8 3 true (2)
theorem kid05_part413_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part413) = true := by rfl

def kid05_part389 : Audit := .split 10 (4,false) (byMove [(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413)])

theorem kid05_part389_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part389) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part390_checked

  · exact kid05_part396_checked

  · exact kid05_part402_checked

  · exact kid05_part408_checked

  · exact kid05_part391_checked

  · exact kid05_part397_checked

  · exact kid05_part403_checked

  · exact kid05_part409_checked

  · exact kid05_part392_checked

  · exact kid05_part398_checked

  · exact kid05_part404_checked

  · exact kid05_part410_checked

  · exact kid05_part393_checked

  · exact kid05_part399_checked

  · exact kid05_part405_checked

  · exact kid05_part411_checked

  · exact kid05_part394_checked

  · exact kid05_part400_checked

  · exact kid05_part406_checked

  · exact kid05_part412_checked

  · exact kid05_part395_checked

  · exact kid05_part401_checked

  · exact kid05_part407_checked

  · exact kid05_part413_checked

def kid05_part414 : Audit := .cycle 16 1 false (4)
theorem kid05_part414_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part414) = true := by rfl

def kid05_part415 : Audit := .cycle 0 10 true (0)
theorem kid05_part415_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part415) = true := by rfl

def kid05_part416 : Audit := .cycle 1 9 true (1)
theorem kid05_part416_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part416) = true := by rfl

def kid05_part417 : Audit := .cycle 2 8 true (1)
theorem kid05_part417_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part417) = true := by rfl

def kid05_part418 : Audit := .cycle 1 12 true (1)
theorem kid05_part418_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part418) = true := by rfl

def kid05_part419 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 19 3 false (2),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (4,true),
.last 21 (4,true),
.last 23 (4,true),
.cycle 9 3 true (3),
.cycle 7 6 true (2),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.last 19 (4,true),
.last 21 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.cycle 19 3 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 17 1 false (1),
.cycle 9 3 true (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 1 21 true (0),
.cycle 15 1 false (-1),
.cycle 8 7 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 9 13 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 39 1 false (3),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1040, 4, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 4, 4096, 1, 16, 32, 128, 1024, 4096, 1, 16, 32, 4096],4096⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.last 24 (2,true),
.last 21 (2,true),
.cycle 1 22 true (1),
.last 23 (2,true),
.cycle 8 14 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
]),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 6 5 true (2),
.split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 21 3 false (1),
.last 21 (2,true),
.cycle 0 28 true (0),
.last 24 (2,true),
.cycle 28 3 false (5),
.cycle 6 15 true (0),
.cycle 14 44 true (0),
.last 21 (2,true),
.cycle 1 22 true (0),
.last 25 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1056, 4096, 1024, 128, 256, 8, 128, 32, 1024, 4096],[128, 32, 4096, 1, 32, 32, 128, 1024, 4096, 1, 32, 32, 4096],4112⟩,
.cycle 34 3 false (5),
.cycle 21 3 false (1),
.last 21 (2,true),
.cycle 1 28 true (0),
.last 24 (2,true),
.cycle 25 3 false (6),
.cycle 1 33 true (0),
.cycle 1 24 true (0),
.last 21 (2,true),
.cycle 1 22 true (0),
.cycle 22 5 true (3),
.cycle 8 14 true (0)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 21 (4,true),
.cycle 21 1 false (1),
.cycle 7 9 true (1),
.last 20 (4,true),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.last 25 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.last 16 (4,true),
.cycle 17 6 false (1),
.cycle 1 14 true (1),
.last 19 (4,true),
.cycle 5 9 true (1),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.last 22 (2,true),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.cycle 28 3 false (5),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 24 1 false (6),
.cycle 8 4 true (2),
.cycle 6 11 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 27 1 false (3),
.cycle 15 1 false (-1),
.cycle 8 8 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 8 4 true (2)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part419_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part419) = true := by rfl

def kid05_part420 : Audit := .cycle 9 1 true (3)
theorem kid05_part420_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part420) = true := by rfl

def kid05_part348 : Audit := .split 9 (5,false) (byMove [(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420)])

theorem kid05_part348_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (kid05_part348) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part349_checked

  · exact kid05_part355_checked

  · exact kid05_part385_checked

  · exact kid05_part415_checked

  · exact kid05_part350_checked

  · exact kid05_part356_checked

  · exact kid05_part386_checked

  · exact kid05_part416_checked

  · exact kid05_part351_checked

  · exact kid05_part357_checked

  · exact kid05_part387_checked

  · exact kid05_part417_checked

  · exact kid05_part352_checked

  · exact kid05_part358_checked

  · exact kid05_part388_checked

  · exact kid05_part418_checked

  · exact kid05_part353_checked

  · exact kid05_part359_checked

  · exact kid05_part389_checked

  · exact kid05_part419_checked

  · exact kid05_part354_checked

  · exact kid05_part384_checked

  · exact kid05_part414_checked

  · exact kid05_part420_checked

def kid05_part421 : Audit := .cycle 13 3 false (1)
theorem kid05_part421_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,0⟩)) (kid05_part421) = true := by rfl

def kid05_part423 : Audit := .cycle 1 11 true (1)
theorem kid05_part423_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part423) = true := by rfl

def kid05_part424 : Audit := .split 16 (5,false) (byMove [
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
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 27 8 false (0),
.cycle 1 17 false (3),
.cycle 11 12 false (1),
.cycle 1 20 false (3),
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
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 0 20 true (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 19 (4,true),
.cycle 19 16 true (-2),
.cycle 1 17 false (3),
.cycle 11 12 true (-2),
.cycle 1 20 true (-2),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
]),
.cycle 16 1 true (-2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.last 38 (4,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 1 18 false (3),
.cycle 15 3 false (-1),
.cycle 11 14 false (1),
.cycle 0 19 false (3),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 1 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 27 8 false (0),
.cycle 11 7 false (1),
.cycle 14 4 false (0),
.cycle 7 23 false (3),
.last 18 (4,true),
.cycle 15 4 false (-1)
]),
.cycle 16 1 false (-2),
.cycle 28 5 false (0),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 1 19 false (3),
.split 17 (4,false) (byMove [
.cycle 1 18 false (3),
.cycle 15 3 false (-1),
.cycle 11 14 false (1),
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
.cycle 15 3 false (-1),
.cycle 33 16 false (1),
.cycle 1 19 false (3),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 27 12 false (2),
.cycle 28 5 false (0),
.cycle 2 16 false (3),
.cycle 7 24 false (3),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
]),
.cycle 16 1 true (-2)
])
theorem kid05_part424_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part424) = true := by rfl

def kid05_part425 : Audit := .cycle 14 1 false (0)
theorem kid05_part425_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part425) = true := by rfl

def kid05_part426 : Audit := .cycle 0 12 true (0)
theorem kid05_part426_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part426) = true := by rfl

def kid05_part428 : Audit := .cycle 1 12 true (0)
theorem kid05_part428_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part428) = true := by rfl

def kid05_part429 : Audit := .split 13 (5,false) (byMove [
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
.cycle 15 11 false (-1),
.cycle 14 11 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 26 11 false (0),
.cycle 1 13 false (3),
.cycle 14 11 false (1),
.cycle 1 16 true (-1),
.last 14 (4,false),
.cycle 13 1 true (-1)
])
theorem kid05_part429_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part429) = true := by rfl

def kid05_part430 : Audit := .split 13 (4,false) (byMove [
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
.cycle 21 1 false (-3),
.cycle 18 1 false (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 29 1 false (-1),
.cycle 1 13 false (3),
.cycle 25 1 false (-1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.last 14 (5,false)
])
theorem kid05_part430_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part430) = true := by rfl

def kid05_part431 : Audit := .cycle 0 13 true (0)
theorem kid05_part431_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part431) = true := by rfl

def kid05_part432 : Audit := .split 13 (4,false) (byMove [
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
.cycle 12 7 false (0),
.cycle 12 4 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 11 15 false (3),
.cycle 1 13 false (3),
.cycle 12 11 false (1),
.cycle 1 16 true (-1),
.cycle 13 1 true (-1),
.last 14 (5,false)
])
theorem kid05_part432_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part432) = true := by rfl

def kid05_part433 : Audit := .split 16 (5,false) (byMove [
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
.cycle 12 7 false (0),
.cycle 13 4 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 29 5 false (-1),
.cycle 1 16 false (3),
.cycle 12 11 false (0),
.cycle 1 19 false (3),
.last 17 (4,false),
.cycle 16 1 true (-2)
])
theorem kid05_part433_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part433) = true := by rfl

def kid05_part434 : Audit := .cycle 0 12 true (0)
theorem kid05_part434_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part434) = true := by rfl

def kid05_part435 : Audit := .cycle 1 11 true (1)
theorem kid05_part435_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part435) = true := by rfl

def kid05_part436 : Audit := .cycle 24 1 false (2)
theorem kid05_part436_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part436) = true := by rfl

def kid05_part437 : Audit := .cycle 21 1 false (1)
theorem kid05_part437_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part437) = true := by rfl

def kid05_part438 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 15 1 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.last 13 (5,false),
.last 17 (5,false),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (3),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid05_part438_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part438) = true := by rfl

def kid05_part439 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 17 7 false (-1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid05_part439_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part439) = true := by rfl

def kid05_part440 : Audit := .cycle 13 6 false (1)
theorem kid05_part440_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part440) = true := by rfl

def kid05_part441 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 22 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 17 3 false (0),
.cycle 14 3 false (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 16 3 false (1),
.cycle 17 3 false (-2),
.cycle 14 3 false (-1),
.cycle 19 3 false (0),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 12 5 false (1),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 19 3 false (0),
.last 14 (4,false),
.cycle 18 3 false (-1)
])
theorem kid05_part441_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part441) = true := by rfl

def kid05_part442 : Audit := .split 13 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 9 19 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 22 true (-2),
.cycle 0 19 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 0 18 true (-1),
.last 14 (5,false),
.far true 2 ⟨0,[0, 1, 0, 0],[144, 352, 648, 512, 64, 4096, 128, 256, 128, 8, 1, 4096, 4096],[144, 32, 16, 320, 256, 128, 128, 32, 16, 320, 4, 2, 4096],6178⟩,
.cycle 9 11 false (2),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 18 (5,false),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.cycle 0 28 true (-2),
.last 14 (5,false)
])
theorem kid05_part442_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part442) = true := by rfl

def kid05_part443 : Audit := .cycle 1 13 true (0)
theorem kid05_part443_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part443) = true := by rfl

def kid05_part444 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.cycle 1 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 1 21 false (3),
.last 15 (5,false),
.cycle 0 18 true (-1),
.cycle 1 15 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 12 4 false (0),
.cycle 1 25 false (3),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 18 (5,false),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.cycle 1 15 true (-1),
.cycle 11 3 false (1),
.last 16 (5,false)
])
theorem kid05_part444_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part444) = true := by rfl

def kid05_part445 : Audit := .split 16 (5,false) (byMove [
.cycle 9 9 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 8, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 393, 393, 128, 393, 393, 1, 393, 393, 4096],5136⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 9 9 false (2),
.cycle 0 22 true (-2),
.last 18 (4,false),
.cycle 0 26 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 13 4 false (0),
.cycle 9 11 false (2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 21 5 false (-1),
.cycle 12 6 false (0),
.cycle 14 3 false (0),
.cycle 7 12 false (3),
.cycle 11 6 false (1),
.cycle 12 11 false (0)
])
theorem kid05_part445_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part445) = true := by rfl

def kid05_part446 : Audit := .cycle 0 12 true (0)
theorem kid05_part446_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part446) = true := by rfl

def kid05_part447 : Audit := .cycle 1 11 true (1)
theorem kid05_part447_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part447) = true := by rfl

def kid05_part448 : Audit := .cycle 2 10 true (1)
theorem kid05_part448_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part448) = true := by rfl

def kid05_part449 : Audit := .cycle 1 14 true (1)
theorem kid05_part449_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part449) = true := by rfl

def kid05_part450 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.last 20 (5,false),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.last 13 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.cycle 13 11 false (1),
.cycle 1 14 true (1),
.cycle 11 3 true (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.last 13 (5,false)
])
theorem kid05_part450_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part450) = true := by rfl

def kid05_part451 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 13 14 false (1),
.last 17 (4,false),
.cycle 0 14 true (0),
.cycle 11 2 true (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 12 1 true (2),
.cycle 19 7 false (-1),
.cycle 15 6 false (0),
.last 17 (4,false),
.cycle 1 14 true (1),
.last 25 (4,false),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 1 true (2)
])
theorem kid05_part451_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part451) = true := by rfl

def kid05_part427 : Audit := .split 11 (4,true) (byMove [(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part436),(kid05_part437),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444),(kid05_part445),(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part451)])

theorem kid05_part427_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part427) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part436),(kid05_part437),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444),(kid05_part445),(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part451)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part428_checked

  · exact kid05_part434_checked

  · exact kid05_part440_checked

  · exact kid05_part446_checked

  · exact kid05_part429_checked

  · exact kid05_part435_checked

  · exact kid05_part441_checked

  · exact kid05_part447_checked

  · exact kid05_part430_checked

  · exact kid05_part436_checked

  · exact kid05_part442_checked

  · exact kid05_part448_checked

  · exact kid05_part431_checked

  · exact kid05_part437_checked

  · exact kid05_part443_checked

  · exact kid05_part449_checked

  · exact kid05_part432_checked

  · exact kid05_part438_checked

  · exact kid05_part444_checked

  · exact kid05_part450_checked

  · exact kid05_part433_checked

  · exact kid05_part439_checked

  · exact kid05_part445_checked

  · exact kid05_part451_checked

def kid05_part452 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 21 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (-2),
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
.cycle 21 3 false (-1),
.cycle 9 9 false (2),
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
.cycle 1 15 true (-1),
.cycle 25 3 false (3),
.cycle 19 1 false (3),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 15 3 false (1),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 16 (4,true),
.cycle 28 3 false (0),
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
.cycle 8 15 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 9 7 false (2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 20 3 false (-2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 7 10 false (3),
.last 15 (4,true),
.cycle 11 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 18 3 false (0),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 1 15 true (-1),
.cycle 33 3 false (-1),
.cycle 3 17 false (3),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 17 3 false (-1),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 24 9 false (3),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 17 3 false (-1)
]),
.cycle 17 3 false (-1)
])
theorem kid05_part452_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part452) = true := by rfl

def kid05_part453 : Audit := .cycle 0 11 true (0)
theorem kid05_part453_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part453) = true := by rfl

def kid05_part454 : Audit := .cycle 1 10 true (1)
theorem kid05_part454_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part454) = true := by rfl

def kid05_part455 : Audit := .cycle 0 23 true (0)
theorem kid05_part455_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part455) = true := by rfl

def kid05_part456 : Audit := .cycle 3 8 true (1)
theorem kid05_part456_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part456) = true := by rfl

def kid05_part458 : Audit := .cycle 0 12 true (0)
theorem kid05_part458_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part458) = true := by rfl

def kid05_part459 : Audit := .cycle 1 11 true (1)
theorem kid05_part459_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part459) = true := by rfl

def kid05_part460 : Audit := .cycle 2 10 true (1)
theorem kid05_part460_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part460) = true := by rfl

def kid05_part461 : Audit := .cycle 1 14 true (1)
theorem kid05_part461_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part461) = true := by rfl

def kid05_part462 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.last 20 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.last 14 (5,false),
.cycle 15 8 false (1),
.last 15 (5,false),
.cycle 0 18 true (0),
.cycle 1 15 true (0),
.cycle 15 1 false (-1),
.last 18 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (1),
.last 14 (5,false)
])
theorem kid05_part462_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part462) = true := by rfl

def kid05_part463 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 13 14 false (1),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (2),
.cycle 12 1 true (2),
.cycle 19 7 false (-1),
.cycle 15 6 false (1),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 16 10 false (1),
.cycle 12 1 true (2)
])
theorem kid05_part463_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part463) = true := by rfl

def kid05_part464 : Audit := .cycle 0 12 true (0)
theorem kid05_part464_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part464) = true := by rfl

def kid05_part465 : Audit := .cycle 1 11 true (1)
theorem kid05_part465_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part465) = true := by rfl

def kid05_part466 : Audit := .split 25 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 12 14 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 16541, 4, 262144, 8192, 16384, 8, 128, 4, 262144, 128, 256, 8, 128, 4, 262144, 262144],[128, 262144, 16, 1, 16541, 16, 8192, 4, 16, 1, 128, 262144, 128, 262144, 16, 1, 128, 16, 262144],395296⟩,
.cycle 0 45 true (0),
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 20, 4, 262144, 8192, 16384, 8, 128, 4, 262144, 128, 256, 8, 128, 4, 262144, 262144],[128, 262144, 16, 1, 4, 16, 8192, 4, 16, 1, 4, 262144, 128, 262144, 16, 1, 4, 16, 262144],395296⟩,
.cycle 0 41 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 20, 4, 262144, 8192, 16384, 8, 128, 4, 262144, 128, 256, 8, 128, 4, 262144, 262144],[128, 262144, 16, 1, 16, 16, 8192, 4, 16, 1, 16, 262144, 128, 262144, 16, 1, 16, 16, 262144],395296⟩,
.last 26 (5,false),
.cycle 7 20 true (1),
.cycle 9 17 true (1),
.cycle 0 28 true (0),
.cycle 14 12 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 20, 4, 262144, 8192, 16384, 8, 128, 4, 262144, 128, 256, 8, 128, 4, 262144, 262144],[128, 262144, 16, 1, 16, 16, 8192, 4, 16, 1, 16, 262144, 128, 262144, 16, 1, 16, 16, 262144],395296⟩,
.last 26 (5,false),
.cycle 0 26 true (0),
.cycle 1 25 true (1),
.cycle 2 24 true (1),
.cycle 1 28 true (1),
.cycle 25 32 true (5),
.last 26 (5,false)
])
theorem kid05_part466_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part466) = true := by rfl

def kid05_part467 : Audit := .cycle 0 23 true (0)
theorem kid05_part467_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part467) = true := by rfl

def kid05_part468 : Audit := .cycle 11 1 true (3)
theorem kid05_part468_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part468) = true := by rfl

def kid05_part469 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 16 true (1),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,true),
.last 27 (4,true),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 8 14 true (1),
.cycle 8 6 true (1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part469_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part469) = true := by rfl

def kid05_part470 : Audit := .split 24 (5,false) (byMove [
.cycle 26 44 true (-2),
.cycle 15 16 false (1),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 15 12 false (1),
.cycle 24 1 false (-2),
.cycle 15 11 false (1),
.cycle 17 8 true (-2),
.cycle 0 40 true (-2),
.cycle 25 1 false (-1),
.cycle 15 12 false (1),
.cycle 16 10 true (-2),
.cycle 15 11 false (1),
.cycle 17 8 false (1),
.cycle 15 13 false (1),
.cycle 25 1 false (-3),
.cycle 15 12 false (1),
.cycle 24 1 false (-2),
.cycle 20 5 false (1),
.cycle 9 16 false (3),
.cycle 0 40 true (-2),
.cycle 15 13 false (1),
.cycle 15 12 false (1),
.cycle 14 12 false (2)
])
theorem kid05_part470_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part470) = true := by rfl

def kid05_part471 : Audit := .cycle 9 3 true (1)
theorem kid05_part471_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part471) = true := by rfl

def kid05_part472 : Audit := .cycle 0 14 true (0)
theorem kid05_part472_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part472) = true := by rfl

def kid05_part473 : Audit := .cycle 4 8 true (1)
theorem kid05_part473_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part473) = true := by rfl

def kid05_part474 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.last 15 (5,false),
.cycle 15 1 false (1),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.last 20 (5,false),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 36 1 false (6),
.cycle 1 15 true (1),
.cycle 25 1 false (5),
.last 18 (5,false),
.cycle 15 8 false (1),
.last 15 (5,false),
.cycle 15 10 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.last 18 (5,false),
.last 28 (5,false),
.last 17 (5,false),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 14 3 true (2),
.last 24 (5,false)
])
theorem kid05_part474_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part474) = true := by rfl

def kid05_part475 : Audit := .split 12 (5,false) (byMove [
.cycle 9 5 true (1),
.cycle 13 14 false (1),
.cycle 20 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 19 7 false (-1),
.cycle 15 6 false (1),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 15 1 false (-1),
.cycle 1 13 true (1),
.cycle 9 16 false (3),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 18 7 false (1)
])
theorem kid05_part475_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part475) = true := by rfl

def kid05_part476 : Audit := .cycle 0 12 true (0)
theorem kid05_part476_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part476) = true := by rfl

def kid05_part477 : Audit := .cycle 1 11 true (1)
theorem kid05_part477_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part477) = true := by rfl

def kid05_part478 : Audit := .cycle 2 10 true (1)
theorem kid05_part478_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part478) = true := by rfl

def kid05_part479 : Audit := .cycle 1 14 true (1)
theorem kid05_part479_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part479) = true := by rfl

def kid05_part480 : Audit := .cycle 11 1 true (3)
theorem kid05_part480_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part480) = true := by rfl

def kid05_part481 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 15 16 false (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 29 true (0),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (1),
.cycle 17 8 false (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part481_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part481) = true := by rfl

def kid05_part457 : Audit := .split 11 (4,false) (byMove [(kid05_part458),(kid05_part459),(kid05_part460),(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part481)])

theorem kid05_part457_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part457) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part458),(kid05_part459),(kid05_part460),(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part481)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part458_checked

  · exact kid05_part464_checked

  · exact kid05_part470_checked

  · exact kid05_part476_checked

  · exact kid05_part459_checked

  · exact kid05_part465_checked

  · exact kid05_part471_checked

  · exact kid05_part477_checked

  · exact kid05_part460_checked

  · exact kid05_part466_checked

  · exact kid05_part472_checked

  · exact kid05_part478_checked

  · exact kid05_part461_checked

  · exact kid05_part467_checked

  · exact kid05_part473_checked

  · exact kid05_part479_checked

  · exact kid05_part462_checked

  · exact kid05_part468_checked

  · exact kid05_part474_checked

  · exact kid05_part480_checked

  · exact kid05_part463_checked

  · exact kid05_part469_checked

  · exact kid05_part475_checked

  · exact kid05_part481_checked

def kid05_part482 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 13 15 false (1),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 11 2 true (2),
.cycle 20 7 false (-2),
.cycle 15 7 false (1),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 15 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.last 14 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 17 true (1),
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
.cycle 7 7 true (1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.last 22 (4,true),
.last 15 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3),
.cycle 15 11 false (1),
.cycle 9 3 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 12 (4,false) (byMove [
.cycle 9 5 true (1),
.last 38 (4,true),
.cycle 20 1 false (0),
.cycle 7 8 true (1),
.last 13 (4,true),
.cycle 15 2 false (-1),
.cycle 1 13 true (1),
.last 15 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 5 true (1),
.cycle 20 7 false (-2),
.cycle 8 16 false (3),
.cycle 8 9 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 15 2 false (-1),
.cycle 1 13 true (1),
.cycle 15 11 false (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 15 4 false (1)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 18 3 false (0),
.cycle 10 3 true (2),
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
.cycle 18 3 false (0),
.cycle 8 6 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 8 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid05_part482_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part482) = true := by rfl

def kid05_part483 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 21 5 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.split 16 (4,false) (byMove [
.cycle 0 17 false (3),
.cycle 22 5 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 9 9 false (2),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 19 (4,true),
.cycle 15 2 true (-2),
.cycle 18 5 false (-2),
.cycle 17 5 false (-2),
.cycle 9 11 false (2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 23 5 false (-1),
.cycle 0 20 true (-2),
.cycle 21 5 false (0),
.cycle 9 11 false (2),
.last 19 (4,true),
.last 18 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 17 5 false (1),
.cycle 16 5 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.split 16 (4,false) (byMove [
.cycle 9 9 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 2 true (-1),
.cycle 1 17 true (-1),
.cycle 25 5 false (4),
.cycle 19 5 false (1),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 17 5 false (1),
.cycle 18 5 false (0),
.cycle 17 5 false (0),
.cycle 1 19 true (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.last 18 (4,true),
.cycle 31 5 false (1),
.cycle 17 5 false (1),
.cycle 17 5 false (1),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 13 4 true (-1)
]),
.cycle 17 5 false (1),
.cycle 17 5 false (-1),
.cycle 16 5 false (-1),
.cycle 19 5 false (1),
.cycle 16 1 false (-2),
.split 16 (4,false) (byMove [
.cycle 9 9 false (2),
.cycle 6 19 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 9 9 false (2),
.cycle 14 3 false (0),
.cycle 19 5 false (-1),
.cycle 19 5 false (1),
.last 17 (4,true),
.cycle 17 5 false (-1),
.cycle 18 5 false (-2),
.cycle 17 5 false (-2),
.cycle 9 11 false (2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 23 5 false (-1),
.cycle 17 5 false (-1),
.cycle 17 5 false (-1),
.cycle 7 12 false (3),
.last 17 (4,true),
.cycle 13 4 false (1)
]),
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 18 5 false (1),
.split 16 (4,false) (byMove [
.cycle 9 9 false (2),
.cycle 14 3 false (0),
.cycle 19 5 false (-1),
.cycle 19 5 false (1),
.last 17 (4,true),
.cycle 17 5 false (-1),
.cycle 1 17 true (-1),
.cycle 38 5 false (0),
.cycle 12 7 false (2),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 8 9 false (2),
.cycle 17 5 false (0),
.cycle 14 3 false (0),
.cycle 19 5 false (-1),
.cycle 18 5 false (1),
.last 17 (4,true),
.cycle 17 5 false (-1),
.cycle 26 11 false (3),
.cycle 12 5 false (2),
.cycle 10 7 false (2),
.cycle 0 18 true (-1),
.last 17 (4,true),
.cycle 18 5 false (0)
]),
.cycle 18 5 false (0)
])
theorem kid05_part483_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part483) = true := by rfl

def kid05_part484 : Audit := .split 16 (5,false) (byMove [
.cycle 18 32 true (-2),
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
.cycle 9 10 false (2),
.last 28 (4,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.last 20 (4,true),
.cycle 16 2 true (-3),
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 9 12 false (2),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 15 8 false (0),
.last 28 (4,true),
.cycle 11 12 false (1),
.cycle 9 12 false (2),
.last 20 (4,true),
.last 19 (4,true)
]),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 4 true (-2),
.cycle 0 28 true (-2),
.cycle 17 1 false (-1),
.split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 0 32 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 true (-2),
.cycle 9 10 true (-2),
.cycle 21 16 true (0),
.cycle 13 6 true (-2),
.cycle 0 28 true (-2),
.last 18 (4,true),
.cycle 12 6 true (-2),
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 9 12 true (-2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.last 19 (4,true),
.cycle 15 8 true (-2),
.cycle 11 7 false (1),
.cycle 14 4 true (-2),
.cycle 7 13 false (3),
.last 18 (4,true),
.cycle 15 4 true (-2)
]),
.cycle 12 6 true (-2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 11 9 false (1),
.cycle 17 1 false (-3),
.split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.last 28 (4,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 9 10 false (2),
.cycle 15 3 false (-1),
.cycle 13 6 false (0),
.cycle 11 9 false (1),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.cycle 9 12 false (2),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 16 2 false (-2),
.cycle 15 8 false (0),
.cycle 11 7 false (1),
.cycle 14 4 false (0),
.cycle 7 13 false (3),
.last 18 (4,true),
.cycle 15 4 false (-1)
]),
.cycle 16 1 false (-2),
.cycle 15 5 false (0),
.cycle 9 8 false (2),
.cycle 0 28 true (-2),
.cycle 11 9 false (1),
.split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 15 3 false (-1),
.cycle 13 6 false (0),
.cycle 11 9 false (1),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 7 14 false (3),
.cycle 21 16 true (0),
.cycle 9 10 false (2),
.cycle 0 28 true (-2),
.last 18 (4,true),
.cycle 8 10 false (2),
.cycle 11 8 false (1),
.cycle 15 3 false (-1),
.cycle 13 6 false (0),
.cycle 11 9 false (1),
.last 18 (4,true),
.cycle 12 6 false (0),
.cycle 11 12 false (2),
.cycle 15 5 false (0),
.cycle 10 8 false (2),
.cycle 15 11 false (2),
.last 18 (4,true),
.cycle 11 8 false (1)
]),
.cycle 11 8 false (1)
])
theorem kid05_part484_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part484) = true := by rfl

def kid05_part485 : Audit := .cycle 1 23 true (-1)
theorem kid05_part485_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part485) = true := by rfl

def kid05_part486 : Audit := .cycle 1 12 true (1)
theorem kid05_part486_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part486) = true := by rfl

def kid05_part488 : Audit := .cycle 9 4 true (0)
theorem kid05_part488_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part488) = true := by rfl

def kid05_part489 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.cycle 1 33 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 9 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 0 23 true (-1),
.cycle 78 20 false (-2),
.cycle 9 17 false (2),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 7 29 false (3),
.cycle 0 17 true (-1),
.cycle 0 36 true (-2),
.cycle 9 8 true (-1),
.last 14 (4,false),
.cycle 22 34 false (2)
])
theorem kid05_part489_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part489) = true := by rfl

def kid05_part490 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.cycle 34 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 6 true (-1),
.last 15 (5,false),
.cycle 12 2 true (-1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 21 1 false (-3),
.cycle 18 1 false (-2),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 17 1 false (-1),
.cycle 7 9 false (3),
.cycle 11 3 false (1),
.last 16 (5,false)
])
theorem kid05_part490_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part490) = true := by rfl

def kid05_part491 : Audit := .cycle 19 1 false (-1)
theorem kid05_part491_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part491) = true := by rfl

def kid05_part492 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 12 12 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 17 1 true (1),
.last 14 (5,false),
.cycle 12 7 false (0),
.cycle 12 4 false (0),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 0 25 true (-2),
.cycle 0 17 true (-1),
.cycle 0 36 true (-2),
.cycle 9 8 true (-1),
.cycle 20 1 true (-2),
.last 14 (5,false)
])
theorem kid05_part492_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part492) = true := by rfl

def kid05_part493 : Audit := .split 16 (5,false) (byMove [
.cycle 18 32 true (-2),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 4 true (-2),
.cycle 0 28 true (-2),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 12 6 true (-2),
.cycle 12 7 false (0),
.cycle 13 4 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 16 5 false (0),
.cycle 9 8 false (2),
.cycle 0 28 true (-2),
.cycle 12 9 false (0),
.last 17 (4,false),
.cycle 12 8 false (0)
])
theorem kid05_part493_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part493) = true := by rfl

def kid05_part494 : Audit := .cycle 1 12 true (1)
theorem kid05_part494_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part494) = true := by rfl

def kid05_part495 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 14 13 false (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 28 (4,false),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 13 1 true (1),
.cycle 15 8 false (1),
.cycle 14 5 false (0),
.last 15 (4,false),
.cycle 1 15 true (0),
.last 17 (4,false),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 13 1 true (1)
])
theorem kid05_part495_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part495) = true := by rfl

def kid05_part496 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 true (0),
.last 15 (5,false),
.cycle 17 1 false (-1),
.cycle 23 1 false (-1),
.cycle 0 17 true (0),
.last 20 (5,false),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 1 32 true (0),
.cycle 8 6 true (1),
.cycle 15 8 false (1),
.last 15 (5,false),
.cycle 9 20 true (-2),
.cycle 23 1 false (-1),
.cycle 16 1 false (0),
.last 20 (5,false),
.cycle 1 14 true (1),
.last 17 (5,false),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.last 24 (5,false)
])
theorem kid05_part496_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part496) = true := by rfl

def kid05_part497 : Audit := .cycle 0 13 true (0)
theorem kid05_part497_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part497) = true := by rfl

def kid05_part498 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 2 true (2),
.cycle 1 28 true (0),
.cycle 13 1 true (3),
.last 14 (5,false),
.cycle 7 8 true (1),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (4),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid05_part498_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part498) = true := by rfl

def kid05_part499 : Audit := .cycle 8 4 true (1)
theorem kid05_part499_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part499) = true := by rfl

def kid05_part500 : Audit := .cycle 13 6 false (1)
theorem kid05_part500_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part500) = true := by rfl

def kid05_part501 : Audit := .split 13 (5,false) (byMove [
.cycle 1 18 true (-2),
.cycle 22 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 17 3 false (0),
.cycle 14 3 false (1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 16 3 false (1),
.cycle 17 3 false (-2),
.cycle 14 3 false (-1),
.cycle 19 3 false (0),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 13 1 false (-1),
.cycle 12 5 false (1),
.cycle 9 5 false (2),
.cycle 1 16 true (-1),
.cycle 19 3 false (0),
.last 14 (4,false),
.cycle 18 3 false (-1)
])
theorem kid05_part501_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part501) = true := by rfl

def kid05_part502 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.cycle 1 25 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 9 14 true (-2),
.last 15 (5,false),
.cycle 12 2 true (-1),
.cycle 1 23 true (-1),
.cycle 1 25 true (-1),
.cycle 9 20 true (-2),
.cycle 9 14 false (2),
.cycle 9 19 false (2),
.cycle 9 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 18 (5,false),
.cycle 9 13 false (2),
.cycle 9 18 true (-2),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.last 16 (5,false)
])
theorem kid05_part502_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part502) = true := by rfl

def kid05_part503 : Audit := .cycle 19 1 false (-1)
theorem kid05_part503_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part503) = true := by rfl

def kid05_part504 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.last 25 (5,false),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.cycle 12 7 false (1),
.last 15 (5,false),
.cycle 13 2 true (-1),
.cycle 1 23 true (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 12 4 false (0),
.cycle 12 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 18 (5,false),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.last 16 (5,false)
])
theorem kid05_part504_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part504) = true := by rfl

def kid05_part505 : Audit := .split 16 (5,false) (byMove [
.cycle 9 9 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 8, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 393, 393, 128, 393, 393, 1, 393, 393, 4096],5136⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 6 true (-2),
.last 18 (4,false),
.cycle 9 18 true (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.cycle 13 4 false (0),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 18 5 false (0),
.cycle 12 6 false (0),
.cycle 14 3 false (0),
.cycle 5 12 false (3),
.cycle 11 6 false (1),
.cycle 12 11 false (0)
])
theorem kid05_part505_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part505) = true := by rfl

def kid05_part506 : Audit := .cycle 1 12 true (1)
theorem kid05_part506_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part506) = true := by rfl

def kid05_part507 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 5 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 17 5 false (1),
.cycle 16 5 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 17 5 false (1),
.cycle 17 5 false (-1),
.cycle 16 5 false (-1),
.cycle 19 5 false (1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 19 5 false (1),
.last 16 (4,false),
.cycle 18 5 false (0)
])
theorem kid05_part507_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part507) = true := by rfl

def kid05_part508 : Audit := .cycle 10 2 true (1)
theorem kid05_part508_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part508) = true := by rfl

def kid05_part509 : Audit := .cycle 0 13 true (0)
theorem kid05_part509_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part509) = true := by rfl

def kid05_part510 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.last 17 (5,false),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 26 2 true (4),
.cycle 3 11 true (1),
.cycle 13 1 true (3),
.last 14 (5,false),
.last 28 (5,false),
.last 17 (5,false),
.cycle 11 5 true (1),
.cycle 1 15 true (1),
.cycle 11 3 true (1),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.last 14 (5,false)
])
theorem kid05_part510_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part510) = true := by rfl

def kid05_part511 : Audit := .split 20 (5,false) (byMove [
.cycle 22 38 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.cycle 15 6 true (-2),
.cycle 0 34 true (-2),
.cycle 21 1 false (-1),
.last 21 (4,false),
.cycle 14 8 true (-2),
.cycle 13 9 false (1),
.cycle 15 6 false (0),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.last 21 (4,false),
.cycle 20 1 false (-2),
.cycle 18 5 false (0),
.cycle 9 12 false (2),
.cycle 0 34 true (-2),
.cycle 13 11 false (1),
.last 21 (4,false),
.cycle 12 10 false (2)
])
theorem kid05_part511_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part511) = true := by rfl

def kid05_part487 : Audit := .split 11 (4,true) (byMove [(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510),(kid05_part511)])

theorem kid05_part487_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part487) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510),(kid05_part511)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part488_checked

  · exact kid05_part494_checked

  · exact kid05_part500_checked

  · exact kid05_part506_checked

  · exact kid05_part489_checked

  · exact kid05_part495_checked

  · exact kid05_part501_checked

  · exact kid05_part507_checked

  · exact kid05_part490_checked

  · exact kid05_part496_checked

  · exact kid05_part502_checked

  · exact kid05_part508_checked

  · exact kid05_part491_checked

  · exact kid05_part497_checked

  · exact kid05_part503_checked

  · exact kid05_part509_checked

  · exact kid05_part492_checked

  · exact kid05_part498_checked

  · exact kid05_part504_checked

  · exact kid05_part510_checked

  · exact kid05_part493_checked

  · exact kid05_part499_checked

  · exact kid05_part505_checked

  · exact kid05_part511_checked

def kid05_part512 : Audit := .split 13 (5,false) (byMove [
.cycle 1 18 true (-2),
.cycle 21 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (-2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 9 7 false (2),
.cycle 1 18 true (-2),
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
.cycle 1 18 true (-2),
.cycle 21 3 false (-1),
.cycle 9 9 false (2),
.last 17 (4,true),
.last 16 (4,true)
]),
.cycle 13 1 false (-1),
.cycle 16 3 false (0),
.cycle 14 3 false (1),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 2 true (-1),
.cycle 17 3 false (1),
.cycle 28 3 false (4),
.last 17 (4,true),
.cycle 1 16 true (-1),
.last 15 (4,true),
.cycle 15 3 false (1),
.cycle 17 3 false (-1),
.cycle 15 3 false (0),
.cycle 19 3 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.last 16 (4,true),
.cycle 34 3 false (0),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 1 16 true (-1),
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
.cycle 8 15 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 9 7 false (2),
.cycle 12 3 false (0),
.cycle 13 3 false (-1),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 17 3 false (-3),
.cycle 15 3 false (-2),
.cycle 9 9 false (2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 20 3 false (-2),
.cycle 16 3 false (-2),
.cycle 15 3 false (-1),
.cycle 7 10 false (3),
.last 15 (4,true),
.cycle 11 4 false (1)
]),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 9 5 false (2),
.cycle 1 16 true (-1),
.cycle 18 3 false (0),
.split 14 (4,false) (byMove [
.cycle 9 7 false (2),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 6 9 false (3),
.cycle 50 3 false (-2),
.last 17 (4,true),
.cycle 1 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 17 3 false (-1),
.cycle 12 3 false (0),
.last 17 (4,true),
.cycle 18 3 false (0),
.last 15 (4,true),
.cycle 15 3 false (-1),
.cycle 19 3 false (-1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 1 16 true (-1),
.last 15 (4,true),
.cycle 17 3 false (-1)
]),
.cycle 17 3 false (-1)
])
theorem kid05_part512_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part512) = true := by rfl

def kid05_part513 : Audit := .cycle 0 11 true (0)
theorem kid05_part513_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part513) = true := by rfl

def kid05_part514 : Audit := .cycle 1 10 true (1)
theorem kid05_part514_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part514) = true := by rfl

def kid05_part515 : Audit := .cycle 2 9 true (1)
theorem kid05_part515_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part515) = true := by rfl

def kid05_part516 : Audit := .cycle 1 13 true (1)
theorem kid05_part516_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part516) = true := by rfl

def kid05_part518 : Audit := .cycle 1 12 true (1)
theorem kid05_part518_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part518) = true := by rfl

def kid05_part519 : Audit := .split 15 (5,false) (byMove [
.cycle 0 20 true (-2),
.cycle 22 5 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 23 5 false (-1),
.cycle 15 1 false (-1),
.cycle 17 5 false (1),
.cycle 16 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 0 20 true (-1),
.cycle 17 5 false (2),
.cycle 17 5 false (-1),
.cycle 16 5 false (0),
.cycle 19 5 false (1),
.cycle 16 1 false (-2),
.cycle 7 19 false (3),
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.cycle 9 7 false (3),
.cycle 0 18 true (-1),
.cycle 19 5 false (1),
.cycle 14 3 false (0),
.cycle 18 5 false (0)
])
theorem kid05_part519_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part519) = true := by rfl

def kid05_part520 : Audit := .cycle 10 2 true (2)
theorem kid05_part520_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part520) = true := by rfl

def kid05_part521 : Audit := .cycle 0 13 true (0)
theorem kid05_part521_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part521) = true := by rfl

def kid05_part522 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.last 20 (5,false),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 19 1 false (1),
.last 13 (5,false),
.last 17 (5,false),
.last 20 (5,false),
.cycle 12 2 true (1),
.cycle 1 14 true (1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (2),
.last 13 (5,false)
])
theorem kid05_part522_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part522) = true := by rfl

def kid05_part523 : Audit := .split 20 (5,false) (byMove [
.cycle 22 38 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 2 false (-2),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.cycle 15 6 true (-2),
.cycle 0 34 true (-2),
.cycle 21 1 false (-1),
.cycle 20 2 true (-2),
.cycle 14 8 true (-2),
.cycle 13 9 false (1),
.cycle 15 6 false (1),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.cycle 20 2 false (-2),
.cycle 20 1 false (-2),
.cycle 18 5 false (0),
.cycle 9 12 false (3),
.cycle 0 34 true (-2),
.cycle 13 11 false (1),
.cycle 14 8 false (1),
.cycle 12 10 false (2)
])
theorem kid05_part523_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part523) = true := by rfl

def kid05_part524 : Audit := .cycle 0 12 true (0)
theorem kid05_part524_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part524) = true := by rfl

def kid05_part525 : Audit := .cycle 1 11 true (1)
theorem kid05_part525_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part525) = true := by rfl

def kid05_part526 : Audit := .cycle 10 13 true (2)
theorem kid05_part526_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part526) = true := by rfl

def kid05_part527 : Audit := .cycle 3 9 true (1)
theorem kid05_part527_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part527) = true := by rfl

def kid05_part528 : Audit := .cycle 11 1 true (3)
theorem kid05_part528_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part528) = true := by rfl

def kid05_part529 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 30 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 28 (4,true),
.cycle 8 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 329728, 32, 2048, 8192, 16384, 8, 2176, 32, 2048, 8192, 16384, 512, 8320, 2048, 2048, 262144],[128, 2048, 1024, 1, 262144, 65536, 8192, 2048, 65536, 1, 262144, 65536, 8192, 2048, 65536, 64, 262144, 65536, 262144],262414⟩,
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 6 true (1),
.last 23 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part529_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part529) = true := by rfl

def kid05_part530 : Audit := .split 24 (5,false) (byMove [
.cycle 26 44 true (-2),
.cycle 15 16 false (1),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 15 12 false (1),
.cycle 24 1 false (-2),
.cycle 15 11 false (1),
.cycle 17 8 true (-2),
.cycle 0 40 true (-2),
.cycle 25 1 false (-1),
.cycle 15 12 false (1),
.cycle 16 10 true (-2),
.cycle 15 11 false (1),
.cycle 17 8 false (1),
.cycle 15 13 false (1),
.cycle 25 1 false (-3),
.cycle 15 12 false (1),
.cycle 24 1 false (-2),
.cycle 21 5 false (1),
.cycle 9 16 false (3),
.cycle 0 40 true (-2),
.cycle 15 13 false (1),
.cycle 15 12 false (1),
.cycle 14 12 false (2)
])
theorem kid05_part530_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part530) = true := by rfl

def kid05_part531 : Audit := .split 15 (5,false) (byMove [
.cycle 33 5 false (-1),
.cycle 22 5 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 17 5 false (-1),
.cycle 15 1 false (-1),
.cycle 17 5 false (1),
.cycle 16 5 false (2),
.cycle 19 5 false (3),
.cycle 16 1 false (0),
.last 19 (4,true),
.cycle 17 5 false (2),
.cycle 17 5 false (-1),
.cycle 16 5 false (0),
.cycle 19 5 false (1),
.cycle 16 1 false (-2),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.cycle 9 7 false (3),
.cycle 7 17 false (3),
.cycle 19 5 false (1),
.cycle 14 3 false (0),
.cycle 18 5 false (0)
])
theorem kid05_part531_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part531) = true := by rfl

def kid05_part532 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.last 17 (5,false),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.cycle 0 20 true (-2),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 17 true (2),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.last 14 (5,false),
.last 28 (5,false),
.last 17 (5,false),
.cycle 12 2 true (2),
.cycle 1 15 true (1),
.cycle 14 13 false (2),
.last 24 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (2),
.last 14 (5,false)
])
theorem kid05_part532_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part532) = true := by rfl

def kid05_part533 : Audit := .cycle 1 13 true (1)
theorem kid05_part533_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part533) = true := by rfl

def kid05_part534 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 true (1),
.last 20 (5,false),
.cycle 20 1 false (0),
.cycle 7 8 true (1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 32 1 false (6),
.cycle 8 5 true (1),
.last 17 (5,false),
.last 20 (5,false),
.cycle 12 2 true (1),
.cycle 5 8 true (1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 13 true (1),
.last 24 (5,false),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 11 3 true (2),
.last 17 (5,false)
])
theorem kid05_part534_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part534) = true := by rfl

def kid05_part535 : Audit := .split 20 (5,false) (byMove [
.cycle 22 51 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 2 false (-2),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.last 23 (4,true),
.cycle 1 45 true (-2),
.cycle 21 1 false (-1),
.last 23 (4,true),
.last 25 (4,true),
.cycle 13 9 false (1),
.cycle 15 6 false (1),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.cycle 20 2 false (-2),
.cycle 20 1 false (-2),
.cycle 18 5 false (0),
.last 23 (4,true),
.cycle 1 45 true (-2),
.cycle 13 11 false (1),
.last 25 (4,true),
.cycle 12 10 false (2)
])
theorem kid05_part535_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part535) = true := by rfl

def kid05_part536 : Audit := .cycle 0 12 true (0)
theorem kid05_part536_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part536) = true := by rfl

def kid05_part537 : Audit := .cycle 1 11 true (1)
theorem kid05_part537_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part537) = true := by rfl

def kid05_part538 : Audit := .cycle 2 10 true (1)
theorem kid05_part538_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part538) = true := by rfl

def kid05_part539 : Audit := .cycle 1 14 true (1)
theorem kid05_part539_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part539) = true := by rfl

def kid05_part540 : Audit := .cycle 11 1 true (3)
theorem kid05_part540_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part540) = true := by rfl

def kid05_part541 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 15 16 false (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 19 32 true (-2),
.cycle 3 10 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4),
.cycle 15 20 false (3),
.cycle 17 8 false (2),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (3),
.cycle 12 1 true (4)
])
theorem kid05_part541_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part541) = true := by rfl

def kid05_part517 : Audit := .split 11 (4,false) (byMove [(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534),(kid05_part535),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part541)])

theorem kid05_part517_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part517) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534),(kid05_part535),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part541)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part518_checked

  · exact kid05_part524_checked

  · exact kid05_part530_checked

  · exact kid05_part536_checked

  · exact kid05_part519_checked

  · exact kid05_part525_checked

  · exact kid05_part531_checked

  · exact kid05_part537_checked

  · exact kid05_part520_checked

  · exact kid05_part526_checked

  · exact kid05_part532_checked

  · exact kid05_part538_checked

  · exact kid05_part521_checked

  · exact kid05_part527_checked

  · exact kid05_part533_checked

  · exact kid05_part539_checked

  · exact kid05_part522_checked

  · exact kid05_part528_checked

  · exact kid05_part534_checked

  · exact kid05_part540_checked

  · exact kid05_part523_checked

  · exact kid05_part529_checked

  · exact kid05_part535_checked

  · exact kid05_part541_checked

def kid05_part542 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 22 5 false (0),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.last 21 (4,false),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 15 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.last 25 (4,false),
.cycle 1 14 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 11 2 true (2)
]),
.cycle 20 1 false (-2),
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
.last 27 (4,true),
.cycle 9 4 true (1),
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
.cycle 15 11 false (1),
.cycle 16 5 false (0),
.cycle 21 7 false (1),
.cycle 1 13 true (1),
.split 12 (4,true) (byMove [
.cycle 9 5 true (1),
.last 21 (4,false),
.cycle 20 1 false (0),
.cycle 7 8 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.last 21 (4,false),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.cycle 8 5 true (1),
.last 18 (4,false),
.last 21 (4,false),
.last 25 (4,false),
.cycle 5 8 true (1),
.last 15 (4,false),
.last 16 (4,false),
.cycle 1 13 true (1),
.last 25 (4,false),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 18 (4,false)
]),
.cycle 20 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.last 20 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 23 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.last 27 (4,true),
.last 20 (4,true),
.last 22 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 28 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
]),
.cycle 11 1 true (3)
])
theorem kid05_part542_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part542) = true := by rfl

def kid05_part422 : Audit := .split 10 (2,true) (byMove [(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part482),(kid05_part483),(kid05_part484),(kid05_part485),(kid05_part486),(kid05_part487),(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part542)])

theorem kid05_part422_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (kid05_part422) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part482),(kid05_part483),(kid05_part484),(kid05_part485),(kid05_part486),(kid05_part487),(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part542)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part423_checked

  · exact kid05_part453_checked

  · exact kid05_part483_checked

  · exact kid05_part513_checked

  · exact kid05_part424_checked

  · exact kid05_part454_checked

  · exact kid05_part484_checked

  · exact kid05_part514_checked

  · exact kid05_part425_checked

  · exact kid05_part455_checked

  · exact kid05_part485_checked

  · exact kid05_part515_checked

  · exact kid05_part426_checked

  · exact kid05_part456_checked

  · exact kid05_part486_checked

  · exact kid05_part516_checked

  · exact kid05_part427_checked

  · exact kid05_part457_checked

  · exact kid05_part487_checked

  · exact kid05_part517_checked

  · exact kid05_part452_checked

  · exact kid05_part482_checked

  · exact kid05_part512_checked

  · exact kid05_part542_checked

def kid05_part543 : Audit := .cycle 0 11 true (0)
theorem kid05_part543_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,2⟩)) (kid05_part543) = true := by rfl

def kid05_part544 : Audit := .cycle 14 1 false (0)
theorem kid05_part544_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,3⟩)) (kid05_part544) = true := by rfl

def kid05_part547 : Audit := .cycle 1 13 true (0)
theorem kid05_part547_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part547) = true := by rfl

def kid05_part548 : Audit := .cycle 11 6 false (2)
theorem kid05_part548_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part548) = true := by rfl

def kid05_part549 : Audit := .cycle 16 1 false (0)
theorem kid05_part549_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part549) = true := by rfl

def kid05_part550 : Audit := .cycle 0 14 true (0)
theorem kid05_part550_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part550) = true := by rfl

def kid05_part551 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 0 16 false (3),
.cycle 0 15 true (0),
.cycle 0 16 false (3),
.cycle 11 6 false (2),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 11 13 false (3),
.cycle 11 11 false (2),
.cycle 0 15 true (0),
.last 14 (5,false),
.cycle 11 8 false (2),
.last 15 (5,false),
.cycle 0 20 true (-2),
.cycle 1 15 true (0),
.cycle 11 6 false (2),
.cycle 11 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.last 14 (5,false)
])
theorem kid05_part551_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part551) = true := by rfl

def kid05_part552 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (-2),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.cycle 11 7 false (2),
.cycle 11 9 false (2),
.cycle 11 9 false (2),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 11 6 false (2),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 11 8 false (2),
.cycle 11 8 false (2),
.cycle 0 16 true (0),
.cycle 1 17 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part552_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part552) = true := by rfl

def kid05_part553 : Audit := .cycle 0 13 true (0)
theorem kid05_part553_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part553) = true := by rfl

def kid05_part554 : Audit := .cycle 11 12 true (1)
theorem kid05_part554_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part554) = true := by rfl

def kid05_part555 : Audit := .cycle 0 27 true (0)
theorem kid05_part555_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part555) = true := by rfl

def kid05_part556 : Audit := .cycle 3 10 true (0)
theorem kid05_part556_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part556) = true := by rfl

def kid05_part557 : Audit := .cycle 0 14 true (0)
theorem kid05_part557_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part557) = true := by rfl

def kid05_part558 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 11 21 true (0),
.cycle 0 27 true (0),
.cycle 0 15 true (0),
.cycle 13 1 true (3),
.last 17 (4,true),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 9 5 true (0),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 11 12 true (1),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.cycle 13 1 true (3)
])
theorem kid05_part558_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part558) = true := by rfl

def kid05_part559 : Audit := .split 16 (4,true) (byMove [
.cycle 11 7 false (2),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 22 true (-2),
.last 17 (5,false),
.cycle 1 17 true (0),
.last 18 (5,false),
.cycle 11 12 false (2),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.cycle 11 9 false (2),
.cycle 11 11 false (2),
.cycle 11 13 false (2),
.cycle 1 19 true (-1),
.cycle 17 1 false (-1),
.cycle 11 8 false (2),
.last 17 (5,false),
.cycle 1 17 true (0),
.cycle 11 10 false (2),
.cycle 11 12 false (2),
.cycle 0 18 true (0),
.cycle 1 19 true (0),
.cycle 15 2 true (0)
])
theorem kid05_part559_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part559) = true := by rfl

def kid05_part560 : Audit := .cycle 11 6 false (2)
theorem kid05_part560_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part560) = true := by rfl

def kid05_part561 : Audit := .cycle 11 11 false (2)
theorem kid05_part561_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part561) = true := by rfl

def kid05_part562 : Audit := .cycle 1 14 true (0)
theorem kid05_part562_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part562) = true := by rfl

def kid05_part563 : Audit := .split 13 (4,true) (byMove [
.cycle 10 4 true (0),
.last 15 (5,false),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 0 16 false (3),
.cycle 11 6 false (2),
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 9 6 true (0),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.cycle 8 6 true (0),
.cycle 11 8 false (2),
.last 15 (5,false),
.cycle 11 6 false (2),
.cycle 11 9 false (2),
.cycle 11 6 false (2),
.cycle 11 6 false (2),
.cycle 1 14 true (0),
.cycle 11 10 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.cycle 1 16 true (0),
.cycle 13 2 true (1)
])
theorem kid05_part563_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part563) = true := by rfl

def kid05_part564 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 false (2),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 20 true (-2),
.last 15 (5,false),
.cycle 11 9 false (2),
.last 16 (5,false),
.last 16 (5,false),
.cycle 1 16 true (0),
.cycle 0 18 true (0),
.cycle 11 7 false (2),
.cycle 11 9 false (2),
.cycle 11 9 false (2),
.cycle 11 11 false (2),
.cycle 15 1 false (-1),
.cycle 11 6 false (2),
.last 15 (5,false),
.cycle 1 19 true (0),
.cycle 11 8 false (2),
.cycle 11 8 false (2),
.cycle 1 16 true (0),
.cycle 1 18 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part564_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part564) = true := by rfl

def kid05_part565 : Audit := .cycle 0 13 true (0)
theorem kid05_part565_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part565) = true := by rfl

def kid05_part566 : Audit := .cycle 1 12 true (0)
theorem kid05_part566_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part566) = true := by rfl

def kid05_part567 : Audit := .cycle 2 11 true (0)
theorem kid05_part567_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part567) = true := by rfl

def kid05_part568 : Audit := .cycle 1 15 true (0)
theorem kid05_part568_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part568) = true := by rfl

def kid05_part569 : Audit := .cycle 1 14 true (0)
theorem kid05_part569_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part569) = true := by rfl

def kid05_part570 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.last 16 (4,true),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 24 15 true (2),
.cycle 3 11 true (0),
.cycle 0 15 true (0),
.cycle 13 1 true (3),
.last 17 (4,true),
.last 16 (4,true),
.last 16 (4,true),
.cycle 1 15 true (0),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.cycle 13 1 true (3)
])
theorem kid05_part570_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part570) = true := by rfl

def kid05_part546 : Audit := .split 12 (2,true) (byMove [(kid05_part547),(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564),(kid05_part565),(kid05_part566),(kid05_part567),(kid05_part568),(kid05_part569),(kid05_part570)])

theorem kid05_part546_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part546) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid05_part547),(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564),(kid05_part565),(kid05_part566),(kid05_part567),(kid05_part568),(kid05_part569),(kid05_part570)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part547_checked

  · exact kid05_part553_checked

  · exact kid05_part559_checked

  · exact kid05_part565_checked

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

def kid05_part572 : Audit := .cycle 0 12 false (3)
theorem kid05_part572_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part572) = true := by rfl

def kid05_part573 : Audit := .split 26 (2,true) (byMove [
.cycle 18 19 true (-3),
.cycle 18 36 false (4),
.cycle 18 51 false (3),
.cycle 1 41 false (5),
.last 27 (4,true),
.last 28 (4,true),
.last 162 (4,true),
.last 62 (4,true),
.cycle 1 37 false (4),
.cycle 1 35 false (3),
.cycle 18 19 true (-3),
.cycle 18 19 true (-3),
.last 30 (4,true),
.last 63 (4,true),
.cycle 129 45 true (-2),
.cycle 1 41 false (5),
.last 27 (4,true),
.last 28 (4,true),
.last 39 (4,true),
.last 38 (4,true),
.cycle 18 17 true (-3),
.last 174 (4,true),
.last 30 (4,true),
.last 30 (4,true)
])
theorem kid05_part573_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part573) = true := by rfl

def kid05_part574 : Audit := .cycle 13 1 false (-1)
theorem kid05_part574_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part574) = true := by rfl

def kid05_part575 : Audit := .cycle 12 1 false (-2)
theorem kid05_part575_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part575) = true := by rfl

def kid05_part576 : Audit := .cycle 61 28 false (0)
theorem kid05_part576_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part576) = true := by rfl

def kid05_part577 : Audit := .cycle 11 1 false (-1)
theorem kid05_part577_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part577) = true := by rfl

def kid05_part578 : Audit := .split 14 (2,true) (byMove [
.cycle 12 19 true (-2),
.cycle 0 21 true (-2),
.cycle 18 1 false (0),
.cycle 0 16 true (-1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 0 27 true (-1),
.cycle 0 31 true (-1),
.cycle 3 12 true (-1),
.cycle 12 19 true (-2),
.cycle 0 16 true (-1),
.last 18 (4,true),
.cycle 0 28 true (-2),
.cycle 0 26 true (-1),
.cycle 1 16 true (-1),
.last 15 (4,true),
.last 16 (4,true),
.last 27 (4,true),
.last 26 (4,true),
.cycle 12 17 true (-2),
.cycle 1 17 true (-1),
.last 18 (4,true),
.cycle 0 16 true (-1)
])
theorem kid05_part578_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part578) = true := by rfl

def kid05_part579 : Audit := .cycle 0 15 true (-1)
theorem kid05_part579_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part579) = true := by rfl

def kid05_part580 : Audit := .cycle 13 1 false (1)
theorem kid05_part580_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part580) = true := by rfl

def kid05_part581 : Audit := .cycle 12 1 false (0)
theorem kid05_part581_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part581) = true := by rfl

def kid05_part582 : Audit := .cycle 0 32 true (-2)
theorem kid05_part582_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part582) = true := by rfl

def kid05_part583 : Audit := .cycle 0 19 true (-1)
theorem kid05_part583_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part583) = true := by rfl

def kid05_part584 : Audit := .split 38 (4,true) (byMove [
.last 41 (2,true),
.proven (BB6.Agent11Raw39Pumps.M275.table) (fun m hm => BB6.Agent11Raw39Pumps.M275.never m hm),
.last 39 (2,true),
.last 67 (2,true),
.last 65 (2,true),
.last 79 (2,true),
.last 125 (2,true),
.cycle 67 25 false (0),
.last 39 (2,true),
.cycle 18 21 true (-2),
.last 55 (2,true),
.proven (BB6.Agent11Raw39Pumps.M276.table) (fun m hm => BB6.Agent11Raw39Pumps.M276.never m hm),
.last 89 (2,true),
.last 46 (2,true),
.last 39 (2,true),
.cycle 119 1 false (-7),
.cycle 45 36 false (4),
.proven (BB6.Agent11Raw39Pumps.M277.table) (fun m hm => BB6.Agent11Raw39Pumps.M277.never m hm),
.cycle 20 40 true (-1),
.cycle 64 22 false (0),
.last 39 (2,true),
.cycle 18 21 true (-2),
.cycle 70 24 false (0),
.cycle 37 2 true (0)
])
theorem kid05_part584_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part584) = true := by rfl

def kid05_part585 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 false (3),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 0 19 true (-2),
.last 14 (4,true),
.last 38 (4,true),
.last 94 (4,true),
.cycle 0 17 true (-2),
.last 65 (4,true),
.cycle 3 35 false (3),
.cycle 1 14 false (3),
.last 24 (4,true),
.last 42 (4,true),
.cycle 10 4 false (0),
.cycle 18 37 true (-2),
.cycle 0 19 true (-2),
.last 14 (4,true),
.last 38 (4,true),
.last 29 (4,true),
.cycle 0 17 true (-2),
.cycle 2 12 false (3),
.last 112 (4,true),
.last 42 (4,true),
.last 34 (4,true)
])
theorem kid05_part585_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part585) = true := by rfl

def kid05_part586 : Audit := .split 16 (2,true) (byMove [
.cycle 12 19 true (-2),
.cycle 0 23 true (-2),
.cycle 20 1 false (0),
.cycle 31 1 false (-1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 34 true (-2),
.cycle 0 29 true (-2),
.cycle 0 35 true (-2),
.cycle 3 14 true (-2),
.cycle 12 19 true (-2),
.cycle 0 20 true (-2),
.last 20 (4,true),
.cycle 0 30 true (-2),
.cycle 0 28 true (-2),
.cycle 31 1 false (-1),
.last 17 (4,true),
.last 18 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.cycle 12 17 true (-2),
.cycle 13 19 true (-1),
.last 20 (4,true),
.last 20 (4,true)
])
theorem kid05_part586_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part586) = true := by rfl

def kid05_part587 : Audit := .cycle 12 1 false (-2)
theorem kid05_part587_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part587) = true := by rfl

def kid05_part588 : Audit := .split 18 (2,true) (byMove [
.cycle 12 19 true (-3),
.cycle 12 28 false (4),
.cycle 12 43 false (3),
.last 32 (4,true),
.last 19 (4,true),
.last 20 (4,true),
.last 31 (4,true),
.last 46 (4,true),
.cycle 9 21 false (4),
.cycle 9 19 false (3),
.cycle 12 19 true (-3),
.cycle 12 11 true (-3),
.last 22 (4,true),
.last 47 (4,true),
.last 45 (4,true),
.last 32 (4,true),
.last 19 (4,true),
.last 20 (4,true),
.last 31 (4,true),
.last 30 (4,true),
.cycle 12 17 true (-3),
.last 33 (4,true),
.last 22 (4,true),
.last 20 (4,true)
])
theorem kid05_part588_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part588) = true := by rfl

def kid05_part589 : Audit := .cycle 11 1 false (-1)
theorem kid05_part589_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part589) = true := by rfl

def kid05_part590 : Audit := .split 14 (2,true) (byMove [
.last 27 (4,true),
.last 17 (4,true),
.cycle 19 1 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 0 27 true (-1),
.cycle 0 35 true (-3),
.cycle 7 43 false (3),
.last 27 (4,true),
.last 31 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.cycle 0 34 true (-2),
.cycle 1 16 true (-1),
.last 15 (4,true),
.last 16 (4,true),
.last 27 (4,true),
.last 26 (4,true),
.last 25 (4,true),
.cycle 1 17 true (-1),
.last 18 (4,true),
.last 28 (4,true)
])
theorem kid05_part590_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part590) = true := by rfl

def kid05_part591 : Audit := .cycle 0 15 true (-1)
theorem kid05_part591_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part591) = true := by rfl

def kid05_part592 : Audit := .cycle 0 30 true (-2)
theorem kid05_part592_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part592) = true := by rfl

def kid05_part593 : Audit := .split 16 (2,true) (byMove [
.cycle 15 19 true (-2),
.cycle 0 23 true (-2),
.cycle 20 1 false (0),
.cycle 0 18 true (-1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 17 true (-1),
.cycle 0 29 true (-1),
.cycle 0 35 true (-1),
.cycle 3 14 true (-1),
.cycle 15 19 true (-2),
.cycle 1 20 true (-1),
.last 20 (4,true),
.cycle 0 30 true (-2),
.cycle 0 28 true (-1),
.cycle 1 18 true (-1),
.last 17 (4,true),
.last 18 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.cycle 15 17 true (-2),
.cycle 1 19 true (-1),
.last 20 (4,true),
.cycle 1 20 true (-1)
])
theorem kid05_part593_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part593) = true := by rfl

def kid05_part594 : Audit := .cycle 9 3 false (1)
theorem kid05_part594_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part594) = true := by rfl

def kid05_part595 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.last 24 (2,true),
.last 16 (2,true),
.cycle 7 11 false (3),
.cycle 79 46 false (0),
.last 36 (2,true),
.cycle 1 16 true (-1),
.cycle 17 1 true (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 0 30 true (-1),
.last 26 (2,true),
.last 36 (2,true),
.last 59 (2,true),
.last 16 (2,true),
.cycle 5 11 false (3),
.cycle 63 52 true (-4),
.cycle 16 3 false (0),
.cycle 0 33 true (-1),
.cycle 7 43 false (3),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 7 55 false (3),
.cycle 14 2 true (1)
])
theorem kid05_part595_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part595) = true := by rfl

def kid05_part571 : Audit := .split 11 (5,false) (byMove [(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592),(kid05_part593),(kid05_part594),(kid05_part595)])

theorem kid05_part571_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part571) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (5,false) (some mv)) (byMove [(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592),(kid05_part593),(kid05_part594),(kid05_part595)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part572_checked

  · exact kid05_part578_checked

  · exact kid05_part584_checked

  · exact kid05_part590_checked

  · exact kid05_part573_checked

  · exact kid05_part579_checked

  · exact kid05_part585_checked

  · exact kid05_part591_checked

  · exact kid05_part574_checked

  · exact kid05_part580_checked

  · exact kid05_part586_checked

  · exact kid05_part592_checked

  · exact kid05_part575_checked

  · exact kid05_part581_checked

  · exact kid05_part587_checked

  · exact kid05_part593_checked

  · exact kid05_part576_checked

  · exact kid05_part582_checked

  · exact kid05_part588_checked

  · exact kid05_part594_checked

  · exact kid05_part577_checked

  · exact kid05_part583_checked

  · exact kid05_part589_checked

  · exact kid05_part595_checked

def kid05_part596 : Audit := .split 10 (2,true) (byMove [
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.last 18 (4,true),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.last 18 (4,true),
.cycle 9 3 false (1),
.last 15 (4,true)
]),
.cycle 16 1 false (0),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 13 1 false (1),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 24 1 false (2),
.cycle 15 1 false (5),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.cycle 8 6 true (0),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 16 1 false (0),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 16 1 false (-2),
.split 14 (5,false) (byMove [
.cycle 2 21 false (3),
.cycle 25 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 17 1 false (-3),
.cycle 14 1 false (-2),
.cycle 20 1 false (-2),
.cycle 11 4 true (-2),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 20 1 false (-4),
.cycle 11 4 false (0),
.cycle 22 1 false (-2),
.cycle 15 1 false (-3),
.cycle 17 1 false (-3),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 21 1 false (-3),
.cycle 30 1 false (-2),
.cycle 22 1 false (-2),
.cycle 9 6 false (1),
.last 17 (4,true)
]),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 28 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 0 17 true (-1),
.cycle 10 2 true (-1),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-3),
.cycle 17 1 false (-3),
.last 18 (4,true),
.cycle 12 1 false (-2),
.cycle 14 1 false (-2),
.cycle 11 1 false (-1),
.last 16 (4,true),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 7 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
]),
.split 14 (4,true) (byMove [
.cycle 16 18 true (0),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 18 1 false (2),
.cycle 18 1 false (0),
.cycle 20 1 false (-2),
.cycle 36 1 false (-2),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 19 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.cycle 13 2 true (0)
]),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (0),
.split 11 (5,false) (byMove [
.cycle 1 16 true (0),
.cycle 24 1 false (-2),
.cycle 10 2 true (0),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (0),
.cycle 32 1 false (0),
.cycle 32 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.last 14 (4,true),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (0),
.last 14 (4,true),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
])
theorem kid05_part596_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part596) = true := by rfl

def kid05_part597 : Audit := .cycle 15 1 false (-1)
theorem kid05_part597_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part597) = true := by rfl

def kid05_part599 : Audit := .cycle 0 15 true (-1)
theorem kid05_part599_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part599) = true := by rfl

def kid05_part600 : Audit := .cycle 19 1 false (-1)
theorem kid05_part600_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part600) = true := by rfl

def kid05_part601 : Audit := .cycle 12 1 false (0)
theorem kid05_part601_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part601) = true := by rfl

def kid05_part602 : Audit := .cycle 11 1 false (-1)
theorem kid05_part602_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part602) = true := by rfl

def kid05_part603 : Audit := .cycle 11 1 false (-1)
theorem kid05_part603_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part603) = true := by rfl

def kid05_part604 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 false (3),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 15 1 false (1),
.cycle 15 1 false (-3),
.last 13 (2,true),
.last 16 (2,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.last 16 (2,true),
.cycle 9 3 false (1),
.cycle 23 1 false (-3)
])
theorem kid05_part604_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part604) = true := by rfl

def kid05_part605 : Audit := .cycle 14 1 false (0)
theorem kid05_part605_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part605) = true := by rfl

def kid05_part606 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (0),
.last 14 (5,false),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 24 1 false (2),
.last 13 (5,false),
.cycle 16 1 false (0),
.last 14 (5,false),
.cycle 1 16 true (0),
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 0 29 true (0),
.last 13 (5,false)
])
theorem kid05_part606_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part606) = true := by rfl

def kid05_part607 : Audit := .cycle 0 13 true (0)
theorem kid05_part607_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part607) = true := by rfl

def kid05_part608 : Audit := .cycle 11 1 false (1)
theorem kid05_part608_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part608) = true := by rfl

def kid05_part609 : Audit := .cycle 11 1 false (1)
theorem kid05_part609_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part609) = true := by rfl

def kid05_part610 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 22 1 false (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.cycle 13 1 false (1),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 15 1 false (1)
])
theorem kid05_part610_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part610) = true := by rfl

def kid05_part611 : Audit := .cycle 14 1 false (-2)
theorem kid05_part611_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part611) = true := by rfl

def kid05_part612 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.last 14 (5,false),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 7 7 false (3),
.cycle 0 31 true (-1),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 9 5 false (1),
.last 13 (5,false),
.cycle 16 1 false (-2),
.last 14 (5,false),
.cycle 26 1 false (0),
.cycle 1 18 true (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.last 18 (5,false),
.cycle 25 5 false (1),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 16 (5,false),
.last 13 (5,false)
])
theorem kid05_part612_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part612) = true := by rfl

def kid05_part613 : Audit := .cycle 16 1 false (0)
theorem kid05_part613_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part613) = true := by rfl

def kid05_part614 : Audit := .cycle 11 1 false (-1)
theorem kid05_part614_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part614) = true := by rfl

def kid05_part615 : Audit := .cycle 11 1 false (-1)
theorem kid05_part615_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part615) = true := by rfl

def kid05_part616 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.last 27 (2,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 14 (2,true),
.cycle 0 17 true (-1),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-3),
.last 13 (2,true),
.last 16 (2,true),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 14 (2,true),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 7 7 false (3),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
])
theorem kid05_part616_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part616) = true := by rfl

def kid05_part617 : Audit := .cycle 1 15 true (0)
theorem kid05_part617_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part617) = true := by rfl

def kid05_part618 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 0 27 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 1 15 true (0),
.last 13 (5,false),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.cycle 20 1 false (0),
.cycle 1 14 true (0),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.cycle 1 14 true (0),
.last 13 (5,false)
])
theorem kid05_part618_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part618) = true := by rfl

def kid05_part619 : Audit := .cycle 0 13 true (0)
theorem kid05_part619_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part619) = true := by rfl

def kid05_part620 : Audit := .cycle 16 1 false (0)
theorem kid05_part620_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part620) = true := by rfl

def kid05_part621 : Audit := .cycle 9 2 true (0)
theorem kid05_part621_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part621) = true := by rfl

def kid05_part622 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 22 1 false (-2),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 1 12 true (0),
.last 27 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 4 true (2),
.cycle 8 4 true (0),
.cycle 15 1 false (-1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 12 2 true (0),
.cycle 13 1 false (-1),
.cycle 1 12 true (0),
.cycle 13 2 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 12 2 true (1)
])
theorem kid05_part622_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part622) = true := by rfl

def kid05_part598 : Audit := .split 10 (4,true) (byMove [(kid05_part599),(kid05_part600),(kid05_part601),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619),(kid05_part620),(kid05_part621),(kid05_part622)])

theorem kid05_part598_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part598) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part599),(kid05_part600),(kid05_part601),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619),(kid05_part620),(kid05_part621),(kid05_part622)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part599_checked

  · exact kid05_part605_checked

  · exact kid05_part611_checked

  · exact kid05_part617_checked

  · exact kid05_part600_checked

  · exact kid05_part606_checked

  · exact kid05_part612_checked

  · exact kid05_part618_checked

  · exact kid05_part601_checked

  · exact kid05_part607_checked

  · exact kid05_part613_checked

  · exact kid05_part619_checked

  · exact kid05_part602_checked

  · exact kid05_part608_checked

  · exact kid05_part614_checked

  · exact kid05_part620_checked

  · exact kid05_part603_checked

  · exact kid05_part609_checked

  · exact kid05_part615_checked

  · exact kid05_part621_checked

  · exact kid05_part604_checked

  · exact kid05_part610_checked

  · exact kid05_part616_checked

  · exact kid05_part622_checked

def kid05_part623 : Audit := .split 12 (5,false) (byMove [
.cycle 14 26 true (-2),
.cycle 10 10 false (0),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.cycle 10 5 false (0),
.split 14 (2,true) (byMove [
.cycle 0 19 true (-2),
.cycle 10 14 true (-2),
.cycle 17 1 false (-1),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 256, 2, 8192, 16384, 8, 17024, 17024, 2, 524288, 1048576, 512, 128, 16777216, 128, 524288, 1048576, 2097152, 20717568, 20717568, 524288, 16777216],[128, 256, 17024, 1, 16777216, 17025, 8192, 17024, 16512, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 7 9 false (3),
.cycle 15 12 true (1),
.cycle 0 17 true (-2),
.cycle 10 10 true (-2),
.cycle 15 14 true (0),
.cycle 17 13 true (1),
.cycle 10 7 false (0),
.cycle 12 4 true (-2),
.cycle 1 35 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 256, 2, 8192, 16384, 8, 17024, 17024, 2, 524288, 1048576, 512, 128, 16777216, 128, 524288, 1048576, 2097152, 20717568, 20717568, 524288, 16777216],[128, 256, 17025, 1, 16777216, 17025, 8192, 17024, 17024, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 15 (4,true),
.cycle 10 5 false (0),
.last 18 (4,true),
.last 27 (4,true),
.cycle 0 17 true (-2),
.cycle 4 11 false (3),
.last 17 (4,true),
.cycle 17 13 true (1)
]),
.cycle 0 22 true (-2),
.cycle 13 1 false (-1),
.cycle 11 2 true (-2),
.cycle 10 4 true (-2),
.cycle 10 5 false (0),
.split 14 (2,true) (byMove [
.cycle 10 15 false (2),
.cycle 12 4 false (-2),
.cycle 17 1 false (-3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 16384, 128, 8192, 16384, 8, 128, 16384, 128, 33554432, 67108864, 2097152, 128, 1073741824, 128, 33554432, 67108864, 2097152, 16512, 1327775872, 1327775872, 33554432, 67108864, 134217728, 1327775872, 1327775872, 1327775872, 1073741824],[128, 16384, 2113536, 1, 1073741824, 128, 8192, 16384, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 1327775872, 2113536, 262144, 1073741824, 1327775872, 33554432, 1327775872, 1327775872, 16777216, 1073741824, 1327775872, 1073741824],2144153664⟩,
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 7 9 false (3),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.cycle 0 26 true (-3),
.cycle 10 10 false (0),
.cycle 12 6 false (-1),
.last 21 (4,true),
.cycle 10 7 false (0),
.cycle 12 4 false (-2),
.cycle 10 17 false (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 16384, 128, 8192, 16384, 8, 128, 16384, 128, 33554432, 67108864, 2097152, 128, 1073741824, 128, 33554432, 67108864, 2097152, 16512, 1327775872, 1327775872, 33554432, 67108864, 134217728, 1327775872, 1327775872, 1327775872, 1073741824],[128, 16384, 16512, 1, 1073741824, 128, 8192, 16384, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 1327775872, 16512, 262144, 1073741824, 1327775872, 33554432, 1327775872, 1327775872, 16777216, 1073741824, 1327775872, 1073741824],2144153664⟩,
.last 15 (4,true),
.cycle 10 5 false (0),
.last 18 (4,true),
.last 29 (4,true),
.cycle 10 13 false (2),
.cycle 4 11 false (3),
.last 17 (4,true),
.cycle 10 7 false (0)
]),
.cycle 10 7 false (0),
.cycle 13 1 false (-3),
.cycle 11 2 false (-1),
.cycle 12 1 false (-2),
.split 16 (4,true) (byMove [
.last 19 (2,true),
.last 22 (2,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 21 (2,true),
.cycle 12 5 false (0),
.cycle 0 21 true (-2),
.cycle 0 23 true (-2),
.last 17 (2,true),
.last 20 (2,true),
.last 22 (2,true),
.cycle 10 7 false (0),
.cycle 10 9 false (0),
.last 18 (2,true),
.last 40 (2,true),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.cycle 14 5 false (0),
.cycle 0 21 true (-2),
.cycle 10 8 false (0),
.last 17 (2,true),
.last 20 (2,true),
.cycle 15 4 true (-2),
.cycle 15 2 true (-2)
]),
.split 14 (2,true) (byMove [
.cycle 0 19 true (-2),
.cycle 10 6 false (0),
.cycle 18 1 false (-2),
.proven (BB6.Agent11Raw39Pumps.M283.table) (fun m hm => BB6.Agent11Raw39Pumps.M283.never m hm),
.last 15 (4,true),
.last 16 (4,true),
.last 20 (4,true),
.cycle 15 12 true (1),
.cycle 0 17 true (-2),
.cycle 3 12 false (3),
.last 31 (4,true),
.last 20 (4,true),
.last 18 (4,true),
.cycle 10 6 false (0),
.cycle 10 11 false (0),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 3, 2, 2],[268435456, 131072, 512, 512, 32, 268435456, 268436480, 131072, 268435456, 512, 131072, 268436480, 268435456, 1082261504, 402653696, 134217728, 8388608, 268435456, 1346371584, 1082261504, 1348501504, 2097152, 8388608, 1346371584, 4194304, 131072, 1346371584, 32768, 131072, 4194304, 1073741824],[268435456, 32, 512, 131072, 1073741824, 1024, 268436480, 131072, 512, 131072, 1073741824, 1024, 268435456, 8388608, 134217728, 8519680, 1073741824, 268435456, 1346371584, 8388608, 2097152, 1082261504, 1073741824, 4194304, 4194304, 131072, 32768, 131072, 1073741824, 65536, 1073741824],1708990464⟩,
.last 15 (4,true),
.last 16 (4,true),
.last 18 (4,true),
.last 27 (4,true),
.cycle 0 17 true (-2),
.last 22 (4,true),
.last 17 (4,true),
.last 18 (4,true)
]),
.cycle 0 22 true (-2),
.cycle 10 7 false (0),
.cycle 9 4 false (1),
.split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 10 13 false (0),
.last 16 (2,true),
.cycle 10 9 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 0, 64],64⟩,
.cycle 10 6 false (0),
.last 18 (2,true),
.cycle 23 1 true (1),
.last 16 (2,true),
.cycle 0 26 true (-2),
.cycle 24 1 true (2),
.cycle 8 8 false (2),
.cycle 10 8 false (0),
.cycle 12 5 false (0),
.last 16 (2,true),
.cycle 10 9 false (0),
.cycle 11 6 false (0),
.cycle 10 6 false (0),
.last 18 (2,true),
.cycle 10 10 false (0),
.last 16 (2,true),
.cycle 7 18 false (3),
.cycle 14 4 true (-1),
.cycle 14 2 true (-1)
])
])
theorem kid05_part623_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part623) = true := by rfl

def kid05_part624 : Audit := .cycle 1 10 true (1)
theorem kid05_part624_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part624) = true := by rfl

def kid05_part625 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 12 11 false (0),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 26 1 false (2),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 18 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 1 15 true (0),
.cycle 36 1 false (0),
.cycle 11 2 true (0)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 12 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 12 true (-1),
.cycle 13 12 true (-2),
.cycle 0 13 true (0),
.cycle 13 12 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 12 true (1),
.cycle 13 12 true (0),
.cycle 14 12 true (-3),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 12 true (-2),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 12 true (-1),
.cycle 1 15 true (0),
.cycle 13 12 true (1),
.cycle 11 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.split 15 (2,true) (byMove [
.cycle 0 20 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 2, 128, 8192, 16384, 8, 128, 2, 128, 33554432, 67108864, 2097152, 128, 524288, 16777216, 33554432, 67108864, 134217728, 2097152, 33554432, 1327497216, 33554432, 67108864, 134217728, 1327497216, 33554432, 1327497216, 1073741824],[128, 16384, 1327513600, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 16384, 16777216, 1073741824, 33554432, 33554432, 1327497216, 1327497216, 16777216, 1073741824, 1327497216, 1073741824],2145334622⟩,
.last 16 (4,true),
.cycle 12 6 false (0),
.cycle 7 10 false (3),
.cycle 16 13 true (0),
.cycle 0 18 true (-2),
.cycle 12 11 false (0),
.cycle 16 14 true (-1),
.last 42 (4,true),
.cycle 12 8 false (0),
.cycle 12 4 false (0),
.cycle 1 37 false (3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1327497216, 2, 128, 8192, 16384, 8, 128, 2, 128, 33554432, 67108864, 2097152, 128, 524288, 16777216, 33554432, 67108864, 134217728, 2097152, 33554432, 1325400064, 33554432, 67108864, 134217728, 1325400064, 33554432, 1325400064, 1073741824],[128, 16384, 1327497216, 1, 1073741824, 16384, 8192, 2097152, 128, 1, 1073741824, 1073741824, 33554432, 1073741824, 128, 262144, 1073741824, 1073741824, 33554432, 33554432, 2097152, 16777216, 1073741824, 33554432, 33554432, 1325400064, 1325400064, 16777216, 1073741824, 1325400064, 1073741824],2145334622⟩,
.last 16 (4,true),
.cycle 12 6 false (0),
.last 19 (4,true),
.last 31 (4,true),
.cycle 0 18 true (-2),
.cycle 4 12 false (3),
.cycle 27 14 true (-1),
.cycle 12 8 false (0)
]),
.split 12 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 19 true (-1),
.last 27 (4,true),
.cycle 20 10 true (-3),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 26 true (-2),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 0 20 true (-2),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 13 3 false (-1),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 23 3 false (4),
.cycle 14 3 false (1),
.cycle 16 3 false (-1),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 13 3 false (-1),
.cycle 1 13 true (0),
.cycle 15 3 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 9 17 true (0),
.cycle 12 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1)
])
theorem kid05_part625_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part625) = true := by rfl

def kid05_part627 : Audit := .cycle 0 11 true (0)
theorem kid05_part627_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part627) = true := by rfl

def kid05_part628 : Audit := .cycle 1 10 true (1)
theorem kid05_part628_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part628) = true := by rfl

def kid05_part629 : Audit := .cycle 21 1 false (1)
theorem kid05_part629_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part629) = true := by rfl

def kid05_part630 : Audit := .cycle 1 13 true (0)
theorem kid05_part630_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part630) = true := by rfl

def kid05_part631 : Audit := .cycle 24 1 false (2)
theorem kid05_part631_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part631) = true := by rfl

def kid05_part632 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 28 true (0),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 13 6 false (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 0 27 true (0),
.cycle 11 1 true (1)
])
theorem kid05_part632_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part632) = true := by rfl

def kid05_part633 : Audit := .cycle 0 11 true (0)
theorem kid05_part633_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part633) = true := by rfl

def kid05_part634 : Audit := .cycle 1 10 true (1)
theorem kid05_part634_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part634) = true := by rfl

def kid05_part635 : Audit := .cycle 1 24 true (0)
theorem kid05_part635_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part635) = true := by rfl

def kid05_part636 : Audit := .cycle 20 1 false (2)
theorem kid05_part636_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part636) = true := by rfl

def kid05_part637 : Audit := .split 26 (4,true) (byMove [
.cycle 0 45 true (0),
.cycle 0 30 true (0),
.cycle 28 1 false (4),
.cycle 27 1 false (3),
.cycle 0 30 true (0),
.last 27 (5,false),
.cycle 1 27 true (0),
.last 28 (5,false),
.cycle 30 1 false (8),
.cycle 0 28 true (0),
.cycle 30 1 false (8),
.cycle 32 1 false (8),
.cycle 36 1 false (8),
.cycle 28 17 true (4),
.cycle 1 29 true (0),
.cycle 27 1 false (3),
.cycle 34 1 false (8),
.last 27 (5,false),
.cycle 1 27 true (0),
.cycle 33 1 false (7),
.cycle 54 1 false (12),
.cycle 0 28 true (0),
.cycle 26 34 true (4),
.cycle 26 2 true (4)
])
theorem kid05_part637_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part637) = true := by rfl

def kid05_part638 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 28 true (0),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 34 1 false (8),
.cycle 1 24 true (0),
.last 27 (4,true),
.cycle 11 1 true (3),
.cycle 7 6 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 26 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 24 (4,true),
.cycle 11 1 true (3)
])
theorem kid05_part638_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part638) = true := by rfl

def kid05_part639 : Audit := .split 14 (4,true) (byMove [
.cycle 12 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 16 (5,false),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 18 1 false (4),
.cycle 15 5 false (1),
.cycle 15 5 false (0),
.cycle 18 5 false (0),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 17 5 false (1),
.cycle 0 16 true (0),
.cycle 0 35 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part639_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part639) = true := by rfl

def kid05_part640 : Audit := .split 20 (5,false) (byMove [
.cycle 22 38 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 23 1 false (-1),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.cycle 17 4 true (-2),
.cycle 0 34 true (-2),
.cycle 21 1 false (-1),
.cycle 15 6 true (-2),
.cycle 14 8 true (-2),
.cycle 13 9 false (1),
.cycle 17 4 false (0),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.cycle 15 6 false (0),
.cycle 20 1 false (-2),
.last 24 (4,true),
.cycle 11 10 false (2),
.cycle 0 34 true (-2),
.cycle 13 11 false (1),
.cycle 9 12 false (2),
.last 23 (4,true)
])
theorem kid05_part640_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part640) = true := by rfl

def kid05_part641 : Audit := .cycle 0 13 true (0)
theorem kid05_part641_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part641) = true := by rfl

def kid05_part642 : Audit := .cycle 18 1 false (0)
theorem kid05_part642_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part642) = true := by rfl

def kid05_part643 : Audit := .cycle 9 2 true (1)
theorem kid05_part643_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part643) = true := by rfl

def kid05_part644 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.last 32 (4,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 13 6 false (-1),
.last 28 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.last 14 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part644_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part644) = true := by rfl

def kid05_part645 : Audit := .cycle 0 11 true (0)
theorem kid05_part645_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part645) = true := by rfl

def kid05_part646 : Audit := .cycle 1 10 true (1)
theorem kid05_part646_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part646) = true := by rfl

def kid05_part647 : Audit := .cycle 2 9 true (1)
theorem kid05_part647_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part647) = true := by rfl

def kid05_part648 : Audit := .cycle 1 13 true (1)
theorem kid05_part648_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part648) = true := by rfl

def kid05_part649 : Audit := .cycle 9 13 true (1)
theorem kid05_part649_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part649) = true := by rfl

def kid05_part650 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 13 false (1),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.last 25 (4,true),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.cycle 13 10 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 24 (4,true),
.cycle 11 1 true (3)
])
theorem kid05_part650_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part650) = true := by rfl

def kid05_part626 : Audit := .split 10 (2,true) (byMove [(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650)])

theorem kid05_part626_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part626) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part627_checked

  · exact kid05_part633_checked

  · exact kid05_part639_checked

  · exact kid05_part645_checked

  · exact kid05_part628_checked

  · exact kid05_part634_checked

  · exact kid05_part640_checked

  · exact kid05_part646_checked

  · exact kid05_part629_checked

  · exact kid05_part635_checked

  · exact kid05_part641_checked

  · exact kid05_part647_checked

  · exact kid05_part630_checked

  · exact kid05_part636_checked

  · exact kid05_part642_checked

  · exact kid05_part648_checked

  · exact kid05_part631_checked

  · exact kid05_part637_checked

  · exact kid05_part643_checked

  · exact kid05_part649_checked

  · exact kid05_part632_checked

  · exact kid05_part638_checked

  · exact kid05_part644_checked

  · exact kid05_part650_checked

def kid05_part651 : Audit := .cycle 0 11 true (0)
theorem kid05_part651_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part651) = true := by rfl

def kid05_part652 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 11 1 true (1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 true (-2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 12 3 false (0),
.cycle 15 1 false (-1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 9 3 true (1),
.cycle 26 1 false (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
]),
.cycle 14 5 false (0),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 20 (5,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 13 1 true (3),
.last 13 (5,false),
.cycle 16 7 false (0),
.last 20 (5,false),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (3),
.last 13 (5,false)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.split 11 (5,false) (byMove [
.last 14 (2,true),
.last 30 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 12 4 true (-2),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.cycle 16 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 11 1 true (3),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 13 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 6 6 true (1),
.last 17 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 12 2 true (2),
.cycle 14 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
])
theorem kid05_part652_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part652) = true := by rfl

def kid05_part653 : Audit := .cycle 8 2 true (1)
theorem kid05_part653_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part653) = true := by rfl

def kid05_part654 : Audit := .cycle 11 4 false (1)
theorem kid05_part654_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part654) = true := by rfl

def kid05_part656 : Audit := .cycle 1 16 true (-2)
theorem kid05_part656_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part656) = true := by rfl

def kid05_part657 : Audit := .split 22 (2,true) (byMove [
.last 53 (4,true),
.cycle 10 13 false (0),
.cycle 25 1 false (-3),
.cycle 18 7 false (0),
.last 23 (4,true),
.cycle 19 4 false (-1),
.cycle 7 31 false (5),
.cycle 10 15 false (0),
.cycle 1 26 true (-3),
.last 61 (4,true),
.last 23 (4,true),
.cycle 8 15 false (2),
.cycle 17 6 false (0),
.cycle 10 13 false (0),
.cycle 16 9 false (0),
.cycle 16 7 false (0),
.last 23 (4,true),
.cycle 19 4 false (-1),
.last 38 (4,true),
.last 25 (4,true),
.last 49 (4,true),
.cycle 18 10 false (1),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid05_part657_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part657) = true := by rfl

def kid05_part658 : Audit := .cycle 13 1 false (-1)
theorem kid05_part658_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part658) = true := by rfl

def kid05_part659 : Audit := .cycle 12 1 false (-2)
theorem kid05_part659_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part659) = true := by rfl

def kid05_part660 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 false (3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.cycle 33 7 false (-1),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 33 (4,true),
.cycle 1 51 true (-4),
.cycle 30 30 true (-3),
.last 21 (4,true),
.cycle 9 7 false (1),
.cycle 12 6 false (-2),
.cycle 10 5 false (0),
.cycle 35 9 false (-1),
.cycle 33 7 false (-1),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 33 (4,true),
.cycle 2 13 false (3),
.last 33 (4,true),
.last 21 (4,true),
.last 16 (4,true)
])
theorem kid05_part660_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part660) = true := by rfl

def kid05_part661 : Audit := .cycle 11 1 false (-1)
theorem kid05_part661_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part661) = true := by rfl

def kid05_part662 : Audit := .split 17 (2,true) (byMove [
.cycle 0 25 true (-2),
.cycle 13 10 false (1),
.cycle 20 1 false (-2),
.cycle 12 7 false (1),
.last 18 (4,true),
.cycle 14 4 false (0),
.cycle 33 18 false (4),
.last 54 (4,true),
.cycle 0 21 true (-2),
.cycle 0 26 true (-2),
.last 18 (4,true),
.cycle 8 10 false (2),
.cycle 13 6 false (1),
.cycle 10 8 false (1),
.cycle 13 9 false (1),
.cycle 13 7 false (1),
.last 18 (4,true),
.cycle 14 4 false (0),
.last 33 (4,true),
.last 20 (4,true),
.cycle 0 21 true (-2),
.cycle 13 10 false (2),
.last 18 (4,true),
.last 19 (4,true)
])
theorem kid05_part662_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part662) = true := by rfl

def kid05_part663 : Audit := .split 13 (2,true) (byMove [
.cycle 1 39 true (-2),
.cycle 0 19 true (-1),
.cycle 16 1 false (0),
.cycle 12 7 false (2),
.last 14 (4,true),
.cycle 12 4 false (1),
.cycle 1 14 true (-1),
.cycle 12 13 true (0),
.cycle 1 30 true (-1),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 8 6 true (-1),
.cycle 12 6 false (1),
.cycle 10 4 true (-1),
.cycle 12 9 false (2),
.cycle 12 7 false (2),
.last 14 (4,true),
.cycle 12 4 false (1),
.last 26 (4,true),
.last 16 (4,true),
.cycle 1 31 true (-2),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part663_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part663) = true := by rfl

def kid05_part664 : Audit := .cycle 1 14 true (-1)
theorem kid05_part664_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part664) = true := by rfl

def kid05_part665 : Audit := .cycle 12 1 false (0)
theorem kid05_part665_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part665) = true := by rfl

def kid05_part666 : Audit := .split 14 (2,true) (byMove [
.last 33 (4,true),
.cycle 10 5 false (0),
.cycle 17 1 false (-1),
.cycle 12 7 false (1),
.last 15 (4,true),
.cycle 12 4 false (0),
.cycle 6 9 false (3),
.cycle 17 16 true (0),
.cycle 1 55 true (-2),
.cycle 1 16 true (-1),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 12 6 false (0),
.cycle 10 5 false (0),
.cycle 12 9 false (1),
.cycle 12 7 false (1),
.last 15 (4,true),
.cycle 12 4 false (0),
.last 18 (4,true),
.last 17 (4,true),
.last 27 (4,true),
.cycle 1 16 true (-1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part666_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part666) = true := by rfl

def kid05_part667 : Audit := .split 16 (2,true) (byMove [
.last 35 (4,true),
.cycle 11 8 true (-2),
.cycle 19 1 false (-1),
.cycle 13 7 false (1),
.last 17 (4,true),
.cycle 13 4 false (1),
.cycle 6 11 false (3),
.cycle 25 1 true (1),
.cycle 1 57 true (-2),
.cycle 1 18 true (-1),
.last 17 (4,true),
.cycle 8 9 false (2),
.cycle 13 6 false (1),
.cycle 10 7 false (1),
.cycle 13 9 false (1),
.cycle 13 7 false (1),
.last 17 (4,true),
.cycle 13 4 false (1),
.last 20 (4,true),
.last 19 (4,true),
.last 29 (4,true),
.cycle 1 18 true (-1),
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid05_part667_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part667) = true := by rfl

def kid05_part668 : Audit := .split 17 (2,true) (byMove [
.last 61 (4,true),
.cycle 10 8 false (0),
.cycle 20 1 false (-4),
.cycle 12 7 false (-1),
.last 18 (4,true),
.cycle 14 4 false (-2),
.last 37 (4,true),
.cycle 13 8 false (-1),
.last 77 (4,true),
.last 38 (4,true),
.last 18 (4,true),
.cycle 8 10 false (2),
.cycle 13 6 false (-1),
.cycle 10 8 false (0),
.cycle 13 9 false (-1),
.cycle 13 7 false (-1),
.last 18 (4,true),
.cycle 14 4 false (-2),
.last 37 (4,true),
.last 20 (4,true),
.last 49 (4,true),
.last 38 (4,true),
.last 18 (4,true),
.last 19 (4,true)
])
theorem kid05_part668_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part668) = true := by rfl

def kid05_part669 : Audit := .split 13 (2,true) (byMove [
.cycle 1 18 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 7 13 false (3),
.last 14 (4,true),
.cycle 12 4 false (-1),
.cycle 7 8 false (3),
.proven (BB6.Agent11Raw39Pumps.M288.table) (fun m hm => BB6.Agent11Raw39Pumps.M288.never m hm),
.cycle 1 16 true (-2),
.last 61 (4,true),
.last 17 (4,true),
.cycle 8 16 false (2),
.cycle 12 6 false (-1),
.cycle 10 4 false (0),
.cycle 20 9 false (1),
.cycle 5 13 false (3),
.last 14 (4,true),
.cycle 12 4 false (-1),
.last 17 (4,true),
.last 18 (4,true),
.cycle 1 16 true (-2),
.cycle 4 10 false (3),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid05_part669_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part669) = true := by rfl

def kid05_part670 : Audit := .split 19 (2,true) (byMove [
.cycle 0 27 true (-2),
.cycle 15 12 false (1),
.cycle 22 1 false (-2),
.cycle 13 7 false (1),
.last 20 (4,true),
.cycle 16 4 false (0),
.cycle 24 16 true (1),
.cycle 0 122 true (-3),
.cycle 0 23 true (-2),
.cycle 0 28 true (-2),
.last 20 (4,true),
.cycle 8 12 false (2),
.cycle 15 6 false (1),
.cycle 10 10 false (1),
.cycle 15 9 false (1),
.cycle 15 7 false (1),
.last 20 (4,true),
.cycle 16 4 false (0),
.last 35 (4,true),
.last 22 (4,true),
.cycle 0 23 true (-2),
.cycle 15 10 false (2),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid05_part670_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part670) = true := by rfl

def kid05_part671 : Audit := .cycle 12 1 false (-2)
theorem kid05_part671_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part671) = true := by rfl

def kid05_part672 : Audit := .split 14 (2,true) (byMove [
.last 37 (4,true),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.cycle 12 7 false (-1),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 17 (4,true),
.cycle 1 18 true (-3),
.last 45 (4,true),
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 12 6 false (-2),
.cycle 10 5 false (0),
.cycle 12 9 false (-1),
.cycle 12 7 false (-1),
.last 15 (4,true),
.cycle 12 4 false (-2),
.last 30 (4,true),
.last 17 (4,true),
.last 33 (4,true),
.cycle 12 10 false (1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part672_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part672) = true := by rfl

def kid05_part673 : Audit := .cycle 11 1 false (-1)
theorem kid05_part673_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part673) = true := by rfl

def kid05_part674 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.last 24 (2,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (2,true),
.cycle 11 5 false (1),
.last 18 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (-2),
.last 18 (2,true),
.cycle 13 5 false (1),
.last 18 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.cycle 7 11 false (3),
.last 22 (2,true),
.cycle 14 2 true (-1)
])
theorem kid05_part674_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part674) = true := by rfl

def kid05_part675 : Audit := .split 13 (2,true) (byMove [
.last 29 (4,true),
.last 34 (4,true),
.cycle 17 1 false (-1),
.cycle 7 9 false (3),
.last 14 (4,true),
.last 15 (4,true),
.cycle 1 14 true (-1),
.last 27 (4,true),
.cycle 1 32 true (-2),
.cycle 0 15 true (-1),
.last 14 (4,true),
.cycle 8 13 false (2),
.last 17 (4,true),
.cycle 10 9 false (1),
.cycle 14 9 false (1),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true),
.last 26 (4,true),
.last 16 (4,true),
.last 25 (4,true),
.cycle 0 15 true (-1),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part675_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part675) = true := by rfl

def kid05_part676 : Audit := .cycle 1 14 true (-1)
theorem kid05_part676_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part676) = true := by rfl

def kid05_part677 : Audit := .split 19 (2,true) (byMove [
.cycle 0 27 true (-2),
.cycle 15 12 false (1),
.cycle 22 1 false (-2),
.cycle 15 7 false (1),
.last 20 (4,true),
.cycle 16 4 false (0),
.cycle 38 20 false (4),
.last 62 (4,true),
.cycle 0 23 true (-2),
.cycle 0 28 true (-2),
.last 20 (4,true),
.cycle 8 12 false (2),
.cycle 14 6 false (1),
.cycle 10 10 false (1),
.cycle 13 9 false (1),
.cycle 13 7 false (1),
.last 20 (4,true),
.cycle 16 4 false (0),
.last 35 (4,true),
.last 22 (4,true),
.cycle 0 23 true (-2),
.cycle 15 10 false (2),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid05_part677_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part677) = true := by rfl

def kid05_part678 : Audit := .cycle 9 3 false (1)
theorem kid05_part678_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part678) = true := by rfl

def kid05_part679 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.last 25 (2,true),
.last 15 (2,true),
.last 21 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.cycle 6 9 false (3),
.cycle 21 1 true (1),
.last 15 (2,true),
.cycle 1 16 true (-1),
.last 19 (2,true),
.cycle 8 7 false (2),
.last 20 (2,true),
.cycle 10 5 false (1),
.last 15 (2,true),
.last 21 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 34 (2,true),
.last 22 (2,true),
.last 15 (2,true),
.cycle 1 16 true (-1),
.last 32 (2,true),
.cycle 13 2 true (0)
])
theorem kid05_part679_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part679) = true := by rfl

def kid05_part655 : Audit := .split 11 (5,false) (byMove [(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661),(kid05_part662),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part666),(kid05_part667),(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675),(kid05_part676),(kid05_part677),(kid05_part678),(kid05_part679)])

theorem kid05_part655_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part655) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some mv)) (byMove [(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661),(kid05_part662),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part666),(kid05_part667),(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675),(kid05_part676),(kid05_part677),(kid05_part678),(kid05_part679)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part656_checked

  · exact kid05_part662_checked

  · exact kid05_part668_checked

  · exact kid05_part674_checked

  · exact kid05_part657_checked

  · exact kid05_part663_checked

  · exact kid05_part669_checked

  · exact kid05_part675_checked

  · exact kid05_part658_checked

  · exact kid05_part664_checked

  · exact kid05_part670_checked

  · exact kid05_part676_checked

  · exact kid05_part659_checked

  · exact kid05_part665_checked

  · exact kid05_part671_checked

  · exact kid05_part677_checked

  · exact kid05_part660_checked

  · exact kid05_part666_checked

  · exact kid05_part672_checked

  · exact kid05_part678_checked

  · exact kid05_part661_checked

  · exact kid05_part667_checked

  · exact kid05_part673_checked

  · exact kid05_part679_checked

def kid05_part681 : Audit := .cycle 12 17 true (0)
theorem kid05_part681_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part681) = true := by rfl

def kid05_part682 : Audit := .cycle 1 14 true (-1)
theorem kid05_part682_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part682) = true := by rfl

def kid05_part683 : Audit := .cycle 12 1 false (0)
theorem kid05_part683_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part683) = true := by rfl

def kid05_part684 : Audit := .cycle 11 1 false (-1)
theorem kid05_part684_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part684) = true := by rfl

def kid05_part685 : Audit := .split 23 (4,true) (byMove [
.cycle 1 24 true (-2),
.last 25 (5,false),
.cycle 0 28 true (-2),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.cycle 1 28 true (-2),
.cycle 1 50 true (-2),
.cycle 1 35 true (-2),
.cycle 15 15 true (-2),
.cycle 1 33 true (-2),
.cycle 0 27 true (-2),
.last 24 (5,false),
.cycle 1 30 true (-2),
.last 25 (5,false),
.cycle 1 34 true (-2),
.cycle 1 25 true (-2),
.cycle 1 34 true (-2),
.cycle 1 34 true (-2),
.cycle 20 20 true (0),
.cycle 21 17 true (0),
.cycle 2 22 true (-2),
.cycle 1 52 true (-2),
.cycle 9 18 true (-2),
.last 24 (5,false)
])
theorem kid05_part685_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part685) = true := by rfl

def kid05_part686 : Audit := .split 11 (5,false) (byMove [
.cycle 1 16 true (-2),
.last 27 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 19 (4,true),
.cycle 11 1 false (-1),
.last 22 (4,true),
.last 22 (4,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 1 21 true (-1),
.cycle 1 23 true (-1),
.last 37 (4,true),
.last 37 (4,true),
.last 24 (4,true),
.cycle 12 1 false (-2),
.last 19 (4,true),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 15 (4,true),
.cycle 1 14 true (-1),
.last 24 (4,true),
.cycle 9 3 false (1),
.last 14 (4,true)
])
theorem kid05_part686_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part686) = true := by rfl

def kid05_part687 : Audit := .cycle 1 17 true (-1)
theorem kid05_part687_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part687) = true := by rfl

def kid05_part688 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 1 38 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 30 true (-2),
.cycle 12 1 false (0),
.cycle 1 19 true (-1),
.cycle 1 26 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 1 16 true (0),
.cycle 1 18 true (0),
.cycle 24 44 true (-3),
.cycle 1 28 true (-1),
.cycle 1 21 true (-1),
.cycle 13 1 false (-1),
.cycle 1 30 true (-2),
.cycle 12 1 false (0),
.last 16 (4,true),
.cycle 1 26 true (0),
.cycle 0 15 true (0),
.cycle 1 21 true (-1),
.cycle 9 4 true (0),
.last 15 (4,true)
])
theorem kid05_part688_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part688) = true := by rfl

def kid05_part689 : Audit := .cycle 14 1 false (4)
theorem kid05_part689_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part689) = true := by rfl

def kid05_part690 : Audit := .cycle 1 12 true (0)
theorem kid05_part690_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part690) = true := by rfl

def kid05_part691 : Audit := .split 11 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 1 21 true (-1),
.last 12 (5,false),
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 0 24 true (-2),
.cycle 0 20 true (0),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 1 21 true (-1),
.last 12 (5,false),
.cycle 1 12 true (0),
.cycle 1 17 true (-1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 11 2 true (1)
])
theorem kid05_part691_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part691) = true := by rfl

def kid05_part692 : Audit := .cycle 1 21 true (-1)
theorem kid05_part692_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part692) = true := by rfl

def kid05_part693 : Audit := .split 23 (4,true) (byMove [
.cycle 18 7 false (1),
.cycle 50 42 true (-5),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.cycle 38 64 true (-3),
.last 24 (5,false),
.cycle 1 31 true (-3),
.last 25 (5,false),
.cycle 36 60 true (-3),
.cycle 1 31 true (-3),
.cycle 1 28 true (-3),
.cycle 1 39 true (-3),
.cycle 11 13 false (1),
.cycle 12 15 false (1),
.cycle 1 35 true (-3),
.cycle 24 1 false (-2),
.cycle 38 64 true (-3),
.last 24 (5,false),
.cycle 17 29 true (-1),
.cycle 34 56 true (-3),
.cycle 36 60 true (-3),
.cycle 7 19 false (3),
.cycle 12 16 true (-3),
.cycle 22 2 true (-1)
])
theorem kid05_part693_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part693) = true := by rfl

def kid05_part694 : Audit := .split 14 (5,false) (byMove [
.cycle 16 25 true (-2),
.cycle 21 8 true (-4),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 19 8 true (-4),
.cycle 14 1 false (-2),
.cycle 16 8 true (-3),
.cycle 11 4 true (-2),
.cycle 1 23 true (-2),
.cycle 15 1 false (-1),
.cycle 19 8 true (-2),
.cycle 21 8 true (-2),
.last 49 (4,true),
.cycle 11 4 false (0),
.cycle 18 8 true (-3),
.cycle 15 1 false (-3),
.cycle 15 8 true (-4),
.cycle 14 1 false (-2),
.last 18 (4,true),
.cycle 15 8 true (-4),
.cycle 1 23 true (-2),
.cycle 18 8 true (-3),
.cycle 9 6 false (1),
.last 17 (4,true)
])
theorem kid05_part694_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part694) = true := by rfl

def kid05_part695 : Audit := .cycle 1 19 true (-1)
theorem kid05_part695_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part695) = true := by rfl

def kid05_part696 : Audit := .cycle 11 1 false (-1)
theorem kid05_part696_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part696) = true := by rfl

def kid05_part697 : Audit := .split 23 (4,true) (byMove [
.cycle 20 4 true (0),
.last 25 (5,false),
.cycle 17 8 true (-2),
.cycle 1 31 true (-2),
.cycle 21 8 true (-2),
.cycle 16 8 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 384, 1, 4096, 128, 256, 8, 128, 256, 4096, 4096],[128, 4096, 128, 1, 1, 128, 128, 256, 128, 1, 1, 128, 4096],6176⟩,
.last 25 (5,false),
.cycle 9 16 true (-2),
.cycle 0 25 true (-2),
.cycle 0 28 true (-2),
.cycle 8 16 true (-2),
.cycle 14 10 true (-2),
.last 25 (5,false),
.cycle 10 14 true (-2),
.cycle 1 31 true (-2),
.cycle 11 14 true (-2),
.cycle 11 14 true (-2),
.cycle 20 20 true (0),
.cycle 1 32 true (-2),
.cycle 22 2 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 1, 4096, 128, 256, 8, 128, 393, 4096, 4096],[128, 4096, 393, 1, 512, 393, 128, 393, 1, 1, 512, 1, 4096],6176⟩,
.cycle 23 5 true (1),
.cycle 23 2 true (1)
])
theorem kid05_part697_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part697) = true := by rfl

def kid05_part698 : Audit := .split 11 (5,false) (byMove [
.last 16 (4,true),
.cycle 1 21 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.last 25 (4,true),
.cycle 11 1 false (-1),
.last 22 (4,true),
.last 30 (4,true),
.cycle 10 2 true (-1),
.cycle 1 19 true (-1),
.last 12 (4,true),
.last 26 (4,true),
.last 22 (4,true),
.last 28 (4,true),
.last 24 (4,true),
.cycle 12 1 false (-2),
.last 25 (4,true),
.cycle 11 1 false (-1),
.last 15 (4,true),
.last 21 (4,true),
.last 27 (4,true),
.cycle 5 7 false (3),
.last 12 (4,true),
.last 13 (4,true)
])
theorem kid05_part698_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part698) = true := by rfl

def kid05_part699 : Audit := .split 14 (4,true) (byMove [
.cycle 16 18 true (0),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 24 true (-2),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 0 19 true (0),
.cycle 1 19 true (-1),
.cycle 44 17 false (3),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[524288, 1048576, 2097152, 512, 256, 4398046511104, 1024, 17179869184, 274877906944, 2097152, 1048576, 4398046511104, 137438953472, 33554432, 134217728, 8589934592, 4294967296, 4398046511104, 17179869184, 17179869184, 274877906944, 134217728, 67108864, 4398046511104, 4553504325632, 4828449341440, 5378339373056, 134217728, 67108864, 4398046511104, 268435456, 537001984, 5378339373056, 549755813888, 274877906944, 4398046511104, 268435456, 17179869184, 274877906944, 134217728, 67108864, 4398046511104, 4398046511104],[524288, 32, 131072, 17179869184, 128, 1024, 1024, 131072, 131072, 17179869184, 524288, 4194304, 137438953472, 536870912, 137473032192, 274946064384, 2147483648, 17179869184, 17179869184, 131072, 524288, 1048576, 33554432, 268435456, 4553504325632, 536870912, 4553504325632, 4828449341440, 33554432, 268435456, 268435456, 536870912, 131072, 17179869184, 137438953472, 1099511627776, 268435456, 131072, 33554432, 67108864, 33554432, 268435456, 4398046511104],7808112338976⟩,
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 1 24 true (-2),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 1 20 true (-2),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 1 18 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part699_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part699) = true := by rfl

def kid05_part700 : Audit := .split 31 (4,true) (byMove [
.cycle 17 18 true (0),
.last 33 (5,false),
.cycle 17 18 true (0),
.cycle 0 43 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 1, 4096, 128, 256, 8, 128, 393, 4096, 4096],[128, 4096, 128, 1, 393, 393, 128, 393, 128, 1, 393, 393, 4096],6176⟩,
.far true 1 ⟨0,[0, 0],[16, 36, 8, 8, 4, 64, 64],[16, 32, 16, 4, 32, 16, 64],98⟩,
.cycle 16 16 true (0),
.last 33 (5,false),
.cycle 17 16 true (1),
.cycle 1 39 true (-2),
.cycle 1 36 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 384, 1, 4096, 128, 256, 8, 128, 256, 4096, 4096],[128, 4096, 128, 1, 32, 128, 128, 256, 128, 1, 32, 128, 4096],6176⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 384, 1, 4096, 128, 256, 8, 128, 256, 4096, 4096],[128, 4096, 128, 1, 256, 128, 128, 256, 128, 1, 256, 128, 4096],6176⟩,
.last 33 (5,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 384, 1, 4096, 128, 256, 8, 128, 256, 4096, 4096],[128, 4096, 128, 1, 1, 128, 128, 256, 128, 1, 256, 128, 4096],6176⟩,
.cycle 0 43 true (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 1, 4096, 128, 256, 8, 128, 393, 4096, 4096],[128, 4096, 128, 1, 393, 393, 128, 393, 128, 1, 393, 393, 4096],6176⟩,
.far true 1 ⟨0,[0, 0],[16, 36, 8, 8, 4, 64, 64],[16, 32, 16, 4, 32, 16, 64],98⟩,
.cycle 16 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 1, 4096, 128, 256, 8, 128, 393, 4096, 4096],[128, 4096, 128, 1, 128, 393, 128, 393, 128, 1, 128, 393, 4096],6176⟩,
.cycle 17 16 true (1),
.cycle 7 36 true (-2),
.cycle 27 6 true (1),
.cycle 30 2 true (1)
])
theorem kid05_part700_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part700) = true := by rfl

def kid05_part701 : Audit := .cycle 2 11 true (0)
theorem kid05_part701_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part701) = true := by rfl

def kid05_part702 : Audit := .cycle 1 12 true (0)
theorem kid05_part702_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part702) = true := by rfl

def kid05_part703 : Audit := .split 11 (4,true) (byMove [
.cycle 1 18 true (0),
.last 13 (5,false),
.cycle 9 4 true (0),
.cycle 1 19 true (-1),
.cycle 0 28 true (-2),
.cycle 11 12 true (-2),
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 9 36 true (0),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.cycle 8 4 true (0),
.cycle 11 16 true (-2),
.last 13 (5,false),
.cycle 10 2 true (0),
.cycle 1 19 true (-1),
.cycle 26 16 true (-2),
.cycle 26 16 true (-2),
.cycle 1 12 true (0),
.cycle 1 20 true (-2),
.cycle 2 14 true (0),
.cycle 0 13 true (0),
.cycle 12 3 true (2),
.cycle 11 2 true (1)
])
theorem kid05_part703_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part703) = true := by rfl

def kid05_part704 : Audit := .split 12 (4,true) (byMove [
.last 21 (5,false),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 1 19 true (-1),
.last 14 (5,false),
.last 17 (5,false),
.cycle 1 14 true (0),
.cycle 0 18 true (0),
.cycle 1 23 true (-1),
.last 37 (5,false),
.last 18 (5,false),
.cycle 1 21 true (-1),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 1 17 true (0),
.last 21 (5,false),
.last 17 (5,false),
.cycle 1 14 true (0),
.cycle 13 5 true (1),
.cycle 11 2 true (0)
])
theorem kid05_part704_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part704) = true := by rfl

def kid05_part680 : Audit := .split 10 (2,true) (byMove [(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part704)])

theorem kid05_part680_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part680) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part704)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part681_checked

  · exact kid05_part687_checked

  · exact kid05_part693_checked

  · exact kid05_part699_checked

  · exact kid05_part682_checked

  · exact kid05_part688_checked

  · exact kid05_part694_checked

  · exact kid05_part700_checked

  · exact kid05_part683_checked

  · exact kid05_part689_checked

  · exact kid05_part695_checked

  · exact kid05_part701_checked

  · exact kid05_part684_checked

  · exact kid05_part690_checked

  · exact kid05_part696_checked

  · exact kid05_part702_checked

  · exact kid05_part685_checked

  · exact kid05_part691_checked

  · exact kid05_part697_checked

  · exact kid05_part703_checked

  · exact kid05_part686_checked

  · exact kid05_part692_checked

  · exact kid05_part698_checked

  · exact kid05_part704_checked

def kid05_part705 : Audit := .cycle 15 1 false (-1)
theorem kid05_part705_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part705) = true := by rfl

def kid05_part707 : Audit := .split 13 (2,true) (byMove [
.cycle 12 17 true (0),
.cycle 16 1 false (-2),
.cycle 17 1 false (-1),
.cycle 7 9 false (3),
.cycle 0 19 true (-1),
.cycle 10 5 false (1),
.cycle 1 14 true (-1),
.last 15 (5,false),
.cycle 1 32 true (-2),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.cycle 12 6 true (-1),
.cycle 10 7 false (1),
.cycle 16 1 false (-2),
.cycle 21 1 false (-1),
.cycle 5 9 false (3),
.cycle 12 4 true (-1),
.cycle 10 5 false (1),
.cycle 12 14 true (0),
.cycle 12 19 true (-1),
.cycle 12 13 true (0),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.last 19 (5,false)
])
theorem kid05_part707_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part707) = true := by rfl

def kid05_part708 : Audit := .cycle 1 14 true (-1)
theorem kid05_part708_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part708) = true := by rfl

def kid05_part709 : Audit := .cycle 12 1 false (0)
theorem kid05_part709_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part709) = true := by rfl

def kid05_part710 : Audit := .cycle 11 1 false (-1)
theorem kid05_part710_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part710) = true := by rfl

def kid05_part711 : Audit := .cycle 11 1 false (-1)
theorem kid05_part711_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part711) = true := by rfl

def kid05_part712 : Audit := .split 11 (5,false) (byMove [
.cycle 1 16 true (-2),
.cycle 20 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (-1),
.cycle 17 1 false (-1),
.cycle 9 3 false (1),
.cycle 16 1 false (-2)
])
theorem kid05_part712_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part712) = true := by rfl

def kid05_part713 : Audit := .cycle 14 1 false (0)
theorem kid05_part713_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part713) = true := by rfl

def kid05_part714 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (-1),
.cycle 21 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 0 19 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 9 4 true (0),
.cycle 17 1 true (1)
])
theorem kid05_part714_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part714) = true := by rfl

def kid05_part715 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.cycle 13 1 false (1),
.cycle 15 1 false (-1),
.last 15 (5,false),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 12 1 false (0),
.last 12 (5,false),
.cycle 1 12 true (0),
.cycle 14 1 false (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 21 1 false (1),
.last 15 (5,false)
])
theorem kid05_part715_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part715) = true := by rfl

def kid05_part716 : Audit := .cycle 1 12 true (0)
theorem kid05_part716_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part716) = true := by rfl

def kid05_part717 : Audit := .cycle 13 1 false (3)
theorem kid05_part717_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part717) = true := by rfl

def kid05_part718 : Audit := .cycle 12 1 false (0)
theorem kid05_part718_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part718) = true := by rfl

def kid05_part719 : Audit := .cycle 14 1 false (-2)
theorem kid05_part719_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part719) = true := by rfl

def kid05_part720 : Audit := .split 12 (2,true) (byMove [
.cycle 32 1 false (-2),
.last 14 (5,false),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.cycle 6 7 false (3),
.last 14 (5,false),
.cycle 25 1 false (-1),
.cycle 1 14 true (-1),
.cycle 24 1 false (-2),
.cycle 8 5 false (2),
.cycle 16 1 false (-2),
.last 14 (5,false),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 10 3 false (0),
.cycle 14 1 false (-2),
.last 18 (5,false),
.cycle 10 5 false (1),
.cycle 26 1 false (-2),
.cycle 1 14 true (-1),
.cycle 16 1 false (-2),
.last 16 (5,false)
])
theorem kid05_part720_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part720) = true := by rfl

def kid05_part721 : Audit := .cycle 16 1 false (0)
theorem kid05_part721_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part721) = true := by rfl

def kid05_part722 : Audit := .cycle 11 1 false (-1)
theorem kid05_part722_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part722) = true := by rfl

def kid05_part723 : Audit := .cycle 11 1 false (-1)
theorem kid05_part723_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part723) = true := by rfl

def kid05_part724 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.cycle 9 10 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 15 1 false (-1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 16 1 false (0),
.cycle 10 2 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-3),
.last 13 (2,true),
.cycle 17 1 false (-1),
.cycle 12 1 false (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 10 5 false (1),
.cycle 14 1 false (-2),
.last 12 (2,true),
.cycle 5 7 false (3),
.cycle 14 1 false (-2),
.cycle 10 3 false (0)
])
theorem kid05_part724_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part724) = true := by rfl

def kid05_part725 : Audit := .cycle 1 15 true (0)
theorem kid05_part725_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part725) = true := by rfl

def kid05_part726 : Audit := .cycle 13 1 false (-1)
theorem kid05_part726_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part726) = true := by rfl

def kid05_part727 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.last 13 (5,false),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (-1),
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 9 18 true (0),
.cycle 8 4 true (0),
.cycle 15 1 false (-1),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 10 2 true (0),
.cycle 13 1 false (-1),
.cycle 1 12 true (0),
.cycle 1 15 true (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 2 11 true (0),
.last 15 (5,false)
])
theorem kid05_part727_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part727) = true := by rfl

def kid05_part728 : Audit := .cycle 1 12 true (0)
theorem kid05_part728_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part728) = true := by rfl

def kid05_part729 : Audit := .cycle 11 3 true (1)
theorem kid05_part729_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part729) = true := by rfl

def kid05_part730 : Audit := .cycle 10 2 true (0)
theorem kid05_part730_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part730) = true := by rfl

def kid05_part706 : Audit := .split 10 (4,true) (byMove [(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718),(kid05_part719),(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727),(kid05_part728),(kid05_part729),(kid05_part730)])

theorem kid05_part706_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part706) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718),(kid05_part719),(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727),(kid05_part728),(kid05_part729),(kid05_part730)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part707_checked

  · exact kid05_part713_checked

  · exact kid05_part719_checked

  · exact kid05_part725_checked

  · exact kid05_part708_checked

  · exact kid05_part714_checked

  · exact kid05_part720_checked

  · exact kid05_part726_checked

  · exact kid05_part709_checked

  · exact kid05_part715_checked

  · exact kid05_part721_checked

  · exact kid05_part727_checked

  · exact kid05_part710_checked

  · exact kid05_part716_checked

  · exact kid05_part722_checked

  · exact kid05_part728_checked

  · exact kid05_part711_checked

  · exact kid05_part717_checked

  · exact kid05_part723_checked

  · exact kid05_part729_checked

  · exact kid05_part712_checked

  · exact kid05_part718_checked

  · exact kid05_part724_checked

  · exact kid05_part730_checked

def kid05_part732 : Audit := .split 15 (2,true) (byMove [
.last 36 (4,true),
.cycle 10 7 false (0),
.cycle 19 1 false (-3),
.cycle 7 11 false (3),
.last 16 (4,true),
.last 17 (4,true),
.last 21 (4,true),
.cycle 14 22 true (-2),
.last 87 (4,true),
.cycle 14 26 true (-2),
.last 16 (4,true),
.last 19 (4,true),
.last 19 (4,true),
.cycle 10 7 false (0),
.cycle 10 12 false (0),
.cycle 5 11 false (3),
.last 16 (4,true),
.last 17 (4,true),
.last 19 (4,true),
.last 18 (4,true),
.last 28 (4,true),
.last 22 (4,true),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid05_part732_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part732) = true := by rfl

def kid05_part733 : Audit := .split 42 (2,true) (byMove [
.last 54 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.far true 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[66564, 131104, 32768, 512, 2048, 2, 1024, 4, 557056, 32768, 131072, 2, 1024, 4, 557056, 32768, 131072, 524288, 4, 131104, 32768, 512, 2048, 2, 16777216],[66564, 32, 4, 163840, 16777216, 1024, 1024, 32, 4, 163840, 16777216, 65536, 1024, 8388608, 1048576, 131072, 16777216, 65536, 4, 32, 4, 131072, 16777216, 1024, 16777216],16777216⟩,
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 8, 32, 64, 16, 64],64⟩,
.last 43 (4,true),
.last 44 (4,true),
.last 56 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.last 150 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 10, 32, 64, 16, 64],64⟩,
.proven (BB6.Agent11Raw39Pumps.M305.table) (fun m hm => BB6.Agent11Raw39Pumps.M305.never m hm),
.last 54 (4,true),
.last 46 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.last 70 (4,true),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 8, 32, 64, 16, 64],64⟩,
.last 43 (4,true),
.last 44 (4,true),
.last 54 (4,true),
.last 53 (4,true),
.last 52 (4,true),
.last 58 (4,true),
.last 45 (4,true),
.last 46 (4,true)
])
theorem kid05_part733_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part733) = true := by rfl

def kid05_part734 : Audit := .cycle 14 1 false (-2)
theorem kid05_part734_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part734) = true := by rfl

def kid05_part735 : Audit := .cycle 13 1 false (-3)
theorem kid05_part735_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part735) = true := by rfl

def kid05_part736 : Audit := .cycle 11 2 false (-1)
theorem kid05_part736_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part736) = true := by rfl

def kid05_part737 : Audit := .cycle 12 1 false (-2)
theorem kid05_part737_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part737) = true := by rfl

def kid05_part738 : Audit := .cycle 10 5 false (0)
theorem kid05_part738_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part738) = true := by rfl

def kid05_part739 : Audit := .split 16 (2,true) (byMove [
.last 34 (4,true),
.cycle 1 22 true (-2),
.cycle 19 1 false (-1),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 256, 2, 8192, 16384, 8, 17024, 17025, 2, 524288, 1048576, 512, 128, 16777216, 128, 524288, 1048576, 2097152, 20717568, 20717568, 524288, 16777216],[128, 256, 17024, 1, 16777216, 17025, 8192, 17024, 16512, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 17 (4,true),
.cycle 10 7 false (0),
.cycle 6 11 false (3),
.cycle 17 14 true (0),
.cycle 0 62 true (-2),
.cycle 1 18 true (-2),
.last 17 (4,true),
.cycle 8 9 false (2),
.cycle 10 9 false (0),
.cycle 13 4 true (-2),
.cycle 1 51 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 256, 2, 8192, 16384, 8, 17024, 17025, 2, 524288, 1048576, 512, 128, 16777216, 128, 524288, 1048576, 2097152, 20717568, 20717568, 524288, 16777216],[128, 256, 17025, 1, 16777216, 17025, 8192, 17024, 17024, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 17 (4,true),
.cycle 10 7 false (0),
.last 20 (4,true),
.last 19 (4,true),
.last 28 (4,true),
.last 31 (4,true),
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid05_part739_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part739) = true := by rfl

def kid05_part740 : Audit := .split 13 (2,true) (byMove [
.last 34 (4,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 0 26 true (-2),
.last 36 (4,true),
.cycle 1 18 true (-2),
.cycle 18 1 false (4),
.cycle 0 22 true (-2),
.last 14 (4,true),
.cycle 10 4 true (-2),
.cycle 10 6 false (0),
.cycle 21 14 true (-3),
.cycle 1 39 true (-2),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 17 (4,true),
.cycle 10 5 false (0),
.last 26 (4,true),
.cycle 5 9 false (3),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part740_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part740) = true := by rfl

def kid05_part741 : Audit := .split 22 (2,true) (byMove [
.last 34 (4,true),
.cycle 1 28 true (-2),
.cycle 26 1 false (0),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 1, 8, 8192, 16384, 8, 17024, 17025, 8, 524288, 1048576, 512, 128, 16777216, 512, 524288, 1048576, 2097152, 20717568, 20717568, 2097152, 16777216],[128, 17025, 17024, 1, 16777216, 17025, 8192, 17024, 16512, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 23 (4,true),
.last 24 (4,true),
.last 36 (4,true),
.cycle 1 34 true (-2),
.cycle 0 47 true (-2),
.cycle 3 20 true (-2),
.cycle 0 26 true (-2),
.cycle 0 47 true (-2),
.last 26 (4,true),
.cycle 15 8 true (-2),
.cycle 1 33 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 1, 3, 3, 3],[128, 256, 8, 17025, 1, 8, 8192, 16384, 8, 17024, 17025, 8, 524288, 1048576, 512, 128, 16777216, 512, 524288, 1048576, 2097152, 20717568, 20717568, 2097152, 16777216],[128, 17025, 17025, 1, 16777216, 17025, 8192, 17024, 17024, 1, 16777216, 16777216, 524288, 16777216, 128, 64, 16777216, 16777216, 524288, 20717568, 20717568, 262144, 16777216, 20717568, 16777216],33370176⟩,
.last 23 (4,true),
.last 24 (4,true),
.last 34 (4,true),
.last 33 (4,true),
.last 32 (4,true),
.last 38 (4,true),
.last 25 (4,true),
.last 32 (4,true)
])
theorem kid05_part741_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part741) = true := by rfl

def kid05_part742 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 11 4 true (-2),
.last 22 (2,true),
.cycle 21 16 true (0),
.last 14 (2,true),
.cycle 0 22 true (-2),
.cycle 16 3 true (2),
.cycle 10 4 true (-2),
.cycle 10 6 false (0),
.last 15 (2,true),
.last 26 (2,true),
.cycle 14 1 false (-2),
.cycle 11 3 false (-1),
.cycle 12 2 true (-2),
.last 20 (2,true),
.cycle 10 5 false (0),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 14 5 true (0),
.cycle 13 2 true (-1)
])
theorem kid05_part742_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part742) = true := by rfl

def kid05_part743 : Audit := .cycle 10 3 false (0)
theorem kid05_part743_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part743) = true := by rfl

def kid05_part744 : Audit := .cycle 10 5 false (0)
theorem kid05_part744_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part744) = true := by rfl

def kid05_part745 : Audit := .split 14 (2,true) (byMove [
.last 38 (4,true),
.cycle 12 4 false (-2),
.cycle 17 1 false (-3),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.cycle 6 9 false (3),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 2, 32, 64, 16, 64],64⟩,
.cycle 1 50 true (-5),
.far true 1 ⟨0,[0, 0],[16, 32, 10, 8, 32, 2, 64],[16, 32, 10, 32, 64, 16, 64],64⟩,
.last 15 (4,true),
.cycle 8 7 false (2),
.cycle 10 7 false (0),
.cycle 12 4 false (-2),
.cycle 10 10 false (0),
.cycle 10 8 false (0),
.last 15 (4,true),
.cycle 10 5 false (0),
.last 18 (4,true),
.last 17 (4,true),
.last 28 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid05_part745_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part745) = true := by rfl

def kid05_part746 : Audit := .cycle 10 7 false (0)
theorem kid05_part746_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part746) = true := by rfl

def kid05_part747 : Audit := .cycle 13 1 false (-3)
theorem kid05_part747_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part747) = true := by rfl

def kid05_part748 : Audit := .cycle 11 2 false (-1)
theorem kid05_part748_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part748) = true := by rfl

def kid05_part749 : Audit := .cycle 12 1 false (-2)
theorem kid05_part749_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part749) = true := by rfl

def kid05_part750 : Audit := .split 16 (4,true) (byMove [
.last 19 (2,true),
.last 33 (2,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 21 (2,true),
.cycle 14 5 false (0),
.last 19 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.last 30 (2,true),
.cycle 30 17 true (0),
.cycle 10 7 false (0),
.cycle 10 9 false (0),
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-3),
.cycle 11 6 false (0),
.cycle 12 5 false (0),
.last 19 (2,true),
.cycle 10 8 false (0),
.last 17 (2,true),
.cycle 7 12 false (3),
.cycle 22 5 true (0),
.cycle 15 2 true (-2)
])
theorem kid05_part750_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part750) = true := by rfl

def kid05_part751 : Audit := .cycle 10 4 false (0)
theorem kid05_part751_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part751) = true := by rfl

def kid05_part752 : Audit := .split 13 (2,true) (byMove [
.last 34 (4,true),
.cycle 10 12 false (0),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.last 14 (4,true),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.cycle 1 18 true (-2),
.cycle 0 43 true (-3),
.cycle 0 22 true (-2),
.last 14 (4,true),
.cycle 8 6 false (2),
.cycle 10 6 false (0),
.cycle 19 17 false (1),
.cycle 10 9 false (0),
.cycle 10 7 false (0),
.last 14 (4,true),
.cycle 10 4 false (0),
.last 17 (4,true),
.last 16 (4,true),
.last 26 (4,true),
.last 20 (4,true),
.last 14 (4,true),
.last 15 (4,true)
])
theorem kid05_part752_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part752) = true := by rfl

def kid05_part753 : Audit := .cycle 5 8 false (3)
theorem kid05_part753_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part753) = true := by rfl

def kid05_part754 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 9 7 false (1),
.last 14 (2,true),
.cycle 10 7 false (0),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.cycle 9 12 false (1),
.last 14 (2,true),
.cycle 0 22 true (-2),
.cycle 16 3 true (2),
.cycle 8 6 false (2),
.cycle 10 6 false (0),
.cycle 9 7 false (1),
.last 14 (2,true),
.cycle 10 7 false (0),
.cycle 11 4 false (-1),
.cycle 10 4 false (0),
.last 20 (2,true),
.cycle 10 8 false (0),
.last 14 (2,true),
.cycle 5 16 false (3),
.cycle 14 5 true (0),
.cycle 13 2 true (-1)
])
theorem kid05_part754_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part754) = true := by rfl

def kid05_part755 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.last 46 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 10 9 false (0),
.cycle 10 7 false (0),
.cycle 31 1 true (1),
.last 15 (2,true),
.last 26 (2,true),
.cycle 17 5 true (1),
.cycle 10 5 false (0),
.cycle 10 7 false (0),
.last 16 (2,true),
.cycle 10 9 false (0),
.cycle 15 1 false (-3),
.cycle 11 4 false (-1),
.cycle 12 3 false (-1),
.last 21 (2,true),
.cycle 10 6 false (0),
.last 15 (2,true),
.cycle 5 10 false (3),
.cycle 16 5 true (0),
.cycle 13 2 true (-2)
])
theorem kid05_part755_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part755) = true := by rfl

def kid05_part731 : Audit := .split 12 (5,false) (byMove [(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part751),(kid05_part752),(kid05_part753),(kid05_part754),(kid05_part755)])

theorem kid05_part731_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part731) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part751),(kid05_part752),(kid05_part753),(kid05_part754),(kid05_part755)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part732_checked

  · exact kid05_part738_checked

  · exact kid05_part744_checked

  · exact kid05_part750_checked

  · exact kid05_part733_checked

  · exact kid05_part739_checked

  · exact kid05_part745_checked

  · exact kid05_part751_checked

  · exact kid05_part734_checked

  · exact kid05_part740_checked

  · exact kid05_part746_checked

  · exact kid05_part752_checked

  · exact kid05_part735_checked

  · exact kid05_part741_checked

  · exact kid05_part747_checked

  · exact kid05_part753_checked

  · exact kid05_part736_checked

  · exact kid05_part742_checked

  · exact kid05_part748_checked

  · exact kid05_part754_checked

  · exact kid05_part737_checked

  · exact kid05_part743_checked

  · exact kid05_part749_checked

  · exact kid05_part755_checked

def kid05_part756 : Audit := .cycle 1 10 true (1)
theorem kid05_part756_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part756) = true := by rfl

def kid05_part758 : Audit := .split 15 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 1 17 false (3),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 18 true (-1),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 1 16 true (-1),
.last 16 (5,false),
.cycle 10 7 false (2),
.cycle 16 3 false (0),
.cycle 21 3 false (1),
.cycle 1 17 true (-1),
.cycle 14 4 true (-1),
.cycle 11 5 false (1),
.cycle 14 16 true (0),
.cycle 14 15 true (0),
.cycle 14 14 true (-1),
.cycle 1 18 true (-1),
.cycle 14 16 true (0),
.last 16 (5,false)
])
theorem kid05_part758_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part758) = true := by rfl

def kid05_part759 : Audit := .cycle 0 16 true (-1)
theorem kid05_part759_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part759) = true := by rfl

def kid05_part760 : Audit := .cycle 14 1 false (0)
theorem kid05_part760_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part760) = true := by rfl

def kid05_part761 : Audit := .cycle 13 1 false (-1)
theorem kid05_part761_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part761) = true := by rfl

def kid05_part762 : Audit := .split 15 (2,true) (byMove [
.cycle 0 34 true (-2),
.cycle 16 3 false (0),
.cycle 19 1 false (-1),
.cycle 0 17 true (-1),
.cycle 1 18 false (3),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 0 36 true (-2),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 1 16 true (-1),
.last 16 (5,false),
.cycle 10 7 false (2),
.cycle 16 3 false (0),
.cycle 21 3 false (1),
.cycle 1 17 true (-1),
.cycle 0 22 true (-2),
.cycle 11 5 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 457, 128, 4096, 128, 256, 8, 128, 128, 4096, 4096],[128, 4096, 64, 1, 256, 457, 128, 457, 64, 1, 457, 457, 4096],6176⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 128, 4096, 128, 256, 8, 128, 128, 4096, 4096],[128, 4096, 128, 1, 256, 393, 128, 393, 128, 1, 393, 393, 4096],6176⟩,
.cycle 0 32 true (-2),
.cycle 1 18 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1417, 128, 4096, 128, 256, 8, 128, 128, 4096, 4096],[128, 4096, 1024, 1, 256, 1417, 128, 1417, 1024, 1, 1417, 1417, 4096],6176⟩,
.last 16 (5,false)
])
theorem kid05_part762_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part762) = true := by rfl

def kid05_part763 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 20 3 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 18 true (-2),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.cycle 15 3 false (1),
.cycle 15 3 false (-1),
.last 15 (2,true),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 17 3 false (1),
.cycle 9 5 false (2),
.cycle 17 3 false (-1)
])
theorem kid05_part763_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part763) = true := by rfl

def kid05_part764 : Audit := .cycle 1 13 true (0)
theorem kid05_part764_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part764) = true := by rfl

def kid05_part765 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 1 15 false (3),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 1 15 true (0),
.cycle 14 1 true (0),
.cycle 16 3 false (0),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 14 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 1 17 true (0),
.cycle 1 15 true (0),
.cycle 14 1 true (0)
])
theorem kid05_part765_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part765) = true := by rfl

def kid05_part766 : Audit := .split 13 (2,true) (byMove [
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
.last 17 (5,false),
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
])
theorem kid05_part766_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part766) = true := by rfl

def kid05_part767 : Audit := .cycle 0 14 true (0)
theorem kid05_part767_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part767) = true := by rfl

def kid05_part768 : Audit := .cycle 1 14 true (0)
theorem kid05_part768_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part768) = true := by rfl

def kid05_part769 : Audit := .cycle 13 3 false (1)
theorem kid05_part769_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part769) = true := by rfl

def kid05_part770 : Audit := .cycle 14 3 false (0)
theorem kid05_part770_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part770) = true := by rfl

def kid05_part771 : Audit := .split 14 (2,true) (byMove [
.last 32 (5,false),
.last 16 (5,false),
.cycle 17 1 false (-1),
.cycle 17 3 false (1),
.cycle 12 3 false (0),
.cycle 15 3 false (-1),
.cycle 1 15 true (-1),
.last 16 (5,false),
.cycle 23 3 false (1),
.cycle 0 16 true (-1),
.cycle 1 18 true (-1),
.cycle 8 7 false (2),
.cycle 16 3 false (0),
.last 16 (5,false),
.cycle 19 3 false (1),
.cycle 17 3 false (1),
.cycle 12 3 false (0),
.cycle 15 3 false (-1),
.cycle 28 3 false (0),
.cycle 10 5 false (2),
.last 28 (5,false),
.cycle 0 16 true (-1),
.cycle 16 3 false (0),
.last 18 (5,false)
])
theorem kid05_part771_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part771) = true := by rfl

def kid05_part772 : Audit := .cycle 1 15 true (-1)
theorem kid05_part772_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part772) = true := by rfl

def kid05_part773 : Audit := .cycle 13 1 false (-1)
theorem kid05_part773_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part773) = true := by rfl

def kid05_part774 : Audit := .cycle 13 3 false (0)
theorem kid05_part774_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part774) = true := by rfl

def kid05_part775 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 1 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 16 (2,true),
.cycle 13 1 false (-1),
.cycle 15 3 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 12 2 true (-1),
.cycle 14 3 false (0),
.cycle 15 3 false (-1),
.last 15 (2,true),
.cycle 17 3 false (1),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 10 5 false (2),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 15 3 false (-1),
.cycle 11 3 false (1)
])
theorem kid05_part775_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part775) = true := by rfl

def kid05_part776 : Audit := .cycle 1 13 true (0)
theorem kid05_part776_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part776) = true := by rfl

def kid05_part777 : Audit := .cycle 13 3 false (1)
theorem kid05_part777_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part777) = true := by rfl

def kid05_part778 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (0),
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 20 3 false (2),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 7 16 true (0),
.cycle 20 3 false (2),
.cycle 18 3 false (2),
.cycle 1 14 true (0),
.last 14 (5,false),
.cycle 15 3 false (1),
.last 15 (5,false),
.cycle 1 17 true (-1),
.cycle 1 15 true (0),
.cycle 12 2 true (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 1 14 true (0),
.last 14 (5,false)
])
theorem kid05_part778_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part778) = true := by rfl

def kid05_part779 : Audit := .cycle 0 14 true (0)
theorem kid05_part779_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part779) = true := by rfl

def kid05_part780 : Audit := .cycle 1 14 true (0)
theorem kid05_part780_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part780) = true := by rfl

def kid05_part781 : Audit := .cycle 11 2 true (0)
theorem kid05_part781_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part781) = true := by rfl

def kid05_part757 : Audit := .split 12 (4,true) (byMove [(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774),(kid05_part775),(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781)])

theorem kid05_part757_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part757) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (4,true) (some mv)) (byMove [(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774),(kid05_part775),(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part758_checked

  · exact kid05_part764_checked

  · exact kid05_part770_checked

  · exact kid05_part776_checked

  · exact kid05_part759_checked

  · exact kid05_part765_checked

  · exact kid05_part771_checked

  · exact kid05_part777_checked

  · exact kid05_part760_checked

  · exact kid05_part766_checked

  · exact kid05_part772_checked

  · exact kid05_part778_checked

  · exact kid05_part761_checked

  · exact kid05_part767_checked

  · exact kid05_part773_checked

  · exact kid05_part779_checked

  · exact kid05_part762_checked

  · exact kid05_part768_checked

  · exact kid05_part774_checked

  · exact kid05_part780_checked

  · exact kid05_part763_checked

  · exact kid05_part769_checked

  · exact kid05_part775_checked

  · exact kid05_part781_checked

def kid05_part783 : Audit := .cycle 1 11 true (1)
theorem kid05_part783_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part783) = true := by rfl

def kid05_part784 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (3),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 0 17 false (3),
.cycle 11 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 11 12 true (-2),
.cycle 16 1 true (-2),
.cycle 11 7 false (1),
.cycle 14 4 false (0),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 30 (4,true),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 1 19 false (3),
.cycle 2 16 false (3),
.cycle 16 1 true (-2)
])
theorem kid05_part784_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part784) = true := by rfl

def kid05_part785 : Audit := .cycle 14 1 false (0)
theorem kid05_part785_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part785) = true := by rfl

def kid05_part786 : Audit := .cycle 0 12 true (0)
theorem kid05_part786_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part786) = true := by rfl

def kid05_part787 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 12 11 false (1),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 2 11 true (1),
.last 12 (5,false),
.cycle 13 6 false (1),
.last 13 (5,false),
.cycle 0 16 true (-1),
.cycle 1 13 true (0),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 12 (5,false)
])
theorem kid05_part787_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part787) = true := by rfl

def kid05_part788 : Audit := .split 12 (4,true) (byMove [
.cycle 10 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-1),
.last 13 (5,false),
.cycle 1 13 true (0),
.last 14 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 21 3 false (3),
.cycle 13 3 false (1),
.cycle 15 3 false (-1),
.cycle 14 3 false (0),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 1 13 true (0),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 2 13 true (0),
.cycle 11 2 true (0)
])
theorem kid05_part788_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part788) = true := by rfl

def kid05_part789 : Audit := .cycle 0 11 true (0)
theorem kid05_part789_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part789) = true := by rfl

def kid05_part790 : Audit := .cycle 1 10 true (1)
theorem kid05_part790_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part790) = true := by rfl

def kid05_part791 : Audit := .cycle 0 23 true (0)
theorem kid05_part791_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part791) = true := by rfl

def kid05_part792 : Audit := .cycle 3 8 true (1)
theorem kid05_part792_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part792) = true := by rfl

def kid05_part793 : Audit := .cycle 2 10 true (1)
theorem kid05_part793_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part793) = true := by rfl

def kid05_part794 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 17 true (1),
.cycle 0 23 true (0),
.cycle 2 11 true (1),
.cycle 11 1 true (3),
.last 15 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.cycle 11 1 true (3)
])
theorem kid05_part794_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part794) = true := by rfl

def kid05_part795 : Audit := .split 14 (4,true) (byMove [
.cycle 10 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.last 15 (5,false),
.cycle 1 15 true (0),
.last 16 (5,false),
.cycle 17 5 false (1),
.cycle 0 16 true (0),
.cycle 21 5 false (4),
.cycle 15 5 false (1),
.cycle 16 5 false (0),
.cycle 16 5 false (0),
.cycle 1 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 5 false (0),
.last 15 (5,false),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.cycle 2 15 true (0),
.cycle 13 2 true (0)
])
theorem kid05_part795_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part795) = true := by rfl

def kid05_part796 : Audit := .split 16 (5,false) (byMove [
.cycle 18 32 true (-2),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 14 4 true (-2),
.cycle 0 28 true (-2),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.cycle 11 7 false (1),
.cycle 14 4 false (0),
.cycle 11 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 20 (4,true),
.cycle 10 8 false (2),
.cycle 0 28 true (-2),
.cycle 11 9 false (1),
.cycle 9 8 false (2),
.last 19 (4,true)
])
theorem kid05_part796_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part796) = true := by rfl

def kid05_part797 : Audit := .cycle 1 23 true (-1)
theorem kid05_part797_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part797) = true := by rfl

def kid05_part798 : Audit := .cycle 1 12 true (1)
theorem kid05_part798_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part798) = true := by rfl

def kid05_part799 : Audit := .split 11 (4,true) (byMove [
.cycle 10 4 true (0),
.last 13 (5,false),
.cycle 17 1 false (-1),
.cycle 19 1 false (-1),
.cycle 0 36 true (-2),
.last 16 (5,false),
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 13 (5,false),
.cycle 10 18 true (-2),
.cycle 19 1 false (-1),
.cycle 12 3 false (0),
.last 16 (5,false),
.cycle 1 12 true (1),
.cycle 14 5 false (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.cycle 11 2 true (1)
])
theorem kid05_part799_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part799) = true := by rfl

def kid05_part800 : Audit := .split 12 (4,true) (byMove [
.cycle 10 5 false (2),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 16 true (-1),
.last 13 (5,false),
.cycle 15 3 false (1),
.last 14 (5,false),
.last 14 (5,false),
.cycle 1 14 true (0),
.cycle 22 3 false (4),
.cycle 13 3 false (1),
.cycle 15 3 false (-1),
.cycle 14 3 false (0),
.cycle 17 3 false (1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.last 13 (5,false),
.cycle 1 17 true (0),
.cycle 14 3 false (0),
.cycle 13 3 false (1),
.cycle 1 14 true (0),
.cycle 2 14 true (0),
.cycle 11 2 true (0)
])
theorem kid05_part800_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part800) = true := by rfl

def kid05_part801 : Audit := .cycle 0 11 true (0)
theorem kid05_part801_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part801) = true := by rfl

def kid05_part802 : Audit := .cycle 1 10 true (1)
theorem kid05_part802_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part802) = true := by rfl

def kid05_part803 : Audit := .cycle 2 9 true (1)
theorem kid05_part803_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part803) = true := by rfl

def kid05_part804 : Audit := .cycle 1 13 true (1)
theorem kid05_part804_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part804) = true := by rfl

def kid05_part805 : Audit := .cycle 2 10 true (1)
theorem kid05_part805_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part805) = true := by rfl

def kid05_part806 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.last 14 (4,true),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 11 1 true (3),
.last 15 (4,true),
.last 14 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.cycle 11 1 true (3)
])
theorem kid05_part806_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part806) = true := by rfl

def kid05_part782 : Audit := .split 10 (2,true) (byMove [(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799),(kid05_part800),(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806)])

theorem kid05_part782_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part782) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799),(kid05_part800),(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part783_checked

  · exact kid05_part789_checked

  · exact kid05_part795_checked

  · exact kid05_part801_checked

  · exact kid05_part784_checked

  · exact kid05_part790_checked

  · exact kid05_part796_checked

  · exact kid05_part802_checked

  · exact kid05_part785_checked

  · exact kid05_part791_checked

  · exact kid05_part797_checked

  · exact kid05_part803_checked

  · exact kid05_part786_checked

  · exact kid05_part792_checked

  · exact kid05_part798_checked

  · exact kid05_part804_checked

  · exact kid05_part787_checked

  · exact kid05_part793_checked

  · exact kid05_part799_checked

  · exact kid05_part805_checked

  · exact kid05_part788_checked

  · exact kid05_part794_checked

  · exact kid05_part800_checked

  · exact kid05_part806_checked

def kid05_part807 : Audit := .cycle 0 11 true (0)
theorem kid05_part807_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part807) = true := by rfl

def kid05_part809 : Audit := .cycle 1 11 true (1)
theorem kid05_part809_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part809) = true := by rfl

def kid05_part810 : Audit := .split 16 (5,false) (byMove [
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
.cycle 11 7 false (1),
.last 18 (2,true),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 69 (2,true),
.cycle 1 16 false (3),
.cycle 11 11 false (1),
.cycle 1 19 false (3),
.cycle 17 1 true (-1),
.cycle 16 1 true (-2)
])
theorem kid05_part810_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part810) = true := by rfl

def kid05_part811 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.last 13 (5,false),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 14 1 false (0),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 12 (5,false),
.cycle 13 6 false (1),
.last 13 (5,false),
.cycle 1 15 true (-1),
.cycle 1 13 true (0),
.cycle 14 1 false (0),
.last 16 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.last 12 (5,false)
])
theorem kid05_part811_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part811) = true := by rfl

def kid05_part812 : Audit := .cycle 0 12 true (0)
theorem kid05_part812_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part812) = true := by rfl

def kid05_part813 : Audit := .cycle 13 1 true (-1)
theorem kid05_part813_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part813) = true := by rfl

def kid05_part814 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (-2),
.cycle 21 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 3 false (-1),
.cycle 13 1 false (-1),
.cycle 16 3 false (0),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 14 3 false (1),
.cycle 15 3 false (1),
.cycle 16 3 false (-2),
.last 15 (2,true),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 18 3 false (0),
.cycle 9 5 false (2),
.cycle 16 3 false (0)
])
theorem kid05_part814_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part814) = true := by rfl

def kid05_part815 : Audit := .cycle 0 11 true (0)
theorem kid05_part815_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part815) = true := by rfl

def kid05_part816 : Audit := .cycle 1 10 true (1)
theorem kid05_part816_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part816) = true := by rfl

def kid05_part817 : Audit := .cycle 0 23 true (0)
theorem kid05_part817_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part817) = true := by rfl

def kid05_part818 : Audit := .cycle 3 8 true (1)
theorem kid05_part818_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part818) = true := by rfl

def kid05_part819 : Audit := .cycle 11 1 true (3)
theorem kid05_part819_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part819) = true := by rfl

def kid05_part820 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (2),
.cycle 15 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 8 8 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 9 3 true (1),
.cycle 8 13 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
theorem kid05_part820_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part820) = true := by rfl

def kid05_part821 : Audit := .cycle 16 5 false (0)
theorem kid05_part821_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part821) = true := by rfl

def kid05_part822 : Audit := .split 16 (5,false) (byMove [
.cycle 18 32 true (-2),
.cycle 11 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 25 (2,true),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.last 18 (2,true),
.cycle 0 28 true (-2),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.cycle 11 7 false (1),
.last 18 (2,true),
.cycle 11 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.last 22 (2,true),
.last 18 (2,true),
.cycle 0 28 true (-2),
.cycle 11 9 false (1),
.cycle 9 8 false (2),
.cycle 14 5 false (0)
])
theorem kid05_part822_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part822) = true := by rfl

def kid05_part823 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.last 13 (5,false),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 9 13 false (2),
.last 16 (5,false),
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 1 28 true (0),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 13 (5,false),
.cycle 1 23 true (-1),
.cycle 19 1 false (-1),
.cycle 18 3 false (1),
.last 16 (5,false),
.cycle 1 12 true (1),
.cycle 1 17 true (-1),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 1 29 true (-1)
])
theorem kid05_part823_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part823) = true := by rfl

def kid05_part824 : Audit := .cycle 1 12 true (1)
theorem kid05_part824_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part824) = true := by rfl

def kid05_part825 : Audit := .cycle 11 3 false (1)
theorem kid05_part825_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part825) = true := by rfl

def kid05_part826 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 8 14 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 9 6 false (2),
.cycle 13 1 false (-1),
.cycle 16 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 17 3 false (1),
.cycle 12 2 true (-1),
.cycle 14 3 false (0),
.cycle 16 3 false (-2),
.last 15 (2,true),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 14 3 false (-1),
.cycle 13 1 false (-1),
.cycle 11 5 false (1),
.cycle 15 3 false (-1),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 14 3 false (0),
.cycle 11 3 false (1)
])
theorem kid05_part826_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part826) = true := by rfl

def kid05_part827 : Audit := .cycle 0 11 true (0)
theorem kid05_part827_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part827) = true := by rfl

def kid05_part828 : Audit := .cycle 1 10 true (1)
theorem kid05_part828_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part828) = true := by rfl

def kid05_part829 : Audit := .cycle 2 9 true (1)
theorem kid05_part829_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part829) = true := by rfl

def kid05_part830 : Audit := .cycle 1 13 true (1)
theorem kid05_part830_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part830) = true := by rfl

def kid05_part831 : Audit := .cycle 11 1 true (3)
theorem kid05_part831_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part831) = true := by rfl

def kid05_part832 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 2 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 12 2 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3),
.cycle 14 2 true (1),
.cycle 13 2 true (0),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 12 2 true (2),
.cycle 12 2 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 11 1 true (3)
])
theorem kid05_part832_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part832) = true := by rfl

def kid05_part808 : Audit := .split 10 (4,true) (byMove [(kid05_part809),(kid05_part810),(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832)])

theorem kid05_part808_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part808) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part809),(kid05_part810),(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part809_checked

  · exact kid05_part815_checked

  · exact kid05_part821_checked

  · exact kid05_part827_checked

  · exact kid05_part810_checked

  · exact kid05_part816_checked

  · exact kid05_part822_checked

  · exact kid05_part828_checked

  · exact kid05_part811_checked

  · exact kid05_part817_checked

  · exact kid05_part823_checked

  · exact kid05_part829_checked

  · exact kid05_part812_checked

  · exact kid05_part818_checked

  · exact kid05_part824_checked

  · exact kid05_part830_checked

  · exact kid05_part813_checked

  · exact kid05_part819_checked

  · exact kid05_part825_checked

  · exact kid05_part831_checked

  · exact kid05_part814_checked

  · exact kid05_part820_checked

  · exact kid05_part826_checked

  · exact kid05_part832_checked

def kid05_part834 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 13 8 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 13 5 false (2),
.cycle 0 15 true (0),
.cycle 13 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 16 (5,false),
.last 15 (5,false),
.cycle 13 7 false (2),
.cycle 13 8 false (2),
.cycle 13 13 false (2),
.cycle 1 16 true (0),
.cycle 11 4 true (0),
.cycle 13 5 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 17 true (0),
.last 16 (5,false),
.last 15 (5,false)
])
theorem kid05_part834_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part834) = true := by rfl

def kid05_part835 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (3),
.last 30 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 77 36 false (0),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 1 16 true (-1),
.cycle 0 23 true (-1),
.proven (BB6.Agent11Raw39Pumps.M317.table) (fun m hm => BB6.Agent11Raw39Pumps.M317.never m hm),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.last 22 (2,true),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 0 36 true (-2),
.last 18 (2,true),
.cycle 0 23 true (-2),
.last 28 (2,true)
])
theorem kid05_part835_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part835) = true := by rfl

def kid05_part836 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 20 1 false (0),
.cycle 37 1 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 17 1 false (1),
.last 13 (5,false),
.cycle 20 1 false (-2),
.last 16 (5,false),
.cycle 22 1 false (0),
.cycle 13 1 false (-1),
.cycle 17 1 false (-1),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (0),
.last 13 (5,false)
])
theorem kid05_part836_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part836) = true := by rfl

def kid05_part837 : Audit := .cycle 19 1 false (-1)
theorem kid05_part837_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part837) = true := by rfl

def kid05_part838 : Audit := .split 14 (5,false) (byMove [
.cycle 0 19 true (-1),
.cycle 12 15 false (0),
.last 15 (2,true),
.last 18 (2,true),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 7 9 false (3),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 0 36 true (-2),
.cycle 21 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 0, 64],64⟩,
.cycle 12 8 false (0),
.last 18 (2,true),
.last 15 (2,true),
.last 18 (2,true),
.cycle 12 3 false (0),
.cycle 12 6 false (0),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.cycle 29 2 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 0, 64],64⟩
])
theorem kid05_part838_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part838) = true := by rfl

def kid05_part839 : Audit := .split 16 (5,false) (byMove [
.cycle 18 32 true (-2),
.cycle 12 12 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 4 false (-1),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.last 18 (2,true),
.cycle 0 28 true (-2),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 6 true (-2),
.cycle 12 7 false (0),
.last 18 (2,true),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 0 28 true (-2),
.cycle 12 9 false (0),
.cycle 9 8 false (2),
.cycle 10 8 false (2)
])
theorem kid05_part839_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part839) = true := by rfl

def kid05_part840 : Audit := .cycle 1 12 true (1)
theorem kid05_part840_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part840) = true := by rfl

def kid05_part841 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 16 true (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 13 2 true (1),
.cycle 13 1 true (1),
.cycle 15 8 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 14 5 false (1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 2 true (1),
.cycle 13 1 true (1)
])
theorem kid05_part841_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part841) = true := by rfl

def kid05_part842 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 14 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 7 false (1),
.last 24 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 9 4 true (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
theorem kid05_part842_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part842) = true := by rfl

def kid05_part843 : Audit := .cycle 0 13 true (0)
theorem kid05_part843_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part843) = true := by rfl

def kid05_part844 : Audit := .split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 1 16 true (1),
.last 15 (2,true),
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
.last 18 (2,true),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 11 4 true (1),
.cycle 11 8 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4)
])
theorem kid05_part844_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part844) = true := by rfl

def kid05_part845 : Audit := .cycle 8 4 true (1)
theorem kid05_part845_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part845) = true := by rfl

def kid05_part846 : Audit := .cycle 13 6 false (1)
theorem kid05_part846_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part846) = true := by rfl

def kid05_part847 : Audit := .split 13 (5,false) (byMove [
.cycle 1 18 true (-2),
.last 26 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 18 (2,true),
.cycle 13 1 false (-1),
.last 21 (2,true),
.last 15 (2,true),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.last 18 (2,true),
.last 20 (2,true),
.last 21 (2,true),
.last 15 (2,true),
.last 23 (2,true),
.cycle 14 1 false (-2),
.last 18 (2,true),
.cycle 13 1 false (-1),
.last 19 (2,true),
.last 15 (2,true),
.cycle 1 16 true (-1),
.last 23 (2,true),
.cycle 9 5 false (2),
.cycle 10 5 false (2)
])
theorem kid05_part847_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part847) = true := by rfl

def kid05_part848 : Audit := .split 12 (2,true) (byMove [
.cycle 14 19 true (0),
.cycle 1 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 1 21 true (-1),
.last 14 (5,false),
.cycle 16 1 false (4),
.cycle 1 14 true (0),
.cycle 1 16 true (0),
.cycle 1 27 true (-1),
.cycle 1 39 true (-3),
.last 16 (5,false),
.cycle 1 23 true (-1),
.cycle 13 1 false (-1),
.cycle 11 18 true (-2),
.last 13 (5,false),
.cycle 1 19 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 384, 2048, 4096, 128, 256, 8, 128, 2048, 4096, 4096],[128, 4096, 128, 1, 1, 128, 128, 256, 128, 1, 256, 128, 4096],7216⟩,
.cycle 2 13 true (0),
.cycle 1 14 true (0),
.cycle 11 2 true (0),
.cycle 1 25 true (-1)
])
theorem kid05_part848_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part848) = true := by rfl

def kid05_part849 : Audit := .cycle 19 1 false (-1)
theorem kid05_part849_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part849) = true := by rfl

def kid05_part850 : Audit := .cycle 12 3 false (0)
theorem kid05_part850_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part850) = true := by rfl

def kid05_part851 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.last 50 (2,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 4 false (-1),
.cycle 16 1 false (-2),
.cycle 12 7 false (0),
.last 20 (2,true),
.last 17 (2,true),
.last 28 (2,true),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 12 7 false (0),
.last 18 (2,true),
.cycle 12 9 false (0),
.cycle 17 1 false (-3),
.cycle 13 4 false (0),
.cycle 16 1 false (-2),
.cycle 14 5 false (0),
.cycle 12 6 false (0),
.last 17 (2,true),
.cycle 5 12 false (3),
.cycle 11 6 false (1),
.cycle 14 3 false (0)
])
theorem kid05_part851_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part851) = true := by rfl

def kid05_part852 : Audit := .cycle 1 12 true (1)
theorem kid05_part852_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part852) = true := by rfl

def kid05_part853 : Audit := .cycle 13 5 false (1)
theorem kid05_part853_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part853) = true := by rfl

def kid05_part854 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 20 (5,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 14 (5,false),
.last 13 (5,false),
.cycle 15 7 false (1),
.last 20 (5,false),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 14 (5,false),
.last 13 (5,false)
])
theorem kid05_part854_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part854) = true := by rfl

def kid05_part855 : Audit := .cycle 0 13 true (0)
theorem kid05_part855_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part855) = true := by rfl

def kid05_part856 : Audit := .split 14 (5,false) (byMove [
.cycle 1 15 true (1),
.cycle 10 6 true (1),
.last 15 (2,true),
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
.cycle 9 10 true (1),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 11 4 true (1),
.cycle 11 6 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 2 true (3),
.cycle 14 1 true (4)
])
theorem kid05_part856_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part856) = true := by rfl

def kid05_part857 : Audit := .cycle 10 2 true (1)
theorem kid05_part857_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part857) = true := by rfl

def kid05_part833 : Audit := .split 11 (4,true) (byMove [(kid05_part834),(kid05_part835),(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851),(kid05_part852),(kid05_part853),(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857)])

theorem kid05_part833_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part833) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some mv)) (byMove [(kid05_part834),(kid05_part835),(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851),(kid05_part852),(kid05_part853),(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part834_checked

  · exact kid05_part840_checked

  · exact kid05_part846_checked

  · exact kid05_part852_checked

  · exact kid05_part835_checked

  · exact kid05_part841_checked

  · exact kid05_part847_checked

  · exact kid05_part853_checked

  · exact kid05_part836_checked

  · exact kid05_part842_checked

  · exact kid05_part848_checked

  · exact kid05_part854_checked

  · exact kid05_part837_checked

  · exact kid05_part843_checked

  · exact kid05_part849_checked

  · exact kid05_part855_checked

  · exact kid05_part838_checked

  · exact kid05_part844_checked

  · exact kid05_part850_checked

  · exact kid05_part856_checked

  · exact kid05_part839_checked

  · exact kid05_part845_checked

  · exact kid05_part851_checked

  · exact kid05_part857_checked

def kid05_part545 : Audit := .split 9 (4,false) (byMove [(kid05_part546),(kid05_part571),(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part651),(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part680),(kid05_part705),(kid05_part706),(kid05_part731),(kid05_part756),(kid05_part757),(kid05_part782),(kid05_part807),(kid05_part808),(kid05_part833)])

theorem kid05_part545_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (kid05_part545) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part546),(kid05_part571),(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part651),(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part680),(kid05_part705),(kid05_part706),(kid05_part731),(kid05_part756),(kid05_part757),(kid05_part782),(kid05_part807),(kid05_part808),(kid05_part833)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part546_checked

  · exact kid05_part624_checked

  · exact kid05_part654_checked

  · exact kid05_part756_checked

  · exact kid05_part571_checked

  · exact kid05_part625_checked

  · exact kid05_part655_checked

  · exact kid05_part757_checked

  · exact kid05_part596_checked

  · exact kid05_part626_checked

  · exact kid05_part680_checked

  · exact kid05_part782_checked

  · exact kid05_part597_checked

  · exact kid05_part651_checked

  · exact kid05_part705_checked

  · exact kid05_part807_checked

  · exact kid05_part598_checked

  · exact kid05_part652_checked

  · exact kid05_part706_checked

  · exact kid05_part808_checked

  · exact kid05_part623_checked

  · exact kid05_part653_checked

  · exact kid05_part731_checked

  · exact kid05_part833_checked

def kid05_part859 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (0),
.cycle 11 6 false (2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 0 16 false (3),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 11 6 false (2),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 11 13 false (3),
.cycle 11 11 false (2),
.last 14 (4,false),
.cycle 0 15 true (0),
.cycle 11 8 false (2),
.cycle 0 20 true (-2),
.last 15 (4,false),
.cycle 1 15 true (0),
.last 15 (4,false),
.cycle 11 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.last 14 (4,false),
.cycle 1 15 true (0)
]),
.cycle 11 6 false (2),
.cycle 0 13 true (0),
.cycle 11 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.last 15 (4,true),
.cycle 1 15 true (0),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.last 29 (4,true),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 0 15 true (0),
.last 23 (4,true),
.cycle 11 3 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.last 15 (4,true),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 11 12 true (1),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 1 15 true (0)
]),
.cycle 0 14 true (0),
.cycle 11 8 false (2),
.cycle 11 6 false (2),
.cycle 11 11 false (2),
.cycle 1 14 true (0),
.split 13 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 0 16 false (3),
.last 15 (4,false),
.cycle 11 9 false (2),
.last 15 (4,false),
.cycle 11 6 false (2),
.cycle 1 14 true (0),
.cycle 1 16 true (0),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 8 6 true (0),
.cycle 11 8 false (2),
.cycle 1 20 true (-2),
.last 15 (4,false),
.cycle 11 9 false (2),
.last 15 (4,false),
.cycle 11 6 false (2),
.cycle 1 14 true (0),
.cycle 11 8 false (2),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 15 (4,false),
.cycle 11 8 false (2)
]),
.cycle 11 6 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.last 21 (4,true),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 14 true (0),
.cycle 11 13 true (1),
.cycle 24 15 true (2),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.cycle 0 15 true (0),
.last 23 (4,true),
.last 21 (4,true),
.last 15 (4,true),
.cycle 1 15 true (0),
.last 14 (4,true),
.last 21 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 1 15 true (0)
]),
.cycle 1 14 true (0)
])
theorem kid05_part859_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part859) = true := by rfl

def kid05_part860 : Audit := .split 26 (2,true) (byMove [
.cycle 18 19 true (-3),
.cycle 18 36 false (4),
.cycle 18 51 false (3),
.cycle 1 41 false (5),
.split 27 (4,true) (byMove [
.cycle 1 39 false (3),
.cycle 1 29 false (3),
.last 29 (4,false),
.cycle 0 29 true (-3),
.last 29 (4,false),
.cycle 18 36 false (4),
.cycle 1 41 false (5),
.cycle 21 98 true (-3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 8, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 4, 393, 128, 393, 8, 1, 4, 393, 4096],5136⟩,
.cycle 129 45 true (-2),
.last 28 (4,false),
.cycle 1 39 false (3),
.cycle 18 38 false (4),
.cycle 1 29 false (3),
.last 29 (4,false),
.cycle 1 29 true (-3),
.last 29 (4,false),
.cycle 18 36 false (4),
.cycle 21 100 true (-3),
.cycle 18 19 true (-3),
.cycle 1 37 false (3),
.cycle 1 43 false (5),
.last 28 (4,false),
.cycle 18 38 false (4)
]),
.cycle 18 36 false (4),
.cycle 169 109 true (-6),
.cycle 21 47 true (-3),
.cycle 1 37 false (4),
.cycle 1 35 false (3),
.split 27 (4,false) (byMove [
.cycle 21 100 true (-3),
.cycle 18 19 true (-3),
.cycle 1 37 false (3),
.cycle 1 43 false (5),
.last 29 (4,true),
.cycle 18 38 false (4),
.cycle 21 74 true (-3),
.cycle 284 113 true (8),
.proven (BB6.Agent11Raw39Pumps.M322.table) (fun m hm => BB6.Agent11Raw39Pumps.M322.never m hm),
.cycle 1 37 false (4),
.cycle 27 1 true (3),
.cycle 21 49 true (-3),
.cycle 73 60 true (-4),
.cycle 25 3 true (1),
.cycle 21 78 true (-3),
.cycle 1 35 false (3),
.last 29 (4,true),
.cycle 18 11 true (-3),
.last 65 (4,true),
.cycle 169 109 true (-6),
.cycle 21 47 true (-3),
.cycle 21 78 true (-3),
.cycle 27 1 true (3),
.cycle 18 40 false (4)
]),
.cycle 18 19 true (-3),
.cycle 18 38 false (4),
.cycle 69 56 true (-4),
.cycle 129 45 true (-2),
.cycle 1 41 false (5),
.split 27 (4,true) (byMove [
.cycle 25 4 true (0),
.cycle 1 29 false (3),
.last 29 (4,false),
.cycle 123 43 true (-2),
.last 29 (4,false),
.cycle 69 56 true (-4),
.cycle 1 41 false (5),
.cycle 1 31 false (3),
.last 29 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 393, 4096, 8, 128, 256, 8, 128, 4096, 393, 4096],[128, 393, 4096, 1, 8, 393, 128, 393, 1, 1, 8, 393, 4096],5136⟩,
.last 29 (4,false),
.cycle 1 31 false (3),
.cycle 71 58 true (-4),
.cycle 1 29 false (3),
.last 29 (4,false),
.cycle 125 43 true (-2),
.last 29 (4,false),
.cycle 69 56 true (-4),
.cycle 21 100 true (-3),
.cycle 18 38 false (4),
.cycle 26 2 true (1),
.cycle 181 117 true (-6),
.last 29 (4,false),
.cycle 71 58 true (-4)
]),
.cycle 69 56 true (-4),
.cycle 46 86 true (-1),
.cycle 21 96 true (-3),
.cycle 18 17 true (-3),
.cycle 181 117 true (-6),
.split 27 (4,false) (byMove [
.cycle 21 100 true (-3),
.cycle 18 38 false (4),
.cycle 26 2 true (2),
.cycle 181 117 true (-6),
.last 28 (4,true),
.cycle 71 58 true (-4),
.cycle 94 46 true (1),
.cycle 21 56 true (-3),
.cycle 21 92 true (-3),
.cycle 18 17 true (-3),
.cycle 27 1 true (3),
.cycle 21 100 true (-3),
.cycle 73 60 true (-4),
.cycle 25 11 true (-2),
.last 29 (4,true),
.cycle 181 117 true (-6),
.last 28 (4,true),
.cycle 79 73 true (-4),
.cycle 163 192 true (-4),
.cycle 46 86 true (-1),
.cycle 21 96 true (-3),
.cycle 98 48 true (1),
.cycle 27 1 true (3),
.cycle 73 60 true (-4)
]),
.cycle 18 38 false (4)
])
theorem kid05_part860_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part860) = true := by rfl

def kid05_part861 : Audit := .split 10 (2,true) (byMove [
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 22 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (4,true),
.cycle 14 1 false (0),
.cycle 17 1 false (-3),
.last 14 (4,true),
.last 17 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (4,true),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 9 3 false (1)
]),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 1 12 true (0),
.cycle 15 1 false (1),
.cycle 15 1 false (5),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.last 14 (4,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 14 1 false (0),
.cycle 1 12 true (0),
.cycle 16 1 false (0),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 16 1 false (0)
]),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.cycle 16 1 false (-2),
.cycle 18 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 28 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (4,true),
.cycle 15 1 false (-1),
.cycle 10 2 true (-1),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-3),
.last 14 (4,true),
.last 17 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 14 1 false (-2),
.last 15 (4,true),
.cycle 16 1 false (-2),
.last 13 (4,true),
.cycle 7 7 false (3),
.last 12 (4,true),
.cycle 16 1 false (-2)
]),
.cycle 13 1 false (-1),
.cycle 17 1 false (-1),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.cycle 1 16 true (0),
.cycle 15 1 false (-1),
.cycle 10 2 true (0),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (0),
.cycle 34 1 false (0),
.cycle 32 1 false (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (0),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 13 (4,true),
.cycle 18 1 false (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (0),
.cycle 17 1 false (-1),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 17 1 false (-1)
]),
.cycle 9 2 true (0)
])
theorem kid05_part861_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part861) = true := by rfl

def kid05_part862 : Audit := .cycle 15 1 false (-1)
theorem kid05_part862_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part862) = true := by rfl

def kid05_part864 : Audit := .cycle 0 15 true (-1)
theorem kid05_part864_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part864) = true := by rfl

def kid05_part865 : Audit := .split 20 (4,false) (byMove [
.cycle 22 34 true (-2),
.cycle 11 10 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 17 5 false (1),
.last 22 (2,true),
.cycle 0 30 true (-2),
.cycle 21 1 false (-1),
.cycle 10 12 true (-2),
.cycle 19 2 true (-2),
.cycle 17 5 false (1),
.last 22 (2,true),
.cycle 17 7 false (1),
.cycle 21 1 false (-3),
.cycle 20 1 false (-2),
.cycle 19 2 false (-1),
.cycle 18 6 false (0),
.last 22 (2,true),
.cycle 0 30 true (-2),
.cycle 14 7 false (1),
.cycle 17 6 false (1),
.cycle 9 12 false (1)
])
theorem kid05_part865_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part865) = true := by rfl

def kid05_part866 : Audit := .cycle 12 1 false (0)
theorem kid05_part866_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part866) = true := by rfl

def kid05_part867 : Audit := .cycle 11 1 false (-1)
theorem kid05_part867_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part867) = true := by rfl

def kid05_part868 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 11 10 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 15 1 true (1),
.cycle 11 2 true (-1),
.cycle 11 5 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 0 30 true (-2),
.last 16 (2,true),
.cycle 18 1 true (-2),
.cycle 9 3 false (1)
])
theorem kid05_part868_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part868) = true := by rfl

def kid05_part869 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 false (3),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.last 24 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 18 1 true (0),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 14 (2,true),
.last 32 (2,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 0 17 true (-2),
.cycle 1 12 false (3),
.last 26 (2,true),
.cycle 0 19 true (-2),
.cycle 19 6 false (-1),
.cycle 9 4 false (1)
])
theorem kid05_part869_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part869) = true := by rfl

def kid05_part870 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 12 10 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 0 18 true (-1),
.cycle 14 2 true (-1),
.cycle 11 5 false (2),
.last 17 (2,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 13 6 false (1),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.cycle 0 18 true (-1),
.cycle 9 7 false (2)
])
theorem kid05_part870_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part870) = true := by rfl

def kid05_part871 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (0),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.last 23 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.last 22 (4,false),
.last 20 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 15 (4,false),
.cycle 1 16 true (0),
.cycle 1 14 true (0),
.last 16 (4,false),
.last 15 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.last 13 (4,false),
.last 24 (4,false)
])
theorem kid05_part871_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part871) = true := by rfl

def kid05_part872 : Audit := .cycle 0 13 true (0)
theorem kid05_part872_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part872) = true := by rfl

def kid05_part873 : Audit := .cycle 11 1 false (1)
theorem kid05_part873_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part873) = true := by rfl

def kid05_part874 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 1 12 true (0),
.last 26 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 13 2 true (0),
.cycle 11 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 1 12 true (0),
.last 17 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 9 7 false (2)
])
theorem kid05_part874_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part874) = true := by rfl

def kid05_part875 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 11 10 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 5 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 16 1 true (2),
.cycle 11 2 true (0),
.cycle 11 5 false (1),
.last 14 (2,true),
.cycle 11 7 false (2),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 2 false (1),
.cycle 11 6 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 7 false (2),
.cycle 16 1 true (2),
.cycle 9 4 true (0)
])
theorem kid05_part875_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part875) = true := by rfl

def kid05_part876 : Audit := .split 15 (4,false) (byMove [
.last 22 (2,true),
.cycle 12 10 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 11 5 false (0),
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (-2),
.cycle 10 7 false (0),
.cycle 14 2 true (-3),
.cycle 11 5 false (0),
.last 17 (2,true),
.cycle 11 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 13 6 false (-1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 12 7 false (0),
.cycle 13 8 false (-1),
.cycle 9 7 false (1)
])
theorem kid05_part876_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part876) = true := by rfl

def kid05_part877 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 7 7 false (3),
.last 24 (4,false),
.cycle 0 15 true (-1),
.last 20 (4,false),
.last 13 (4,false),
.last 14 (4,false),
.last 17 (4,false),
.last 15 (4,false),
.last 27 (4,false),
.cycle 1 18 true (-1),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 19 (4,false),
.last 29 (4,false),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 13 (4,false),
.last 17 (4,false)
])
theorem kid05_part877_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part877) = true := by rfl

def kid05_part878 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 14 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 0 22 true (-1),
.cycle 16 2 true (-1),
.cycle 13 5 false (2),
.last 19 (2,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 15 6 false (1),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 14 7 false (2),
.last 20 (2,true),
.cycle 9 9 false (2)
])
theorem kid05_part878_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part878) = true := by rfl

def kid05_part879 : Audit := .cycle 11 1 false (-1)
theorem kid05_part879_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part879) = true := by rfl

def kid05_part880 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 21 10 false (-3),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (2,true),
.last 26 (2,true),
.last 12 (2,true),
.cycle 18 1 false (0),
.cycle 10 2 true (-1),
.cycle 13 2 true (-2),
.cycle 11 5 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.last 12 (2,true),
.cycle 7 7 false (3),
.cycle 10 3 false (0),
.cycle 9 7 false (1)
])
theorem kid05_part880_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part880) = true := by rfl

def kid05_part881 : Audit := .split 12 (4,false) (byMove [
.cycle 14 26 true (-2),
.cycle 11 10 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.last 14 (2,true),
.cycle 0 22 true (-2),
.cycle 13 1 false (-1),
.cycle 10 4 true (-2),
.cycle 11 2 true (-2),
.cycle 11 5 false (-1),
.last 14 (2,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 6 false (0),
.last 14 (2,true),
.cycle 0 22 true (-2),
.cycle 11 7 false (0),
.cycle 11 6 false (0),
.cycle 9 4 false (1)
])
theorem kid05_part881_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part881) = true := by rfl

def kid05_part882 : Audit := .split 16 (4,false) (byMove [
.cycle 18 21 true (-2),
.cycle 14 10 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 1 19 true (-2),
.cycle 17 1 false (-1),
.cycle 12 28 true (-2),
.cycle 15 2 true (-2),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 14 7 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 11 6 false (2),
.last 18 (2,true),
.cycle 1 19 true (-2),
.cycle 14 7 false (0),
.cycle 33 10 false (1),
.cycle 9 8 false (2)
])
theorem kid05_part882_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part882) = true := by rfl

def kid05_part883 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (0),
.last 16 (4,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 16 (4,false),
.cycle 0 13 true (0),
.last 22 (4,false),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 13 (4,false),
.last 14 (4,false),
.last 18 (4,false),
.last 16 (4,false),
.last 21 (4,false),
.cycle 1 14 true (0),
.last 18 (4,false),
.last 16 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 1 15 true (0),
.last 13 (4,false),
.cycle 1 14 true (0)
])
theorem kid05_part883_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part883) = true := by rfl

def kid05_part884 : Audit := .cycle 0 13 true (0)
theorem kid05_part884_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part884) = true := by rfl

def kid05_part885 : Audit := .split 17 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 11 10 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 14 5 false (2),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 1 22 true (-1),
.cycle 16 2 true (-1),
.cycle 14 5 false (2),
.last 19 (2,true),
.cycle 14 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 15 6 false (1),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 11 7 false (2),
.cycle 1 22 true (-1),
.cycle 9 9 false (2)
])
theorem kid05_part885_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part885) = true := by rfl

def kid05_part886 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 13 10 false (-1),
.last 12 (2,true),
.cycle 18 1 false (-2),
.cycle 10 2 true (0),
.cycle 13 2 false (-1),
.cycle 1 12 true (0),
.last 27 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 8 4 true (0),
.cycle 13 5 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 18 1 false (-2),
.cycle 13 3 true (1),
.cycle 13 2 false (-1),
.cycle 1 12 true (0),
.last 18 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 true (3),
.cycle 9 8 false (2)
])
theorem kid05_part886_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part886) = true := by rfl

def kid05_part887 : Audit := .cycle 9 2 true (0)
theorem kid05_part887_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part887) = true := by rfl

def kid05_part863 : Audit := .split 10 (4,true) (byMove [(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887)])

theorem kid05_part863_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part863) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part864_checked

  · exact kid05_part870_checked

  · exact kid05_part876_checked

  · exact kid05_part882_checked

  · exact kid05_part865_checked

  · exact kid05_part871_checked

  · exact kid05_part877_checked

  · exact kid05_part883_checked

  · exact kid05_part866_checked

  · exact kid05_part872_checked

  · exact kid05_part878_checked

  · exact kid05_part884_checked

  · exact kid05_part867_checked

  · exact kid05_part873_checked

  · exact kid05_part879_checked

  · exact kid05_part885_checked

  · exact kid05_part868_checked

  · exact kid05_part874_checked

  · exact kid05_part880_checked

  · exact kid05_part886_checked

  · exact kid05_part869_checked

  · exact kid05_part875_checked

  · exact kid05_part881_checked

  · exact kid05_part887_checked

def kid05_part888 : Audit := .cycle 11 1 false (-1)
theorem kid05_part888_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part888) = true := by rfl

def kid05_part889 : Audit := .cycle 1 10 true (1)
theorem kid05_part889_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part889) = true := by rfl

def kid05_part890 : Audit := .cycle 1 11 true (1)
theorem kid05_part890_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part890) = true := by rfl

def kid05_part891 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 15 1 false (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 1 28 true (0),
.cycle 13 6 false (1),
.cycle 0 16 true (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 0 27 true (0)
]),
.cycle 24 1 false (2),
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
.cycle 1 28 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.last 30 (4,true),
.cycle 7 6 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 28 (4,true)
]),
.cycle 34 1 false (8),
.cycle 14 5 false (0),
.cycle 0 34 true (-2),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 15 1 false (1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 0 28 true (-2),
.cycle 1 12 true (1),
.cycle 28 1 false (2),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 1 16 true (-1),
.last 27 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 13 5 false (1)
]),
.cycle 9 2 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 28 1 false (2),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.last 28 (4,true),
.cycle 6 6 true (1),
.cycle 0 16 true (0),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.last 29 (4,true)
]),
.cycle 9 13 true (1)
])
theorem kid05_part891_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part891) = true := by rfl

def kid05_part892 : Audit := .cycle 0 11 true (0)
theorem kid05_part892_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part892) = true := by rfl

def kid05_part894 : Audit := .cycle 0 11 true (0)
theorem kid05_part894_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part894) = true := by rfl

def kid05_part895 : Audit := .cycle 1 10 true (1)
theorem kid05_part895_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part895) = true := by rfl

def kid05_part896 : Audit := .cycle 21 1 false (1)
theorem kid05_part896_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part896) = true := by rfl

def kid05_part897 : Audit := .cycle 1 13 true (0)
theorem kid05_part897_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part897) = true := by rfl

def kid05_part898 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 11 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 15 2 true (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1)
])
theorem kid05_part898_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part898) = true := by rfl

def kid05_part899 : Audit := .split 12 (4,false) (byMove [
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
.cycle 16 7 false (0),
.last 14 (2,true),
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
theorem kid05_part899_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part899) = true := by rfl

def kid05_part900 : Audit := .cycle 0 11 true (0)
theorem kid05_part900_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part900) = true := by rfl

def kid05_part901 : Audit := .cycle 1 10 true (1)
theorem kid05_part901_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part901) = true := by rfl

def kid05_part902 : Audit := .cycle 1 24 true (0)
theorem kid05_part902_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part902) = true := by rfl

def kid05_part903 : Audit := .cycle 20 1 false (2)
theorem kid05_part903_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part903) = true := by rfl

def kid05_part904 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (1),
.last 13 (2,true),
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
theorem kid05_part904_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part904) = true := by rfl

def kid05_part905 : Audit := .split 12 (4,false) (byMove [
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
.cycle 7 7 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 29 1 false (5),
.cycle 30 1 false (6),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part905_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part905) = true := by rfl

def kid05_part906 : Audit := .cycle 14 5 false (0)
theorem kid05_part906_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part906) = true := by rfl

def kid05_part907 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 21 (4,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.cycle 16 7 false (0),
.last 21 (4,false),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 16 (4,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 14 (4,false)
])
theorem kid05_part907_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part907) = true := by rfl

def kid05_part908 : Audit := .cycle 0 13 true (0)
theorem kid05_part908_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part908) = true := by rfl

def kid05_part909 : Audit := .cycle 18 1 false (0)
theorem kid05_part909_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part909) = true := by rfl

def kid05_part910 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 0 38 true (-2),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 2 true (-2),
.cycle 1 12 true (1),
.cycle 1 14 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.cycle 13 5 false (1)
])
theorem kid05_part910_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part910) = true := by rfl

def kid05_part911 : Audit := .cycle 9 2 true (1)
theorem kid05_part911_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part911) = true := by rfl

def kid05_part912 : Audit := .cycle 0 11 true (0)
theorem kid05_part912_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part912) = true := by rfl

def kid05_part913 : Audit := .cycle 1 10 true (1)
theorem kid05_part913_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part913) = true := by rfl

def kid05_part914 : Audit := .cycle 2 9 true (1)
theorem kid05_part914_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part914) = true := by rfl

def kid05_part915 : Audit := .cycle 1 13 true (1)
theorem kid05_part915_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part915) = true := by rfl

def kid05_part916 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 1 14 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid05_part916_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part916) = true := by rfl

def kid05_part917 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 4 true (4),
.cycle 9 13 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3),
.cycle 15 4 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 14 4 true (1),
.cycle 9 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part917_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part917) = true := by rfl

def kid05_part893 : Audit := .split 10 (4,true) (byMove [(kid05_part894),(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904),(kid05_part905),(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917)])

theorem kid05_part893_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part893) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part894),(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904),(kid05_part905),(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part894_checked

  · exact kid05_part900_checked

  · exact kid05_part906_checked

  · exact kid05_part912_checked

  · exact kid05_part895_checked

  · exact kid05_part901_checked

  · exact kid05_part907_checked

  · exact kid05_part913_checked

  · exact kid05_part896_checked

  · exact kid05_part902_checked

  · exact kid05_part908_checked

  · exact kid05_part914_checked

  · exact kid05_part897_checked

  · exact kid05_part903_checked

  · exact kid05_part909_checked

  · exact kid05_part915_checked

  · exact kid05_part898_checked

  · exact kid05_part904_checked

  · exact kid05_part910_checked

  · exact kid05_part916_checked

  · exact kid05_part899_checked

  · exact kid05_part905_checked

  · exact kid05_part911_checked

  · exact kid05_part917_checked

def kid05_part918 : Audit := .cycle 8 2 true (1)
theorem kid05_part918_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part918) = true := by rfl

def kid05_part919 : Audit := .cycle 11 4 false (1)
theorem kid05_part919_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part919) = true := by rfl

def kid05_part920 : Audit := .split 13 (2,true) (byMove [
.cycle 1 18 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 7 13 false (3),
.split 14 (4,true) (byMove [
.cycle 0 15 false (3),
.cycle 11 12 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 7 13 false (3),
.cycle 1 18 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 11 4 true (-2),
.cycle 11 7 false (-1),
.cycle 12 3 false (-1),
.last 22 (4,false),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 23 8 false (-1),
.cycle 1 18 true (-2),
.cycle 79 66 true (-4),
.cycle 4 17 false (3),
.last 15 (4,false),
.cycle 9 6 false (1)
]),
.cycle 11 4 false (-1),
.cycle 7 8 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 2, 1, 64, 15, 64],80⟩,
.cycle 1 16 true (-2),
.cycle 67 54 true (-4),
.split 14 (4,false) (byMove [
.last 18 (4,true),
.cycle 1 18 true (-2),
.last 25 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.cycle 9 6 false (1),
.last 21 (4,true),
.last 36 (4,true),
.last 16 (4,true),
.cycle 1 16 true (-2),
.last 15 (4,true),
.last 19 (4,true),
.last 22 (4,true),
.last 17 (4,true),
.last 23 (4,true),
.last 23 (4,true),
.last 16 (4,true),
.cycle 9 6 false (1),
.cycle 8 10 false (2),
.cycle 7 8 false (3),
.last 16 (4,true),
.cycle 27 12 false (1),
.last 15 (4,true),
.cycle 8 8 false (2)
]),
.cycle 8 16 false (2),
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 20 9 false (1),
.cycle 5 13 false (3),
.split 14 (4,true) (byMove [
.cycle 16 4 true (-3),
.cycle 21 17 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 6 13 false (3),
.cycle 10 5 false (0),
.last 16 (4,false),
.cycle 0 29 true (-2),
.last 16 (4,false),
.cycle 11 5 false (-1),
.cycle 11 7 false (-1),
.cycle 12 3 false (-1),
.last 22 (4,false),
.cycle 15 1 false (-3),
.last 15 (4,false),
.cycle 11 4 false (-1),
.cycle 23 8 false (-1),
.cycle 11 6 false (-1),
.cycle 13 2 true (-2),
.cycle 7 10 false (3),
.last 16 (4,false),
.cycle 11 6 false (-1)
]),
.cycle 11 4 false (-1),
.cycle 15 8 false (1),
.cycle 19 6 false (-1),
.cycle 1 16 true (-2),
.cycle 4 10 false (3),
.split 14 (4,false) (byMove [
.last 18 (4,true),
.last 20 (4,true),
.cycle 13 2 true (-1),
.cycle 7 10 false (3),
.last 15 (4,true),
.last 20 (4,true),
.last 24 (4,true),
.last 22 (4,true),
.last 16 (4,true),
.cycle 1 16 true (-2),
.last 15 (4,true),
.last 22 (4,true),
.last 22 (4,true),
.last 20 (4,true),
.last 16 (4,true),
.cycle 5 10 false (3),
.last 15 (4,true),
.last 20 (4,true),
.last 24 (4,true),
.last 22 (4,true),
.last 16 (4,true),
.last 34 (4,true),
.last 15 (4,true),
.last 22 (4,true)
]),
.cycle 16 6 false (-2)
])
theorem kid05_part920_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part920) = true := by rfl

def kid05_part921 : Audit := .split 10 (2,true) (byMove [
.cycle 12 17 true (0),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.cycle 1 16 true (-2),
.last 26 (4,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 18 (4,true),
.last 21 (4,true),
.last 14 (4,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.last 13 (4,true),
.cycle 1 21 true (-1),
.last 51 (4,true),
.last 14 (4,true),
.last 23 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 18 (4,true),
.last 47 (4,true),
.last 14 (4,true),
.cycle 1 14 true (-1),
.last 23 (4,true),
.last 13 (4,true),
.cycle 9 3 false (1)
]),
.cycle 1 34 true (-2),
.cycle 1 17 true (-1),
.cycle 1 21 true (-1),
.cycle 14 1 false (4),
.cycle 1 12 true (0),
.split 11 (4,true) (byMove [
.last 15 (4,false),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 1 21 true (-1),
.cycle 1 12 true (0),
.cycle 0 16 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 1 16 true (0),
.last 21 (4,false),
.last 17 (4,false),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.cycle 1 21 true (-1),
.cycle 1 12 true (0),
.cycle 1 17 true (-1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 1 23 true (-1)
]),
.cycle 1 21 true (-1),
.cycle 38 64 true (-3),
.cycle 18 8 true (-3),
.cycle 1 19 true (-1),
.cycle 11 1 false (-1),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 1 21 true (-2),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 24 (4,true),
.last 21 (4,true),
.last 25 (4,true),
.cycle 10 2 true (-1),
.cycle 1 19 true (-1),
.last 12 (4,true),
.last 25 (4,true),
.last 21 (4,true),
.last 14 (4,true),
.last 23 (4,true),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.last 24 (4,true),
.last 47 (4,true),
.last 20 (4,true),
.last 13 (4,true),
.cycle 5 7 false (3),
.last 12 (4,true),
.last 26 (4,true)
]),
.cycle 11 14 true (-2),
.cycle 1 24 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 2, 1, 64, 15, 64],80⟩,
.cycle 2 11 true (0),
.cycle 1 12 true (0),
.split 11 (4,true) (byMove [
.last 15 (4,false),
.last 19 (4,false),
.last 13 (4,false),
.cycle 1 19 true (-1),
.last 13 (4,false),
.last 19 (4,false),
.cycle 1 12 true (0),
.cycle 1 27 true (0),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (0),
.last 21 (4,false),
.last 25 (4,false),
.cycle 10 2 true (0),
.cycle 1 19 true (-1),
.last 13 (4,false),
.last 25 (4,false),
.cycle 1 12 true (0),
.cycle 1 24 true (-2),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.last 27 (4,false)
]),
.cycle 26 16 true (-2)
])
theorem kid05_part921_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part921) = true := by rfl

def kid05_part922 : Audit := .cycle 15 1 false (-1)
theorem kid05_part922_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part922) = true := by rfl

def kid05_part924 : Audit := .split 13 (2,true) (byMove [
.cycle 12 17 true (0),
.last 17 (4,false),
.cycle 17 1 false (-1),
.cycle 7 9 false (3),
.cycle 0 19 true (-1),
.last 17 (4,false),
.cycle 1 14 true (-1),
.last 29 (4,false),
.cycle 1 32 true (-2),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.cycle 12 6 true (-1),
.last 19 (4,false),
.last 17 (4,false),
.last 22 (4,false),
.cycle 5 9 false (3),
.cycle 12 4 true (-1),
.last 17 (4,false),
.cycle 12 14 true (0),
.last 19 (4,false),
.cycle 12 13 true (0),
.cycle 0 15 true (-1),
.cycle 12 15 true (0),
.last 19 (4,false)
])
theorem kid05_part924_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part924) = true := by rfl

def kid05_part925 : Audit := .cycle 1 14 true (-1)
theorem kid05_part925_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part925) = true := by rfl

def kid05_part926 : Audit := .cycle 12 1 false (0)
theorem kid05_part926_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part926) = true := by rfl

def kid05_part927 : Audit := .cycle 11 1 false (-1)
theorem kid05_part927_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part927) = true := by rfl

def kid05_part928 : Audit := .split 11 (4,false) (byMove [
.cycle 1 16 true (-2),
.last 27 (2,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 13 5 false (1),
.last 13 (2,true),
.cycle 1 14 true (-1),
.cycle 12 1 false (0),
.cycle 17 1 true (1),
.cycle 12 3 false (0),
.cycle 11 5 false (-1),
.last 13 (2,true),
.cycle 15 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 13 6 false (1),
.last 13 (2,true),
.cycle 1 14 true (-1),
.last 22 (2,true),
.cycle 25 1 true (-3),
.cycle 9 3 false (1)
])
theorem kid05_part928_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part928) = true := by rfl

def kid05_part929 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.last 29 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (2,true),
.cycle 11 3 false (-1),
.last 13 (2,true),
.last 22 (2,true),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.cycle 11 5 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.last 15 (2,true),
.cycle 11 4 false (-1),
.last 13 (2,true),
.cycle 7 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part929_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part929) = true := by rfl

def kid05_part930 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.cycle 1 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 11 5 false (2),
.cycle 14 3 false (0),
.last 16 (2,true),
.cycle 1 17 true (-1),
.cycle 1 17 true (-1),
.cycle 13 3 false (1),
.cycle 12 5 false (2),
.last 17 (2,true),
.cycle 11 7 false (2),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 2 false (0),
.cycle 13 6 false (1),
.cycle 12 4 false (2),
.last 16 (2,true),
.cycle 1 17 true (-1),
.cycle 1 17 true (-1),
.cycle 13 4 false (1)
])
theorem kid05_part930_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part930) = true := by rfl

def kid05_part931 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 30 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.last 16 (2,true),
.cycle 11 3 false (1),
.last 14 (2,true),
.cycle 1 21 true (-1),
.last 16 (2,true),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.last 16 (2,true),
.cycle 12 4 false (0),
.last 14 (2,true),
.cycle 7 9 false (3),
.last 16 (2,true),
.cycle 12 4 false (0)
])
theorem kid05_part931_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part931) = true := by rfl

def kid05_part932 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (0),
.last 14 (4,false),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 14 1 false (4),
.last 14 (4,false),
.last 16 (4,false),
.last 16 (4,false),
.cycle 1 14 true (0),
.cycle 12 1 false (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 1 12 true (0),
.last 15 (4,false),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.last 22 (4,false),
.last 15 (4,false)
])
theorem kid05_part932_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part932) = true := by rfl

def kid05_part933 : Audit := .cycle 1 12 true (0)
theorem kid05_part933_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part933) = true := by rfl

def kid05_part934 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 27 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 22 3 false (4),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 14 3 false (4),
.cycle 13 5 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 13 2 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 23 (2,true),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid05_part934_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part934) = true := by rfl

def kid05_part935 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 30 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 5 false (1),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 1 21 true (-1),
.cycle 10 4 true (-1),
.cycle 11 3 false (1),
.cycle 11 5 false (1),
.last 15 (2,true),
.cycle 11 7 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 12 2 false (0),
.cycle 11 6 false (1),
.cycle 11 4 false (1),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 8 7 false (2),
.cycle 11 4 false (1)
])
theorem kid05_part935_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part935) = true := by rfl

def kid05_part936 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-3),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 12 5 false (0),
.cycle 14 3 false (-2),
.last 16 (2,true),
.last 19 (2,true),
.cycle 10 6 false (0),
.cycle 13 3 false (-1),
.cycle 11 5 false (0),
.last 17 (2,true),
.cycle 12 7 false (0),
.cycle 16 1 false (-4),
.cycle 15 1 false (-3),
.cycle 14 2 false (-2),
.cycle 13 6 false (-1),
.cycle 12 4 false (0),
.last 16 (2,true),
.last 19 (2,true),
.cycle 12 6 false (0),
.cycle 13 4 false (-1)
])
theorem kid05_part936_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part936) = true := by rfl

def kid05_part937 : Audit := .split 12 (2,true) (byMove [
.last 33 (4,false),
.last 15 (4,false),
.cycle 15 1 false (-1),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.cycle 6 7 false (3),
.cycle 9 5 false (1),
.last 26 (4,false),
.cycle 1 14 true (-1),
.last 19 (4,false),
.cycle 8 5 false (2),
.last 17 (4,false),
.last 15 (4,false),
.last 20 (4,false),
.last 18 (4,false),
.cycle 10 3 false (0),
.last 15 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.last 27 (4,false),
.cycle 1 14 true (-1),
.last 17 (4,false),
.last 17 (4,false)
])
theorem kid05_part937_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part937) = true := by rfl

def kid05_part938 : Audit := .split 17 (4,false) (byMove [
.last 20 (2,true),
.cycle 1 21 true (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 13 5 false (2),
.cycle 16 3 false (0),
.last 18 (2,true),
.cycle 1 19 true (-1),
.cycle 1 21 true (-1),
.cycle 15 3 false (1),
.cycle 14 5 false (2),
.last 19 (2,true),
.cycle 11 7 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 2 false (0),
.cycle 15 6 false (1),
.cycle 14 4 false (2),
.last 18 (2,true),
.cycle 1 19 true (-1),
.last 19 (2,true),
.cycle 15 4 false (1)
])
theorem kid05_part938_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part938) = true := by rfl

def kid05_part939 : Audit := .cycle 11 1 false (-1)
theorem kid05_part939_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part939) = true := by rfl

def kid05_part940 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.last 28 (2,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 5 false (1),
.cycle 11 3 false (0),
.last 12 (2,true),
.cycle 1 19 true (-1),
.cycle 10 2 true (-1),
.cycle 11 3 false (0),
.cycle 11 5 false (-1),
.last 13 (2,true),
.cycle 11 7 false (1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 6 false (1),
.cycle 11 4 false (0),
.last 12 (2,true),
.cycle 5 7 false (3),
.cycle 10 3 false (0),
.cycle 11 4 false (0)
])
theorem kid05_part940_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part940) = true := by rfl

def kid05_part941 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.last 29 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 5 false (0),
.cycle 11 3 false (-1),
.last 13 (2,true),
.last 22 (2,true),
.cycle 10 3 false (0),
.cycle 11 3 false (-1),
.cycle 11 5 false (-1),
.last 14 (2,true),
.cycle 11 7 false (0),
.cycle 13 1 false (-3),
.cycle 12 1 false (-2),
.cycle 11 2 false (-1),
.cycle 11 6 false (0),
.cycle 11 4 false (-1),
.last 13 (2,true),
.cycle 5 8 false (3),
.cycle 11 4 false (-1),
.cycle 11 4 false (-1)
])
theorem kid05_part941_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part941) = true := by rfl

def kid05_part942 : Audit := .split 16 (4,false) (byMove [
.last 19 (2,true),
.last 33 (2,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 14 5 false (0),
.cycle 15 3 false (-1),
.last 17 (2,true),
.cycle 1 24 true (-2),
.cycle 10 7 false (2),
.cycle 14 3 false (0),
.cycle 14 5 false (0),
.last 18 (2,true),
.cycle 14 7 false (0),
.cycle 17 1 false (-3),
.cycle 16 1 false (-2),
.cycle 15 2 false (-1),
.cycle 11 6 false (2),
.cycle 14 4 false (0),
.last 17 (2,true),
.cycle 5 12 false (3),
.cycle 13 8 false (1),
.cycle 13 4 false (1)
])
theorem kid05_part942_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part942) = true := by rfl

def kid05_part943 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 5 false (1),
.cycle 13 3 false (-1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 10 5 false (1),
.cycle 12 3 false (0),
.cycle 11 5 false (1),
.last 16 (2,true),
.cycle 11 7 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 6 false (0),
.cycle 11 4 false (1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 12 6 false (0),
.cycle 12 4 false (0)
])
theorem kid05_part943_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part943) = true := by rfl

def kid05_part944 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.last 14 (4,false),
.cycle 1 12 true (0),
.last 25 (4,false),
.last 23 (4,false),
.cycle 0 13 true (0),
.last 21 (4,false),
.cycle 8 4 true (0),
.last 16 (4,false),
.last 14 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 10 2 true (0),
.last 14 (4,false),
.cycle 1 12 true (0),
.last 16 (4,false),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 2 11 true (0),
.last 16 (4,false)
])
theorem kid05_part944_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part944) = true := by rfl

def kid05_part945 : Audit := .cycle 1 12 true (0)
theorem kid05_part945_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part945) = true := by rfl

def kid05_part946 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (0),
.last 35 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.cycle 17 2 false (-1),
.cycle 0 14 true (0),
.cycle 11 20 true (1),
.last 27 (2,true),
.cycle 3 11 true (0),
.cycle 13 1 true (3),
.cycle 8 8 true (0),
.cycle 18 5 false (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 11 3 true (1),
.cycle 17 2 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid05_part946_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part946) = true := by rfl

def kid05_part947 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 31 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 12 5 false (0),
.cycle 13 3 false (-1),
.last 15 (2,true),
.last 24 (2,true),
.cycle 10 5 false (1),
.cycle 12 3 false (0),
.cycle 12 5 false (0),
.last 16 (2,true),
.cycle 12 7 false (0),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 6 false (1),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 5 10 false (3),
.cycle 11 6 false (1),
.cycle 11 4 false (1)
])
theorem kid05_part947_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part947) = true := by rfl

def kid05_part923 : Audit := .split 10 (4,true) (byMove [(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929),(kid05_part930),(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943),(kid05_part944),(kid05_part945),(kid05_part946),(kid05_part947)])

theorem kid05_part923_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part923) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929),(kid05_part930),(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943),(kid05_part944),(kid05_part945),(kid05_part946),(kid05_part947)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part924_checked

  · exact kid05_part930_checked

  · exact kid05_part936_checked

  · exact kid05_part942_checked

  · exact kid05_part925_checked

  · exact kid05_part931_checked

  · exact kid05_part937_checked

  · exact kid05_part943_checked

  · exact kid05_part926_checked

  · exact kid05_part932_checked

  · exact kid05_part938_checked

  · exact kid05_part944_checked

  · exact kid05_part927_checked

  · exact kid05_part933_checked

  · exact kid05_part939_checked

  · exact kid05_part945_checked

  · exact kid05_part928_checked

  · exact kid05_part934_checked

  · exact kid05_part940_checked

  · exact kid05_part946_checked

  · exact kid05_part929_checked

  · exact kid05_part935_checked

  · exact kid05_part941_checked

  · exact kid05_part947_checked

def kid05_part948 : Audit := .cycle 11 1 false (-1)
theorem kid05_part948_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part948) = true := by rfl

def kid05_part949 : Audit := .cycle 1 10 true (1)
theorem kid05_part949_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part949) = true := by rfl

def kid05_part950 : Audit := .cycle 12 3 false (0)
theorem kid05_part950_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part950) = true := by rfl

def kid05_part951 : Audit := .split 10 (2,true) (byMove [
.cycle 1 11 true (1),
.cycle 11 11 false (1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (0),
.cycle 14 11 false (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 12 11 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 2 11 true (1),
.cycle 13 6 false (1),
.cycle 0 16 true (-1),
.last 13 (4,false),
.cycle 1 13 true (0),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 2 11 true (1)
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
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (4,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 2 11 true (1),
.last 19 (4,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.cycle 9 3 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1)
]),
.cycle 2 10 true (1),
.cycle 14 5 false (0),
.cycle 0 28 true (-2),
.cycle 1 23 true (-1),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.cycle 10 4 true (0),
.cycle 0 36 true (-2),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 13 (4,false),
.cycle 0 28 true (-2),
.cycle 1 12 true (1),
.cycle 2 12 true (1),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 1 16 true (-1),
.last 13 (4,false),
.cycle 19 1 false (-1),
.last 13 (4,false),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 13 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.last 17 (4,true),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1),
.last 19 (4,true),
.last 17 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1)
]),
.cycle 2 10 true (1)
])
theorem kid05_part951_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part951) = true := by rfl

def kid05_part952 : Audit := .cycle 0 11 true (0)
theorem kid05_part952_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part952) = true := by rfl

def kid05_part954 : Audit := .cycle 1 11 true (1)
theorem kid05_part954_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part954) = true := by rfl

def kid05_part955 : Audit := .split 17 (4,false) (byMove [
.cycle 1 18 false (3),
.cycle 15 3 false (-1),
.last 18 (2,true),
.cycle 0 19 false (3),
.cycle 11 14 false (1),
.cycle 12 6 false (0),
.cycle 7 22 false (3),
.cycle 11 13 true (-2),
.cycle 11 13 false (1),
.cycle 11 11 false (1),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2),
.cycle 11 8 false (1),
.cycle 15 3 false (-1),
.last 18 (2,true),
.cycle 1 19 false (3),
.cycle 33 16 false (1),
.cycle 12 6 false (0),
.cycle 29 10 false (1),
.last 37 (2,true),
.cycle 2 16 false (3),
.cycle 7 24 false (3),
.cycle 17 1 true (-1),
.cycle 16 2 true (-2)
])
theorem kid05_part955_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part955) = true := by rfl

def kid05_part956 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 14 1 false (0),
.last 17 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 13 6 false (1),
.last 14 (4,false),
.cycle 1 15 true (-1),
.cycle 1 13 true (0),
.cycle 14 1 false (0),
.cycle 13 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.last 13 (4,false)
])
theorem kid05_part956_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part956) = true := by rfl

def kid05_part957 : Audit := .cycle 0 12 true (0)
theorem kid05_part957_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part957) = true := by rfl

def kid05_part958 : Audit := .split 13 (4,false) (byMove [
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
.cycle 11 7 false (1),
.last 15 (2,true),
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
theorem kid05_part958_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part958) = true := by rfl

def kid05_part959 : Audit := .cycle 12 3 false (0)
theorem kid05_part959_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part959) = true := by rfl

def kid05_part960 : Audit := .cycle 0 11 true (0)
theorem kid05_part960_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part960) = true := by rfl

def kid05_part961 : Audit := .cycle 1 10 true (1)
theorem kid05_part961_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part961) = true := by rfl

def kid05_part962 : Audit := .cycle 0 23 true (0)
theorem kid05_part962_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part962) = true := by rfl

def kid05_part963 : Audit := .cycle 3 8 true (1)
theorem kid05_part963_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part963) = true := by rfl

def kid05_part964 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (2,true),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.last 13 (2,true),
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
theorem kid05_part964_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part964) = true := by rfl

def kid05_part965 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 8 13 false (4),
.last 13 (2,true),
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
.cycle 8 18 true (-1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 8 6 true (1),
.cycle 8 8 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part965_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part965) = true := by rfl

def kid05_part966 : Audit := .cycle 14 5 false (0)
theorem kid05_part966_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part966) = true := by rfl

def kid05_part967 : Audit := .split 17 (4,false) (byMove [
.last 20 (2,true),
.cycle 15 3 false (-1),
.last 18 (2,true),
.cycle 11 9 false (1),
.last 20 (2,true),
.cycle 12 6 false (0),
.last 20 (2,true),
.last 22 (2,true),
.last 18 (2,true),
.cycle 0 28 true (-2),
.last 20 (2,true),
.cycle 8 10 false (2),
.cycle 11 8 false (1),
.cycle 15 3 false (-1),
.last 18 (2,true),
.cycle 11 9 false (1),
.last 20 (2,true),
.cycle 12 6 false (0),
.last 20 (2,true),
.cycle 12 8 false (0),
.last 18 (2,true),
.last 35 (2,true),
.cycle 10 8 false (2),
.cycle 12 8 false (0)
])
theorem kid05_part967_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part967) = true := by rfl

def kid05_part968 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.last 21 (4,false),
.last 17 (4,false),
.cycle 1 12 true (1),
.last 14 (4,false),
.cycle 1 28 true (0),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 14 (4,false),
.cycle 1 23 true (-1),
.cycle 19 1 false (-1),
.last 21 (4,false),
.cycle 13 3 false (0),
.cycle 1 12 true (1),
.cycle 14 5 false (0),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 13 5 false (1)
])
theorem kid05_part968_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part968) = true := by rfl

def kid05_part969 : Audit := .cycle 1 12 true (1)
theorem kid05_part969_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part969) = true := by rfl

def kid05_part970 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 23 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.cycle 16 18 true (0),
.last 14 (2,true),
.cycle 1 23 true (-1),
.cycle 12 2 true (-1),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.last 15 (2,true),
.cycle 11 9 false (1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 11 4 false (1),
.cycle 11 8 false (1),
.cycle 11 6 false (1),
.last 14 (2,true),
.cycle 5 9 false (3),
.cycle 11 3 false (1),
.cycle 11 6 false (1)
])
theorem kid05_part970_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part970) = true := by rfl

def kid05_part971 : Audit := .cycle 12 3 false (0)
theorem kid05_part971_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part971) = true := by rfl

def kid05_part972 : Audit := .cycle 0 11 true (0)
theorem kid05_part972_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part972) = true := by rfl

def kid05_part973 : Audit := .cycle 1 10 true (1)
theorem kid05_part973_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part973) = true := by rfl

def kid05_part974 : Audit := .cycle 2 9 true (1)
theorem kid05_part974_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part974) = true := by rfl

def kid05_part975 : Audit := .cycle 1 13 true (1)
theorem kid05_part975_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part975) = true := by rfl

def kid05_part976 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 10 7 false (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 0, 16, 64],[2, 0, 64, 1, 16, 16, 64],64⟩,
.cycle 10 7 false (3),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3)
])
theorem kid05_part976_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part976) = true := by rfl

def kid05_part977 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 14 5 false (2),
.last 13 (2,true),
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
.cycle 14 5 false (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 16 5 false (2),
.cycle 14 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 2 true (3)
])
theorem kid05_part977_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part977) = true := by rfl

def kid05_part953 : Audit := .split 10 (4,true) (byMove [(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part966),(kid05_part967),(kid05_part968),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977)])

theorem kid05_part953_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part953) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part966),(kid05_part967),(kid05_part968),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part954_checked

  · exact kid05_part960_checked

  · exact kid05_part966_checked

  · exact kid05_part972_checked

  · exact kid05_part955_checked

  · exact kid05_part961_checked

  · exact kid05_part967_checked

  · exact kid05_part973_checked

  · exact kid05_part956_checked

  · exact kid05_part962_checked

  · exact kid05_part968_checked

  · exact kid05_part974_checked

  · exact kid05_part957_checked

  · exact kid05_part963_checked

  · exact kid05_part969_checked

  · exact kid05_part975_checked

  · exact kid05_part958_checked

  · exact kid05_part964_checked

  · exact kid05_part970_checked

  · exact kid05_part976_checked

  · exact kid05_part959_checked

  · exact kid05_part965_checked

  · exact kid05_part971_checked

  · exact kid05_part977_checked

def kid05_part978 : Audit := .cycle 11 3 false (1)
theorem kid05_part978_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part978) = true := by rfl

def kid05_part858 : Audit := .split 9 (5,false) (byMove [(kid05_part859),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part918),(kid05_part919),(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part978)])

theorem kid05_part858_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (kid05_part858) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid05_part859),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part918),(kid05_part919),(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part978)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part859_checked

  · exact kid05_part889_checked

  · exact kid05_part919_checked

  · exact kid05_part949_checked

  · exact kid05_part860_checked

  · exact kid05_part890_checked

  · exact kid05_part920_checked

  · exact kid05_part950_checked

  · exact kid05_part861_checked

  · exact kid05_part891_checked

  · exact kid05_part921_checked

  · exact kid05_part951_checked

  · exact kid05_part862_checked

  · exact kid05_part892_checked

  · exact kid05_part922_checked

  · exact kid05_part952_checked

  · exact kid05_part863_checked

  · exact kid05_part893_checked

  · exact kid05_part923_checked

  · exact kid05_part953_checked

  · exact kid05_part888_checked

  · exact kid05_part918_checked

  · exact kid05_part948_checked

  · exact kid05_part978_checked

def kid05_part979 : Audit := .cycle 0 9 true (0)
theorem kid05_part979_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,0⟩)) (kid05_part979) = true := by rfl

def kid05_part980 : Audit := .cycle 1 8 true (1)
theorem kid05_part980_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,1⟩)) (kid05_part980) = true := by rfl

def kid05_part981 : Audit := .cycle 2 7 true (1)
theorem kid05_part981_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,2⟩)) (kid05_part981) = true := by rfl

def kid05_part982 : Audit := .cycle 1 11 true (1)
theorem kid05_part982_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,3⟩)) (kid05_part982) = true := by rfl

def kid05_part984 : Audit := .cycle 1 10 true (1)
theorem kid05_part984_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part984) = true := by rfl

def kid05_part985 : Audit := .split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 12 11 false (0),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 18 1 false (-2),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
]),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 12 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 12 false (0),
.cycle 13 12 false (-1),
.cycle 0 13 true (0),
.cycle 13 12 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 12 false (2),
.cycle 13 12 false (1),
.cycle 14 12 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 13 12 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 12 false (2),
.cycle 1 15 true (0),
.cycle 13 12 false (1),
.cycle 11 2 true (0)
]),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.split 15 (2,true) (byMove [
.cycle 0 20 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.last 16 (4,true),
.cycle 12 6 false (0),
.cycle 7 10 false (3),
.cycle 16 13 true (0),
.cycle 0 18 true (-2),
.cycle 12 11 false (0),
.cycle 0 20 true (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[128, 256, 8, 25166880, 2097160, 8388640, 8192, 16384, 8, 128, 8388640, 1024, 8192, 16384, 2097152, 128, 8388640, 1024, 128, 256, 8, 8388640, 2097152, 8388608, 16777216],[128, 8388640, 32, 1, 16777216, 1024, 8192, 8388640, 32, 1, 16777216, 65536, 8192, 8388640, 8388608, 262144, 16777216, 65536, 128, 8388640, 32, 1, 16777216, 1024, 16777216],18350366⟩,
.cycle 12 8 false (0),
.cycle 12 4 false (0),
.cycle 1 37 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.last 16 (4,true),
.last 17 (4,true),
.cycle 17 68 false (3),
.cycle 228 72 false (-4),
.cycle 0 18 true (-2),
.cycle 4 12 false (3),
.cycle 12 8 false (0),
.cycle 12 8 false (0)
]),
.split 12 (2,true) (byMove [
.cycle 14 16 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 30 (4,true),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 0 17 true (-1),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 19 true (-1),
.cycle 0 35 false (3),
.cycle 20 10 true (-3),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 1 17 true (-2),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.cycle 0 20 true (-2),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 0 22 true (-2)
]),
.cycle 1 13 true (0),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 31 (2,true),
.last 33 (2,true),
.cycle 1 13 true (0),
.cycle 0 19 true (-2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 0 30 true (-1),
.cycle 0 21 true (-2),
.last 25 (2,true),
.last 14 (2,true),
.cycle 1 15 true (-1),
.cycle 13 1 false (-1),
.cycle 1 17 true (-2),
.last 33 (2,true),
.cycle 1 13 true (0),
.last 49 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 53 (2,true),
.last 53 (2,true)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 10 18 true (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 1 14 true (0),
.cycle 8 10 true (0),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 1 19 true (-2),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 1 16 true (0),
.cycle 19 1 false (-1),
.cycle 11 3 true (0)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 15 3 false (1),
.cycle 11 1 true (1)
])
theorem kid05_part985_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part985) = true := by rfl

def kid05_part986 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 15 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.cycle 13 6 false (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 15 3 false (1),
.cycle 11 1 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 1 24 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 27 (4,true),
.cycle 1 24 true (0),
.last 25 (4,true),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.last 15 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 5 false (1),
.split 20 (5,false) (byMove [
.cycle 22 38 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 23 1 false (-3),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.cycle 17 4 true (-2),
.cycle 0 34 true (-2),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.cycle 14 8 true (-2),
.cycle 13 9 false (1),
.cycle 17 4 false (0),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.cycle 23 1 false (-3),
.cycle 20 1 false (-2),
.cycle 18 7 false (0),
.cycle 11 10 false (2),
.cycle 0 34 true (-2),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.cycle 12 12 false (2)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.split 11 (5,false) (byMove [
.last 16 (4,true),
.last 32 (4,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 17 (4,true),
.last 28 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 16 (4,true)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 13 false (1),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.cycle 13 10 false (1),
.cycle 8 5 true (2),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid05_part986_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part986) = true := by rfl

def kid05_part987 : Audit := .cycle 0 11 true (0)
theorem kid05_part987_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part987) = true := by rfl

def kid05_part988 : Audit := .split 10 (4,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.cycle 1 12 true (0),
.cycle 13 11 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 11 1 true (1),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 14 1 false (-2),
.cycle 17 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 15 3 false (1),
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
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 18 1 false (2),
.cycle 11 1 true (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 8 14 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
]),
.cycle 17 5 false (1),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 20 (5,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 15 (5,false),
.last 17 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 17 (5,false),
.last 13 (5,false),
.last 19 (5,false),
.last 20 (5,false),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 15 (5,false),
.last 24 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 24 (5,false),
.last 13 (5,false)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.split 11 (5,false) (byMove [
.last 14 (2,true),
.last 30 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 1 12 true (1),
.cycle 1 13 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 1 12 true (1),
.cycle 15 2 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 2 true (1),
.cycle 14 2 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (2),
.split 11 (5,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 13 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 9 4 true (2),
.cycle 11 1 true (3),
.cycle 6 6 true (2),
.last 17 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 8 5 true (2),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.cycle 11 1 true (3)
])
])
theorem kid05_part988_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part988) = true := by rfl

def kid05_part989 : Audit := .cycle 8 2 true (2)
theorem kid05_part989_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part989) = true := by rfl

def kid05_part990 : Audit := .cycle 0 10 true (0)
theorem kid05_part990_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part990) = true := by rfl

def kid05_part991 : Audit := .cycle 1 9 true (1)
theorem kid05_part991_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part991) = true := by rfl

def kid05_part992 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.cycle 1 22 true (1),
.cycle 45 1 false (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 20 1 true (4),
.cycle 6 15 true (2),
.cycle 0 29 true (0),
.cycle 7 19 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 12 true (2),
.cycle 20 1 true (4)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 4, 1, 4096, 1024, 128, 4, 4, 1, 4096, 1024, 4096],6176⟩,
.cycle 11 9 true (2),
.split 33 (4,true) (byMove [
.cycle 0 50 true (0),
.cycle 0 37 true (0),
.cycle 10 35 true (2),
.cycle 0 43 true (0),
.cycle 0 37 true (0),
.last 34 (5,false),
.cycle 1 34 true (1),
.last 35 (5,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 16, 1, 4, 1024, 128, 4, 16, 1, 4, 1024, 4096],6176⟩,
.cycle 0 35 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 16, 1, 16, 1024, 128, 4, 16, 1, 16, 1024, 4096],6176⟩,
.cycle 8 26 true (2),
.cycle 16 19 true (3),
.cycle 35 15 true (7),
.cycle 1 36 true (1),
.cycle 12 31 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 20, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 16, 1, 16, 1024, 128, 4, 16, 1, 16, 1024, 4096],6176⟩,
.last 34 (5,false),
.cycle 1 34 true (1),
.cycle 7 27 true (2),
.cycle 2 46 true (1),
.cycle 0 35 true (0),
.cycle 9 26 true (2),
.cycle 8 26 true (2)
]),
.split 20 (5,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 8 25 true (2),
.cycle 8 15 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 34 (4,true),
.cycle 8 23 true (2),
.last 36 (4,true),
.cycle 20 1 true (6),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 12 9 true (2),
.cycle 18 3 true (4),
.last 24 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 12 true (2),
.cycle 20 1 true (6)
]),
.cycle 7 14 true (2),
.cycle 16 6 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.split 20 (5,false) (byMove [
.last 25 (4,true),
.cycle 0 34 true (0),
.cycle 36 1 false (0),
.cycle 7 16 true (2),
.last 21 (4,true),
.cycle 17 4 true (3),
.cycle 1 21 true (1),
.cycle 1 22 true (1),
.cycle 19 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 15 6 true (3),
.last 26 (4,true),
.cycle 14 10 true (1),
.cycle 5 16 true (1),
.last 21 (4,true),
.last 22 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 23 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (2),
.split 20 (5,false) (byMove [
.cycle 1 21 true (1),
.cycle 1 24 true (1),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 8 25 true (2),
.cycle 20 1 true (6),
.cycle 6 15 true (2),
.cycle 94 24 false (4),
.cycle 8 14 true (2),
.cycle 1 22 true (1),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 9 12 true (2),
.cycle 20 1 true (6)
])
])
theorem kid05_part992_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part992) = true := by rfl

def kid05_part993 : Audit := .cycle 3 7 true (1)
theorem kid05_part993_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part993) = true := by rfl

def kid05_part994 : Audit := .cycle 9 1 true (3)
theorem kid05_part994_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part994) = true := by rfl

def kid05_part995 : Audit := .split 10 (5,false) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (4,true) (byMove [
.cycle 1 23 true (1),
.cycle 8 26 true (2),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 9 15 true (2),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 8 24 true (2),
.cycle 3 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 59, 32, 4, 64],[2, 40, 64, 1, 16, 16, 64],64⟩,
.cycle 10 13 true (2),
.cycle 6 17 true (2),
.cycle 0 27 true (0),
.last 23 (2,true),
.cycle 1 24 true (1),
.cycle 20 4 true (4),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 9 14 true (2),
.cycle 8 25 true (2)
]),
.cycle 8 11 true (2),
.cycle 9 2 true (3),
.cycle 10 1 true (4),
.cycle 7 5 true (2),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
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
.cycle 8 8 true (2),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 8 9 true (2)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.cycle 8 4 true (2),
.split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 19 1 false (-1),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 22 1 false (0),
.cycle 8 8 true (2),
.cycle 1 14 true (1),
.cycle 1 17 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 6 true (2),
.cycle 8 10 true (2),
.cycle 19 1 false (-1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 12 4 true (1),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 9 6 true (2),
.cycle 8 6 true (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part995_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part995) = true := by rfl

def kid05_part996 : Audit := .cycle 6 4 true (2)
theorem kid05_part996_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part996) = true := by rfl

def kid05_part998 : Audit := .cycle 0 16 true (0)
theorem kid05_part998_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part998) = true := by rfl

def kid05_part999 : Audit := .cycle 12 11 false (0)
theorem kid05_part999_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part999) = true := by rfl

def kid05_part1000 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 19 (4,true),
.cycle 15 1 false (1),
.cycle 20 1 false (-2),
.cycle 18 1 false (-2),
.cycle 29 1 false (1),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.cycle 1 20 true (0),
.cycle 17 1 false (-1),
.cycle 11 2 true (0)
])
theorem kid05_part1000_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part1000) = true := by rfl

def kid05_part1001 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.cycle 0 33 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 4, 1, 64, 16, 64],64⟩,
.cycle 3 13 true (0),
.cycle 14 3 true (2),
.cycle 1 19 true (0),
.cycle 25 1 false (-1),
.cycle 21 1 false (-1),
.cycle 26 1 false (0),
.cycle 1 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 25 1 false (-1),
.cycle 0 18 true (0)
])
theorem kid05_part1001_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part1001) = true := by rfl

def kid05_part1002 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (3),
.last 26 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 15 (2,true),
.last 16 (2,true),
.last 21 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 25 (2,true),
.last 17 (2,true),
.last 18 (2,true),
.cycle 11 2 true (0)
])
theorem kid05_part1002_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part1002) = true := by rfl

def kid05_part1003 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1003_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part1003) = true := by rfl

def kid05_part1004 : Audit := .cycle 7 6 true (1)
theorem kid05_part1004_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part1004) = true := by rfl

def kid05_part1005 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 2, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 3 11 true (1),
.cycle 12 3 true (2),
.cycle 1 14 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 22 (4,true),
.cycle 1 14 true (1)
])
theorem kid05_part1005_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part1005) = true := by rfl

def kid05_part1006 : Audit := .cycle 0 14 true (0)
theorem kid05_part1006_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part1006) = true := by rfl

def kid05_part1007 : Audit := .cycle 21 1 false (1)
theorem kid05_part1007_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part1007) = true := by rfl

def kid05_part1008 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.cycle 18 5 false (0),
.cycle 18 1 false (0),
.cycle 7 10 true (1),
.last 15 (4,true),
.cycle 18 7 false (1),
.cycle 1 15 true (1),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 16, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 8 7 true (1),
.cycle 19 9 false (1),
.cycle 18 5 false (0),
.cycle 15 12 true (-1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 18 11 false (2),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 32 (4,true)
])
theorem kid05_part1008_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part1008) = true := by rfl

def kid05_part1009 : Audit := .cycle 8 5 true (1)
theorem kid05_part1009_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part1009) = true := by rfl

def kid05_part1010 : Audit := .cycle 13 6 false (1)
theorem kid05_part1010_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part1010) = true := by rfl

def kid05_part1011 : Audit := .split 15 (2,true) (byMove [
.cycle 0 32 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.last 16 (4,true),
.cycle 12 6 false (0),
.cycle 7 10 false (3),
.cycle 16 15 true (0),
.cycle 0 28 true (-2),
.cycle 12 11 false (0),
.last 19 (4,true),
.last 34 (4,true),
.cycle 12 8 false (0),
.cycle 12 4 false (0),
.cycle 12 18 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 15, 1, 64, 16, 64],64⟩,
.last 16 (4,true),
.last 17 (4,true),
.cycle 12 14 false (1),
.cycle 34 18 false (2),
.cycle 0 28 true (-2),
.cycle 4 12 false (3),
.cycle 12 8 false (0),
.cycle 12 8 false (0)
])
theorem kid05_part1011_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part1011) = true := by rfl

def kid05_part1012 : Audit := .split 12 (2,true) (byMove [
.cycle 0 20 true (-1),
.cycle 14 8 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 13 8 true (-2),
.cycle 0 16 true (0),
.cycle 26 8 true (3),
.cycle 0 16 true (0),
.cycle 13 8 true (0),
.last 13 (4,true),
.cycle 13 8 true (-1),
.cycle 13 8 true (-3),
.cycle 15 8 true (-3),
.cycle 23 8 true (0),
.cycle 13 1 false (-1),
.last 16 (4,true),
.cycle 17 8 true (-2),
.cycle 0 16 true (0),
.cycle 13 8 true (-2),
.cycle 0 16 true (0),
.cycle 7 8 true (0),
.last 13 (4,true),
.cycle 15 8 true (-2)
])
theorem kid05_part1012_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part1012) = true := by rfl

def kid05_part1013 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 2, 1, 64, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 15, 15, 64],[2, 15, 4, 1, 64, 16, 64],64⟩,
.cycle 3 13 true (0),
.cycle 14 3 true (2),
.cycle 4 13 true (0),
.cycle 25 1 false (-1),
.cycle 21 1 false (-1),
.cycle 26 1 false (0),
.cycle 1 17 true (0),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 25 1 false (-1),
.cycle 1 18 true (0)
])
theorem kid05_part1013_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part1013) = true := by rfl

def kid05_part1014 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.last 27 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.last 17 (2,true),
.last 13 (2,true),
.last 22 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.last 21 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.last 20 (2,true),
.last 13 (2,true),
.cycle 7 8 true (0),
.last 22 (2,true),
.last 22 (2,true)
])
theorem kid05_part1014_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part1014) = true := by rfl

def kid05_part1015 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 15 1 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.last 17 (2,true),
.cycle 17 1 false (-1),
.cycle 7 8 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 22 1 false (0),
.last 16 (2,true),
.cycle 8 16 true (0),
.cycle 19 1 false (-1),
.cycle 15 1 false (-1),
.last 14 (2,true),
.last 17 (2,true),
.last 17 (2,true),
.cycle 12 2 true (0),
.cycle 25 1 false (-1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 19 1 false (-1),
.cycle 29 1 false (-1)
])
theorem kid05_part1015_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1015) = true := by rfl

def kid05_part1016 : Audit := .cycle 16 9 false (2)
theorem kid05_part1016_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1016) = true := by rfl

def kid05_part1017 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 7 false (1),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 17 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 6, 4, 2, 64],[2, 4, 4, 1, 64, 16, 64],64⟩,
.cycle 3 11 true (1),
.cycle 12 3 true (2),
.cycle 1 14 true (1),
.cycle 18 11 false (2),
.cycle 17 7 false (1),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 28 (4,true),
.cycle 1 14 true (1)
])
theorem kid05_part1017_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1017) = true := by rfl

def kid05_part1018 : Audit := .cycle 0 14 true (0)
theorem kid05_part1018_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1018) = true := by rfl

def kid05_part1019 : Audit := .cycle 4 8 true (1)
theorem kid05_part1019_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1019) = true := by rfl

def kid05_part1020 : Audit := .cycle 15 3 false (1)
theorem kid05_part1020_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1020) = true := by rfl

def kid05_part1021 : Audit := .split 28 (4,true) (byMove [
.last 31 (2,true),
.cycle 18 11 false (2),
.last 29 (2,true),
.cycle 0 40 true (-1),
.last 34 (2,true),
.cycle 16 13 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1153, 4096, 2048, 128, 256, 8, 128, 1153, 2048, 4096],[128, 2048, 4096, 1, 1, 1024, 128, 1153, 4096, 1, 1, 1024, 4096],4112⟩,
.cycle 60 1 true (4),
.last 29 (2,true),
.cycle 1 30 true (-1),
.last 33 (2,true),
.cycle 31 1 true (5),
.cycle 15 15 false (3),
.cycle 18 11 false (2),
.last 29 (2,true),
.cycle 1 40 true (-1),
.last 34 (2,true),
.cycle 27 2 true (1),
.cycle 13 21 false (4),
.cycle 13 17 false (4),
.last 29 (2,true),
.cycle 1 30 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 4096, 2048, 128, 256, 8, 128, 1024, 2048, 4096],[128, 2048, 4096, 1, 1024, 1024, 128, 1024, 4096, 1, 1024, 1024, 4096],4112⟩,
.cycle 31 1 true (5)
])
theorem kid05_part1021_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1021) = true := by rfl

def kid05_part997 : Audit := .split 11 (5,false) (byMove [(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019),(kid05_part1020),(kid05_part1021)])

theorem kid05_part997_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part997) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (5,false) (some mv)) (byMove [(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019),(kid05_part1020),(kid05_part1021)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part1002_checked

  · exact kid05_part1008_checked

  · exact kid05_part1014_checked

  · exact kid05_part1020_checked

  · exact kid05_part1003_checked

  · exact kid05_part1009_checked

  · exact kid05_part1015_checked

  · exact kid05_part1021_checked

def kid05_part1022 : Audit := .split 10 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.cycle 11 8 true (-2),
.split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 13 11 false (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 7 6 true (1),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (1),
.cycle 8 5 true (1),
.cycle 13 6 false (1),
.cycle 13 6 false (-1),
.cycle 12 8 true (-2),
.cycle 23 1 false (-1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 17 9 false (2),
.cycle 16 9 false (2),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 3 false (1),
.last 28 (4,true)
]),
.cycle 1 11 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 0 16 true (0),
.cycle 12 1 true (2),
.cycle 21 7 false (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 1 38 true (-2),
.last 15 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
]),
.cycle 29 1 false (7),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 0 31 true (0),
.cycle 1 24 true (0),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 7 6 true (2),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 1 15 true (1),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 8 3 true (2),
.cycle 17 5 false (1),
.split 20 (5,false) (byMove [
.cycle 22 51 true (-2),
.cycle 13 14 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 11 14 false (2),
.cycle 20 1 false (-2),
.cycle 13 9 false (1),
.cycle 17 4 true (-2),
.cycle 1 45 true (-2),
.cycle 21 1 false (-1),
.cycle 13 12 true (-2),
.last 23 (4,true),
.cycle 13 9 false (1),
.cycle 17 4 false (0),
.cycle 13 11 false (1),
.cycle 21 1 false (-3),
.cycle 11 14 false (2),
.cycle 20 1 false (-2),
.cycle 18 7 false (0),
.cycle 11 10 false (2),
.cycle 1 45 true (-2),
.cycle 13 11 false (1),
.cycle 15 6 false (1),
.last 23 (4,true)
]),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 11 8 true (-2),
.split 11 (5,false) (byMove [
.last 16 (4,true),
.last 32 (4,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 15 1 false (-1),
.cycle 6 6 true (1),
.last 17 (4,true),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 13 6 false (1),
.last 17 (4,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 13 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true)
]),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 2 10 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 9 4 true (2),
.cycle 0 13 true (0),
.cycle 0 20 true (-2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 15 true (2),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.last 12 (5,false),
.cycle 6 6 true (2),
.last 13 (5,false),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.cycle 13 10 true (-2),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
]),
.cycle 8 3 true (2)
])
theorem kid05_part1022_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1022) = true := by rfl

def kid05_part1023 : Audit := .cycle 1 11 true (1)
theorem kid05_part1023_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1023) = true := by rfl

def kid05_part1025 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 12 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 4, 1, 256, 1024, 128, 4, 4, 1, 256, 1024, 4096],6176⟩,
.cycle 3 11 true (1),
.cycle 0 21 true (0),
.last 14 (5,false),
.cycle 12 8 true (1),
.cycle 19 7 false (2),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.cycle 1 16 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (2),
.last 14 (5,false)
])
theorem kid05_part1025_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1025) = true := by rfl

def kid05_part1026 : Audit := .cycle 0 14 true (0)
theorem kid05_part1026_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1026) = true := by rfl

def kid05_part1027 : Audit := .cycle 21 1 false (1)
theorem kid05_part1027_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1027) = true := by rfl

def kid05_part1028 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.far false 5 ⟨0,[0, 1, 2, 3, 0, 4, 1, 0, 0, 0],[128, 256, 8, 1074274434, 1073750146, 1073741824, 524288, 1048576, 32768, 128, 1073750146, 1073741824, 33554432, 67108864, 8, 1073750146, 1073750146, 1073741824, 2, 4, 512, 33554432, 1073750146, 1073741824, 2, 4, 8, 128, 128, 1073741824, 1073741824],[128, 1073750146, 2, 1, 1142423940, 1024, 524288, 1073750146, 8192, 4096, 132, 4194304, 33554432, 1073741824, 2, 1, 1048576, 268435456, 2, 1073750146, 128, 64, 33554432, 16, 2, 128, 2, 1, 128, 16, 1073741824],1743781246⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 133, 4096, 128, 256, 8, 128, 5, 4096, 4096],[128, 4096, 4, 1, 392, 1024, 128, 5, 4, 1, 128, 1024, 4096],6176⟩,
.cycle 3 13 true (0),
.cycle 25 1 false (1),
.last 16 (5,false),
.cycle 27 1 false (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.cycle 0 19 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.cycle 7 13 true (0),
.last 16 (5,false)
])
theorem kid05_part1028_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1028) = true := by rfl

def kid05_part1029 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1029_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1029) = true := by rfl

def kid05_part1030 : Audit := .split 11 (5,false) (byMove [
.cycle 0 16 true (0),
.cycle 13 11 false (0),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.cycle 8 5 true (1),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 14 1 false (-2),
.cycle 17 1 false (-1),
.cycle 17 9 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 15 3 false (1),
.cycle 15 13 false (3)
])
theorem kid05_part1030_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1030) = true := by rfl

def kid05_part1031 : Audit := .cycle 1 11 true (1)
theorem kid05_part1031_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1031) = true := by rfl

def kid05_part1032 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.cycle 19 1 false (1),
.cycle 12 1 true (2),
.cycle 21 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 1 false (-1),
.last 41 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (2)
])
theorem kid05_part1032_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1032) = true := by rfl

def kid05_part1033 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 16 1 false (0),
.last 12 (5,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 1 24 true (0),
.cycle 22 1 false (6),
.last 12 (5,false),
.cycle 7 6 true (2),
.last 15 (5,false),
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
])
theorem kid05_part1033_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1033) = true := by rfl

def kid05_part1034 : Audit := .cycle 0 12 true (0)
theorem kid05_part1034_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1034) = true := by rfl

def kid05_part1035 : Audit := .cycle 21 1 false (5)
theorem kid05_part1035_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1035) = true := by rfl

def kid05_part1036 : Audit := .cycle 8 3 true (2)
theorem kid05_part1036_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1036) = true := by rfl

def kid05_part1037 : Audit := .cycle 17 5 false (1)
theorem kid05_part1037_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1037) = true := by rfl

def kid05_part1038 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 20 (5,false),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 15 (5,false),
.last 17 (5,false),
.cycle 1 13 true (1),
.last 14 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 262148, 262144, 8192, 16384, 8, 128, 4, 262144, 128, 256, 8, 128, 262144, 262144, 262144],[128, 262144, 4, 1, 4, 1024, 8192, 4, 4, 1, 262144, 65536, 128, 262144, 4, 1, 4, 1024, 262144],460848⟩,
.cycle 0 14 true (0),
.far true 5 ⟨0,[0, 1, 2, 3, 4, 4, 0, 1, 4, 4],[128, 131072, 2097152, 512, 1024, 1073741824, 524288, 128, 1073741952, 2097152, 4194304, 1073741824, 131072, 1073872896, 512, 134217728, 268435456, 1073741824, 128, 131072, 128, 512, 1024, 1073741824, 1644822688, 1644822688, 1779040416, 134217728, 268435456, 1073741824, 1073741824],[128, 32, 4194304, 128, 128, 524288, 524288, 131072, 128, 128, 524288, 131072, 131072, 536870912, 1024, 131072, 33554432, 128, 128, 32, 131072, 131072, 128, 32, 1644822688, 536870912, 1913258144, 1644822688, 33554432, 570425344, 1073741824],1737111906⟩,
.cycle 8 5 true (1),
.last 19 (5,false),
.last 20 (5,false),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 15 (5,false),
.last 24 (5,false),
.cycle 1 13 true (1),
.last 28 (5,false),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 19 (5,false),
.last 21 (5,false)
])
theorem kid05_part1038_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1038) = true := by rfl

def kid05_part1039 : Audit := .cycle 1 13 true (1)
theorem kid05_part1039_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1039) = true := by rfl

def kid05_part1040 : Audit := .cycle 18 1 false (0)
theorem kid05_part1040_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1040) = true := by rfl

def kid05_part1041 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1041_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1041) = true := by rfl

def kid05_part1042 : Audit := .split 11 (5,false) (byMove [
.last 14 (2,true),
.last 30 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 1 false (-1),
.cycle 6 6 true (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 12 2 true (2),
.cycle 13 6 false (1),
.last 15 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 2 true (0),
.cycle 16 2 true (1),
.cycle 15 2 true (0),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 12 2 true (1),
.cycle 12 2 true (2)
])
theorem kid05_part1042_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1042) = true := by rfl

def kid05_part1043 : Audit := .cycle 1 11 true (1)
theorem kid05_part1043_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1043) = true := by rfl

def kid05_part1044 : Audit := .cycle 7 4 true (2)
theorem kid05_part1044_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1044) = true := by rfl

def kid05_part1045 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 13 (5,false),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 4, 1, 256, 1024, 128, 4, 4, 1, 256, 1024, 4096],6176⟩,
.cycle 3 9 true (1),
.cycle 2 15 true (1),
.last 12 (5,false),
.cycle 6 6 true (2),
.last 13 (5,false),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 2 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (2),
.last 12 (5,false)
])
theorem kid05_part1045_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1045) = true := by rfl

def kid05_part1046 : Audit := .cycle 0 12 true (0)
theorem kid05_part1046_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1046) = true := by rfl

def kid05_part1047 : Audit := .cycle 9 3 true (2)
theorem kid05_part1047_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1047) = true := by rfl

def kid05_part1048 : Audit := .cycle 8 3 true (2)
theorem kid05_part1048_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1048) = true := by rfl

def kid05_part1024 : Audit := .split 10 (4,true) (byMove [(kid05_part1025),(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046),(kid05_part1047),(kid05_part1048)])

theorem kid05_part1024_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1024) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1025),(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046),(kid05_part1047),(kid05_part1048)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1025_checked

  · exact kid05_part1031_checked

  · exact kid05_part1037_checked

  · exact kid05_part1043_checked

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

def kid05_part1050 : Audit := .cycle 1 12 true (1)
theorem kid05_part1050_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1050) = true := by rfl

def kid05_part1051 : Audit := .split 13 (5,false) (byMove [
.cycle 1 14 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 27 2 false (-1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 16 true (1),
.cycle 13 1 true (1),
.cycle 15 8 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (0),
.cycle 0 18 true (-1),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 19 5 false (1),
.cycle 13 1 true (1)
])
theorem kid05_part1051_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1051) = true := by rfl

def kid05_part1052 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 1 15 true (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 1 28 true (0),
.cycle 24 1 false (2),
.last 14 (5,false),
.last 13 (5,false),
.cycle 21 7 false (1),
.last 24 (5,false),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.last 13 (5,false)
])
theorem kid05_part1052_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1052) = true := by rfl

def kid05_part1053 : Audit := .cycle 0 13 true (0)
theorem kid05_part1053_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1053) = true := by rfl

def kid05_part1054 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.far false 7 ⟨0,[0, 1, 2, 3, 0, 4, 5, 6, 2, 3, 0, 4, 5, 6],[128, 256, 8, 4398046511104, 1, 32768, 524288, 1048576, 32768, 128, 1048576, 8589934592, 33554432, 67108864, 8, 1048576, 1, 8589934592, 137438953472, 274877906944, 8589934592, 33554432, 8589934592, 8589934592, 524288, 1048576, 32768, 128, 0, 0, 33554432, 67108864, 8, 0, 1, 8589934592, 137438953472, 274877906944, 8589934592, 33554432, 0, 0, 4398046511104],[128, 1048576, 4398046511104, 1, 128, 1024, 524288, 1048576, 4398046511104, 4096, 1048576, 4194304, 33554432, 0, 4398046511104, 1, 8589934592, 268435456, 137438953472, 8589934592, 4398046511104, 1073741824, 8589934592, 1099511627776, 524288, 0, 4398046511104, 4096, 0, 4194304, 33554432, 0, 4398046511104, 1, 0, 268435456, 137438953472, 0, 4398046511104, 1073741824, 0, 1099511627776, 4398046511104],4402341494796⟩,
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 1 19 false (3),
.cycle 13 16 true (-2),
.last 19 (2,true),
.cycle 0 20 true (-2),
.cycle 16 3 false (0),
.cycle 13 7 false (1),
.cycle 13 9 false (1),
.last 20 (2,true),
.cycle 1 21 false (3),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 15 20 false (2),
.cycle 13 8 false (1),
.last 19 (2,true),
.cycle 9 24 false (3),
.cycle 15 4 false (1),
.cycle 15 8 false (1)
])
theorem kid05_part1054_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1054) = true := by rfl

def kid05_part1055 : Audit := .cycle 8 4 true (2)
theorem kid05_part1055_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1055) = true := by rfl

def kid05_part1056 : Audit := .cycle 0 12 true (0)
theorem kid05_part1056_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1056) = true := by rfl

def kid05_part1057 : Audit := .cycle 1 11 true (1)
theorem kid05_part1057_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1057) = true := by rfl

def kid05_part1058 : Audit := .split 23 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 9 15 true (2),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4096, 4096, 128, 256, 8, 128, 4, 4096, 4096],[128, 4096, 4, 1, 4, 1024, 128, 4, 4, 1, 4, 1024, 4096],6192⟩,
.cycle 13 11 true (2),
.last 25 (5,false),
.last 24 (5,false),
.cycle 7 18 true (2),
.cycle 18 8 true (3),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.cycle 20 4 true (3),
.last 24 (5,false),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 1 26 true (1),
.cycle 9 15 true (2),
.last 24 (5,false)
])
theorem kid05_part1058_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1058) = true := by rfl

def kid05_part1059 : Audit := .cycle 3 9 true (1)
theorem kid05_part1059_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1059) = true := by rfl

def kid05_part1060 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 15 15 false (1),
.last 14 (2,true),
.cycle 7 9 true (2),
.cycle 23 2 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.cycle 8 6 true (2),
.cycle 15 9 true (2),
.last 19 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 41 2 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 16, 16, 64],[2, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (3),
.cycle 8 6 true (2)
])
theorem kid05_part1060_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1060) = true := by rfl

def kid05_part1061 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 15 true (2),
.cycle 8 15 true (2),
.cycle 11 4 true (3),
.cycle 12 1 true (4),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 8 true (2),
.cycle 8 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part1061_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1061) = true := by rfl

def kid05_part1062 : Audit := .cycle 6 6 true (2)
theorem kid05_part1062_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1062) = true := by rfl

def kid05_part1063 : Audit := .split 13 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 14 13 false (0),
.last 14 (2,true),
.last 17 (2,true),
.last 16 (2,true),
.cycle 19 1 false (-1),
.cycle 7 8 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 18 (2,true),
.cycle 8 7 true (1),
.cycle 15 8 false (1),
.last 17 (2,true),
.last 14 (2,true),
.last 17 (2,true),
.last 16 (2,true),
.cycle 17 1 false (-1),
.cycle 20 13 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 19 5 false (1),
.cycle 22 15 false (3)
])
theorem kid05_part1063_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1063) = true := by rfl

def kid05_part1064 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 0 16 true (0),
.cycle 8 5 true (2),
.cycle 21 7 false (1),
.last 24 (5,false),
.cycle 1 15 true (1),
.cycle 22 1 false (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part1064_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1064) = true := by rfl

def kid05_part1065 : Audit := .cycle 1 13 true (1)
theorem kid05_part1065_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1065) = true := by rfl

def kid05_part1066 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 13 28 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 13 9 false (1),
.last 22 (2,true),
.last 19 (2,true),
.cycle 13 10 true (-2),
.cycle 16 3 false (0),
.cycle 14 5 false (1),
.cycle 13 9 false (1),
.last 20 (2,true),
.cycle 13 11 false (1),
.cycle 19 1 false (-3),
.cycle 17 2 false (-1),
.cycle 18 1 false (-2),
.cycle 15 10 false (1),
.cycle 13 8 false (1),
.last 19 (2,true),
.cycle 5 14 false (3),
.cycle 15 4 false (1),
.cycle 15 6 false (1)
])
theorem kid05_part1066_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1066) = true := by rfl

def kid05_part1067 : Audit := .cycle 10 2 true (2)
theorem kid05_part1067_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1067) = true := by rfl

def kid05_part1068 : Audit := .cycle 0 12 true (0)
theorem kid05_part1068_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1068) = true := by rfl

def kid05_part1069 : Audit := .cycle 1 11 true (1)
theorem kid05_part1069_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1069) = true := by rfl

def kid05_part1070 : Audit := .cycle 2 10 true (1)
theorem kid05_part1070_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1070) = true := by rfl

def kid05_part1071 : Audit := .cycle 1 14 true (1)
theorem kid05_part1071_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1071) = true := by rfl

def kid05_part1072 : Audit := .cycle 9 3 true (2)
theorem kid05_part1072_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1072) = true := by rfl

def kid05_part1073 : Audit := .split 12 (5,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
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
.cycle 8 10 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 8 6 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (2),
.cycle 12 1 true (4)
])
theorem kid05_part1073_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1073) = true := by rfl

def kid05_part1049 : Audit := .split 11 (4,true) (byMove [(kid05_part1050),(kid05_part1051),(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073)])

theorem kid05_part1049_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1049) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some mv)) (byMove [(kid05_part1050),(kid05_part1051),(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1050_checked

  · exact kid05_part1056_checked

  · exact kid05_part1062_checked

  · exact kid05_part1068_checked

  · exact kid05_part1051_checked

  · exact kid05_part1057_checked

  · exact kid05_part1063_checked

  · exact kid05_part1069_checked

  · exact kid05_part1052_checked

  · exact kid05_part1058_checked

  · exact kid05_part1064_checked

  · exact kid05_part1070_checked

  · exact kid05_part1053_checked

  · exact kid05_part1059_checked

  · exact kid05_part1065_checked

  · exact kid05_part1071_checked

  · exact kid05_part1054_checked

  · exact kid05_part1060_checked

  · exact kid05_part1066_checked

  · exact kid05_part1072_checked

  · exact kid05_part1055_checked

  · exact kid05_part1061_checked

  · exact kid05_part1067_checked

  · exact kid05_part1073_checked

def kid05_part1074 : Audit := .cycle 0 10 true (0)
theorem kid05_part1074_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1074) = true := by rfl

def kid05_part1075 : Audit := .cycle 1 9 true (1)
theorem kid05_part1075_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1075) = true := by rfl

def kid05_part1076 : Audit := .cycle 2 8 true (1)
theorem kid05_part1076_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1076) = true := by rfl

def kid05_part1077 : Audit := .cycle 1 12 true (1)
theorem kid05_part1077_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1077) = true := by rfl

def kid05_part1078 : Audit := .cycle 9 1 true (3)
theorem kid05_part1078_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1078) = true := by rfl

def kid05_part1079 : Audit := .split 10 (5,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 29 1 false (-1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 13 true (2),
.cycle 3 9 true (1),
.cycle 9 3 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 20 1 false (-2),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (3),
.cycle 10 2 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 13 16 false (2),
.last 12 (2,true),
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
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 16 5 false (2),
.cycle 11 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
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
.cycle 8 6 true (2),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 16 12 true (0),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.cycle 8 6 true (2),
.cycle 1 12 true (1),
.cycle 0 19 true (0),
.last 24 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 28 (4,true),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.last 13 (4,true),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.last 20 (2,true),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 16 3 false (0),
.cycle 8 6 true (2),
.cycle 1 12 true (1),
.cycle 23 13 false (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2),
.cycle 8 8 true (2),
.last 16 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 16 5 false (2),
.cycle 11 2 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 9 4 true (3),
.cycle 8 4 true (2)
]),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
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
.cycle 8 8 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 5 false (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 9 4 true (3),
.cycle 10 3 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (3),
.cycle 10 1 true (4)
])
theorem kid05_part1079_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1079) = true := by rfl

def kid05_part983 : Audit := .split 9 (4,false) (byMove [(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995),(kid05_part996),(kid05_part997),(kid05_part1022),(kid05_part1023),(kid05_part1024),(kid05_part1049),(kid05_part1074),(kid05_part1075),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079)])

theorem kid05_part983_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (kid05_part983) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995),(kid05_part996),(kid05_part997),(kid05_part1022),(kid05_part1023),(kid05_part1024),(kid05_part1049),(kid05_part1074),(kid05_part1075),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part984_checked

  · exact kid05_part990_checked

  · exact kid05_part996_checked

  · exact kid05_part1074_checked

  · exact kid05_part985_checked

  · exact kid05_part991_checked

  · exact kid05_part997_checked

  · exact kid05_part1075_checked

  · exact kid05_part986_checked

  · exact kid05_part992_checked

  · exact kid05_part1022_checked

  · exact kid05_part1076_checked

  · exact kid05_part987_checked

  · exact kid05_part993_checked

  · exact kid05_part1023_checked

  · exact kid05_part1077_checked

  · exact kid05_part988_checked

  · exact kid05_part994_checked

  · exact kid05_part1024_checked

  · exact kid05_part1078_checked

  · exact kid05_part989_checked

  · exact kid05_part995_checked

  · exact kid05_part1049_checked

  · exact kid05_part1079_checked

def kid05_part1081 : Audit := .cycle 1 10 true (1)
theorem kid05_part1081_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid05_part1081) = true := by rfl

def kid05_part1082 : Audit := .cycle 11 11 false (1)
theorem kid05_part1082_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid05_part1082) = true := by rfl

def kid05_part1083 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 18 1 false (-2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 25 1 false (1),
.cycle 13 6 false (1),
.cycle 15 1 false (-1),
.cycle 0 24 true (-2),
.cycle 1 13 true (0),
.last 12 (4,true),
.last 16 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.last 14 (4,true)
]),
.cycle 15 1 false (-1),
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
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 26 (4,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 48 1 false (8),
.cycle 7 6 true (2),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 25 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 24 1 false (2),
.cycle 17 5 false (1),
.cycle 22 1 false (-2),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 18 1 false (-2),
.cycle 1 12 true (1),
.cycle 19 1 false (-1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.cycle 15 1 false (-1),
.last 27 (4,true),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 17 (4,true),
.cycle 1 12 true (1),
.last 16 (4,true),
.last 13 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 15 (4,true)
]),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 19 1 false (-1),
.cycle 10 2 true (2),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 10 13 true (2),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 2 11 true (1),
.cycle 6 6 true (2),
.cycle 19 1 false (-1),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
]),
.cycle 9 2 true (2)
])
theorem kid05_part1083_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid05_part1083) = true := by rfl

def kid05_part1084 : Audit := .cycle 0 11 true (0)
theorem kid05_part1084_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid05_part1084) = true := by rfl

def kid05_part1086 : Audit := .cycle 0 11 true (0)
theorem kid05_part1086_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1086) = true := by rfl

def kid05_part1087 : Audit := .cycle 1 10 true (1)
theorem kid05_part1087_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1087) = true := by rfl

def kid05_part1088 : Audit := .cycle 21 1 false (1)
theorem kid05_part1088_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1088) = true := by rfl

def kid05_part1089 : Audit := .cycle 1 13 true (0)
theorem kid05_part1089_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1089) = true := by rfl

def kid05_part1090 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (0),
.cycle 14 11 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 1 true (1),
.cycle 11 2 true (1),
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 1 13 true (0),
.cycle 13 1 false (-1),
.cycle 17 2 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (1),
.cycle 14 3 false (0)
])
theorem kid05_part1090_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1090) = true := by rfl

def kid05_part1091 : Audit := .split 14 (4,false) (byMove [
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
.last 16 (2,true),
.cycle 0 17 false (3),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 18 false (2),
.cycle 1 14 false (3),
.cycle 11 11 false (1),
.cycle 1 17 false (3),
.cycle 14 1 true (-2),
.cycle 11 4 false (1)
])
theorem kid05_part1091_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1091) = true := by rfl

def kid05_part1092 : Audit := .cycle 0 11 true (0)
theorem kid05_part1092_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1092) = true := by rfl

def kid05_part1093 : Audit := .cycle 1 10 true (1)
theorem kid05_part1093_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1093) = true := by rfl

def kid05_part1094 : Audit := .cycle 1 24 true (0)
theorem kid05_part1094_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1094) = true := by rfl

def kid05_part1095 : Audit := .cycle 20 1 false (2)
theorem kid05_part1095_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1095) = true := by rfl

def kid05_part1096 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 17 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 1 24 true (0),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 7 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 1 false (4),
.cycle 21 2 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid05_part1096_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1096) = true := by rfl

def kid05_part1097 : Audit := .split 12 (4,false) (byMove [
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
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 26 1 false (2),
.cycle 15 2 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 9 4 true (2)
])
theorem kid05_part1097_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1097) = true := by rfl

def kid05_part1098 : Audit := .cycle 17 5 false (1)
theorem kid05_part1098_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1098) = true := by rfl

def kid05_part1099 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.last 21 (4,false),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 16 (4,false),
.last 18 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.last 14 (4,false),
.last 20 (4,false),
.last 21 (4,false),
.cycle 1 27 true (-1),
.cycle 1 14 true (1),
.last 16 (4,false),
.last 29 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 25 (4,false)
])
theorem kid05_part1099_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1099) = true := by rfl

def kid05_part1100 : Audit := .cycle 0 13 true (0)
theorem kid05_part1100_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1100) = true := by rfl

def kid05_part1101 : Audit := .cycle 18 1 false (0)
theorem kid05_part1101_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1101) = true := by rfl

def kid05_part1102 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.cycle 71 32 false (0),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 1 12 true (1),
.cycle 13 14 true (-2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (1),
.cycle 8 4 true (1),
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 19 2 false (-1),
.cycle 1 12 true (1),
.cycle 16 5 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 2, 32, 0, 64],[2, 0, 64, 1, 32, 32, 64],64⟩
])
theorem kid05_part1102_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1102) = true := by rfl

def kid05_part1103 : Audit := .split 14 (4,false) (byMove [
.cycle 16 30 true (-2),
.cycle 11 12 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.last 16 (2,true),
.cycle 0 26 true (-2),
.cycle 15 1 false (-1),
.cycle 12 4 true (-2),
.cycle 13 2 true (-2),
.cycle 11 7 false (1),
.last 16 (2,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 17 4 true (-2),
.last 16 (2,true),
.cycle 0 26 true (-2),
.cycle 11 9 false (1),
.cycle 16 4 true (-1),
.cycle 11 4 false (1)
])
theorem kid05_part1103_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1103) = true := by rfl

def kid05_part1104 : Audit := .cycle 0 11 true (0)
theorem kid05_part1104_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1104) = true := by rfl

def kid05_part1105 : Audit := .cycle 1 10 true (1)
theorem kid05_part1105_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1105) = true := by rfl

def kid05_part1106 : Audit := .cycle 2 9 true (1)
theorem kid05_part1106_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1106) = true := by rfl

def kid05_part1107 : Audit := .cycle 1 13 true (1)
theorem kid05_part1107_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1107) = true := by rfl

def kid05_part1108 : Audit := .split 11 (4,false) (byMove [
.cycle 1 12 true (1),
.cycle 13 14 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 11 1 true (3),
.cycle 11 2 true (3),
.cycle 6 6 true (2),
.last 20 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 1 true (3),
.cycle 9 3 true (2)
])
theorem kid05_part1108_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1108) = true := by rfl

def kid05_part1109 : Audit := .cycle 9 2 true (2)
theorem kid05_part1109_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1109) = true := by rfl

def kid05_part1085 : Audit := .split 10 (4,true) (byMove [(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1107),(kid05_part1108),(kid05_part1109)])

theorem kid05_part1085_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid05_part1085) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1107),(kid05_part1108),(kid05_part1109)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1086_checked

  · exact kid05_part1092_checked

  · exact kid05_part1098_checked

  · exact kid05_part1104_checked

  · exact kid05_part1087_checked

  · exact kid05_part1093_checked

  · exact kid05_part1099_checked

  · exact kid05_part1105_checked

  · exact kid05_part1088_checked

  · exact kid05_part1094_checked

  · exact kid05_part1100_checked

  · exact kid05_part1106_checked

  · exact kid05_part1089_checked

  · exact kid05_part1095_checked

  · exact kid05_part1101_checked

  · exact kid05_part1107_checked

  · exact kid05_part1090_checked

  · exact kid05_part1096_checked

  · exact kid05_part1102_checked

  · exact kid05_part1108_checked

  · exact kid05_part1091_checked

  · exact kid05_part1097_checked

  · exact kid05_part1103_checked

  · exact kid05_part1109_checked

def kid05_part1110 : Audit := .cycle 8 2 true (2)
theorem kid05_part1110_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid05_part1110) = true := by rfl

def kid05_part1111 : Audit := .cycle 0 10 true (0)
theorem kid05_part1111_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid05_part1111) = true := by rfl

def kid05_part1112 : Audit := .cycle 1 9 true (1)
theorem kid05_part1112_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid05_part1112) = true := by rfl

def kid05_part1113 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.cycle 38 1 false (2),
.cycle 45 1 false (1),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (4),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 32, 4, 128, 256, 8, 128, 32, 4, 4096],[128, 8, 4, 1, 4096, 2048, 128, 4, 4096, 1, 4096, 2048, 4096],4096⟩,
.cycle 6 15 true (2),
.cycle 0 25 true (0),
.cycle 7 19 true (1),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 8 14 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (4),
.cycle 9 12 true (2)
]),
.cycle 9 11 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 4, 64],[2, 12, 4, 1, 64, 32, 64],80⟩,
.cycle 11 9 true (2),
.split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.last 23 (4,true),
.last 33 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.last 33 (4,true),
.last 31 (4,true),
.cycle 20 1 true (6),
.last 35 (4,true),
.cycle 7 15 true (2),
.cycle 19 3 true (5),
.cycle 0 23 true (0),
.cycle 12 9 true (2),
.last 23 (4,true),
.cycle 18 3 true (4),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6),
.cycle 9 12 true (2)
]),
.cycle 8 26 true (2),
.cycle 7 14 true (2),
.cycle 16 6 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.split 20 (4,false) (byMove [
.last 24 (4,true),
.cycle 38 1 false (2),
.cycle 36 1 false (0),
.cycle 7 16 true (2),
.last 21 (4,true),
.cycle 17 4 true (3),
.cycle 1 21 true (1),
.cycle 9 13 true (2),
.cycle 19 2 true (4),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 15 6 true (3),
.cycle 1 25 true (1),
.cycle 14 10 true (1),
.cycle 5 16 true (1),
.last 21 (4,true),
.cycle 8 15 true (2),
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 22 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2)
]),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.split 20 (4,false) (byMove [
.cycle 1 21 true (1),
.cycle 9 13 true (2),
.cycle 19 2 true (5),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 10 11 true (2),
.cycle 3 18 true (1),
.cycle 20 1 true (6),
.last 33 (4,true),
.cycle 6 15 true (2),
.cycle 0 25 true (0),
.last 22 (4,true),
.cycle 1 22 true (1),
.last 21 (4,true),
.cycle 8 14 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 20 1 true (6),
.cycle 9 12 true (2)
]),
.cycle 9 11 true (2)
])
theorem kid05_part1113_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid05_part1113) = true := by rfl

def kid05_part1114 : Audit := .cycle 3 7 true (1)
theorem kid05_part1114_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid05_part1114) = true := by rfl

def kid05_part1115 : Audit := .split 10 (4,false) (byMove [
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
.last 24 (2,true),
.cycle 12 9 true (0),
.cycle 17 1 false (1),
.cycle 20 1 false (2),
.cycle 21 7 false (2),
.last 14 (2,true),
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
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 2 29 true (1),
.last 26 (2,true),
.cycle 0 25 true (0),
.last 24 (2,true),
.cycle 1 22 true (1),
.last 40 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 4, 16, 128, 256, 8, 128, 4, 16, 4096],[128, 4, 4096, 1, 16, 2048, 128, 16, 4096, 1, 16, 2048, 4096],4096⟩,
.cycle 8 14 true (2),
.cycle 7 21 true (2),
.last 23 (2,true),
.cycle 1 24 true (1),
.cycle 4 25 true (1),
.last 23 (2,true),
.cycle 20 2 true (4),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 22 11 true (6),
.cycle 8 14 true (2)
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
.last 31 (2,true),
.cycle 11 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 27, 8, 16, 64],[2, 24, 64, 1, 16, 32, 64],64⟩,
.cycle 8 26 true (2),
.cycle 7 14 true (2),
.last 21 (2,true),
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
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 29 1 false (1),
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
.last 16 (4,true),
.cycle 5 11 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 17 (4,true),
.cycle 9 4 true (3)
]),
.cycle 0 13 true (0),
.cycle 4 7 true (1),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 43 1 false (3),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 18 1 false (0),
.cycle 6 7 true (2),
.cycle 21 1 false (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 26 1 false (6),
.cycle 8 6 true (2),
.cycle 14 17 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 36 1 false (2),
.cycle 15 1 false (-1),
.cycle 12 2 true (1),
.cycle 6 7 true (2),
.cycle 1 16 true (1),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.cycle 8 6 true (2)
]),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 11 9 true (2),
.cycle 10 3 true (3),
.cycle 9 4 true (3),
.cycle 7 7 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 8 8 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 7 true (2),
.cycle 9 4 true (3)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part1115_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid05_part1115) = true := by rfl

def kid05_part1116 : Audit := .cycle 9 1 true (3)
theorem kid05_part1116_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid05_part1116) = true := by rfl

def kid05_part1117 : Audit := .cycle 6 4 true (2)
theorem kid05_part1117_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid05_part1117) = true := by rfl

def kid05_part1118 : Audit := .split 15 (2,true) (byMove [
.cycle 0 32 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 32, 64],80⟩,
.split 16 (4,true) (byMove [
.cycle 0 17 false (3),
.cycle 11 14 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 128, 4096, 128, 128, 256, 8, 128, 4096, 128, 4096],[128, 256, 4096, 1, 1, 2048, 128, 128, 128, 1, 1, 2048, 4096],5136⟩,
.cycle 0 32 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 13 4 true (-2),
.cycle 11 9 false (1),
.cycle 14 3 false (-1),
.last 24 (4,false),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 40 22 false (2),
.cycle 0 32 true (-2),
.cycle 11 13 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 128, 4096, 128, 128, 256, 8, 128, 4096, 128, 4096],[128, 256, 4096, 1, 512, 2048, 128, 128, 128, 1, 512, 2048, 4096],5136⟩,
.last 17 (4,false),
.cycle 11 6 false (1)
]),
.cycle 11 6 false (1),
.cycle 7 10 false (3),
.cycle 16 15 true (0),
.cycle 0 28 true (-2),
.cycle 11 11 false (1),
.split 16 (4,false) (byMove [
.last 60 (4,true),
.cycle 0 32 true (-2),
.cycle 11 13 false (1),
.far true 8 ⟨0,[0, 2, 1, 4, 6, 7, 5, 4, 4, 1, 1, 3, 4, 3, 4, 4],[34359738368, 524288, 35184372088832, 32768, 8, 8192, 281509873321984, 281509907400832, 281510041619072, 134217728, 512, 33554432, 2199023255552, 524288, 524288, 35184372088832, 549755813888, 8796093022208, 34896611328, 524288, 281509907400832, 134217728, 8589934592, 33554432, 281509873321984, 281509907400832, 281510041619072, 512, 134217728, 128, 34359738368, 281509873321984, 512, 2097152, 512, 524288, 34359738368, 34359738368, 134217728, 2097152, 134217728, 524288, 536870912, 281474976710656, 524288, 134217728, 134217728, 33554432, 281474976710656],[34359738368, 32, 32768, 524288, 281474976710656, 2199023255552, 281509873321984, 2048, 281475110928384, 281475010789504, 281474976710656, 34896611328, 2199023255552, 2199023255552, 281474976710656, 524288, 281474976710656, 536870912, 34896611328, 34359738368, 281474976710656, 524288, 281474976710656, 34896611328, 281509873321984, 536870912, 281474976711168, 281475010789504, 281474976710656, 34896611328, 34359738368, 2048, 2097152, 34078848, 281474976710656, 536870912, 34359738368, 536870912, 2097152, 524288, 281474976710656, 536870912, 536870912, 536870912, 281474976710656, 524288, 281474976710656, 34896611328, 281474976710656],435409416227264⟩,
.last 18 (4,true),
.cycle 11 6 false (1),
.cycle 0 21 true (-2),
.cycle 22 19 true (2),
.last 41 (4,true),
.cycle 0 28 true (-2),
.last 17 (4,true),
.cycle 17 11 true (-1),
.cycle 11 12 false (1),
.last 19 (4,true),
.cycle 0 25 true (-2),
.cycle 11 11 false (1),
.last 18 (4,true),
.cycle 11 6 false (1),
.last 54 (4,true),
.cycle 7 10 false (3),
.cycle 17 15 true (1),
.cycle 9 14 false (3),
.last 17 (4,true),
.cycle 7 12 false (3)
]),
.cycle 19 18 false (2),
.cycle 11 8 false (1),
.cycle 12 4 false (0),
.cycle 11 18 true (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 15, 64, 15, 64],[2, 15, 15, 1, 64, 32, 64],80⟩,
.split 16 (4,true) (byMove [
.cycle 18 4 true (-3),
.cycle 24 17 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 128, 4096, 128, 128, 256, 8, 128, 4096, 128, 4096],[128, 256, 4096, 1, 1, 2048, 128, 128, 128, 1, 1, 2048, 4096],5136⟩,
.cycle 12 5 false (0),
.last 18 (4,false),
.cycle 11 10 true (-2),
.last 18 (4,false),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 14 3 false (-1),
.last 24 (4,false),
.cycle 17 1 false (-3),
.last 17 (4,false),
.cycle 13 4 false (-1),
.cycle 40 22 false (2),
.cycle 11 8 false (1),
.cycle 15 2 true (-2),
.cycle 7 12 false (3),
.last 18 (4,false),
.cycle 11 10 false (1)
]),
.cycle 11 10 false (1),
.cycle 11 14 false (1),
.cycle 34 18 false (2),
.cycle 0 28 true (-2),
.cycle 4 12 false (3),
.split 16 (4,false) (byMove [
.last 60 (4,true),
.cycle 11 8 false (1),
.cycle 15 2 true (-1),
.cycle 7 12 false (3),
.last 17 (4,true),
.cycle 11 10 false (1),
.cycle 38 14 false (2),
.cycle 11 10 false (1),
.last 36 (4,true),
.cycle 0 28 true (-2),
.last 17 (4,true),
.cycle 17 16 false (2),
.cycle 11 12 false (1),
.cycle 11 8 false (1),
.last 18 (4,true),
.cycle 5 12 false (3),
.last 17 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 6144, 1024, 128, 256, 8, 128, 2048, 2048, 4096],[128, 2048, 1024, 1, 4096, 2048, 128, 2048, 1024, 1, 4096, 2048, 4096],4112⟩,
.cycle 42 18 false (2),
.cycle 11 14 false (1),
.last 52 (4,true),
.cycle 19 18 false (3),
.last 17 (4,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 2048, 1024, 128, 256, 8, 128, 2048, 2048, 4096],[128, 2048, 1024, 1, 4096, 2048, 128, 2048, 1024, 1, 4096, 2048, 4096],4096⟩
]),
.cycle 11 8 false (1)
])
theorem kid05_part1118_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid05_part1118) = true := by rfl

def kid05_part1119 : Audit := .split 10 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 17 true (0),
.split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 0 20 true (-2),
.cycle 15 1 false (-1),
.last 16 (4,true),
.last 12 (4,true),
.last 22 (4,true),
.cycle 7 6 true (1),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 13 (4,true),
.cycle 1 15 true (1),
.cycle 13 6 false (1),
.last 24 (4,true),
.cycle 12 8 true (-2),
.last 16 (4,true),
.last 12 (4,true),
.last 16 (4,true),
.last 17 (4,true),
.last 14 (4,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 11 8 true (-2),
.cycle 1 11 true (1),
.cycle 0 15 true (0),
.cycle 29 1 false (7),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 28 (4,false),
.cycle 1 24 true (0),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 7 6 true (2),
.last 14 (4,false),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 12 (4,false),
.cycle 1 15 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 8 3 true (2),
.cycle 17 5 false (1),
.cycle 13 11 false (1),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.split 11 (4,false) (byMove [
.last 15 (4,true),
.last 19 (4,true),
.cycle 15 1 false (-1),
.cycle 19 1 false (-1),
.last 12 (4,true),
.cycle 12 9 false (1),
.cycle 6 6 true (1),
.cycle 13 10 true (-2),
.cycle 10 2 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true),
.cycle 13 6 false (1),
.last 24 (4,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.last 12 (4,true),
.last 18 (4,true),
.last 17 (4,true),
.last 16 (4,true),
.last 13 (4,true),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 16 (4,true)
]),
.cycle 11 8 true (-2),
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.cycle 2 10 true (1),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 0 20 true (-2),
.last 13 (4,false),
.cycle 0 13 true (0),
.last 13 (4,false),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (4,false),
.cycle 3 9 true (1),
.last 12 (4,false),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 13 10 true (-2),
.cycle 10 2 true (2),
.cycle 1 13 true (1),
.last 13 (4,false),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
]),
.cycle 8 3 true (2)
])
theorem kid05_part1119_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid05_part1119) = true := by rfl

def kid05_part1120 : Audit := .cycle 1 11 true (1)
theorem kid05_part1120_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid05_part1120) = true := by rfl

def kid05_part1122 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 19 7 false (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 12 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 4104, 4, 1, 256, 2048, 128, 4, 4, 1, 256, 2048, 4096],5168⟩,
.cycle 3 11 true (1),
.last 14 (4,false),
.last 15 (4,false),
.cycle 12 8 true (1),
.cycle 19 7 false (2),
.cycle 14 12 true (-1),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.cycle 12 7 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 14 (4,false),
.cycle 12 5 true (2)
])
theorem kid05_part1122_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid05_part1122) = true := by rfl

def kid05_part1123 : Audit := .cycle 0 14 true (0)
theorem kid05_part1123_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid05_part1123) = true := by rfl

def kid05_part1124 : Audit := .cycle 21 1 false (1)
theorem kid05_part1124_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid05_part1124) = true := by rfl

def kid05_part1125 : Audit := .split 15 (2,true) (byMove [
.cycle 1 16 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 0 18 true (0),
.cycle 25 1 false (1),
.cycle 0 16 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 8577, 262144, 262144, 128, 256, 32768, 128, 262144, 8193, 128, 256, 8, 8193, 262144, 262144, 262144],[128, 262144, 2, 1, 33152, 2048, 128, 8193, 8192, 4096, 128, 2048, 128, 384, 2, 1, 256, 2048, 262144],459824⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 133, 4096, 4096, 128, 256, 8, 128, 4096, 5, 4096],[128, 4232, 4, 1, 392, 2048, 128, 5, 4, 1, 128, 2048, 4096],5168⟩,
.cycle 3 13 true (0),
.last 16 (4,false),
.last 17 (4,false),
.cycle 27 1 false (1),
.cycle 20 1 false (0),
.cycle 25 1 false (1),
.cycle 1 17 true (0),
.cycle 23 1 false (1),
.cycle 7 15 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 1 18 true (0),
.last 16 (4,false),
.cycle 7 13 true (0)
])
theorem kid05_part1125_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid05_part1125) = true := by rfl

def kid05_part1126 : Audit := .split 11 (4,false) (byMove [
.cycle 0 16 true (0),
.last 65 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 7 6 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 14 1 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 17 2 false (-1),
.cycle 0 24 true (-1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 17 1 true (-1),
.cycle 14 3 false (0)
])
theorem kid05_part1126_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid05_part1126) = true := by rfl

def kid05_part1127 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 33 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 13 3 false (-1),
.last 15 (2,true),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 11 5 false (1),
.cycle 11 7 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.last 17 (2,true),
.cycle 11 6 false (1),
.last 15 (2,true),
.cycle 7 10 false (3),
.cycle 11 6 false (1),
.cycle 11 8 false (1)
])
theorem kid05_part1127_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid05_part1127) = true := by rfl

def kid05_part1128 : Audit := .cycle 1 11 true (1)
theorem kid05_part1128_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid05_part1128) = true := by rfl

def kid05_part1129 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.last 22 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.last 16 (2,true),
.cycle 18 2 false (0),
.cycle 1 14 true (1),
.cycle 17 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 8 6 true (1),
.cycle 15 8 false (1),
.last 18 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 17 1 false (-1),
.cycle 26 2 false (0),
.cycle 1 14 true (1),
.cycle 19 7 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 18 9 false (2)
])
theorem kid05_part1129_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid05_part1129) = true := by rfl

def kid05_part1130 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 1 24 true (0),
.last 12 (4,false),
.last 13 (4,false),
.cycle 7 6 true (2),
.last 22 (4,false),
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
theorem kid05_part1130_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid05_part1130) = true := by rfl

def kid05_part1131 : Audit := .cycle 0 12 true (0)
theorem kid05_part1131_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid05_part1131) = true := by rfl

def kid05_part1132 : Audit := .split 12 (4,false) (byMove [
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
.cycle 7 7 true (2),
.last 14 (2,true),
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
theorem kid05_part1132_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid05_part1132) = true := by rfl

def kid05_part1133 : Audit := .cycle 8 3 true (2)
theorem kid05_part1133_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid05_part1133) = true := by rfl

def kid05_part1134 : Audit := .cycle 17 5 false (1)
theorem kid05_part1134_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid05_part1134) = true := by rfl

def kid05_part1135 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 21 (4,false),
.cycle 16 1 false (0),
.cycle 7 8 true (1),
.last 16 (4,false),
.last 18 (4,false),
.cycle 1 13 true (1),
.last 18 (4,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 1],[128, 256, 8, 4, 262144, 262144, 8192, 16384, 8, 128, 262144, 4, 128, 256, 8, 128, 262144, 262276, 262144],[128, 278536, 4, 1, 4, 2048, 8192, 4, 4, 1, 262149, 131072, 128, 262276, 4, 1, 4, 2048, 262144],459824⟩,
.cycle 0 14 true (0),
.last 16 (4,false),
.cycle 8 5 true (1),
.last 20 (4,false),
.last 21 (4,false),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 16 (4,false),
.last 24 (4,false),
.cycle 1 13 true (1),
.last 29 (4,false),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 20 (4,false),
.last 22 (4,false)
])
theorem kid05_part1135_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid05_part1135) = true := by rfl

def kid05_part1136 : Audit := .cycle 1 13 true (1)
theorem kid05_part1136_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid05_part1136) = true := by rfl

def kid05_part1137 : Audit := .cycle 18 1 false (0)
theorem kid05_part1137_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid05_part1137) = true := by rfl

def kid05_part1138 : Audit := .split 11 (4,false) (byMove [
.last 14 (2,true),
.last 20 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 15 2 false (-1),
.cycle 6 6 true (1),
.cycle 15 3 false (0),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 13 6 false (1),
.last 16 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 21 2 false (-1),
.cycle 17 7 false (1),
.cycle 16 5 false (0),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 13 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid05_part1138_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid05_part1138) = true := by rfl

def kid05_part1139 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.last 33 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 11 7 false (1),
.cycle 13 3 false (-1),
.last 15 (2,true),
.cycle 11 8 true (-2),
.cycle 12 3 false (0),
.cycle 17 5 true (1),
.cycle 11 7 false (1),
.last 16 (2,true),
.cycle 11 9 false (1),
.cycle 15 1 false (-3),
.cycle 14 1 false (-2),
.cycle 13 2 false (-1),
.cycle 23 5 true (1),
.cycle 11 6 false (1),
.last 15 (2,true),
.cycle 5 10 false (3),
.cycle 19 5 true (1),
.cycle 17 5 true (1)
])
theorem kid05_part1139_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid05_part1139) = true := by rfl

def kid05_part1140 : Audit := .cycle 1 11 true (1)
theorem kid05_part1140_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid05_part1140) = true := by rfl

def kid05_part1141 : Audit := .cycle 7 4 true (2)
theorem kid05_part1141_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid05_part1141) = true := by rfl

def kid05_part1142 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.last 18 (4,false),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4096, 4096, 128, 256, 8, 128, 4096, 4, 4096],[128, 4104, 4, 1, 256, 2048, 128, 4, 4, 1, 256, 2048, 4096],5168⟩,
.cycle 3 9 true (1),
.last 12 (4,false),
.last 13 (4,false),
.cycle 6 6 true (2),
.last 18 (4,false),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (2),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 12 (4,false),
.cycle 9 3 true (2)
])
theorem kid05_part1142_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid05_part1142) = true := by rfl

def kid05_part1143 : Audit := .cycle 0 12 true (0)
theorem kid05_part1143_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid05_part1143) = true := by rfl

def kid05_part1144 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 13 (2,true),
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
.cycle 10 7 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 10 3 true (2),
.cycle 8 6 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 9 4 true (2)
])
theorem kid05_part1144_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid05_part1144) = true := by rfl

def kid05_part1145 : Audit := .cycle 8 3 true (2)
theorem kid05_part1145_checked : zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid05_part1145) = true := by rfl

def kid05_part1121 : Audit := .split 10 (4,true) (byMove [(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130),(kid05_part1131),(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144),(kid05_part1145)])

theorem kid05_part1121_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid05_part1121) = true := by

  change (zipQueryOK 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 175 (refine (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130),(kid05_part1131),(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144),(kid05_part1145)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part1127_checked

  · exact kid05_part1133_checked

  · exact kid05_part1139_checked

  · exact kid05_part1145_checked

def kid05_part1146 : Audit := .cycle 8 3 true (2)
theorem kid05_part1146_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid05_part1146) = true := by rfl

def kid05_part1147 : Audit := .cycle 0 10 true (0)
theorem kid05_part1147_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid05_part1147) = true := by rfl

def kid05_part1148 : Audit := .cycle 1 9 true (1)
theorem kid05_part1148_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid05_part1148) = true := by rfl

def kid05_part1149 : Audit := .cycle 2 8 true (1)
theorem kid05_part1149_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid05_part1149) = true := by rfl

def kid05_part1150 : Audit := .cycle 1 12 true (1)
theorem kid05_part1150_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid05_part1150) = true := by rfl

def kid05_part1151 : Audit := .split 10 (4,false) (byMove [
.cycle 1 11 true (1),
.cycle 7 4 true (2),
.split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 13 15 false (2),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (4,true),
.cycle 3 9 true (1),
.cycle 2 11 true (1),
.cycle 9 3 true (3),
.cycle 6 6 true (2),
.cycle 15 6 false (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 0 12 true (0),
.split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 13 15 false (2),
.last 12 (2,true),
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
.last 21 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 15 1 false (-1),
.cycle 8 5 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
]),
.cycle 8 3 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 20 (4,true) (byMove [
.cycle 1 21 true (1),
.cycle 7 14 true (2),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 52 1 false (2),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 11 10 true (3),
.cycle 3 18 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1040, 4, 1024, 128, 256, 8, 128, 4, 1024, 4096],[128, 4, 4096, 1, 16, 2048, 128, 1024, 4096, 1, 16, 2048, 4096],4096⟩,
.cycle 9 12 true (3),
.cycle 6 15 true (2),
.cycle 17 4 true (4),
.last 21 (2,true),
.cycle 1 22 true (1),
.last 24 (2,true),
.cycle 8 14 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 10 11 true (3),
.cycle 9 12 true (3)
]),
.cycle 3 8 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3),
.cycle 6 5 true (2),
.split 14 (4,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 17 3 false (1),
.cycle 8 7 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (2),
.cycle 3 12 true (1),
.last 17 (2,true),
.cycle 8 16 true (2),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 17 3 false (1),
.cycle 8 8 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 10 5 true (2),
.cycle 9 6 true (2)
]),
.split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.last 40 (4,true),
.cycle 25 1 false (1),
.cycle 7 7 true (2),
.last 12 (4,true),
.last 14 (4,true),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.last 23 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2),
.last 16 (4,true),
.cycle 15 6 false (1),
.cycle 5 9 true (1),
.cycle 5 7 true (1),
.last 12 (4,true),
.cycle 8 6 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 4 true (2)
]),
.cycle 1 12 true (1),
.split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 41 13 true (0),
.last 12 (2,true),
.cycle 7 7 true (2),
.cycle 15 1 false (-1),
.cycle 8 7 true (2),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 33 1 false (7),
.cycle 8 4 true (2),
.cycle 6 11 true (2),
.last 21 (2,true),
.last 12 (2,true),
.cycle 5 7 true (1),
.cycle 15 1 false (-1),
.cycle 8 6 true (2),
.cycle 1 12 true (1),
.cycle 7 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 3 true (3),
.cycle 8 4 true (2)
]),
.cycle 8 4 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 10 1 true (4),
.cycle 9 2 true (3)
])
theorem kid05_part1151_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid05_part1151) = true := by rfl

def kid05_part1152 : Audit := .cycle 9 1 true (3)
theorem kid05_part1152_checked : zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid05_part1152) = true := by rfl

def kid05_part1080 : Audit := .split 9 (5,false) (byMove [(kid05_part1081),(kid05_part1082),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118),(kid05_part1119),(kid05_part1120),(kid05_part1121),(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152)])

theorem kid05_part1080_checked : zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (kid05_part1080) = true := by

  change (zipQueryOK 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 175 (refine (refine (child39 ⟨false,false,5⟩) (5,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid05_part1081),(kid05_part1082),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118),(kid05_part1119),(kid05_part1120),(kid05_part1121),(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1081_checked

  · exact kid05_part1111_checked

  · exact kid05_part1117_checked

  · exact kid05_part1147_checked

  · exact kid05_part1082_checked

  · exact kid05_part1112_checked

  · exact kid05_part1118_checked

  · exact kid05_part1148_checked

  · exact kid05_part1083_checked

  · exact kid05_part1113_checked

  · exact kid05_part1119_checked

  · exact kid05_part1149_checked

  · exact kid05_part1084_checked

  · exact kid05_part1114_checked

  · exact kid05_part1120_checked

  · exact kid05_part1150_checked

  · exact kid05_part1085_checked

  · exact kid05_part1115_checked

  · exact kid05_part1121_checked

  · exact kid05_part1151_checked

  · exact kid05_part1110_checked

  · exact kid05_part1116_checked

  · exact kid05_part1146_checked

  · exact kid05_part1152_checked

def kid05 : Audit := .split 8 (5,true) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part5),(kid05_part150),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part348),(kid05_part421),(kid05_part422),(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part858),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part1080)])

theorem check05 : zipCheck 175 (child39 ⟨false,false,5⟩) (kid05) = true := by

  change (zipQueryOK 175 (child39 ⟨false,false,5⟩) 8 (5,true) && allMoves (fun mv => zipCheck 175 (refine (child39 ⟨false,false,5⟩) (5,true) (some mv)) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part5),(kid05_part150),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part348),(kid05_part421),(kid05_part422),(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part858),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part1080)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1_checked

  · exact kid05_part223_checked

  · exact kid05_part421_checked

  · exact kid05_part979_checked

  · exact kid05_part2_checked

  · exact kid05_part224_checked

  · exact kid05_part422_checked

  · exact kid05_part980_checked

  · exact kid05_part3_checked

  · exact kid05_part225_checked

  · exact kid05_part543_checked

  · exact kid05_part981_checked

  · exact kid05_part4_checked

  · exact kid05_part226_checked

  · exact kid05_part544_checked

  · exact kid05_part982_checked

  · exact kid05_part5_checked

  · exact kid05_part227_checked

  · exact kid05_part545_checked

  · exact kid05_part983_checked

  · exact kid05_part150_checked

  · exact kid05_part348_checked

  · exact kid05_part858_checked

  · exact kid05_part1080_checked

end BB6.Agent11Raw39
