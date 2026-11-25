import Raw39B0REBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid10_part1 : Audit := .cycle 0 9 true (0)
theorem kid10_part1_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,0⟩)) (kid10_part1) = true := by rfl

def kid10_part2 : Audit := .cycle 1 8 true (1)
theorem kid10_part2_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,1⟩)) (kid10_part2) = true := by rfl

def kid10_part3 : Audit := .cycle 21 1 false (5)
theorem kid10_part3_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,2⟩)) (kid10_part3) = true := by rfl

def kid10_part4 : Audit := .cycle 17 1 false (3)
theorem kid10_part4_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,3⟩)) (kid10_part4) = true := by rfl

def kid10_part5 : Audit := .cycle 13 1 false (1)
theorem kid10_part5_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,4⟩)) (kid10_part5) = true := by rfl

def kid10_part7 : Audit := .cycle 0 10 true (0)
theorem kid10_part7_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part7) = true := by rfl

def kid10_part8 : Audit := .cycle 1 9 true (1)
theorem kid10_part8_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part8) = true := by rfl

def kid10_part9 : Audit := .cycle 21 1 false (3)
theorem kid10_part9_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part9) = true := by rfl

def kid10_part10 : Audit := .cycle 17 1 false (1)
theorem kid10_part10_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part10) = true := by rfl

def kid10_part11 : Audit := .cycle 13 2 false (1)
theorem kid10_part11_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part11) = true := by rfl

def kid10_part12 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.split 14 (1,true) (byMove [
.cycle 17 1 false (-1),
.cycle 24 1 false (0),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 9 15 false (4),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.last 17 (2,true),
.last 15 (2,true),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.cycle 10 21 false (5),
.cycle 30 1 false (0),
.cycle 2 13 false (4),
.cycle 10 9 false (2),
.cycle 20 1 false (0),
.cycle 20 1 false (0)
]),
.split 14 (2,true) (byMove [
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 9 15 false (4),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.last 28 (1,true),
.last 27 (1,true),
.cycle 2 13 false (4),
.cycle 10 9 false (2),
.last 17 (1,true),
.last 17 (1,true)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.cycle 12 2 true (0),
.cycle 11 2 true (0)
])
theorem kid10_part12_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part12) = true := by rfl

def kid10_part13 : Audit := .cycle 0 10 true (0)
theorem kid10_part13_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part13) = true := by rfl

def kid10_part14 : Audit := .cycle 1 9 true (1)
theorem kid10_part14_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part14) = true := by rfl

def kid10_part15 : Audit := .cycle 25 1 false (7)
theorem kid10_part15_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part15) = true := by rfl

def kid10_part16 : Audit := .cycle 21 1 false (5)
theorem kid10_part16_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part16) = true := by rfl

def kid10_part17 : Audit := .cycle 8 2 true (3)
theorem kid10_part17_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part17) = true := by rfl

def kid10_part18 : Audit := .cycle 9 1 true (3)
theorem kid10_part18_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part18) = true := by rfl

def kid10_part19 : Audit := .split 11 (1,true) (byMove [
.cycle 22 5 false (2),
.cycle 1 12 true (1),
.split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 22 5 false (2),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 18 4 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 6 8 true (2)
]),
.cycle 0 13 true (0),
.cycle 21 5 false (2),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.cycle 17 4 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 22 5 false (2),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.cycle 18 4 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 12 2 true (2),
.cycle 6 8 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (2),
.cycle 3 9 true (1),
.cycle 6 8 true (2),
.cycle 9 3 true (2),
.cycle 6 6 true (2),
.split 14 (2,true) (byMove [
.cycle 20 8 false (2),
.cycle 16 3 false (0),
.cycle 18 1 false (0),
.cycle 10 6 true (1),
.cycle 19 8 false (2),
.last 15 (5,true),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 1, 64],[3, 2, 2, 2, 3, 64, 64],64⟩,
.cycle 1 17 true (1),
.cycle 7 18 true (1),
.cycle 0 16 true (0),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 32, 1, 64],[3, 2, 3, 3, 3, 64, 64],64⟩,
.last 15 (5,true),
.cycle 7 10 true (1),
.cycle 16 3 false (0),
.cycle 21 12 true (0),
.cycle 5 10 true (1),
.cycle 7 10 true (1),
.last 15 (5,true),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 32, 1, 64],[3, 2, 3, 3, 3, 64, 64],64⟩,
.cycle 16 5 false (2),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 16, 128, 256, 8, 16, 4096, 16, 4096],[16, 1024, 1024, 1, 16, 4096, 16, 16, 1024, 1, 16, 4096, 4096],5120⟩,
.last 15 (5,true)
]),
.split 12 (2,true) (byMove [
.cycle 27 13 false (1),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 8 6 true (2),
.cycle 0 16 true (0),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 22 3 false (3),
.cycle 25 12 true (0),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.last 14 (5,true),
.cycle 19 4 false (3),
.cycle 6 10 true (2),
.cycle 11 2 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 6 10 true (2),
.last 13 (5,true)
]),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.cycle 17 4 false (1),
.cycle 8 6 true (2),
.cycle 25 5 false (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 9 5 true (2),
.cycle 22 3 false (3),
.last 14 (2,true),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.cycle 14 5 false (0),
.cycle 19 4 false (3),
.cycle 6 10 true (2),
.cycle 11 2 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 6 10 true (2),
.cycle 6 9 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (2),
.split 13 (5,true) (byMove [
.cycle 26 7 false (2),
.cycle 1 16 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 25 7 false (2),
.cycle 19 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.cycle 6 10 true (2),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.cycle 6 12 true (2),
.last 14 (2,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 0, 16, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 12 2 true (3),
.cycle 6 9 true (2)
]),
.cycle 6 7 true (2)
])
theorem kid10_part19_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part19) = true := by rfl

def kid10_part21 : Audit := .split 20 (1,true) (byMove [
.cycle 15 7 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (2),
.cycle 29 5 false (5),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.cycle 22 5 false (2),
.last 21 (5,true),
.cycle 26 5 false (2),
.cycle 21 5 false (0),
.cycle 23 5 false (2),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 17 4 true (0),
.cycle 1 21 true (0),
.cycle 21 5 false (1),
.cycle 0 22 true (0),
.cycle 18 4 true (0),
.last 21 (5,true)
])
theorem kid10_part21_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part21) = true := by rfl

def kid10_part22 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 22 5 false (2),
.cycle 9 4 true (2),
.cycle 21 9 false (2),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid10_part22_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part22) = true := by rfl

def kid10_part23 : Audit := .cycle 25 1 false (1)
theorem kid10_part23_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part23) = true := by rfl

def kid10_part24 : Audit := .cycle 0 13 true (0)
theorem kid10_part24_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part24) = true := by rfl

def kid10_part25 : Audit := .split 20 (1,true) (byMove [
.cycle 15 7 false (2),
.cycle 0 24 true (-1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 22 5 false (2),
.cycle 28 5 false (5),
.cycle 22 5 false (0),
.cycle 0 22 true (0),
.cycle 21 5 false (2),
.last 21 (5,true),
.cycle 25 5 false (2),
.cycle 21 5 false (0),
.cycle 24 5 false (2),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 18 4 true (0),
.cycle 1 21 true (0),
.cycle 21 5 false (1),
.cycle 0 22 true (0),
.cycle 17 4 true (0),
.last 21 (5,true)
])
theorem kid10_part25_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part25) = true := by rfl

def kid10_part26 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 20 (1,true),
.cycle 9 4 true (2),
.last 14 (1,true),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 12 2 true (2),
.last 14 (1,true)
])
theorem kid10_part26_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part26) = true := by rfl

def kid10_part27 : Audit := .cycle 0 12 true (0)
theorem kid10_part27_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part27) = true := by rfl

def kid10_part28 : Audit := .cycle 1 11 true (1)
theorem kid10_part28_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part28) = true := by rfl

def kid10_part29 : Audit := .cycle 7 12 true (2)
theorem kid10_part29_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part29) = true := by rfl

def kid10_part30 : Audit := .cycle 3 9 true (1)
theorem kid10_part30_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part30) = true := by rfl

def kid10_part31 : Audit := .split 14 (1,true) (byMove [
.cycle 22 14 false (2),
.cycle 0 18 true (0),
.cycle 30 1 false (2),
.cycle 25 1 false (-1),
.last 16 (5,true),
.cycle 15 6 false (1),
.cycle 8 8 true (2),
.cycle 1 15 true (1),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.last 15 (5,true),
.cycle 7 12 true (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 8 10 true (1),
.cycle 27 1 false (1),
.last 16 (5,true),
.far true 4 ⟨0,[0, 1, 2, 3, 2, 1, 2, 1],[8388608, 128, 2097152, 512, 32, 128, 16777216, 8388608, 25165824, 2097152, 131072, 524288, 25165824, 25165952, 2097664, 512, 131072, 128, 16777216, 16777216, 128, 512, 131072, 128, 16777216],[128, 2048, 128, 128, 128, 16777216, 8388608, 8388608, 8388608, 8388608, 8388608, 16777216, 128, 2048, 128, 16777344, 128, 16777216, 128, 2048, 128, 128, 128, 16777216, 16777216],17578304⟩,
.cycle 12 4 true (2),
.cycle 1 15 true (1),
.cycle 11 4 true (2),
.cycle 0 16 true (0),
.cycle 12 4 true (2),
.last 15 (5,true)
])
theorem kid10_part31_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part31) = true := by rfl

def kid10_part32 : Audit := .cycle 9 3 true (2)
theorem kid10_part32_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part32) = true := by rfl

def kid10_part33 : Audit := .cycle 6 6 true (2)
theorem kid10_part33_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part33) = true := by rfl

def kid10_part34 : Audit := .split 12 (1,true) (byMove [
.cycle 20 10 false (1),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 8 6 true (2),
.cycle 1 13 true (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 7 10 true (1),
.cycle 16 3 false (0),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 12 4 true (2),
.cycle 1 13 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 12 4 true (2),
.last 13 (5,true)
])
theorem kid10_part34_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part34) = true := by rfl

def kid10_part35 : Audit := .cycle 8 8 true (1)
theorem kid10_part35_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part35) = true := by rfl

def kid10_part36 : Audit := .cycle 8 6 true (2)
theorem kid10_part36_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part36) = true := by rfl

def kid10_part37 : Audit := .cycle 7 6 true (2)
theorem kid10_part37_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part37) = true := by rfl

def kid10_part38 : Audit := .split 12 (5,true) (byMove [
.last 20 (1,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (1,true),
.cycle 8 6 true (2),
.last 13 (1,true),
.last 20 (1,true),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 9 5 true (2),
.last 14 (1,true),
.last 16 (1,true),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.cycle 14 5 false (0),
.last 14 (1,true),
.last 16 (1,true),
.last 13 (1,true),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 16 (1,true),
.last 15 (1,true)
])
theorem kid10_part38_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part38) = true := by rfl

def kid10_part39 : Audit := .cycle 0 12 true (0)
theorem kid10_part39_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part39) = true := by rfl

def kid10_part40 : Audit := .cycle 1 11 true (1)
theorem kid10_part40_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part40) = true := by rfl

def kid10_part41 : Audit := .cycle 2 10 true (1)
theorem kid10_part41_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part41) = true := by rfl

def kid10_part42 : Audit := .cycle 8 7 true (2)
theorem kid10_part42_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part42) = true := by rfl

def kid10_part43 : Audit := .split 13 (5,true) (byMove [
.last 24 (1,true),
.last 14 (1,true),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 24 (1,true),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.last 16 (1,true),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.last 14 (1,true),
.last 18 (1,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 16 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 12 2 true (3),
.last 15 (1,true)
])
theorem kid10_part43_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part43) = true := by rfl

def kid10_part44 : Audit := .split 13 (1,true) (byMove [
.cycle 17 9 false (3),
.cycle 7 15 true (1),
.cycle 35 1 false (3),
.cycle 0 18 true (0),
.cycle 25 7 false (-1),
.last 14 (5,true),
.cycle 8 7 true (2),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 14 (5,true),
.cycle 7 9 true (2),
.last 17 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.last 14 (5,true),
.cycle 12 4 true (3),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 12 4 true (3),
.last 14 (5,true)
])
theorem kid10_part44_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part44) = true := by rfl

def kid10_part20 : Audit := .split 11 (2,true) (byMove [(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44)])

theorem kid10_part20_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part20) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid10_part21),(kid10_part22),(kid10_part23),(kid10_part24),(kid10_part25),(kid10_part26),(kid10_part27),(kid10_part28),(kid10_part29),(kid10_part30),(kid10_part31),(kid10_part32),(kid10_part33),(kid10_part34),(kid10_part35),(kid10_part36),(kid10_part37),(kid10_part38),(kid10_part39),(kid10_part40),(kid10_part41),(kid10_part42),(kid10_part43),(kid10_part44)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part21_checked

  · exact kid10_part27_checked

  · exact kid10_part33_checked

  · exact kid10_part39_checked

  · exact kid10_part22_checked

  · exact kid10_part28_checked

  · exact kid10_part34_checked

  · exact kid10_part40_checked

  · exact kid10_part23_checked

  · exact kid10_part29_checked

  · exact kid10_part35_checked

  · exact kid10_part41_checked

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

def kid10_part45 : Audit := .cycle 0 12 true (0)
theorem kid10_part45_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part45) = true := by rfl

def kid10_part46 : Audit := .cycle 18 1 false (2)
theorem kid10_part46_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part46) = true := by rfl

def kid10_part47 : Audit := .cycle 14 2 false (2)
theorem kid10_part47_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part47) = true := by rfl

def kid10_part49 : Audit := .split 15 (2,true) (byMove [
.cycle 11 7 false (1),
.last 16 (1,true),
.cycle 19 1 false (-1),
.last 18 (1,true),
.cycle 11 7 false (1),
.cycle 19 1 false (-1),
.cycle 25 1 false (-1),
.last 16 (1,true),
.far false 4 ⟨0,[0, 1, 1, 2, 2, 3, 3, 3],[128, 256, 8, 0, 0, 0, 8192, 16384, 512, 16, 32768, 16384, 524288, 1048576, 32768, 1024, 2097152, 1048576, 524288, 1048576, 2097152, 4259840, 24740864, 22352896, 16777216],[16, 16777216, 4, 1, 16, 16384, 1024, 16777216, 256, 64, 1024, 1048576, 65536, 16777216, 16384, 4096, 65536, 1081344, 4194304, 16777216, 1048576, 262144, 4194304, 24740864, 16777216],33501248⟩,
.cycle 25 1 false (-1),
.cycle 25 1 false (-1),
.cycle 29 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 16, 128, 256, 8, 16, 8, 16, 4096],[16, 4096, 4096, 1, 16, 256, 16, 4096, 16, 1, 16, 0, 4096],4096⟩,
.last 16 (1,true),
.cycle 25 1 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 16, 128, 256, 8, 16, 8, 16, 4096],[16, 4096, 16, 1, 16, 256, 16, 4096, 16, 1, 16, 0, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 16, 128, 256, 8, 16, 8, 16, 4096],[16, 4096, 1, 1, 16, 256, 16, 4096, 16, 1, 16, 0, 4096],4096⟩,
.cycle 19 1 false (-1),
.last 30 (1,true),
.last 16 (1,true),
.cycle 35 1 false (-1),
.cycle 42 1 false (-2),
.cycle 21 9 false (1),
.cycle 23 1 false (-1)
])
theorem kid10_part49_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part49) = true := by rfl

def kid10_part50 : Audit := .far true 5 ⟨0,[0, 1, 1, 2, 1, 3, 4, 3, 1, 1],[33554432, 8388608, 32768, 512, 32, 2048, 1107296256, 1115684864, 1109426176, 32768, 2048, 131072, 1073741824, 1073741824, 1115684864, 2097152, 2048, 8388608, 1073741824, 1073741824, 8388608, 2097152, 536870912, 8388608, 1073741824, 33554432, 2097152, 512, 2048, 2048, 1073741824],[2048, 1073741824, 1073741824, 33554432, 2048, 2, 131072, 1073741824, 1073741824, 1107427328, 131072, 128, 8388608, 1073741824, 1073741824, 8388608, 8388608, 128, 8388608, 1073741824, 1073741824, 8388608, 8388608, 33554432, 2048, 1073741824, 1073741824, 1073741824, 2048, 128, 1073741824],1091334592⟩
theorem kid10_part50_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part50) = true := by rfl

def kid10_part51 : Audit := .cycle 14 1 false (0)
theorem kid10_part51_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part51) = true := by rfl

def kid10_part52 : Audit := .cycle 13 1 false (-1)
theorem kid10_part52_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part52) = true := by rfl

def kid10_part53 : Audit := .cycle 14 1 false (-2)
theorem kid10_part53_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part53) = true := by rfl

def kid10_part54 : Audit := .cycle 13 1 false (-1)
theorem kid10_part54_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part54) = true := by rfl

def kid10_part55 : Audit := .cycle 17 1 false (3)
theorem kid10_part55_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part55) = true := by rfl

def kid10_part56 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.cycle 8 10 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.cycle 24 1 false (6),
.last 14 (2,true),
.cycle 17 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.cycle 21 1 false (3),
.last 15 (2,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 26 true (0),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 0 22 true (0),
.cycle 36 1 false (6),
.cycle 14 3 true (2)
])
theorem kid10_part56_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part56) = true := by rfl

def kid10_part57 : Audit := .split 13 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 8 10 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 17 1 false (3),
.last 14 (1,true),
.cycle 17 1 false (5),
.cycle 17 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.last 15 (1,true),
.last 16 (1,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 0 26 true (0),
.last 14 (1,true),
.cycle 2 14 true (0),
.cycle 0 22 true (0),
.cycle 29 1 false (5),
.cycle 14 3 true (2)
])
theorem kid10_part57_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part57) = true := by rfl

def kid10_part58 : Audit := .cycle 17 1 false (3)
theorem kid10_part58_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part58) = true := by rfl

def kid10_part59 : Audit := .cycle 17 1 false (3)
theorem kid10_part59_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part59) = true := by rfl

def kid10_part60 : Audit := .cycle 16 1 false (4)
theorem kid10_part60_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part60) = true := by rfl

def kid10_part61 : Audit := .split 14 (1,true) (byMove [
.cycle 17 1 false (-1),
.cycle 27 1 false (3),
.last 15 (2,true),
.cycle 0 25 true (-1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 2, 16, 64],[16, 1, 64, 1, 16, 17, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 4, 18, 64],[16, 2, 64, 1, 16, 18, 64],64⟩,
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 18, 17, 64],[16, 8, 64, 1, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 0, 16, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 44 1 false (4),
.cycle 21 1 false (3),
.last 17 (2,true),
.last 15 (2,true),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 12 3 false (0),
.cycle 29 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 4, 18, 64],[16, 2, 64, 1, 16, 18, 64],64⟩,
.last 15 (2,true),
.cycle 29 1 false (3),
.cycle 29 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 48, 48, 64],[16, 32, 64, 1, 16, 48, 64],64⟩
])
theorem kid10_part61_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part61) = true := by rfl

def kid10_part62 : Audit := .split 14 (2,true) (byMove [
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.last 17 (1,true),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.far true 4 ⟨0,[0, 1, 1, 2, 1, 3, 1, 3],[524288, 8388608, 32768, 512, 32, 2048, 17301504, 25690112, 2621440, 32768, 2048, 131072, 16777216, 17301504, 25690112, 2097152, 2048, 8388608, 16777216, 524288, 8388608, 2097152, 2048, 8388608, 16777216],[2048, 16777216, 524288, 524288, 2048, 128, 131072, 16777216, 17432576, 17432576, 131072, 8192, 8388608, 16777216, 8388608, 8388608, 8388608, 524288, 8388608, 16777216, 8388608, 8388608, 8388608, 524288, 16777216],17068224⟩,
.last 15 (1,true),
.cycle 33 1 false (5),
.far true 5 ⟨0,[0, 1, 1, 2, 1, 3, 1, 4, 1, 4],[33554432, 8388608, 32768, 512, 32, 2048, 1107296256, 1652555776, 169869312, 32768, 2048, 131072, 1073741824, 1610612736, 1115684864, 2097152, 2048, 8388608, 1073741824, 1107296256, 536870912, 134217728, 2048, 536870912, 1073741824, 33554432, 536870912, 134217728, 2048, 536870912, 1073741824],[2048, 1073741824, 32768, 33554432, 2048, 128, 131072, 1073741824, 169869312, 1107427328, 131072, 8192, 8388608, 1073741824, 1115684864, 8388608, 8388608, 524288, 536870912, 1073741824, 536870912, 536870912, 536870912, 33554432, 536870912, 1073741824, 536870912, 536870912, 536870912, 33554432, 1073741824],1091334336⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 131072, 32768, 512, 32, 2048, 270336, 401408, 40960, 32768, 2048, 131072, 262144, 8192, 401408, 32768, 2048, 131072, 262144],[2048, 262144, 2048, 8192, 2048, 128, 131072, 262144, 131072, 401408, 131072, 8192, 131072, 262144, 131072, 131072, 131072, 8192, 262144],282816⟩,
.last 27 (1,true),
.cycle 21 1 false (3),
.last 15 (1,true),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 12 3 false (0),
.last 23 (1,true),
.last 15 (1,true),
.last 29 (1,true),
.last 23 (1,true),
.last 23 (1,true),
.last 16 (1,true)
])
theorem kid10_part62_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part62) = true := by rfl

def kid10_part63 : Audit := .cycle 19 1 false (3)
theorem kid10_part63_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part63) = true := by rfl

def kid10_part64 : Audit := .cycle 13 1 false (-1)
theorem kid10_part64_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part64) = true := by rfl

def kid10_part65 : Audit := .cycle 14 1 false (-2)
theorem kid10_part65_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part65) = true := by rfl

def kid10_part66 : Audit := .cycle 13 1 false (-1)
theorem kid10_part66_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part66) = true := by rfl

def kid10_part67 : Audit := .cycle 7 8 true (0)
theorem kid10_part67_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part67) = true := by rfl

def kid10_part68 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 25 1 false (3),
.last 14 (2,true),
.cycle 0 21 true (0),
.cycle 16 1 false (0),
.last 16 (2,true),
.cycle 6 8 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 4, 2, 64],[16, 2, 64, 1, 16, 2, 64],64⟩,
.last 14 (2,true),
.cycle 8 8 true (0),
.cycle 7 8 true (0),
.cycle 1 20 true (0),
.cycle 19 1 false (3),
.last 16 (2,true),
.last 14 (2,true),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 12 2 true (0),
.cycle 0 26 true (0),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 0 22 true (0),
.cycle 1 27 true (0),
.cycle 14 3 true (2)
])
theorem kid10_part68_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part68) = true := by rfl

def kid10_part69 : Audit := .split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 16 (1,true),
.cycle 16 1 false (0),
.cycle 8 10 true (0),
.cycle 6 8 true (0),
.last 14 (1,true),
.cycle 29 1 false (5),
.cycle 8 8 true (0),
.cycle 7 8 true (0),
.cycle 18 16 true (2),
.cycle 19 1 false (3),
.last 14 (1,true),
.cycle 21 1 false (3),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 12 2 true (0),
.cycle 0 26 true (0),
.last 14 (1,true),
.cycle 2 14 true (0),
.cycle 0 22 true (0),
.cycle 2 26 true (0),
.cycle 14 3 true (2)
])
theorem kid10_part69_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part69) = true := by rfl

def kid10_part70 : Audit := .cycle 5 8 true (0)
theorem kid10_part70_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part70) = true := by rfl

def kid10_part71 : Audit := .cycle 7 8 true (0)
theorem kid10_part71_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part71) = true := by rfl

def kid10_part72 : Audit := .cycle 14 3 true (2)
theorem kid10_part72_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part72) = true := by rfl

def kid10_part48 : Audit := .split 12 (5,true) (byMove [(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53),(kid10_part54),(kid10_part55),(kid10_part56),(kid10_part57),(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72)])

theorem kid10_part48_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part48) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part49),(kid10_part50),(kid10_part51),(kid10_part52),(kid10_part53),(kid10_part54),(kid10_part55),(kid10_part56),(kid10_part57),(kid10_part58),(kid10_part59),(kid10_part60),(kid10_part61),(kid10_part62),(kid10_part63),(kid10_part64),(kid10_part65),(kid10_part66),(kid10_part67),(kid10_part68),(kid10_part69),(kid10_part70),(kid10_part71),(kid10_part72)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part49_checked

  · exact kid10_part55_checked

  · exact kid10_part61_checked

  · exact kid10_part67_checked

  · exact kid10_part50_checked

  · exact kid10_part56_checked

  · exact kid10_part62_checked

  · exact kid10_part68_checked

  · exact kid10_part51_checked

  · exact kid10_part57_checked

  · exact kid10_part63_checked

  · exact kid10_part69_checked

  · exact kid10_part52_checked

  · exact kid10_part58_checked

  · exact kid10_part64_checked

  · exact kid10_part70_checked

  · exact kid10_part53_checked

  · exact kid10_part59_checked

  · exact kid10_part65_checked

  · exact kid10_part71_checked

  · exact kid10_part54_checked

  · exact kid10_part60_checked

  · exact kid10_part66_checked

  · exact kid10_part72_checked

def kid10_part73 : Audit := .cycle 0 10 true (0)
theorem kid10_part73_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part73) = true := by rfl

def kid10_part74 : Audit := .cycle 1 9 true (1)
theorem kid10_part74_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part74) = true := by rfl

def kid10_part75 : Audit := .cycle 2 8 true (1)
theorem kid10_part75_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part75) = true := by rfl

def kid10_part76 : Audit := .cycle 8 5 true (3)
theorem kid10_part76_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part76) = true := by rfl

def kid10_part77 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 9 3 true (3),
.split 13 (1,true) (byMove [
.cycle 28 7 false (2),
.cycle 1 14 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 27 7 false (2),
.cycle 23 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.cycle 6 12 true (2),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 25 3 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 6 10 true (2),
.cycle 6 11 true (2)
]),
.split 13 (2,true) (byMove [
.last 26 (1,true),
.last 14 (1,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 26 (1,true),
.last 18 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.last 18 (1,true),
.cycle 9 5 true (2),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 8 10 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 18 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.last 16 (1,true),
.last 17 (1,true)
]),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 0, 16, 64],[16, 64, 64, 1, 16, 16, 64],64⟩,
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 10 2 true (3),
.cycle 9 3 true (3)
])
theorem kid10_part77_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part77) = true := by rfl

def kid10_part78 : Audit := .cycle 9 1 true (3)
theorem kid10_part78_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part78) = true := by rfl

def kid10_part6 : Audit := .split 9 (5,false) (byMove [(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part45),(kid10_part46),(kid10_part47),(kid10_part48),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78)])

theorem kid10_part6_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (kid10_part6) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part7),(kid10_part8),(kid10_part9),(kid10_part10),(kid10_part11),(kid10_part12),(kid10_part13),(kid10_part14),(kid10_part15),(kid10_part16),(kid10_part17),(kid10_part18),(kid10_part19),(kid10_part20),(kid10_part45),(kid10_part46),(kid10_part47),(kid10_part48),(kid10_part73),(kid10_part74),(kid10_part75),(kid10_part76),(kid10_part77),(kid10_part78)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part7_checked

  · exact kid10_part13_checked

  · exact kid10_part19_checked

  · exact kid10_part73_checked

  · exact kid10_part8_checked

  · exact kid10_part14_checked

  · exact kid10_part20_checked

  · exact kid10_part74_checked

  · exact kid10_part9_checked

  · exact kid10_part15_checked

  · exact kid10_part45_checked

  · exact kid10_part75_checked

  · exact kid10_part10_checked

  · exact kid10_part16_checked

  · exact kid10_part46_checked

  · exact kid10_part76_checked

  · exact kid10_part11_checked

  · exact kid10_part17_checked

  · exact kid10_part47_checked

  · exact kid10_part77_checked

  · exact kid10_part12_checked

  · exact kid10_part18_checked

  · exact kid10_part48_checked

  · exact kid10_part78_checked

def kid10_part79 : Audit := .cycle 0 9 true (0)
theorem kid10_part79_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,0⟩)) (kid10_part79) = true := by rfl

def kid10_part80 : Audit := .cycle 1 8 true (1)
theorem kid10_part80_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,1⟩)) (kid10_part80) = true := by rfl

def kid10_part81 : Audit := .cycle 25 1 false (9)
theorem kid10_part81_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,2⟩)) (kid10_part81) = true := by rfl

def kid10_part82 : Audit := .cycle 21 1 false (7)
theorem kid10_part82_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,3⟩)) (kid10_part82) = true := by rfl

def kid10_part83 : Audit := .cycle 8 1 true (4)
theorem kid10_part83_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,4⟩)) (kid10_part83) = true := by rfl

def kid10_part85 : Audit := .cycle 0 10 true (0)
theorem kid10_part85_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part85) = true := by rfl

def kid10_part86 : Audit := .cycle 1 9 true (1)
theorem kid10_part86_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part86) = true := by rfl

def kid10_part87 : Audit := .cycle 25 1 false (7)
theorem kid10_part87_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part87) = true := by rfl

def kid10_part88 : Audit := .cycle 21 1 false (5)
theorem kid10_part88_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part88) = true := by rfl

def kid10_part89 : Audit := .cycle 8 2 true (4)
theorem kid10_part89_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part89) = true := by rfl

def kid10_part90 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (5),
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 23 1 false (5),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.split 16 (1,true) (byMove [
.cycle 19 1 false (1),
.cycle 26 1 false (2),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 19 1 false (1),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 9 17 false (5),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 11 7 false (3),
.cycle 12 5 false (2),
.cycle 20 1 false (2),
.last 19 (2,true),
.last 17 (2,true),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 14 3 false (0),
.cycle 10 25 false (6),
.cycle 34 1 false (2),
.cycle 2 15 false (5),
.cycle 10 11 false (4),
.cycle 24 1 false (2),
.cycle 22 1 false (2)
]),
.split 16 (2,true) (byMove [
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 19 1 false (1),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 9 17 false (5),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 11 7 false (3),
.cycle 12 5 false (2),
.cycle 20 1 false (2),
.last 17 (1,true),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 14 3 false (0),
.last 32 (1,true),
.last 31 (1,true),
.cycle 2 15 false (5),
.cycle 10 11 false (4),
.last 21 (1,true),
.last 19 (1,true)
]),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 22 1 false (4),
.cycle 19 1 false (3),
.cycle 12 4 true (0),
.cycle 13 2 true (0)
])
theorem kid10_part90_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part90) = true := by rfl

def kid10_part91 : Audit := .cycle 0 10 true (0)
theorem kid10_part91_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part91) = true := by rfl

def kid10_part92 : Audit := .cycle 1 9 true (1)
theorem kid10_part92_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part92) = true := by rfl

def kid10_part93 : Audit := .cycle 29 1 false (11)
theorem kid10_part93_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part93) = true := by rfl

def kid10_part94 : Audit := .cycle 25 1 false (9)
theorem kid10_part94_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part94) = true := by rfl

def kid10_part95 : Audit := .cycle 8 2 true (4)
theorem kid10_part95_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part95) = true := by rfl

def kid10_part96 : Audit := .cycle 9 1 true (5)
theorem kid10_part96_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part96) = true := by rfl

def kid10_part97 : Audit := .split 11 (1,true) (byMove [
.cycle 8 5 true (4),
.cycle 1 12 true (1),
.split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 29 5 false (2),
.cycle 21 4 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 26 3 false (3),
.cycle 34 1 false (4),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 14 (5,true),
.last 22 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (4),
.cycle 8 5 true (4),
.cycle 6 8 true (2)
]),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 29 5 false (2),
.cycle 21 4 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 26 3 false (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 12 2 true (3),
.cycle 22 4 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (4),
.cycle 8 5 true (4),
.cycle 6 8 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4),
.cycle 6 6 true (2),
.split 14 (2,true) (byMove [
.last 17 (5,true),
.cycle 22 3 false (0),
.last 25 (5,true),
.cycle 10 6 true (3),
.last 17 (5,true),
.last 15 (5,true),
.cycle 8 8 true (3),
.cycle 1 17 true (1),
.cycle 7 18 true (3),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 7 10 true (3),
.cycle 22 3 false (0),
.cycle 5 12 true (1),
.cycle 5 10 true (1),
.cycle 7 10 true (3),
.last 15 (5,true),
.cycle 8 8 true (3),
.cycle 26 5 false (2),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (3),
.last 15 (5,true)
]),
.split 12 (2,true) (byMove [
.cycle 8 9 true (3),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.last 21 (5,true),
.last 30 (5,true),
.last 21 (5,true),
.cycle 8 6 true (4),
.cycle 0 16 true (0),
.cycle 37 1 false (11),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 30 3 false (7),
.cycle 5 12 true (1),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.last 14 (5,true),
.cycle 25 4 false (7),
.cycle 8 6 true (4),
.cycle 11 2 true (4),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
]),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 22 1 false (4),
.cycle 30 5 false (2),
.cycle 21 4 false (3),
.cycle 8 6 true (4),
.cycle 37 5 false (7),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 9 5 true (4),
.cycle 30 3 false (7),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.cycle 12 2 true (3),
.cycle 25 4 false (7),
.cycle 8 6 true (4),
.cycle 11 2 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 6 9 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 6 7 true (2)
])
theorem kid10_part97_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part97) = true := by rfl

def kid10_part98 : Audit := .split 11 (2,true) (byMove [
.cycle 8 5 true (4),
.split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 29 5 false (2),
.cycle 18 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 6 9 true (2),
.cycle 22 3 false (0),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 14 (5,true),
.cycle 18 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (4),
.cycle 8 5 true (4),
.last 15 (5,true)
]),
.cycle 29 1 false (5),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 29 5 false (2),
.last 18 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.last 14 (1,true),
.last 22 (1,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 12 2 true (3),
.last 18 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (4),
.cycle 8 5 true (4),
.last 14 (1,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 9 3 true (4),
.cycle 6 6 true (2),
.split 12 (1,true) (byMove [
.last 19 (5,true),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.last 21 (5,true),
.last 30 (5,true),
.cycle 18 4 false (0),
.cycle 8 6 true (4),
.cycle 1 13 true (1),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 7 10 true (3),
.cycle 22 3 false (0),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.last 14 (5,true),
.cycle 18 4 false (0),
.cycle 8 6 true (4),
.cycle 1 13 true (1),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
]),
.cycle 8 8 true (3),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.split 12 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 22 1 false (4),
.cycle 30 5 false (2),
.last 18 (1,true),
.cycle 8 6 true (4),
.last 13 (1,true),
.last 30 (1,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 9 5 true (4),
.last 14 (1,true),
.last 22 (1,true),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.cycle 12 2 true (3),
.last 18 (1,true),
.cycle 8 6 true (4),
.last 13 (1,true),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 15 (1,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.split 13 (1,true) (byMove [
.last 16 (5,true),
.cycle 7 15 true (3),
.cycle 39 1 false (7),
.cycle 0 18 true (0),
.last 16 (5,true),
.last 14 (5,true),
.cycle 8 7 true (4),
.cycle 1 14 true (1),
.cycle 11 3 true (5),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 9 true (3),
.last 17 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 7 9 true (3),
.last 14 (5,true),
.cycle 8 7 true (4),
.cycle 1 14 true (1),
.cycle 11 3 true (5),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
])
])
theorem kid10_part98_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part98) = true := by rfl

def kid10_part99 : Audit := .cycle 0 12 true (0)
theorem kid10_part99_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part99) = true := by rfl

def kid10_part100 : Audit := .cycle 22 1 false (6)
theorem kid10_part100_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part100) = true := by rfl

def kid10_part101 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.cycle 25 3 false (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 9 3 true (4),
.split 13 (1,true) (byMove [
.cycle 8 7 true (4),
.cycle 1 14 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 29 3 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 33 3 false (7),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (4),
.cycle 8 6 true (4),
.cycle 7 9 true (3)
]),
.split 13 (2,true) (byMove [
.cycle 8 7 true (4),
.last 14 (1,true),
.cycle 33 1 false (5),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 24 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 8 10 true (3),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 24 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (4),
.cycle 8 6 true (4),
.cycle 7 9 true (3)
]),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.cycle 10 2 true (4),
.cycle 29 3 false (7),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 7 7 true (3)
])
theorem kid10_part101_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part101) = true := by rfl

def kid10_part103 : Audit := .split 17 (2,true) (byMove [
.cycle 20 15 true (1),
.last 18 (1,true),
.cycle 21 1 false (-1),
.last 20 (1,true),
.cycle 20 15 true (1),
.cycle 21 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 53, 64],[16, 64, 1, 1, 16, 36, 64],64⟩,
.last 18 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[16, 64, 4, 1, 16, 36, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 61, 64],[16, 64, 8, 1, 16, 36, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 16, 1, 16, 36, 64],64⟩,
.cycle 22 9 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 16, 128, 256, 8, 16, 32, 272, 4096],[16, 4096, 4096, 1, 16, 256, 16, 4096, 16, 1, 16, 32, 4096],4096⟩,
.last 18 (1,true),
.cycle 29 1 false (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 16, 1, 16, 36, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 52, 1, 16, 36, 64],64⟩,
.cycle 0 50 true (-1),
.cycle 14 18 true (-1),
.last 18 (1,true),
.cycle 18 22 true (2),
.cycle 14 18 true (-1),
.cycle 14 18 true (-1),
.cycle 18 13 true (1)
])
theorem kid10_part103_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part103) = true := by rfl

def kid10_part104 : Audit := .far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 3, 2, 2],[33554432, 8388608, 2097152, 512, 8388608, 2048, 1073741824, 1073741824, 33554432, 2097152, 8388608, 8388608, 1107304448, 1115824128, 1117954048, 32768, 1115824128, 131072, 1073741824, 1073741824, 8388608, 2097152, 1115824128, 8388608, 1073741824, 33554432, 2097152, 32768, 8388608, 131072, 1073741824],[8388608, 1073741824, 1073741824, 33554432, 8388608, 2, 8388608, 1073741824, 1073741824, 8388608, 8388608, 8192, 1115824128, 1073741824, 1073741824, 1115824128, 1115824128, 8192, 8388608, 1073741824, 1073741824, 8388608, 8388608, 33554432, 1115824128, 1073741824, 1073741824, 1073741824, 1115824128, 8192, 1073741824],1095594176⟩
theorem kid10_part104_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part104) = true := by rfl

def kid10_part105 : Audit := .cycle 16 1 false (0)
theorem kid10_part105_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part105) = true := by rfl

def kid10_part106 : Audit := .cycle 15 1 false (-1)
theorem kid10_part106_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part106) = true := by rfl

def kid10_part107 : Audit := .cycle 16 1 false (0)
theorem kid10_part107_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part107) = true := by rfl

def kid10_part108 : Audit := .cycle 15 1 false (-1)
theorem kid10_part108_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part108) = true := by rfl

def kid10_part109 : Audit := .cycle 21 1 false (7)
theorem kid10_part109_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part109) = true := by rfl

def kid10_part110 : Audit := .split 15 (1,true) (byMove [
.last 18 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 17, 128, 256, 8, 16, 32, 8, 4096],[16, 8, 4096, 1, 16, 2, 16, 441, 4096, 1, 16, 2, 4096],4096⟩,
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 21 1 false (7),
.cycle 28 1 false (10),
.last 16 (2,true),
.cycle 21 1 false (7),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 25 1 false (7),
.last 17 (2,true),
.cycle 23 1 false (7),
.cycle 16 1 false (0),
.cycle 38 1 false (10),
.cycle 16 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 1, 64, 1, 16, 2, 64],64⟩,
.cycle 1 19 true (0),
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 8, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 18 3 true (4)
])
theorem kid10_part110_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part110) = true := by rfl

def kid10_part111 : Audit := .split 15 (2,true) (byMove [
.cycle 0 85 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 17, 128, 256, 8, 16, 32, 8, 4096],[16, 4096, 8, 1, 16, 4, 16, 4096, 4096, 1, 16, 4, 4096],4096⟩,
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 21 1 false (7),
.last 16 (1,true),
.cycle 21 1 false (7),
.cycle 21 1 false (7),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.last 17 (1,true),
.last 18 (1,true),
.cycle 23 1 false (7),
.cycle 16 1 false (0),
.cycle 31 1 false (7),
.cycle 16 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 1, 1, 16, 4, 64],64⟩,
.last 16 (1,true),
.cycle 2 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 64, 8, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 18 3 true (4)
])
theorem kid10_part111_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part111) = true := by rfl

def kid10_part112 : Audit := .cycle 21 1 false (7)
theorem kid10_part112_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part112) = true := by rfl

def kid10_part113 : Audit := .cycle 21 1 false (7)
theorem kid10_part113_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part113) = true := by rfl

def kid10_part114 : Audit := .cycle 20 1 false (6)
theorem kid10_part114_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part114) = true := by rfl

def kid10_part115 : Audit := .split 16 (1,true) (byMove [
.cycle 44 1 false (6),
.cycle 31 1 false (7),
.last 17 (2,true),
.cycle 0 33 true (-1),
.cycle 44 1 false (6),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 1, 64, 1, 16, 17, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 18, 64],[16, 2, 64, 1, 16, 18, 64],64⟩,
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 8, 64, 1, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 80 1 false (12),
.cycle 25 1 false (7),
.last 19 (2,true),
.last 17 (2,true),
.cycle 25 1 false (7),
.cycle 25 1 false (7),
.cycle 14 3 false (0),
.cycle 41 1 false (9),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 18, 64],[16, 2, 64, 1, 16, 18, 64],64⟩,
.last 17 (2,true),
.cycle 41 1 false (9),
.cycle 41 1 false (9),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[16, 32, 64, 1, 16, 48, 64],64⟩
])
theorem kid10_part115_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part115) = true := by rfl

def kid10_part116 : Audit := .split 16 (2,true) (byMove [
.cycle 44 1 false (6),
.last 17 (1,true),
.cycle 19 1 false (-1),
.last 19 (1,true),
.cycle 44 1 false (6),
.cycle 14 3 false (0),
.far false 4 ⟨0,[0, 1, 1, 2, 2, 3, 3, 3],[128, 256, 8, 0, 32, 0, 8192, 16384, 512, 16, 2048, 1024, 524288, 1048576, 32768, 1024, 131072, 16842752, 524288, 1048576, 2097152, 4259840, 8388608, 20971520, 16777216],[16, 16777216, 1, 1, 16, 64, 1024, 16777216, 64, 64, 1024, 16781312, 65536, 16777216, 4096, 4096, 65536, 17039360, 4194304, 16777216, 262144, 262144, 4194304, 17039360, 16777216],33501248⟩,
.last 17 (1,true),
.cycle 41 1 false (9),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 2, 4, 2, 1],[33554432, 8388608, 2097152, 512, 8388608, 2048, 1073741824, 8388736, 33556480, 2097152, 8388736, 8388608, 1107828864, 1653221504, 1789569664, 32768, 1653221504, 131072, 1073741824, 1074266112, 8388608, 134217728, 1074266112, 536870912, 1073741824, 33554432, 536870912, 512, 33554432, 2048, 1073741824],[536870912, 1073741824, 2097152, 33554432, 536870912, 128, 2048, 1073741824, 33556480, 2048, 2048, 524288, 1653221504, 1073741824, 1789569664, 1653221504, 1653221504, 8192, 8388608, 1073741824, 8388608, 8388608, 8388608, 33554432, 536870912, 1073741824, 536870912, 536870912, 536870912, 128, 1073741824],1095594048⟩,
.far false 4 ⟨0,[0, 1, 1, 2, 2, 3, 3, 3],[128, 256, 8, 0, 32, 0, 8192, 16384, 512, 16, 2048, 1024, 524288, 1048576, 32768, 1024, 131072, 16842752, 524288, 1048576, 2097152, 4259840, 8388608, 20971520, 16777216],[16, 16777216, 16, 1, 16, 1024, 1024, 16777216, 1024, 64, 1024, 16842752, 65536, 16777216, 65536, 4096, 65536, 20971520, 4194304, 16777216, 4194304, 262144, 4194304, 20971520, 16777216],33501248⟩,
.last 35 (1,true),
.cycle 25 1 false (7),
.last 17 (1,true),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.cycle 25 1 false (7),
.cycle 14 3 false (0),
.last 31 (1,true),
.last 17 (1,true),
.last 35 (1,true),
.last 31 (1,true),
.last 31 (1,true),
.last 18 (1,true)
])
theorem kid10_part116_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part116) = true := by rfl

def kid10_part117 : Audit := .cycle 23 1 false (7)
theorem kid10_part117_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part117) = true := by rfl

def kid10_part118 : Audit := .cycle 15 1 false (-1)
theorem kid10_part118_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part118) = true := by rfl

def kid10_part119 : Audit := .cycle 14 2 true (-1)
theorem kid10_part119_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part119) = true := by rfl

def kid10_part120 : Audit := .cycle 15 1 false (-1)
theorem kid10_part120_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part120) = true := by rfl

def kid10_part121 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 64, 1, 16, 1, 64],64⟩
theorem kid10_part121_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part121) = true := by rfl

def kid10_part122 : Audit := .split 15 (1,true) (byMove [
.cycle 26 1 false (6),
.cycle 29 1 false (7),
.last 16 (2,true),
.cycle 0 29 true (0),
.cycle 26 1 false (6),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 1, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 2, 64],[16, 2, 64, 1, 16, 2, 64],64⟩,
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 8, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 1 24 true (0),
.cycle 23 1 false (7),
.last 18 (2,true),
.last 16 (2,true),
.cycle 23 1 false (7),
.cycle 23 1 false (7),
.cycle 14 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 1, 64, 1, 16, 2, 64],64⟩,
.cycle 1 19 true (0),
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 8, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 18 3 true (4)
])
theorem kid10_part122_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part122) = true := by rfl

def kid10_part123 : Audit := .split 15 (2,true) (byMove [
.cycle 26 1 false (6),
.last 16 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.cycle 26 1 false (6),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 32, 17, 128, 256, 8, 16, 32, 8, 4096],[16, 4096, 176, 1, 16, 256, 16, 4096, 8, 1, 16, 256, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 1, 1, 16, 4, 64],64⟩,
.last 16 (1,true),
.cycle 37 1 false (9),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 64, 8, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 22 20 true (4),
.cycle 23 1 false (7),
.last 16 (1,true),
.cycle 25 1 false (7),
.cycle 23 1 false (7),
.cycle 23 1 false (7),
.cycle 14 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 1, 1, 16, 4, 64],64⟩,
.last 16 (1,true),
.cycle 2 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 64, 8, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 18 3 true (4)
])
theorem kid10_part123_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part123) = true := by rfl

def kid10_part124 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 64, 1, 16, 8, 64],64⟩
theorem kid10_part124_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part124) = true := by rfl

def kid10_part125 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 64, 1, 16, 16, 64],64⟩
theorem kid10_part125_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part125) = true := by rfl

def kid10_part126 : Audit := .cycle 18 3 true (4)
theorem kid10_part126_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part126) = true := by rfl

def kid10_part102 : Audit := .split 14 (5,true) (byMove [(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116),(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126)])

theorem kid10_part102_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part102) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 14 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part103),(kid10_part104),(kid10_part105),(kid10_part106),(kid10_part107),(kid10_part108),(kid10_part109),(kid10_part110),(kid10_part111),(kid10_part112),(kid10_part113),(kid10_part114),(kid10_part115),(kid10_part116),(kid10_part117),(kid10_part118),(kid10_part119),(kid10_part120),(kid10_part121),(kid10_part122),(kid10_part123),(kid10_part124),(kid10_part125),(kid10_part126)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part103_checked

  · exact kid10_part109_checked

  · exact kid10_part115_checked

  · exact kid10_part121_checked

  · exact kid10_part104_checked

  · exact kid10_part110_checked

  · exact kid10_part116_checked

  · exact kid10_part122_checked

  · exact kid10_part105_checked

  · exact kid10_part111_checked

  · exact kid10_part117_checked

  · exact kid10_part123_checked

  · exact kid10_part106_checked

  · exact kid10_part112_checked

  · exact kid10_part118_checked

  · exact kid10_part124_checked

  · exact kid10_part107_checked

  · exact kid10_part113_checked

  · exact kid10_part119_checked

  · exact kid10_part125_checked

  · exact kid10_part108_checked

  · exact kid10_part114_checked

  · exact kid10_part120_checked

  · exact kid10_part126_checked

def kid10_part127 : Audit := .cycle 0 10 true (0)
theorem kid10_part127_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part127) = true := by rfl

def kid10_part128 : Audit := .cycle 1 9 true (1)
theorem kid10_part128_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part128) = true := by rfl

def kid10_part129 : Audit := .cycle 2 8 true (1)
theorem kid10_part129_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part129) = true := by rfl

def kid10_part130 : Audit := .cycle 8 5 true (4)
theorem kid10_part130_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part130) = true := by rfl

def kid10_part131 : Audit := .cycle 8 2 true (4)
theorem kid10_part131_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part131) = true := by rfl

def kid10_part132 : Audit := .cycle 9 1 true (5)
theorem kid10_part132_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part132) = true := by rfl

def kid10_part84 : Audit := .split 9 (5,false) (byMove [(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132)])

theorem kid10_part84_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (kid10_part84) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part85),(kid10_part86),(kid10_part87),(kid10_part88),(kid10_part89),(kid10_part90),(kid10_part91),(kid10_part92),(kid10_part93),(kid10_part94),(kid10_part95),(kid10_part96),(kid10_part97),(kid10_part98),(kid10_part99),(kid10_part100),(kid10_part101),(kid10_part102),(kid10_part127),(kid10_part128),(kid10_part129),(kid10_part130),(kid10_part131),(kid10_part132)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part85_checked

  · exact kid10_part91_checked

  · exact kid10_part97_checked

  · exact kid10_part127_checked

  · exact kid10_part86_checked

  · exact kid10_part92_checked

  · exact kid10_part98_checked

  · exact kid10_part128_checked

  · exact kid10_part87_checked

  · exact kid10_part93_checked

  · exact kid10_part99_checked

  · exact kid10_part129_checked

  · exact kid10_part88_checked

  · exact kid10_part94_checked

  · exact kid10_part100_checked

  · exact kid10_part130_checked

  · exact kid10_part89_checked

  · exact kid10_part95_checked

  · exact kid10_part101_checked

  · exact kid10_part131_checked

  · exact kid10_part90_checked

  · exact kid10_part96_checked

  · exact kid10_part102_checked

  · exact kid10_part132_checked

def kid10_part134 : Audit := .cycle 8 4 true (3)
theorem kid10_part134_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part134) = true := by rfl

def kid10_part135 : Audit := .cycle 1 11 true (1)
theorem kid10_part135_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part135) = true := by rfl

def kid10_part136 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 22 (5,true),
.cycle 12 1 true (2),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 5 false (3),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 6 8 true (2),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 26 5 false (2),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (3),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 29 5 false (5),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
]),
.cycle 21 3 false (2),
.cycle 30 1 false (2),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.last 14 (5,true),
.cycle 8 6 true (2),
.cycle 29 1 false (3),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.cycle 18 5 false (4),
.last 14 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 18 (5,true),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 6 7 true (2),
.split 12 (5,false) (byMove [
.cycle 8 6 true (3),
.cycle 29 1 false (3),
.cycle 11 2 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.cycle 30 1 false (4),
.last 14 (5,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
])
theorem kid10_part136_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part136) = true := by rfl

def kid10_part137 : Audit := .cycle 0 12 true (0)
theorem kid10_part137_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part137) = true := by rfl

def kid10_part138 : Audit := .cycle 7 4 true (3)
theorem kid10_part138_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part138) = true := by rfl

def kid10_part139 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 22 5 false (0),
.cycle 12 1 true (2),
.cycle 16 4 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 5 false (3),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 6 8 true (2),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 26 5 false (2),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 9 4 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 29 5 false (5),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
]),
.cycle 21 3 false (2),
.split 13 (2,true) (byMove [
.last 27 (5,false),
.last 15 (5,false),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 27 (5,false),
.last 19 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.last 19 (5,false),
.last 14 (5,false),
.cycle 6 8 true (2),
.last 15 (5,false),
.cycle 8 10 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 19 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 6 9 true (2),
.last 14 (5,false)
]),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.cycle 15 1 false (-1),
.cycle 8 6 true (2),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.cycle 16 4 false (0),
.last 14 (2,true),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.cycle 18 5 false (4),
.cycle 15 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 18, 1, 64],[16, 18, 64, 1, 16, 16, 64],64⟩,
.cycle 18 3 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 17 3 false (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 6 7 true (2),
.split 12 (5,false) (byMove [
.cycle 8 6 true (3),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 16 (2,true),
.last 13 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 12 1 true (4)
])
])
theorem kid10_part139_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part139) = true := by rfl

def kid10_part140 : Audit := .cycle 0 11 true (0)
theorem kid10_part140_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part140) = true := by rfl

def kid10_part141 : Audit := .cycle 1 10 true (1)
theorem kid10_part141_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part141) = true := by rfl

def kid10_part142 : Audit := .cycle 7 11 true (3)
theorem kid10_part142_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part142) = true := by rfl

def kid10_part143 : Audit := .cycle 3 8 true (1)
theorem kid10_part143_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part143) = true := by rfl

def kid10_part144 : Audit := .cycle 8 3 true (3)
theorem kid10_part144_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part144) = true := by rfl

def kid10_part145 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 29 1 false (3),
.cycle 25 1 false (1),
.cycle 21 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 8 6 true (3),
.cycle 19 1 false (1),
.cycle 27 5 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 7 14 true (1),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 6 9 true (2),
.cycle 12 2 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 14 true (3),
.cycle 7 11 true (3),
.cycle 8 4 true (3),
.cycle 11 1 true (5),
.cycle 9 3 true (3),
.split 13 (2,true) (byMove [
.cycle 8 7 true (3),
.cycle 10 4 true (4),
.cycle 33 1 false (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (4),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 5 12 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 6 9 true (2),
.last 16 (5,true)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.cycle 7 8 true (3),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 8 10 true (2),
.cycle 31 1 false (5),
.cycle 39 1 false (3),
.cycle 49 6 false (6),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 29 1 false (7),
.cycle 7 21 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 28 1 false (4),
.cycle 7 16 true (1),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 14 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 6 7 true (2),
.cycle 11 1 true (5)
])
theorem kid10_part145_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part145) = true := by rfl

def kid10_part146 : Audit := .cycle 6 5 true (2)
theorem kid10_part146_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part146) = true := by rfl

def kid10_part147 : Audit := .split 13 (2,true) (byMove [
.cycle 25 7 false (1),
.cycle 18 3 false (0),
.cycle 29 1 false (1),
.cycle 9 6 true (2),
.cycle 25 7 false (1),
.split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 7 15 true (1),
.cycle 29 1 false (1),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.last 15 (5,false),
.cycle 9 6 true (2),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 7 false (1),
.last 15 (5,false),
.cycle 17 6 false (1),
.cycle 19 3 false (0),
.cycle 9 8 true (1),
.cycle 26 1 false (0),
.cycle 19 7 false (3),
.last 15 (5,false),
.cycle 24 7 false (2),
.cycle 1 17 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 7 11 true (2),
.last 15 (5,false)
]),
.cycle 8 7 true (2),
.cycle 1 16 true (1),
.cycle 7 17 true (2),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 10 true (2),
.cycle 6 10 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 7 17 true (2),
.cycle 7 14 true (2),
.cycle 8 7 true (2),
.last 15 (5,false),
.cycle 24 7 false (2),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 7 11 true (2),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 10 true (2),
.cycle 6 10 true (2),
.last 15 (5,false)
]),
.cycle 7 9 true (2),
.cycle 18 3 false (0),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.split 14 (5,true) (byMove [
.cycle 23 12 false (1),
.cycle 8 11 true (1),
.cycle 31 1 false (3),
.cycle 25 1 false (-1),
.cycle 18 7 false (2),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 16 (5,false),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.last 17 (5,false),
.cycle 17 6 false (1),
.cycle 19 3 false (0),
.cycle 5 11 true (1),
.cycle 28 1 false (2),
.cycle 21 7 false (5),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 21 5 false (1),
.cycle 13 2 true (2),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.last 17 (5,false)
]),
.cycle 7 18 true (1),
.cycle 20 5 false (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 7 18 true (1),
.split 14 (5,true) (byMove [
.cycle 28 9 false (2),
.cycle 21 5 false (1),
.last 16 (5,false),
.cycle 0 16 true (0),
.cycle 28 9 false (2),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 7 15 true (2),
.cycle 3 12 true (1),
.cycle 7 18 true (1),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 21 5 false (1),
.cycle 13 2 true (3),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 10 true (2),
.cycle 6 10 true (2),
.last 15 (5,false)
])
])
theorem kid10_part147_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part147) = true := by rfl

def kid10_part148 : Audit := .split 11 (2,true) (byMove [
.cycle 32 13 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.last 14 (5,true),
.cycle 9 4 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 22 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 9 6 true (1),
.cycle 22 1 false (0),
.cycle 17 5 false (3),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 7 9 true (2),
.last 14 (5,true)
]),
.cycle 8 5 true (3),
.cycle 0 15 true (0),
.cycle 33 1 false (9),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 26 5 false (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 9 4 true (3),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 29 5 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.last 13 (5,false)
]),
.cycle 24 3 false (5),
.cycle 5 11 true (1),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.split 12 (5,false) (byMove [
.last 16 (5,true),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 8 9 true (2),
.cycle 11 2 true (2),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.cycle 19 5 false (5),
.last 14 (5,true),
.cycle 6 7 true (2),
.last 18 (5,true),
.last 14 (5,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true)
]),
.cycle 8 5 true (3),
.cycle 10 2 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 8 9 true (2),
.cycle 11 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.last 13 (5,false)
])
])
theorem kid10_part148_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part148) = true := by rfl

def kid10_part149 : Audit := .cycle 8 5 true (3)
theorem kid10_part149_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part149) = true := by rfl

def kid10_part150 : Audit := .cycle 7 5 true (3)
theorem kid10_part150_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part150) = true := by rfl

def kid10_part152 : Audit := .split 14 (2,true) (byMove [
.cycle 33 13 false (2),
.cycle 25 5 false (1),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.cycle 34 13 false (2),
.cycle 29 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 7 15 true (2),
.cycle 3 12 true (1),
.cycle 7 26 true (1),
.last 15 (5,false),
.cycle 6 9 true (2),
.cycle 25 5 false (1),
.cycle 5 13 true (1),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.cycle 29 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 10 true (2),
.cycle 6 10 true (2),
.last 15 (5,false)
])
theorem kid10_part152_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part152) = true := by rfl

def kid10_part153 : Audit := .cycle 0 15 true (0)
theorem kid10_part153_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part153) = true := by rfl

def kid10_part154 : Audit := .cycle 26 1 false (4)
theorem kid10_part154_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part154) = true := by rfl

def kid10_part155 : Audit := .cycle 21 1 false (1)
theorem kid10_part155_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part155) = true := by rfl

def kid10_part156 : Audit := .cycle 17 4 false (1)
theorem kid10_part156_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part156) = true := by rfl

def kid10_part157 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.cycle 15 1 false (-1),
.cycle 9 4 true (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 22 5 false (0),
.cycle 15 1 true (3),
.cycle 16 4 false (0),
.last 14 (2,true),
.cycle 9 6 true (1),
.cycle 22 1 false (0),
.cycle 17 5 false (3),
.cycle 15 1 false (-1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 7 9 true (2),
.cycle 17 1 true (1)
])
theorem kid10_part157_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part157) = true := by rfl

def kid10_part158 : Audit := .cycle 8 5 true (3)
theorem kid10_part158_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part158) = true := by rfl

def kid10_part159 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.cycle 21 6 false (1),
.cycle 30 1 false (4),
.cycle 8 7 true (3),
.cycle 12 2 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 30 5 false (5),
.last 15 (2,true),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.cycle 25 6 false (5),
.cycle 18 1 false (0),
.cycle 8 7 true (3),
.cycle 10 4 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 1 14 true (1)
])
theorem kid10_part159_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part159) = true := by rfl

def kid10_part160 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 26 5 false (2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 9 4 true (3),
.last 16 (5,false),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 29 5 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.last 13 (5,false)
])
theorem kid10_part160_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part160) = true := by rfl

def kid10_part161 : Audit := .cycle 0 13 true (0)
theorem kid10_part161_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part161) = true := by rfl

def kid10_part162 : Audit := .cycle 7 5 true (3)
theorem kid10_part162_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part162) = true := by rfl

def kid10_part163 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 8 6 true (3),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (11),
.cycle 33 1 false (9),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 9 5 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 11 7 true (3),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part163_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part163) = true := by rfl

def kid10_part164 : Audit := .cycle 24 3 false (5)
theorem kid10_part164_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part164) = true := by rfl

def kid10_part165 : Audit := .split 13 (2,true) (byMove [
.last 27 (5,false),
.last 15 (5,false),
.cycle 29 1 false (1),
.cycle 9 6 true (2),
.last 27 (5,false),
.last 19 (5,false),
.cycle 8 7 true (2),
.last 15 (5,false),
.cycle 7 17 true (2),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 17 (5,false),
.cycle 7 9 true (2),
.last 15 (5,false),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.last 19 (5,false),
.cycle 7 18 true (1),
.last 17 (5,false),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 7 18 true (1),
.last 23 (5,false)
])
theorem kid10_part165_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part165) = true := by rfl

def kid10_part166 : Audit := .cycle 8 7 true (2)
theorem kid10_part166_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part166) = true := by rfl

def kid10_part167 : Audit := .cycle 23 1 false (3)
theorem kid10_part167_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part167) = true := by rfl

def kid10_part168 : Audit := .cycle 21 4 false (5)
theorem kid10_part168_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part168) = true := by rfl

def kid10_part169 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 16 5 false (2),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 12 2 true (2),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 11 2 true (2),
.cycle 16 4 false (0),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.cycle 19 5 false (5),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.cycle 18 3 false (0),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 17 3 false (1)
])
theorem kid10_part169_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part169) = true := by rfl

def kid10_part170 : Audit := .cycle 8 5 true (3)
theorem kid10_part170_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part170) = true := by rfl

def kid10_part171 : Audit := .cycle 10 2 true (3)
theorem kid10_part171_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part171) = true := by rfl

def kid10_part172 : Audit := .split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.last 14 (5,false),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.last 14 (5,false),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.last 13 (5,false)
])
theorem kid10_part172_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part172) = true := by rfl

def kid10_part173 : Audit := .cycle 0 13 true (0)
theorem kid10_part173_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part173) = true := by rfl

def kid10_part174 : Audit := .cycle 7 5 true (3)
theorem kid10_part174_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part174) = true := by rfl

def kid10_part175 : Audit := .split 13 (5,false) (byMove [
.cycle 8 7 true (3),
.cycle 10 4 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.cycle 11 5 true (3),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 6 9 true (2),
.cycle 13 1 true (5)
])
theorem kid10_part175_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part175) = true := by rfl

def kid10_part151 : Audit := .split 11 (5,true) (byMove [(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165),(kid10_part166),(kid10_part167),(kid10_part168),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part174),(kid10_part175)])

theorem kid10_part151_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part151) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part152),(kid10_part153),(kid10_part154),(kid10_part155),(kid10_part156),(kid10_part157),(kid10_part158),(kid10_part159),(kid10_part160),(kid10_part161),(kid10_part162),(kid10_part163),(kid10_part164),(kid10_part165),(kid10_part166),(kid10_part167),(kid10_part168),(kid10_part169),(kid10_part170),(kid10_part171),(kid10_part172),(kid10_part173),(kid10_part174),(kid10_part175)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part152_checked

  · exact kid10_part158_checked

  · exact kid10_part164_checked

  · exact kid10_part170_checked

  · exact kid10_part153_checked

  · exact kid10_part159_checked

  · exact kid10_part165_checked

  · exact kid10_part171_checked

  · exact kid10_part154_checked

  · exact kid10_part160_checked

  · exact kid10_part166_checked

  · exact kid10_part172_checked

  · exact kid10_part155_checked

  · exact kid10_part161_checked

  · exact kid10_part167_checked

  · exact kid10_part173_checked

  · exact kid10_part156_checked

  · exact kid10_part162_checked

  · exact kid10_part168_checked

  · exact kid10_part174_checked

  · exact kid10_part157_checked

  · exact kid10_part163_checked

  · exact kid10_part169_checked

  · exact kid10_part175_checked

def kid10_part176 : Audit := .cycle 0 11 true (0)
theorem kid10_part176_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part176) = true := by rfl

def kid10_part177 : Audit := .cycle 1 10 true (1)
theorem kid10_part177_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part177) = true := by rfl

def kid10_part178 : Audit := .cycle 2 9 true (1)
theorem kid10_part178_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part178) = true := by rfl

def kid10_part179 : Audit := .cycle 8 6 true (3)
theorem kid10_part179_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part179) = true := by rfl

def kid10_part180 : Audit := .cycle 6 6 true (2)
theorem kid10_part180_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part180) = true := by rfl

def kid10_part181 : Audit := .split 11 (5,false) (byMove [
.cycle 8 5 true (3),
.cycle 10 2 true (4),
.split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 15 true (1),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 11 2 true (4)
]),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 21 1 false (1),
.cycle 6 7 true (2),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 8 true (2),
.cycle 11 2 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.split 13 (5,true) (byMove [
.cycle 8 7 true (3),
.cycle 10 4 true (4),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.last 16 (2,true),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 18 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 6 9 true (2),
.cycle 11 3 true (4)
]),
.split 12 (2,true) (byMove [
.last 17 (5,true),
.cycle 8 12 true (2),
.last 25 (5,true),
.cycle 9 5 true (3),
.last 17 (5,true),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.cycle 7 16 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
]),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 12 (5,true) (byMove [
.cycle 8 11 true (3),
.cycle 8 12 true (2),
.last 13 (2,true),
.cycle 9 5 true (3),
.cycle 7 11 true (3),
.cycle 17 1 false (-1),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 36 1 false (8),
.cycle 7 8 true (3),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 17 1 false (-1),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 11 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 6 7 true (2),
.cycle 11 1 true (5)
])
theorem kid10_part181_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part181) = true := by rfl

def kid10_part133 : Audit := .split 10 (1,true) (byMove [(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140),(kid10_part141),(kid10_part142),(kid10_part143),(kid10_part144),(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181)])

theorem kid10_part133_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (kid10_part133) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid10_part134),(kid10_part135),(kid10_part136),(kid10_part137),(kid10_part138),(kid10_part139),(kid10_part140),(kid10_part141),(kid10_part142),(kid10_part143),(kid10_part144),(kid10_part145),(kid10_part146),(kid10_part147),(kid10_part148),(kid10_part149),(kid10_part150),(kid10_part151),(kid10_part176),(kid10_part177),(kid10_part178),(kid10_part179),(kid10_part180),(kid10_part181)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part134_checked

  · exact kid10_part140_checked

  · exact kid10_part146_checked

  · exact kid10_part176_checked

  · exact kid10_part135_checked

  · exact kid10_part141_checked

  · exact kid10_part147_checked

  · exact kid10_part177_checked

  · exact kid10_part136_checked

  · exact kid10_part142_checked

  · exact kid10_part148_checked

  · exact kid10_part178_checked

  · exact kid10_part137_checked

  · exact kid10_part143_checked

  · exact kid10_part149_checked

  · exact kid10_part179_checked

  · exact kid10_part138_checked

  · exact kid10_part144_checked

  · exact kid10_part150_checked

  · exact kid10_part180_checked

  · exact kid10_part139_checked

  · exact kid10_part145_checked

  · exact kid10_part151_checked

  · exact kid10_part181_checked

def kid10_part183 : Audit := .cycle 8 4 true (3)
theorem kid10_part183_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part183) = true := by rfl

def kid10_part184 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 22 (5,true),
.cycle 12 1 true (2),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 18 (5,true),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 25 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 11 3 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 25 (5,true),
.last 16 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 15 (5,true),
.cycle 12 1 true (4)
]),
.cycle 6 8 true (2),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.split 12 (5,false) (byMove [
.last 17 (5,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 8 6 true (2),
.cycle 11 2 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.cycle 14 5 false (0),
.last 14 (5,true),
.last 18 (5,true),
.last 14 (5,true),
.last 18 (5,true),
.cycle 0 14 true (0),
.last 18 (5,true),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.split 12 (5,false) (byMove [
.cycle 8 6 true (3),
.cycle 11 2 true (3),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 15 (5,true),
.cycle 12 1 true (4)
])
])
theorem kid10_part184_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part184) = true := by rfl

def kid10_part185 : Audit := .cycle 25 1 false (3)
theorem kid10_part185_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part185) = true := by rfl

def kid10_part186 : Audit := .cycle 0 12 true (0)
theorem kid10_part186_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part186) = true := by rfl

def kid10_part187 : Audit := .cycle 7 4 true (3)
theorem kid10_part187_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part187) = true := by rfl

def kid10_part189 : Audit := .cycle 0 12 true (0)
theorem kid10_part189_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part189) = true := by rfl

def kid10_part190 : Audit := .cycle 1 11 true (1)
theorem kid10_part190_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part190) = true := by rfl

def kid10_part191 : Audit := .cycle 25 1 false (3)
theorem kid10_part191_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part191) = true := by rfl

def kid10_part192 : Audit := .cycle 21 1 false (1)
theorem kid10_part192_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part192) = true := by rfl

def kid10_part193 : Audit := .cycle 17 4 false (1)
theorem kid10_part193_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part193) = true := by rfl

def kid10_part194 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 22 5 false (0),
.cycle 12 1 true (2),
.last 14 (1,true),
.cycle 16 4 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (1,true),
.cycle 12 1 true (2)
])
theorem kid10_part194_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part194) = true := by rfl

def kid10_part195 : Audit := .cycle 0 12 true (0)
theorem kid10_part195_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part195) = true := by rfl

def kid10_part196 : Audit := .cycle 1 11 true (1)
theorem kid10_part196_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part196) = true := by rfl

def kid10_part197 : Audit := .cycle 29 1 false (7)
theorem kid10_part197_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part197) = true := by rfl

def kid10_part198 : Audit := .cycle 25 1 false (5)
theorem kid10_part198_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part198) = true := by rfl

def kid10_part199 : Audit := .cycle 8 4 true (3)
theorem kid10_part199_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part199) = true := by rfl

def kid10_part200 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.last 24 (1,true),
.cycle 17 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.last 14 (1,true),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 24 (1,true),
.cycle 21 1 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 14 (1,true),
.cycle 12 1 true (4)
])
theorem kid10_part200_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part200) = true := by rfl

def kid10_part201 : Audit := .split 13 (1,true) (byMove [
.cycle 28 7 false (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 27 7 false (2),
.cycle 23 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.cycle 6 12 true (2),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 21 6 false (2),
.last 15 (5,false),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 25 3 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 6 15 true (2),
.last 14 (5,false)
])
theorem kid10_part201_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part201) = true := by rfl

def kid10_part202 : Audit := .split 18 (1,true) (byMove [
.cycle 15 5 false (2),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 3 false (-1),
.last 19 (5,false),
.cycle 21 3 false (2),
.cycle 28 3 false (5),
.last 20 (5,false),
.cycle 0 20 true (0),
.cycle 21 3 false (2),
.cycle 19 3 false (1),
.cycle 25 3 false (2),
.cycle 19 3 false (0),
.cycle 23 3 false (2),
.cycle 19 1 false (-1),
.cycle 20 3 false (-1),
.last 19 (5,false),
.cycle 15 6 true (0),
.cycle 1 19 true (0),
.cycle 19 3 false (1),
.cycle 0 20 true (0),
.cycle 15 6 true (0),
.cycle 17 2 true (0)
])
theorem kid10_part202_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part202) = true := by rfl

def kid10_part203 : Audit := .cycle 0 14 true (0)
theorem kid10_part203_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part203) = true := by rfl

def kid10_part204 : Audit := .cycle 22 1 false (2)
theorem kid10_part204_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part204) = true := by rfl

def kid10_part205 : Audit := .cycle 18 4 false (2)
theorem kid10_part205_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part205) = true := by rfl

def kid10_part206 : Audit := .split 12 (5,false) (byMove [
.cycle 17 6 false (1),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 8 6 true (2),
.last 13 (1,true),
.cycle 33 1 false (5),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 11 2 true (2),
.last 14 (1,true),
.cycle 16 4 false (0),
.cycle 8 8 true (1),
.cycle 23 1 false (1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 64, 128, 256, 8, 16, 4096, 64, 4096],[16, 4096, 128, 1, 16, 16, 16, 4096, 0, 1, 16, 16, 4096],5120⟩,
.last 13 (1,true),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 0, 1024, 128, 256, 8, 16, 4096, 1024, 4096],[16, 4096, 4096, 1, 16, 16, 16, 4096, 0, 1, 16, 16, 4096],7200⟩,
.cycle 17 3 false (1)
])
theorem kid10_part206_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part206) = true := by rfl

def kid10_part207 : Audit := .cycle 0 12 true (0)
theorem kid10_part207_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part207) = true := by rfl

def kid10_part208 : Audit := .cycle 1 11 true (1)
theorem kid10_part208_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part208) = true := by rfl

def kid10_part209 : Audit := .cycle 2 10 true (1)
theorem kid10_part209_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part209) = true := by rfl

def kid10_part210 : Audit := .cycle 8 7 true (3)
theorem kid10_part210_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part210) = true := by rfl

def kid10_part211 : Audit := .split 13 (1,true) (byMove [
.cycle 35 13 false (2),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.cycle 21 6 false (1),
.last 14 (5,false),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 11 3 true (3),
.cycle 7 11 true (2),
.cycle 24 5 false (0),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.cycle 25 6 false (5),
.last 14 (5,false),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 11 3 true (3)
])
theorem kid10_part211_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part211) = true := by rfl

def kid10_part212 : Audit := .split 12 (5,false) (byMove [
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 12 1 true (4),
.cycle 6 7 true (2),
.last 13 (1,true),
.last 18 (1,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 14 (1,true),
.cycle 12 1 true (4)
])
theorem kid10_part212_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part212) = true := by rfl

def kid10_part188 : Audit := .split 11 (5,true) (byMove [(kid10_part189),(kid10_part190),(kid10_part191),(kid10_part192),(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197),(kid10_part198),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212)])

theorem kid10_part188_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part188) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part189),(kid10_part190),(kid10_part191),(kid10_part192),(kid10_part193),(kid10_part194),(kid10_part195),(kid10_part196),(kid10_part197),(kid10_part198),(kid10_part199),(kid10_part200),(kid10_part201),(kid10_part202),(kid10_part203),(kid10_part204),(kid10_part205),(kid10_part206),(kid10_part207),(kid10_part208),(kid10_part209),(kid10_part210),(kid10_part211),(kid10_part212)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part189_checked

  · exact kid10_part195_checked

  · exact kid10_part201_checked

  · exact kid10_part207_checked

  · exact kid10_part190_checked

  · exact kid10_part196_checked

  · exact kid10_part202_checked

  · exact kid10_part208_checked

  · exact kid10_part191_checked

  · exact kid10_part197_checked

  · exact kid10_part203_checked

  · exact kid10_part209_checked

  · exact kid10_part192_checked

  · exact kid10_part198_checked

  · exact kid10_part204_checked

  · exact kid10_part210_checked

  · exact kid10_part193_checked

  · exact kid10_part199_checked

  · exact kid10_part205_checked

  · exact kid10_part211_checked

  · exact kid10_part194_checked

  · exact kid10_part200_checked

  · exact kid10_part206_checked

  · exact kid10_part212_checked

def kid10_part213 : Audit := .cycle 0 11 true (0)
theorem kid10_part213_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part213) = true := by rfl

def kid10_part214 : Audit := .cycle 1 10 true (1)
theorem kid10_part214_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part214) = true := by rfl

def kid10_part215 : Audit := .cycle 7 11 true (3)
theorem kid10_part215_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part215) = true := by rfl

def kid10_part216 : Audit := .cycle 3 8 true (1)
theorem kid10_part216_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part216) = true := by rfl

def kid10_part217 : Audit := .cycle 8 3 true (3)
theorem kid10_part217_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part217) = true := by rfl

def kid10_part218 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.split 13 (1,true) (byMove [
.last 24 (5,true),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.last 22 (5,true),
.last 24 (5,true),
.cycle 14 7 false (2),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 8 8 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 11 true (2),
.last 16 (5,true),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.last 17 (5,true),
.cycle 14 7 false (2),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 29 1 false (3),
.cycle 25 1 false (1),
.cycle 21 6 false (2),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 8 6 true (3),
.cycle 19 1 false (1),
.last 15 (1,true),
.last 24 (1,true),
.cycle 0 16 true (0),
.cycle 26 1 false (2),
.last 19 (1,true),
.cycle 17 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.last 15 (1,true),
.cycle 12 2 true (3)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 14 true (3),
.cycle 7 11 true (3),
.cycle 8 4 true (3),
.cycle 11 1 true (5),
.split 13 (1,true) (byMove [
.cycle 8 7 true (3),
.cycle 1 15 true (1),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 11 3 true (4),
.cycle 6 8 true (2),
.last 18 (5,true),
.last 15 (5,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 6 9 true (2)
]),
.cycle 9 3 true (3),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 13 (1,true) (byMove [
.last 17 (5,true),
.cycle 8 10 true (2),
.cycle 31 1 false (5),
.last 22 (5,true),
.last 24 (5,true),
.last 21 (5,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 7 12 true (2),
.last 16 (5,true),
.cycle 5 10 true (1),
.cycle 28 1 false (4),
.last 17 (5,true),
.last 21 (5,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true)
]),
.split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 8 10 true (2),
.cycle 31 1 false (5),
.cycle 39 1 false (3),
.last 26 (1,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 41 1 false (11),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 29 1 false (7),
.last 15 (1,true),
.last 25 (1,true),
.cycle 5 10 true (1),
.cycle 28 1 false (4),
.last 19 (1,true),
.cycle 17 1 false (-1),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 14 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.split 13 (1,true) (byMove [
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 7 13 true (3),
.last 20 (5,true),
.last 24 (5,true),
.last 17 (5,true),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 11 true (3),
.last 16 (5,true),
.cycle 8 9 true (3),
.cycle 7 11 true (3),
.last 19 (5,true),
.cycle 7 9 true (3),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 11 1 true (5)
])
theorem kid10_part218_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part218) = true := by rfl

def kid10_part219 : Audit := .cycle 6 5 true (2)
theorem kid10_part219_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part219) = true := by rfl

def kid10_part220 : Audit := .split 11 (1,true) (byMove [
.cycle 27 9 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (5,true),
.last 15 (5,true),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 22 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.last 14 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 18 (5,true),
.last 14 (5,true)
]),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 24 5 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.last 13 (5,false),
.last 15 (5,false),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 24 5 false (1),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 11 3 true (3),
.last 13 (5,false)
]),
.cycle 7 9 true (2),
.cycle 18 3 false (0),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.split 12 (5,false) (byMove [
.last 17 (5,true),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 6 7 true (2),
.cycle 11 2 true (2),
.last 22 (5,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.cycle 14 5 false (0),
.last 14 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 18 (5,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true)
]),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.last 14 (5,false),
.cycle 23 5 false (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 23 5 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 11 3 true (3),
.last 13 (5,false)
])
])
theorem kid10_part220_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part220) = true := by rfl

def kid10_part221 : Audit := .cycle 8 7 true (2)
theorem kid10_part221_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part221) = true := by rfl

def kid10_part222 : Audit := .cycle 8 5 true (3)
theorem kid10_part222_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part222) = true := by rfl

def kid10_part223 : Audit := .cycle 7 5 true (3)
theorem kid10_part223_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part223) = true := by rfl

def kid10_part225 : Audit := .cycle 27 9 false (2)
theorem kid10_part225_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part225) = true := by rfl

def kid10_part226 : Audit := .cycle 0 15 true (0)
theorem kid10_part226_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part226) = true := by rfl

def kid10_part227 : Audit := .cycle 26 1 false (4)
theorem kid10_part227_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part227) = true := by rfl

def kid10_part228 : Audit := .cycle 21 1 false (1)
theorem kid10_part228_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part228) = true := by rfl

def kid10_part229 : Audit := .cycle 17 4 false (1)
theorem kid10_part229_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part229) = true := by rfl

def kid10_part230 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 22 5 false (0),
.cycle 15 1 true (3),
.last 14 (1,true),
.cycle 16 4 false (0),
.last 16 (1,true),
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 15 1 false (-1),
.last 14 (1,true),
.cycle 0 21 true (0),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (1,true),
.cycle 17 1 true (1)
])
theorem kid10_part230_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part230) = true := by rfl

def kid10_part231 : Audit := .cycle 8 5 true (3)
theorem kid10_part231_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part231) = true := by rfl

def kid10_part232 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 24 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 33 1 false (9),
.cycle 29 1 false (7),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 9 true (2),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 24 5 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 13 (5,false)
])
theorem kid10_part232_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part232) = true := by rfl

def kid10_part233 : Audit := .split 13 (5,false) (byMove [
.cycle 35 13 false (2),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.cycle 21 6 false (1),
.cycle 18 1 false (2),
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 37 1 false (9),
.last 15 (1,true),
.last 24 (1,true),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.cycle 25 6 false (5),
.cycle 18 1 false (0),
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 7 15 true (3)
])
theorem kid10_part233_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part233) = true := by rfl

def kid10_part234 : Audit := .cycle 0 13 true (0)
theorem kid10_part234_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part234) = true := by rfl

def kid10_part235 : Audit := .cycle 7 5 true (3)
theorem kid10_part235_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part235) = true := by rfl

def kid10_part236 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 33 1 false (7),
.cycle 29 1 false (5),
.cycle 8 6 true (3),
.cycle 19 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 37 1 false (11),
.cycle 33 1 false (9),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.last 15 (1,true),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 11 7 true (3),
.cycle 24 1 false (6),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.last 15 (1,true),
.cycle 13 1 true (5)
])
theorem kid10_part236_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part236) = true := by rfl

def kid10_part237 : Audit := .split 13 (1,true) (byMove [
.cycle 31 7 false (5),
.cycle 7 15 true (1),
.last 15 (5,false),
.cycle 0 18 true (0),
.cycle 30 7 false (5),
.cycle 23 3 false (1),
.cycle 8 7 true (2),
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 17 (5,false),
.cycle 7 9 true (2),
.cycle 24 6 false (5),
.last 15 (5,false),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.cycle 26 3 false (4),
.cycle 7 14 true (2),
.cycle 1 14 true (1),
.cycle 7 11 true (2),
.cycle 0 15 true (0),
.cycle 7 14 true (2),
.cycle 6 9 true (2)
])
theorem kid10_part237_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part237) = true := by rfl

def kid10_part238 : Audit := .split 18 (1,true) (byMove [
.cycle 15 5 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 3 false (-1),
.last 19 (5,false),
.cycle 24 3 false (5),
.cycle 31 3 false (8),
.last 20 (5,false),
.cycle 24 3 false (5),
.cycle 24 3 false (5),
.cycle 19 3 false (1),
.cycle 28 3 false (5),
.cycle 19 3 false (0),
.cycle 26 3 false (5),
.cycle 19 1 false (-1),
.cycle 20 3 false (-1),
.last 19 (5,false),
.far true 1 ⟨0,[0, 0],[0, 2, 10, 8, 2, 64, 64],[2, 0, 32, 2, 2, 2, 64],96⟩,
.cycle 1 22 true (0),
.cycle 19 3 false (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[0, 2, 10, 8, 2, 64, 64],[2, 0, 32, 2, 2, 2, 64],96⟩,
.cycle 17 2 true (0)
])
theorem kid10_part238_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part238) = true := by rfl

def kid10_part239 : Audit := .cycle 8 7 true (2)
theorem kid10_part239_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part239) = true := by rfl

def kid10_part240 : Audit := .cycle 23 1 false (3)
theorem kid10_part240_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part240) = true := by rfl

def kid10_part241 : Audit := .cycle 21 4 false (5)
theorem kid10_part241_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part241) = true := by rfl

def kid10_part242 : Audit := .split 12 (5,false) (byMove [
.cycle 17 6 false (1),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 12 2 true (2),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 11 2 true (2),
.last 14 (1,true),
.cycle 16 4 false (0),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.last 14 (1,true),
.cycle 15 1 false (-1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 18 3 false (0),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 17 3 false (1)
])
theorem kid10_part242_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part242) = true := by rfl

def kid10_part243 : Audit := .cycle 8 5 true (3)
theorem kid10_part243_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part243) = true := by rfl

def kid10_part244 : Audit := .split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 13 (5,false),
.cycle 6 7 true (2),
.cycle 23 5 false (1),
.last 14 (5,false),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 13 (5,false)
])
theorem kid10_part244_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part244) = true := by rfl

def kid10_part245 : Audit := .cycle 10 2 true (3)
theorem kid10_part245_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part245) = true := by rfl

def kid10_part246 : Audit := .cycle 0 13 true (0)
theorem kid10_part246_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part246) = true := by rfl

def kid10_part247 : Audit := .cycle 7 5 true (3)
theorem kid10_part247_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part247) = true := by rfl

def kid10_part248 : Audit := .split 13 (5,false) (byMove [
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 13 1 true (5),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 11 5 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 11 3 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.last 15 (1,true),
.cycle 13 1 true (5)
])
theorem kid10_part248_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part248) = true := by rfl

def kid10_part224 : Audit := .split 11 (5,true) (byMove [(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245),(kid10_part246),(kid10_part247),(kid10_part248)])

theorem kid10_part224_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part224) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part225),(kid10_part226),(kid10_part227),(kid10_part228),(kid10_part229),(kid10_part230),(kid10_part231),(kid10_part232),(kid10_part233),(kid10_part234),(kid10_part235),(kid10_part236),(kid10_part237),(kid10_part238),(kid10_part239),(kid10_part240),(kid10_part241),(kid10_part242),(kid10_part243),(kid10_part244),(kid10_part245),(kid10_part246),(kid10_part247),(kid10_part248)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid10_part228_checked

  · exact kid10_part234_checked

  · exact kid10_part240_checked

  · exact kid10_part246_checked

  · exact kid10_part229_checked

  · exact kid10_part235_checked

  · exact kid10_part241_checked

  · exact kid10_part247_checked

  · exact kid10_part230_checked

  · exact kid10_part236_checked

  · exact kid10_part242_checked

  · exact kid10_part248_checked

def kid10_part249 : Audit := .cycle 0 11 true (0)
theorem kid10_part249_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part249) = true := by rfl

def kid10_part250 : Audit := .cycle 1 10 true (1)
theorem kid10_part250_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part250) = true := by rfl

def kid10_part251 : Audit := .cycle 2 9 true (1)
theorem kid10_part251_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part251) = true := by rfl

def kid10_part252 : Audit := .cycle 8 6 true (3)
theorem kid10_part252_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part252) = true := by rfl

def kid10_part253 : Audit := .split 12 (1,true) (byMove [
.cycle 7 10 true (3),
.cycle 7 14 true (2),
.cycle 35 1 false (5),
.cycle 0 17 true (0),
.cycle 7 10 true (3),
.split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 7 14 true (2),
.cycle 37 1 false (3),
.cycle 25 1 false (1),
.cycle 21 6 false (2),
.last 14 (5,false),
.cycle 0 17 true (0),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 7 10 true (3),
.last 14 (5,false),
.cycle 26 3 false (2),
.last 25 (5,false),
.cycle 0 21 true (0),
.cycle 20 12 true (3),
.cycle 17 12 true (3),
.last 14 (5,false),
.cycle 0 17 true (0),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (5,false),
.last 14 (5,false)
]),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 32 9 false (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 16 true (3),
.cycle 7 13 true (3),
.cycle 8 6 true (3),
.last 14 (5,false),
.last 16 (5,false),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 7 14 true (2),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 11 3 true (4),
.last 14 (5,false)
]),
.cycle 7 8 true (3),
.cycle 7 10 true (2),
.cycle 7 8 true (3),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.split 13 (5,true) (byMove [
.cycle 7 22 true (2),
.cycle 8 10 true (2),
.cycle 31 1 false (5),
.cycle 19 14 true (2),
.cycle 40 6 false (2),
.last 14 (5,false),
.cycle 6 8 true (2),
.last 15 (5,false),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 16 (5,false),
.cycle 30 3 false (6),
.cycle 7 10 true (2),
.cycle 5 10 true (1),
.cycle 28 1 false (4),
.cycle 7 12 true (1),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 12 2 true (3),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 16 (5,false)
]),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.cycle 8 7 true (3),
.last 15 (5,false),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 16 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.last 14 (5,false),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 16 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 11 3 true (4),
.last 14 (5,false)
])
])
theorem kid10_part253_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part253) = true := by rfl

def kid10_part254 : Audit := .split 11 (5,false) (byMove [
.cycle 8 5 true (3),
.split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 33 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.last 16 (5,true),
.last 14 (5,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 11 2 true (4)
]),
.cycle 10 2 true (4),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 33 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 21 1 false (1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 12 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 14 (1,true),
.cycle 11 2 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (3),
.cycle 11 1 true (5),
.cycle 6 6 true (2),
.split 12 (1,true) (byMove [
.last 17 (5,true),
.cycle 7 14 true (2),
.cycle 35 1 false (5),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 7 8 true (3),
.last 16 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
]),
.split 13 (5,true) (byMove [
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 0 19 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 12 2 true (4),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 7 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.last 15 (1,true),
.cycle 11 3 true (4)
]),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 12 (5,true) (byMove [
.cycle 8 11 true (3),
.last 13 (1,true),
.cycle 35 1 false (5),
.last 15 (1,true),
.cycle 7 11 true (3),
.cycle 17 1 false (-1),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 36 1 false (8),
.cycle 7 8 true (3),
.last 13 (1,true),
.cycle 12 2 true (3),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 17 1 false (-1),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 11 3 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.split 13 (1,true) (byMove [
.last 18 (5,true),
.last 26 (5,true),
.cycle 7 9 true (3),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 14 (5,true),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 9 true (3),
.last 18 (5,true),
.last 15 (5,true),
.cycle 5 9 true (1),
.cycle 7 9 true (3),
.last 14 (5,true),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 11 1 true (5)
])
theorem kid10_part254_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part254) = true := by rfl

def kid10_part182 : Audit := .split 10 (2,true) (byMove [(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part249),(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254)])

theorem kid10_part182_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (kid10_part182) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid10_part183),(kid10_part184),(kid10_part185),(kid10_part186),(kid10_part187),(kid10_part188),(kid10_part213),(kid10_part214),(kid10_part215),(kid10_part216),(kid10_part217),(kid10_part218),(kid10_part219),(kid10_part220),(kid10_part221),(kid10_part222),(kid10_part223),(kid10_part224),(kid10_part249),(kid10_part250),(kid10_part251),(kid10_part252),(kid10_part253),(kid10_part254)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part183_checked

  · exact kid10_part213_checked

  · exact kid10_part219_checked

  · exact kid10_part249_checked

  · exact kid10_part184_checked

  · exact kid10_part214_checked

  · exact kid10_part220_checked

  · exact kid10_part250_checked

  · exact kid10_part185_checked

  · exact kid10_part215_checked

  · exact kid10_part221_checked

  · exact kid10_part251_checked

  · exact kid10_part186_checked

  · exact kid10_part216_checked

  · exact kid10_part222_checked

  · exact kid10_part252_checked

  · exact kid10_part187_checked

  · exact kid10_part217_checked

  · exact kid10_part223_checked

  · exact kid10_part253_checked

  · exact kid10_part188_checked

  · exact kid10_part218_checked

  · exact kid10_part224_checked

  · exact kid10_part254_checked

def kid10_part255 : Audit := .cycle 0 11 true (0)
theorem kid10_part255_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,2⟩)) (kid10_part255) = true := by rfl

def kid10_part256 : Audit := .cycle 18 1 false (4)
theorem kid10_part256_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,3⟩)) (kid10_part256) = true := by rfl

def kid10_part257 : Audit := .cycle 17 1 false (5)
theorem kid10_part257_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,4⟩)) (kid10_part257) = true := by rfl

def kid10_part259 : Audit := .split 12 (2,true) (byMove [
.cycle 25 9 false (2),
.split 13 (1,true) (byMove [
.cycle 24 7 false (1),
.cycle 1 14 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 25 7 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.cycle 26 9 false (2),
.cycle 0 15 true (0),
.cycle 6 8 true (2),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.last 15 (5,true),
.cycle 28 11 false (2)
]),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 26 9 false (2),
.split 13 (5,true) (byMove [
.cycle 24 7 false (1),
.last 14 (1,true),
.cycle 0 25 false (4),
.cycle 0 15 true (0),
.cycle 25 7 false (1),
.cycle 0 25 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (2),
.cycle 3 11 true (1),
.cycle 26 9 false (2),
.cycle 0 15 true (0),
.cycle 6 8 true (2),
.last 14 (1,true),
.last 87 (1,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 18 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (2),
.cycle 7 26 true (1),
.cycle 28 11 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (2),
.cycle 3 10 true (1),
.cycle 7 18 true (1),
.cycle 0 14 true (0),
.cycle 6 7 true (2),
.split 13 (1,true) (byMove [
.cycle 24 7 false (1),
.cycle 7 15 true (1),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 25 7 false (1),
.last 14 (5,true),
.cycle 8 7 true (2),
.cycle 1 14 true (1),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 14 (5,true),
.cycle 7 9 true (2),
.cycle 18 3 false (0),
.cycle 27 15 true (1),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.last 14 (5,true),
.cycle 7 22 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 7 22 true (1),
.last 14 (5,true)
]),
.cycle 5 11 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.split 13 (5,true) (byMove [
.cycle 24 7 false (1),
.last 14 (1,true),
.cycle 18 6 false (1),
.last 16 (1,true),
.cycle 25 7 false (1),
.cycle 67 17 true (1),
.cycle 8 7 true (2),
.last 14 (1,true),
.cycle 27 9 false (1),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.cycle 0 16 true (0),
.cycle 7 9 true (2),
.last 14 (1,true),
.cycle 18 6 false (1),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.cycle 18 6 false (1),
.cycle 7 22 true (1),
.last 14 (1,true),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 7 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[16, 64, 32, 1, 16, 32, 64],64⟩
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.split 14 (5,true) (byMove [
.cycle 55 48 true (3),
.last 15 (1,true),
.cycle 44 1 false (4),
.last 17 (1,true),
.cycle 55 48 true (3),
.cycle 117 127 true (-1),
.cycle 8 8 true (2),
.last 15 (1,true),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.cycle 0 17 true (0),
.cycle 7 10 true (2),
.last 15 (1,true),
.cycle 7 10 true (2),
.cycle 5 10 true (1),
.cycle 7 10 true (2),
.cycle 78 44 true (4),
.cycle 7 25 true (1),
.last 15 (1,true),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 7 25 true (1),
.cycle 7 27 true (1)
]),
.split 26 (5,true) (byMove [
.cycle 30 13 false (3),
.last 27 (1,true),
.cycle 31 15 false (3),
.last 29 (1,true),
.cycle 31 13 false (3),
.cycle 0 32 false (5),
.cycle 61 52 true (4),
.last 27 (1,true),
.cycle 88 62 true (6),
.cycle 0 28 true (0),
.cycle 60 52 true (4),
.cycle 0 29 true (0),
.cycle 7 22 true (1),
.last 27 (1,true),
.cycle 25 2 true (3),
.cycle 5 22 true (1),
.cycle 7 22 true (1),
.cycle 27 8 false (3),
.cycle 161 98 true (7),
.last 27 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 36, 36, 64],[16, 64, 32, 1, 16, 4, 64],64⟩,
.cycle 0 28 true (0),
.cycle 160 98 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[16, 64, 32, 1, 16, 32, 64],64⟩
])
])
theorem kid10_part259_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part259) = true := by rfl

def kid10_part260 : Audit := .cycle 0 13 true (0)
theorem kid10_part260_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part260) = true := by rfl

def kid10_part261 : Audit := .cycle 22 1 false (4)
theorem kid10_part261_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part261) = true := by rfl

def kid10_part262 : Audit := .cycle 17 1 false (1)
theorem kid10_part262_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part262) = true := by rfl

def kid10_part263 : Audit := .cycle 13 2 false (1)
theorem kid10_part263_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part263) = true := by rfl

def kid10_part264 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.cycle 22 1 false (4),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.split 14 (1,true) (byMove [
.cycle 17 1 false (-1),
.cycle 24 1 false (0),
.last 15 (2,true),
.proven (BB6.Agent11Raw39B0RECounter640.M640.table) (fun m hm => BB6.Agent11Raw39B0RECounter640.M640.never m hm),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 19 true (-1),
.cycle 25 15 false (3),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.last 17 (2,true),
.last 15 (2,true),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.cycle 0 19 true (-1),
.cycle 32 1 false (0),
.cycle 2 13 false (4),
.cycle 10 9 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (0)
]),
.split 14 (2,true) (byMove [
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.proven (BB6.Agent11Raw39B0RECounter641.M641.table) (fun m hm => BB6.Agent11Raw39B0RECounter641.M641.never m hm),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 0 19 true (-1),
.cycle 25 15 false (3),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 10 5 false (2),
.cycle 18 1 false (0),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 12 3 false (0),
.cycle 0 19 true (-1),
.last 29 (1,true),
.cycle 2 13 false (4),
.cycle 10 9 false (2),
.last 17 (1,true),
.last 17 (1,true)
]),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 32768, 4194320, 16777216, 256, 128, 256, 2097152, 16, 16777216, 32768, 128, 256, 8, 16, 262144, 16, 16777216],[16, 16777216, 16777216, 1, 16, 128, 65536, 16777216, 16777216, 4096, 65536, 128, 4194304, 16777216, 16777216, 262144, 4194304, 128, 16, 16777216, 16777216, 1, 16, 128, 16777216],16843776⟩,
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 64, 1, 16, 16, 64],64⟩,
.cycle 11 2 true (0)
])
theorem kid10_part264_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part264) = true := by rfl

def kid10_part265 : Audit := .cycle 8 3 true (3)
theorem kid10_part265_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part265) = true := by rfl

def kid10_part266 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.last 21 (2,true),
.cycle 20 3 false (2),
.cycle 19 3 false (1),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 20 3 false (2),
.cycle 28 3 false (6),
.cycle 22 3 false (0),
.last 20 (2,true),
.cycle 22 3 false (2),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 19 3 false (0),
.cycle 14 6 true (0),
.cycle 21 3 false (1),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 14 6 true (0),
.cycle 8 23 true (0)
]),
.cycle 1 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (3),
.cycle 1 11 true (1),
.cycle 6 7 true (2),
.split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.cycle 20 3 false (0),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 20 3 false (0),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 14 (5,true),
.cycle 1 13 true (1)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.split 18 (5,true) (byMove [
.last 21 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 2, 64],[16, 16, 64, 1, 16, 25, 64],64⟩,
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.last 21 (2,true),
.cycle 23 3 false (5),
.cycle 19 3 false (1),
.last 19 (2,true),
.cycle 23 3 false (5),
.cycle 23 3 false (5),
.cycle 31 3 false (9),
.cycle 27 3 false (5),
.last 20 (2,true),
.cycle 25 3 false (5),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 19 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 2, 64],[16, 16, 64, 1, 16, 1, 64],64⟩,
.cycle 25 3 false (5),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 2, 64],[16, 16, 64, 1, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 2, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 18 27 true (0)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 20 12 true (3),
.cycle 23 5 false (1),
.last 15 (2,true),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 7 8 true (3),
.last 14 (2,true),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.cycle 7 10 true (2),
.cycle 7 8 true (3),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid10_part266_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part266) = true := by rfl

def kid10_part267 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.split 18 (5,true) (byMove [
.cycle 14 9 false (2),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 0 22 true (-1),
.cycle 20 3 false (2),
.last 19 (1,true),
.cycle 19 3 false (1),
.cycle 0 20 true (0),
.cycle 20 3 false (2),
.cycle 22 1 false (4),
.last 20 (1,true),
.cycle 22 3 false (0),
.cycle 22 3 false (2),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 19 3 false (0),
.cycle 14 6 true (0),
.last 19 (1,true),
.cycle 21 3 false (1),
.cycle 0 20 true (0),
.cycle 14 6 true (0),
.cycle 8 24 true (0)
]),
.cycle 29 1 false (7),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (3),
.cycle 33 1 false (11),
.split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 24 3 false (2),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 7 16 true (3),
.cycle 6 7 true (2),
.cycle 7 11 true (2),
.cycle 27 3 false (5),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 14 (5,true),
.cycle 7 14 true (3)
]),
.split 13 (1,true) (byMove [
.cycle 33 11 false (2),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.cycle 25 1 false (1),
.cycle 21 6 false (1),
.cycle 0 17 true (0),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 11 true (2),
.cycle 20 3 false (0),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.cycle 25 6 false (5),
.last 24 (5,true),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.split 18 (5,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 4, 64],[16, 64, 16, 1, 16, 20, 64],64⟩,
.far true 5 ⟨0,[0, 1, 2, 3, 2, 1, 4, 3, 2, 1],[33554432, 8388608, 2097152, 512, 2048, 2097152, 1073741824, 8388608, 1107296256, 2097152, 8388608, 8388608, 1107296256, 1082130432, 2097152, 512, 2048, 1109393408, 1073741824, 8388608, 8388608, 2097152, 8388608, 8388608, 33554432, 33554432, 2097152, 512, 2048, 8388608, 1073741824],[8388608, 1073741824, 1024, 33554432, 8388608, 2, 8388608, 1073741824, 4194304, 8388608, 8388608, 8192, 8388608, 1073741824, 1024, 1107296256, 8388608, 8192, 8388608, 1073741824, 4194304, 8388608, 8388608, 33554432, 8388608, 1073741824, 1024, 1073741824, 8388608, 8192, 1073741824],1074147648⟩,
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 25 3 false (5),
.cycle 23 3 false (5),
.last 19 (1,true),
.cycle 19 3 false (1),
.cycle 23 3 false (5),
.cycle 23 3 false (5),
.cycle 25 1 false (7),
.last 20 (1,true),
.cycle 27 3 false (5),
.cycle 25 3 false (5),
.cycle 19 1 false (-1),
.cycle 19 3 false (-1),
.cycle 19 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 4, 64],[16, 64, 16, 1, 16, 1, 64],64⟩,
.last 19 (1,true),
.cycle 25 3 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 4, 64],[16, 64, 16, 1, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 4, 64],[16, 64, 16, 1, 16, 16, 64],64⟩,
.cycle 18 28 true (0)
]),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.split 12 (5,true) (byMove [
.cycle 7 15 true (3),
.cycle 0 16 true (0),
.cycle 30 1 false (6),
.cycle 20 12 true (3),
.cycle 23 5 false (1),
.cycle 0 16 true (0),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 41 1 false (13),
.last 14 (1,true),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 27 1 false (5),
.cycle 7 10 true (2),
.cycle 7 8 true (3),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 7 15 true (3)
]),
.cycle 7 12 true (3)
])
theorem kid10_part267_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part267) = true := by rfl

def kid10_part268 : Audit := .cycle 0 11 true (0)
theorem kid10_part268_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part268) = true := by rfl

def kid10_part269 : Audit := .cycle 7 3 true (3)
theorem kid10_part269_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part269) = true := by rfl

def kid10_part270 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.cycle 18 3 false (0),
.cycle 11 1 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (3),
.cycle 11 1 true (5),
.split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 24 3 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 15 (2,true),
.last 13 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 27 3 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 10 true (3),
.cycle 13 1 true (5)
]),
.split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 20 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 13 1 true (5),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 20 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 15 (1,true),
.cycle 13 1 true (5)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.cycle 18 3 false (0),
.cycle 9 2 true (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 11 1 true (5)
])
theorem kid10_part270_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part270) = true := by rfl

def kid10_part272 : Audit := .cycle 25 5 false (5)
theorem kid10_part272_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part272) = true := by rfl

def kid10_part273 : Audit := .cycle 7 13 true (1)
theorem kid10_part273_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part273) = true := by rfl

def kid10_part274 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 0 16 true (0),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 25 5 false (5),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 18 4 false (2),
.cycle 0 16 true (0),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 7 9 true (2)
])
theorem kid10_part274_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part274) = true := by rfl

def kid10_part275 : Audit := .cycle 0 16 true (0)
theorem kid10_part275_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part275) = true := by rfl

def kid10_part276 : Audit := .cycle 24 5 false (5)
theorem kid10_part276_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part276) = true := by rfl

def kid10_part277 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.cycle 17 4 false (1),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 25 5 false (5),
.cycle 9 4 true (2),
.cycle 20 3 false (1),
.last 14 (2,true),
.cycle 0 20 true (0),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.cycle 18 4 false (2),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 7 9 true (2),
.cycle 7 9 true (2)
])
theorem kid10_part277_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part277) = true := by rfl

def kid10_part278 : Audit := .cycle 8 5 true (2)
theorem kid10_part278_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part278) = true := by rfl

def kid10_part279 : Audit := .cycle 1 12 true (1)
theorem kid10_part279_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part279) = true := by rfl

def kid10_part280 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 15 true (2),
.cycle 7 12 true (2),
.cycle 8 5 true (2),
.cycle 7 16 true (2),
.cycle 7 15 true (2),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 7 9 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 6 8 true (2)
])
theorem kid10_part280_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part280) = true := by rfl

def kid10_part281 : Audit := .cycle 0 13 true (0)
theorem kid10_part281_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part281) = true := by rfl

def kid10_part282 : Audit := .cycle 7 5 true (2)
theorem kid10_part282_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part282) = true := by rfl

def kid10_part283 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 14 7 false (2),
.cycle 6 8 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 15 true (2),
.cycle 7 12 true (2),
.cycle 8 5 true (2),
.cycle 13 3 true (4),
.cycle 13 3 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 14 7 false (2),
.cycle 7 9 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 7 13 true (2),
.cycle 6 8 true (2)
])
theorem kid10_part283_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part283) = true := by rfl

def kid10_part284 : Audit := .cycle 7 7 true (2)
theorem kid10_part284_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part284) = true := by rfl

def kid10_part285 : Audit := .split 14 (2,true) (byMove [
.cycle 23 8 false (5),
.cycle 16 3 false (0),
.cycle 18 1 false (0),
.cycle 10 6 true (1),
.cycle 22 8 false (5),
.last 15 (5,true),
.cycle 6 9 true (1),
.cycle 1 20 true (1),
.cycle 7 21 true (1),
.cycle 8 9 true (1),
.cycle 7 9 true (1),
.last 15 (5,true),
.cycle 7 11 true (1),
.cycle 16 3 false (0),
.cycle 21 13 true (1),
.cycle 7 11 true (1),
.cycle 7 11 true (1),
.last 15 (5,true),
.cycle 29 22 true (2),
.cycle 16 5 false (2),
.cycle 2 15 true (1),
.cycle 30 22 true (2),
.cycle 28 22 true (2),
.last 15 (5,true)
])
theorem kid10_part285_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part285) = true := by rfl

def kid10_part286 : Audit := .split 12 (2,true) (byMove [
.cycle 7 15 true (1),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 17 4 false (1),
.cycle 6 7 true (2),
.cycle 8 9 true (2),
.cycle 37 1 false (9),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 23 3 false (4),
.cycle 25 13 true (1),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.last 14 (5,true),
.cycle 20 4 false (4),
.cycle 6 7 true (2),
.cycle 11 2 true (2),
.cycle 2 13 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true)
])
theorem kid10_part286_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part286) = true := by rfl

def kid10_part287 : Audit := .cycle 5 7 true (1)
theorem kid10_part287_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part287) = true := by rfl

def kid10_part288 : Audit := .cycle 7 7 true (2)
theorem kid10_part288_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part288) = true := by rfl

def kid10_part289 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.cycle 17 4 false (1),
.cycle 6 7 true (2),
.cycle 26 5 false (4),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 13 5 true (3),
.cycle 23 3 false (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.cycle 14 5 false (0),
.cycle 20 4 false (4),
.cycle 6 7 true (2),
.cycle 11 2 true (2),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 6 10 true (2)
])
theorem kid10_part289_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part289) = true := by rfl

def kid10_part290 : Audit := .cycle 7 10 true (2)
theorem kid10_part290_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part290) = true := by rfl

def kid10_part291 : Audit := .cycle 1 12 true (1)
theorem kid10_part291_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part291) = true := by rfl

def kid10_part292 : Audit := .split 12 (2,true) (byMove [
.cycle 7 11 true (2),
.cycle 2 12 true (1),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 7 11 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (2),
.cycle 3 10 true (1),
.cycle 7 10 true (2),
.cycle 2 14 true (1),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 5 11 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 6 8 true (2)
])
theorem kid10_part292_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part292) = true := by rfl

def kid10_part293 : Audit := .cycle 0 13 true (0)
theorem kid10_part293_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part293) = true := by rfl

def kid10_part294 : Audit := .cycle 7 10 true (2)
theorem kid10_part294_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part294) = true := by rfl

def kid10_part295 : Audit := .split 12 (5,true) (byMove [
.cycle 7 11 true (2),
.cycle 6 9 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 11 true (2),
.cycle 22 14 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (2),
.cycle 3 10 true (1),
.cycle 7 10 true (2),
.cycle 6 11 true (2),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 22 6 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 7 13 true (2),
.cycle 6 8 true (2)
])
theorem kid10_part295_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part295) = true := by rfl

def kid10_part271 : Audit := .split 11 (1,true) (byMove [(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295)])

theorem kid10_part271_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part271) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid10_part272),(kid10_part273),(kid10_part274),(kid10_part275),(kid10_part276),(kid10_part277),(kid10_part278),(kid10_part279),(kid10_part280),(kid10_part281),(kid10_part282),(kid10_part283),(kid10_part284),(kid10_part285),(kid10_part286),(kid10_part287),(kid10_part288),(kid10_part289),(kid10_part290),(kid10_part291),(kid10_part292),(kid10_part293),(kid10_part294),(kid10_part295)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part272_checked

  · exact kid10_part278_checked

  · exact kid10_part284_checked

  · exact kid10_part290_checked

  · exact kid10_part273_checked

  · exact kid10_part279_checked

  · exact kid10_part285_checked

  · exact kid10_part291_checked

  · exact kid10_part274_checked

  · exact kid10_part280_checked

  · exact kid10_part286_checked

  · exact kid10_part292_checked

  · exact kid10_part275_checked

  · exact kid10_part281_checked

  · exact kid10_part287_checked

  · exact kid10_part293_checked

  · exact kid10_part276_checked

  · exact kid10_part282_checked

  · exact kid10_part288_checked

  · exact kid10_part294_checked

  · exact kid10_part277_checked

  · exact kid10_part283_checked

  · exact kid10_part289_checked

  · exact kid10_part295_checked

def kid10_part297 : Audit := .split 20 (1,true) (byMove [
.cycle 15 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 1, 2, 2, 64, 64],64⟩,
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 25 5 false (5),
.cycle 32 5 false (8),
.cycle 15 8 true (0),
.cycle 25 5 false (5),
.cycle 25 5 false (5),
.last 21 (5,true),
.cycle 29 5 false (5),
.cycle 21 5 false (0),
.cycle 27 5 false (5),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.far true 1 ⟨0,[0, 0],[0, 2, 10, 8, 32, 2, 64],[2, 0, 1, 2, 2, 64, 64],64⟩,
.cycle 1 24 true (0),
.cycle 21 5 false (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 1, 2, 2, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 8, 16, 4096, 16, 4096],[16, 1024, 256, 1, 16, 4096, 16, 1024, 16, 1, 16, 4096, 4096],5120⟩,
.last 21 (5,true)
])
theorem kid10_part297_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part297) = true := by rfl

def kid10_part298 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 25 5 false (5),
.cycle 9 4 true (2),
.cycle 21 9 false (2),
.cycle 16 3 false (0),
.cycle 0 21 true (0),
.cycle 22 1 false (0),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid10_part298_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part298) = true := by rfl

def kid10_part299 : Audit := .cycle 25 1 false (1)
theorem kid10_part299_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part299) = true := by rfl

def kid10_part300 : Audit := .split 14 (1,true) (byMove [
.cycle 8 8 true (2),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 7 15 true (2),
.cycle 3 12 true (1),
.cycle 7 12 true (2),
.cycle 0 19 true (0),
.cycle 6 9 true (2),
.cycle 10 6 true (2),
.cycle 29 1 false (1),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 8 10 true (2),
.last 16 (5,true),
.last 17 (5,true)
])
theorem kid10_part300_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part300) = true := by rfl

def kid10_part301 : Audit := .split 20 (1,true) (byMove [
.cycle 15 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 16, 2, 2, 64, 64],64⟩,
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.cycle 24 5 false (5),
.cycle 31 5 false (8),
.cycle 22 5 false (0),
.cycle 24 5 false (5),
.cycle 24 5 false (5),
.last 21 (5,true),
.cycle 28 5 false (5),
.cycle 21 5 false (0),
.cycle 26 5 false (5),
.cycle 21 1 false (-1),
.cycle 21 5 false (-1),
.cycle 21 5 false (-1),
.far true 1 ⟨0,[0, 0],[0, 2, 10, 8, 32, 2, 64],[2, 0, 16, 2, 2, 64, 64],64⟩,
.cycle 1 24 true (0),
.cycle 21 5 false (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 32, 2, 64],[2, 2, 16, 2, 2, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 8, 16, 4096, 16, 4096],[16, 1024, 4112, 1, 16, 4096, 16, 1024, 16, 1, 16, 4096, 4096],5120⟩,
.last 21 (5,true)
])
theorem kid10_part301_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part301) = true := by rfl

def kid10_part302 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 7 13 true (1),
.cycle 25 1 false (1),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (1,true),
.last 14 (1,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.last 20 (1,true),
.cycle 9 4 true (2),
.last 14 (1,true),
.last 16 (1,true),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 14 5 false (0),
.last 14 (1,true),
.last 14 (1,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 7 9 true (2),
.last 14 (1,true)
])
theorem kid10_part302_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part302) = true := by rfl

def kid10_part303 : Audit := .cycle 8 5 true (2)
theorem kid10_part303_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part303) = true := by rfl

def kid10_part304 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.cycle 20 19 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 15 true (2),
.cycle 7 12 true (2),
.cycle 8 5 true (2),
.cycle 1 15 true (1),
.cycle 6 9 true (2),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (5,true),
.cycle 14 6 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid10_part304_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part304) = true := by rfl

def kid10_part305 : Audit := .cycle 7 15 true (2)
theorem kid10_part305_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part305) = true := by rfl

def kid10_part306 : Audit := .cycle 0 13 true (0)
theorem kid10_part306_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part306) = true := by rfl

def kid10_part307 : Audit := .cycle 7 5 true (2)
theorem kid10_part307_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part307) = true := by rfl

def kid10_part308 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.cycle 14 7 false (2),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 15 true (2),
.cycle 7 12 true (2),
.cycle 8 5 true (2),
.cycle 13 3 true (4),
.last 14 (1,true),
.cycle 13 3 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 14 7 false (2),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 18 (1,true),
.last 14 (1,true)
])
theorem kid10_part308_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part308) = true := by rfl

def kid10_part309 : Audit := .cycle 7 7 true (2)
theorem kid10_part309_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part309) = true := by rfl

def kid10_part310 : Audit := .split 12 (1,true) (byMove [
.cycle 20 10 false (1),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 10 4 true (2),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 7 11 true (1),
.cycle 16 3 false (0),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.last 14 (5,true),
.cycle 14 4 false (0),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true)
])
theorem kid10_part310_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part310) = true := by rfl

def kid10_part311 : Audit := .cycle 5 9 true (1)
theorem kid10_part311_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part311) = true := by rfl

def kid10_part312 : Audit := .cycle 5 7 true (1)
theorem kid10_part312_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part312) = true := by rfl

def kid10_part313 : Audit := .cycle 7 7 true (2)
theorem kid10_part313_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part313) = true := by rfl

def kid10_part314 : Audit := .split 12 (5,true) (byMove [
.last 20 (1,true),
.cycle 8 9 true (1),
.cycle 27 1 false (3),
.cycle 21 1 false (-1),
.cycle 14 5 false (0),
.last 14 (1,true),
.cycle 6 7 true (2),
.last 13 (1,true),
.last 20 (1,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 13 5 true (3),
.last 14 (1,true),
.last 16 (1,true),
.cycle 5 9 true (1),
.cycle 24 1 false (2),
.cycle 14 5 false (0),
.last 14 (1,true),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 11 2 true (2),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 16 (1,true)
])
theorem kid10_part314_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part314) = true := by rfl

def kid10_part315 : Audit := .split 15 (1,true) (byMove [
.cycle 7 16 true (1),
.cycle 7 18 true (1),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.cycle 7 16 true (1),
.last 16 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 11 5 true (3),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.last 16 (5,true),
.cycle 7 12 true (2),
.cycle 7 14 true (1),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.last 16 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 11 5 true (3),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.last 16 (5,true)
])
theorem kid10_part315_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part315) = true := by rfl

def kid10_part316 : Audit := .split 12 (1,true) (byMove [
.cycle 24 18 false (2),
.cycle 1 14 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.last 18 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (2),
.cycle 3 10 true (1),
.cycle 7 10 true (2),
.cycle 1 15 true (1),
.cycle 6 7 true (2),
.cycle 18 5 false (2),
.cycle 11 2 true (3),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 14 (5,true),
.last 15 (5,true)
])
theorem kid10_part316_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part316) = true := by rfl

def kid10_part317 : Audit := .cycle 2 11 true (1)
theorem kid10_part317_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part317) = true := by rfl

def kid10_part318 : Audit := .cycle 0 13 true (0)
theorem kid10_part318_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part318) = true := by rfl

def kid10_part319 : Audit := .split 15 (1,true) (byMove [
.cycle 7 16 true (1),
.cycle 7 18 true (1),
.last 18 (5,true),
.cycle 0 23 true (0),
.cycle 7 16 true (1),
.last 16 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 11 5 true (3),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.last 16 (5,true),
.cycle 7 12 true (2),
.cycle 7 14 true (1),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.last 16 (5,true),
.cycle 6 10 true (2),
.cycle 1 17 true (1),
.cycle 11 5 true (3),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.last 16 (5,true)
])
theorem kid10_part319_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part319) = true := by rfl

def kid10_part320 : Audit := .split 12 (5,true) (byMove [
.last 16 (1,true),
.last 13 (1,true),
.last 15 (1,true),
.cycle 0 14 true (0),
.last 16 (1,true),
.last 16 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (2),
.cycle 3 10 true (1),
.last 15 (1,true),
.last 17 (1,true),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 11 2 true (3),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.last 16 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (2),
.last 18 (1,true),
.last 14 (1,true)
])
theorem kid10_part320_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part320) = true := by rfl

def kid10_part296 : Audit := .split 11 (2,true) (byMove [(kid10_part297),(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320)])

theorem kid10_part296_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part296) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid10_part297),(kid10_part298),(kid10_part299),(kid10_part300),(kid10_part301),(kid10_part302),(kid10_part303),(kid10_part304),(kid10_part305),(kid10_part306),(kid10_part307),(kid10_part308),(kid10_part309),(kid10_part310),(kid10_part311),(kid10_part312),(kid10_part313),(kid10_part314),(kid10_part315),(kid10_part316),(kid10_part317),(kid10_part318),(kid10_part319),(kid10_part320)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part297_checked

  · exact kid10_part303_checked

  · exact kid10_part309_checked

  · exact kid10_part315_checked

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

def kid10_part321 : Audit := .cycle 8 5 true (2)
theorem kid10_part321_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part321) = true := by rfl

def kid10_part322 : Audit := .cycle 19 1 false (3)
theorem kid10_part322_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part322) = true := by rfl

def kid10_part323 : Audit := .cycle 17 2 false (5)
theorem kid10_part323_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part323) = true := by rfl

def kid10_part325 : Audit := .split 15 (2,true) (byMove [
.cycle 11 7 false (1),
.last 16 (1,true),
.cycle 19 1 false (-1),
.last 18 (1,true),
.cycle 11 7 false (1),
.cycle 19 1 false (-1),
.cycle 27 1 false (-1),
.last 16 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 4, 4, 64],[16, 64, 4, 1, 16, 4, 64],64⟩,
.cycle 27 1 false (-1),
.cycle 27 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 36, 36, 64],[16, 64, 32, 1, 16, 36, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 16, 16, 128, 256, 8, 16, 16, 16, 4096],[16, 4096, 4096, 1, 16, 256, 16, 4096, 16, 1, 16, 16, 4096],4096⟩,
.last 16 (1,true),
.cycle 26 1 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 16, 1, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 16, 1, 16, 20, 64],64⟩,
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 17, 64],[16, 64, 1, 1, 16, 21, 64],64⟩,
.last 16 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 4, 4, 64],[16, 64, 4, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 25, 25, 64],[16, 64, 8, 1, 16, 29, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 16, 1, 16, 20, 64],64⟩,
.cycle 23 1 false (-1)
])
theorem kid10_part325_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part325) = true := by rfl

def kid10_part326 : Audit := .far true 5 ⟨0,[0, 1, 1, 2, 1, 3, 4, 3, 1, 1],[33554432, 8388608, 32768, 512, 2048, 2048, 1107296256, 1115684864, 1109426176, 32768, 131072, 131072, 1073741824, 1073741824, 1115684864, 2097152, 8388608, 8388608, 1073741824, 1073741824, 8388608, 2097152, 8388608, 8388608, 1073741824, 33554432, 2097152, 512, 2048, 2048, 1073741824],[131072, 1073741824, 1073741824, 33554432, 131072, 2, 8519680, 1073741824, 1073741824, 1115684864, 8519680, 128, 8388608, 1073741824, 1073741824, 8388608, 8388608, 128, 8388608, 1073741824, 1073741824, 8388608, 8388608, 33554432, 8388608, 1073741824, 1073741824, 1073741824, 8388608, 128, 1073741824],1091334592⟩
theorem kid10_part326_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part326) = true := by rfl

def kid10_part327 : Audit := .cycle 14 1 false (0)
theorem kid10_part327_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part327) = true := by rfl

def kid10_part328 : Audit := .cycle 13 1 false (-1)
theorem kid10_part328_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part328) = true := by rfl

def kid10_part329 : Audit := .cycle 14 1 false (-2)
theorem kid10_part329_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part329) = true := by rfl

def kid10_part330 : Audit := .cycle 13 1 false (-1)
theorem kid10_part330_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part330) = true := by rfl

def kid10_part331 : Audit := .cycle 18 1 false (4)
theorem kid10_part331_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part331) = true := by rfl

def kid10_part332 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 17, 17, 128, 256, 8, 16, 8, 8, 4096],[16, 8, 4096, 1, 16, 2, 16, 409, 4096, 1, 16, 2, 4096],4096⟩,
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 18 1 false (4),
.cycle 25 1 false (7),
.last 14 (2,true),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 25 1 false (7),
.cycle 22 1 false (4),
.last 15 (2,true),
.cycle 20 1 false (4),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 7 9 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 7 9 true (0),
.cycle 33 3 true (7)
])
theorem kid10_part332_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part332) = true := by rfl

def kid10_part333 : Audit := .split 13 (2,true) (byMove [
.cycle 11 8 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 17, 17, 128, 256, 8, 16, 8, 8, 4096],[16, 4096, 8, 1, 16, 4, 16, 4096, 4096, 1, 16, 4, 4096],4096⟩,
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 18 1 false (4),
.last 14 (1,true),
.cycle 18 1 false (6),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 18 1 false (6),
.last 15 (1,true),
.last 16 (1,true),
.cycle 20 1 false (4),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 7 9 true (0),
.last 14 (1,true),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.cycle 7 9 true (0),
.cycle 12 21 true (0)
])
theorem kid10_part333_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part333) = true := by rfl

def kid10_part334 : Audit := .cycle 18 1 false (4)
theorem kid10_part334_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part334) = true := by rfl

def kid10_part335 : Audit := .cycle 18 1 false (4)
theorem kid10_part335_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part335) = true := by rfl

def kid10_part336 : Audit := .cycle 17 1 false (5)
theorem kid10_part336_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part336) = true := by rfl

def kid10_part337 : Audit := .split 14 (1,true) (byMove [
.cycle 17 1 false (-1),
.cycle 28 1 false (4),
.last 15 (2,true),
.cycle 0 28 true (-1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 1, 64, 1, 16, 17, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 18, 18, 64],[16, 2, 64, 1, 16, 18, 64],64⟩,
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 17, 64],[16, 8, 64, 1, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 16, 64, 1, 16, 16, 64],64⟩,
.cycle 956 1 false (32),
.cycle 22 1 false (4),
.last 17 (2,true),
.last 15 (2,true),
.cycle 22 1 false (4),
.cycle 22 1 false (4),
.cycle 12 3 false (0),
.cycle 33 1 false (5),
.cycle 78 1 false (10),
.last 15 (2,true),
.cycle 33 1 false (5),
.cycle 33 1 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 48, 48, 64],[16, 32, 64, 1, 16, 48, 64],64⟩
])
theorem kid10_part337_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part337) = true := by rfl

def kid10_part338 : Audit := .split 14 (2,true) (byMove [
.cycle 17 1 false (-1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.last 17 (1,true),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.far false 4 ⟨0,[0, 1, 1, 2, 2, 3, 3, 3],[128, 256, 8, 0, 0, 0, 8192, 16384, 512, 16, 1024, 1024, 524288, 1048576, 32768, 1024, 16842752, 16842752, 524288, 1048576, 2097152, 4259840, 20971520, 20971520, 16777216],[16, 16777216, 1, 1, 16, 64, 1024, 16777216, 64, 64, 1024, 16781312, 65536, 16777216, 4096, 4096, 65536, 17039360, 4194304, 16777216, 262144, 262144, 4194304, 17039360, 16777216],33501248⟩,
.last 15 (1,true),
.cycle 36 1 false (6),
.far true 5 ⟨0,[0, 1, 1, 2, 1, 3, 1, 4, 1, 4],[33554432, 536870912, 32768, 512, 2048, 2048, 1107296256, 1644167168, 169869312, 32768, 131072, 131072, 1073741824, 1610612736, 1644167168, 2097152, 8388608, 8388608, 1073741824, 1107296256, 536870912, 134217728, 536870912, 536870912, 1073741824, 33554432, 536870912, 134217728, 536870912, 536870912, 1073741824],[131072, 1073741824, 32768, 33554432, 131072, 128, 545259520, 1073741824, 169869312, 1115684864, 545259520, 8192, 536870912, 1073741824, 1644167168, 536870912, 536870912, 524288, 536870912, 1073741824, 536870912, 536870912, 536870912, 33554432, 536870912, 1073741824, 536870912, 536870912, 536870912, 33554432, 1073741824],1091334336⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 131072, 32768, 512, 2048, 2048, 270336, 401408, 40960, 32768, 131072, 131072, 262144, 8192, 401408, 32768, 131072, 131072, 262144],[131072, 262144, 131072, 8192, 131072, 128, 131072, 262144, 131072, 401408, 131072, 8192, 131072, 262144, 131072, 131072, 131072, 8192, 262144],282816⟩,
.last 30 (1,true),
.cycle 22 1 false (4),
.last 15 (1,true),
.cycle 24 1 false (4),
.cycle 22 1 false (4),
.cycle 22 1 false (4),
.cycle 12 3 false (0),
.last 25 (1,true),
.last 15 (1,true),
.last 30 (1,true),
.last 25 (1,true),
.last 25 (1,true),
.last 16 (1,true)
])
theorem kid10_part338_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part338) = true := by rfl

def kid10_part339 : Audit := .cycle 20 1 false (4)
theorem kid10_part339_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part339) = true := by rfl

def kid10_part340 : Audit := .cycle 13 1 false (-1)
theorem kid10_part340_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part340) = true := by rfl

def kid10_part341 : Audit := .cycle 14 1 false (-2)
theorem kid10_part341_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part341) = true := by rfl

def kid10_part342 : Audit := .cycle 13 1 false (-1)
theorem kid10_part342_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part342) = true := by rfl

def kid10_part343 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 64, 1, 16, 1, 64],64⟩
theorem kid10_part343_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part343) = true := by rfl

def kid10_part344 : Audit := .split 13 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 26 1 false (4),
.last 14 (2,true),
.cycle 0 24 true (0),
.cycle 16 1 false (0),
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 17, 64],[16, 1, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 2, 2, 64],[16, 2, 64, 1, 16, 2, 64],64⟩,
.last 14 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 25, 25, 64],[16, 8, 64, 1, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 16, 64, 1, 16, 2, 64],64⟩,
.cycle 1 16 true (0),
.cycle 20 1 false (4),
.last 16 (2,true),
.last 14 (2,true),
.cycle 20 1 false (4),
.cycle 20 1 false (4),
.cycle 12 2 true (0),
.cycle 7 9 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 7 9 true (0),
.cycle 1 16 true (0)
])
theorem kid10_part344_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part344) = true := by rfl

def kid10_part345 : Audit := .split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 16 (1,true),
.cycle 16 1 false (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 17, 17, 128, 256, 8, 16, 8, 8, 4096],[16, 4096, 145, 1, 16, 256, 16, 4096, 8, 1, 16, 256, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 17, 64],[16, 64, 1, 1, 16, 4, 64],64⟩,
.last 14 (1,true),
.cycle 32 1 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 25, 25, 64],[16, 64, 8, 1, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 16, 1, 16, 4, 64],64⟩,
.cycle 14 22 true (2),
.cycle 20 1 false (4),
.last 14 (1,true),
.cycle 22 1 false (4),
.cycle 20 1 false (4),
.cycle 20 1 false (4),
.cycle 12 2 true (0),
.cycle 7 9 true (0),
.last 14 (1,true),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.cycle 7 9 true (0),
.cycle 2 15 true (0)
])
theorem kid10_part345_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part345) = true := by rfl

def kid10_part346 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 17, 17, 64],[16, 64, 64, 1, 16, 8, 64],64⟩
theorem kid10_part346_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part346) = true := by rfl

def kid10_part347 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 64, 64, 1, 16, 16, 64],64⟩
theorem kid10_part347_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part347) = true := by rfl

def kid10_part348 : Audit := .cycle 15 3 true (3)
theorem kid10_part348_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part348) = true := by rfl

def kid10_part324 : Audit := .split 12 (5,true) (byMove [(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339),(kid10_part340),(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345),(kid10_part346),(kid10_part347),(kid10_part348)])

theorem kid10_part324_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part324) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part325),(kid10_part326),(kid10_part327),(kid10_part328),(kid10_part329),(kid10_part330),(kid10_part331),(kid10_part332),(kid10_part333),(kid10_part334),(kid10_part335),(kid10_part336),(kid10_part337),(kid10_part338),(kid10_part339),(kid10_part340),(kid10_part341),(kid10_part342),(kid10_part343),(kid10_part344),(kid10_part345),(kid10_part346),(kid10_part347),(kid10_part348)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part325_checked

  · exact kid10_part331_checked

  · exact kid10_part337_checked

  · exact kid10_part343_checked

  · exact kid10_part326_checked

  · exact kid10_part332_checked

  · exact kid10_part338_checked

  · exact kid10_part344_checked

  · exact kid10_part327_checked

  · exact kid10_part333_checked

  · exact kid10_part339_checked

  · exact kid10_part345_checked

  · exact kid10_part328_checked

  · exact kid10_part334_checked

  · exact kid10_part340_checked

  · exact kid10_part346_checked

  · exact kid10_part329_checked

  · exact kid10_part335_checked

  · exact kid10_part341_checked

  · exact kid10_part347_checked

  · exact kid10_part330_checked

  · exact kid10_part336_checked

  · exact kid10_part342_checked

  · exact kid10_part348_checked

def kid10_part349 : Audit := .cycle 8 3 true (3)
theorem kid10_part349_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part349) = true := by rfl

def kid10_part350 : Audit := .split 10 (1,true) (byMove [
.cycle 8 4 true (3),
.cycle 1 11 true (1),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 1 12 true (1),
.cycle 22 3 false (2),
.cycle 30 1 false (2),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.last 13 (5,true),
.cycle 1 12 true (1)
]),
.cycle 0 12 true (0),
.cycle 7 4 true (3),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 1 12 true (1),
.cycle 22 3 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 1 12 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 7 11 true (3),
.cycle 3 8 true (1),
.cycle 8 3 true (3),
.cycle 1 11 true (1),
.cycle 6 5 true (2),
.split 13 (2,true) (byMove [
.cycle 25 7 false (1),
.cycle 18 3 false (0),
.cycle 29 1 false (1),
.cycle 10 6 true (2),
.cycle 25 7 false (1),
.last 14 (5,true),
.cycle 8 7 true (2),
.cycle 1 16 true (1),
.cycle 7 17 true (2),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 14 (5,true),
.cycle 7 9 true (2),
.cycle 18 3 false (0),
.cycle 5 11 true (1),
.cycle 5 9 true (1),
.cycle 7 9 true (2),
.last 14 (5,true),
.cycle 7 18 true (1),
.cycle 20 5 false (2),
.cycle 2 13 true (1),
.cycle 0 15 true (0),
.cycle 7 18 true (1),
.last 14 (5,true)
]),
.split 11 (2,true) (byMove [
.cycle 32 13 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.last 15 (5,true),
.cycle 8 5 true (3),
.cycle 0 15 true (0),
.cycle 33 1 false (9),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true),
.cycle 25 3 false (5),
.cycle 5 11 true (1),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.last 18 (5,true),
.cycle 8 5 true (3),
.cycle 10 2 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true)
]),
.cycle 8 5 true (3),
.cycle 7 5 true (3),
.split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.last 14 (2,true),
.cycle 8 5 true (3),
.cycle 9 4 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 1 13 true (1),
.cycle 25 3 false (5),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.cycle 18 3 false (0),
.cycle 8 5 true (3),
.cycle 10 2 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 1 13 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.split 12 (5,true) (byMove [
.cycle 7 10 true (3),
.cycle 8 12 true (2),
.last 13 (2,true),
.cycle 10 5 true (3),
.cycle 7 10 true (3),
.cycle 0 18 true (0),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 7 8 true (3),
.cycle 7 8 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 7 10 true (2),
.cycle 8 6 true (3),
.cycle 10 3 true (4),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1)
]),
.cycle 1 11 true (1)
])
theorem kid10_part350_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part350) = true := by rfl

def kid10_part351 : Audit := .split 10 (2,true) (byMove [
.cycle 8 4 true (3),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 2 11 true (1),
.cycle 6 8 true (2),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.last 13 (5,true),
.cycle 2 11 true (1)
]),
.cycle 25 1 false (3),
.cycle 0 12 true (0),
.cycle 7 4 true (3),
.split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 2 11 true (1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 2 11 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 7 11 true (3),
.cycle 3 8 true (1),
.cycle 8 3 true (3),
.cycle 2 10 true (1),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.cycle 28 9 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 0 15 true (0),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.cycle 10 4 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true),
.cycle 7 9 true (2),
.cycle 18 3 false (0),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.last 18 (5,true),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true)
]),
.cycle 8 7 true (2),
.cycle 8 5 true (3),
.cycle 7 5 true (3),
.split 11 (5,true) (byMove [
.cycle 28 9 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 0 15 true (0),
.cycle 8 5 true (3),
.last 12 (1,true),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 2 12 true (1),
.last 13 (1,true),
.last 18 (1,true),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.cycle 18 3 false (0),
.cycle 8 5 true (3),
.last 12 (1,true),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 2 12 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.split 12 (5,true) (byMove [
.cycle 7 10 true (3),
.last 13 (1,true),
.cycle 35 1 false (5),
.last 15 (1,true),
.cycle 7 10 true (3),
.cycle 7 14 true (2),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 2 13 true (1),
.cycle 7 8 true (3),
.last 13 (1,true),
.cycle 7 8 true (3),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 7 10 true (2),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 2 13 true (1)
]),
.cycle 2 10 true (1)
])
theorem kid10_part351_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part351) = true := by rfl

def kid10_part352 : Audit := .cycle 0 11 true (0)
theorem kid10_part352_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part352) = true := by rfl

def kid10_part353 : Audit := .cycle 7 3 true (3)
theorem kid10_part353_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part353) = true := by rfl

def kid10_part354 : Audit := .split 10 (5,true) (byMove [
.cycle 8 4 true (3),
.split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.cycle 6 8 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.cycle 0 22 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 0 17 true (0),
.cycle 12 1 true (4)
]),
.split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 25 1 false (3),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.cycle 12 1 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (3),
.cycle 12 1 true (4),
.last 13 (1,true),
.last 14 (1,true),
.cycle 0 14 true (0),
.cycle 22 1 false (2),
.cycle 18 4 false (2),
.cycle 20 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (3),
.cycle 30 1 false (4),
.cycle 12 1 true (4)
]),
.cycle 0 12 true (0),
.cycle 7 4 true (3),
.cycle 12 1 true (2),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 7 11 true (3),
.cycle 3 8 true (1),
.cycle 8 3 true (3),
.cycle 11 1 true (5),
.cycle 6 5 true (2),
.split 11 (1,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.last 18 (2,true),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 14 (2,true),
.cycle 7 9 true (2),
.last 13 (2,true),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.last 20 (2,true),
.cycle 8 5 true (3),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 10 2 true (3)
]),
.split 11 (2,true) (byMove [
.cycle 32 13 false (2),
.cycle 0 15 true (0),
.cycle 26 1 false (4),
.cycle 21 1 false (1),
.cycle 17 4 false (1),
.last 20 (1,true),
.cycle 8 5 true (3),
.last 12 (1,true),
.cycle 33 1 false (9),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 0 15 true (0),
.last 13 (1,true),
.last 14 (1,true),
.cycle 8 7 true (2),
.cycle 23 1 false (3),
.cycle 21 4 false (5),
.cycle 26 3 false (5),
.cycle 8 5 true (3),
.last 12 (1,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 10 2 true (3)
]),
.cycle 8 5 true (3),
.cycle 7 5 true (3),
.cycle 17 3 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 11 1 true (5)
])
theorem kid10_part354_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part354) = true := by rfl

def kid10_part258 : Audit := .split 9 (5,false) (byMove [(kid10_part259),(kid10_part260),(kid10_part261),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part296),(kid10_part321),(kid10_part322),(kid10_part323),(kid10_part324),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354)])

theorem kid10_part258_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (kid10_part258) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid10_part259),(kid10_part260),(kid10_part261),(kid10_part262),(kid10_part263),(kid10_part264),(kid10_part265),(kid10_part266),(kid10_part267),(kid10_part268),(kid10_part269),(kid10_part270),(kid10_part271),(kid10_part296),(kid10_part321),(kid10_part322),(kid10_part323),(kid10_part324),(kid10_part349),(kid10_part350),(kid10_part351),(kid10_part352),(kid10_part353),(kid10_part354)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part259_checked

  · exact kid10_part265_checked

  · exact kid10_part271_checked

  · exact kid10_part349_checked

  · exact kid10_part260_checked

  · exact kid10_part266_checked

  · exact kid10_part296_checked

  · exact kid10_part350_checked

  · exact kid10_part261_checked

  · exact kid10_part267_checked

  · exact kid10_part321_checked

  · exact kid10_part351_checked

  · exact kid10_part262_checked

  · exact kid10_part268_checked

  · exact kid10_part322_checked

  · exact kid10_part352_checked

  · exact kid10_part263_checked

  · exact kid10_part269_checked

  · exact kid10_part323_checked

  · exact kid10_part353_checked

  · exact kid10_part264_checked

  · exact kid10_part270_checked

  · exact kid10_part324_checked

  · exact kid10_part354_checked

def kid10_part355 : Audit := .cycle 0 9 true (0)
theorem kid10_part355_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,0⟩)) (kid10_part355) = true := by rfl

def kid10_part356 : Audit := .cycle 1 8 true (1)
theorem kid10_part356_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,1⟩)) (kid10_part356) = true := by rfl

def kid10_part357 : Audit := .cycle 2 7 true (1)
theorem kid10_part357_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,2⟩)) (kid10_part357) = true := by rfl

def kid10_part358 : Audit := .cycle 8 4 true (4)
theorem kid10_part358_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,3⟩)) (kid10_part358) = true := by rfl

def kid10_part359 : Audit := .cycle 8 1 true (4)
theorem kid10_part359_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,4⟩)) (kid10_part359) = true := by rfl

def kid10_part361 : Audit := .cycle 8 3 true (4)
theorem kid10_part361_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid10_part361) = true := by rfl

def kid10_part362 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.cycle 21 3 false (2),
.cycle 1 11 true (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (4),
.cycle 1 11 true (1),
.cycle 6 7 true (2),
.split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.cycle 20 3 false (0),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 20 3 false (0),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 14 true (2),
.last 18 (5,true)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.cycle 24 3 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 1 14 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 1 13 true (1),
.cycle 6 7 true (2),
.cycle 27 3 false (5),
.last 13 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 8 11 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 10 true (3),
.cycle 7 9 true (3)
]),
.cycle 0 15 true (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (4),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part362_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid10_part362) = true := by rfl

def kid10_part363 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.cycle 21 3 false (2),
.cycle 25 1 false (3),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (4),
.cycle 29 1 false (7),
.split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 24 3 false (2),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.cycle 7 11 true (2),
.cycle 27 3 false (5),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 10 true (2),
.cycle 6 9 true (2)
]),
.split 13 (1,true) (byMove [
.last 20 (5,true),
.cycle 0 17 true (0),
.cycle 30 1 false (4),
.last 20 (5,true),
.last 22 (5,true),
.last 22 (5,true),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 7 11 true (2),
.cycle 20 3 false (0),
.cycle 8 9 true (2),
.cycle 27 1 false (3),
.last 15 (5,true),
.cycle 31 1 false (3),
.cycle 8 7 true (3),
.cycle 1 14 true (1),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.split 12 (5,true) (byMove [
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 24 3 false (2),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 2 12 true (1),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 27 3 false (5),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 31 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 7 10 true (3),
.cycle 7 9 true (3)
]),
.cycle 26 1 false (4),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (4),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part363_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid10_part363) = true := by rfl

def kid10_part364 : Audit := .cycle 0 11 true (0)
theorem kid10_part364_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid10_part364) = true := by rfl

def kid10_part365 : Audit := .cycle 7 3 true (3)
theorem kid10_part365_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid10_part365) = true := by rfl

def kid10_part366 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.cycle 21 3 false (2),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 29 1 false (9),
.cycle 25 1 false (7),
.cycle 8 3 true (4),
.cycle 17 1 false (1),
.split 12 (1,true) (byMove [
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 24 3 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.cycle 29 5 false (3),
.cycle 6 7 true (2),
.last 15 (2,true),
.last 13 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 27 3 false (5),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.cycle 6 10 true (2),
.cycle 6 9 true (2)
]),
.split 12 (2,true) (byMove [
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 29 1 false (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 20 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 7 13 true (3),
.cycle 3 10 true (1),
.cycle 8 5 true (3),
.last 26 (1,true),
.cycle 6 7 true (2),
.last 13 (1,true),
.cycle 8 9 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 20 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 8 true (3),
.last 16 (1,true),
.last 15 (1,true)
]),
.cycle 0 13 true (0),
.cycle 22 1 false (4),
.cycle 7 7 true (3),
.cycle 15 1 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 6 true (4),
.cycle 8 3 true (4),
.cycle 9 2 true (4)
])
theorem kid10_part366_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid10_part366) = true := by rfl

def kid10_part367 : Audit := .cycle 0 10 true (0)
theorem kid10_part367_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid10_part367) = true := by rfl

def kid10_part368 : Audit := .cycle 1 9 true (1)
theorem kid10_part368_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid10_part368) = true := by rfl

def kid10_part369 : Audit := .cycle 7 10 true (3)
theorem kid10_part369_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid10_part369) = true := by rfl

def kid10_part370 : Audit := .cycle 3 7 true (1)
theorem kid10_part370_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid10_part370) = true := by rfl

def kid10_part371 : Audit := .cycle 8 2 true (4)
theorem kid10_part371_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid10_part371) = true := by rfl

def kid10_part372 : Audit := .cycle 9 1 true (5)
theorem kid10_part372_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid10_part372) = true := by rfl

def kid10_part373 : Audit := .cycle 6 4 true (2)
theorem kid10_part373_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid10_part373) = true := by rfl

def kid10_part375 : Audit := .split 13 (2,true) (byMove [
.cycle 8 7 true (3),
.cycle 8 8 true (3),
.cycle 33 1 false (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 12 3 true (4),
.cycle 6 8 true (2),
.last 17 (5,true),
.cycle 5 12 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid10_part375_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid10_part375) = true := by rfl

def kid10_part376 : Audit := .cycle 0 14 true (0)
theorem kid10_part376_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid10_part376) = true := by rfl

def kid10_part377 : Audit := .cycle 26 1 false (6)
theorem kid10_part377_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid10_part377) = true := by rfl

def kid10_part378 : Audit := .split 19 (5,true) (byMove [
.cycle 24 1 false (4),
.cycle 21 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 24 1 false (4),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 16 21 true (2),
.cycle 31 1 false (7),
.cycle 28 1 false (6),
.cycle 18 8 true (4),
.last 22 (2,true),
.cycle 25 1 false (5),
.cycle 21 1 false (3),
.last 20 (2,true),
.cycle 25 1 false (5),
.cycle 25 1 false (5),
.last 23 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 17 13 true (3),
.cycle 0 27 true (0),
.cycle 0 26 true (0)
])
theorem kid10_part378_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid10_part378) = true := by rfl

def kid10_part379 : Audit := .split 22 (5,true) (byMove [
.cycle 33 3 false (6),
.cycle 23 3 false (1),
.last 23 (2,true),
.cycle 33 3 false (6),
.cycle 33 3 false (6),
.last 26 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 2048, 4096, 128, 256, 8, 16, 2048, 17, 4096],[16, 17, 4096, 1, 16, 1, 16, 2048, 4096, 1, 16, 1, 4096],4128⟩,
.cycle 16 53 true (0),
.last 23 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 2048, 4096, 128, 256, 8, 16, 2048, 25, 4096],[16, 25, 4096, 1, 16, 8, 16, 2048, 4096, 1, 16, 8, 4096],4128⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 16, 2048, 4096, 128, 256, 8, 16, 2048, 16, 4096],[16, 16, 4096, 1, 16, 16, 16, 2048, 4096, 1, 16, 16, 4096],4128⟩,
.last 28 (2,true),
.cycle 28 3 false (7),
.cycle 23 3 false (1),
.last 23 (2,true),
.cycle 28 3 false (7),
.cycle 28 3 false (7),
.last 26 (2,true),
.cycle 7 18 true (0),
.cycle 23 11 true (2),
.last 23 (2,true),
.cycle 5 18 true (0),
.cycle 7 18 true (0),
.cycle 25 5 true (4)
])
theorem kid10_part379_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid10_part379) = true := by rfl

def kid10_part380 : Audit := .split 13 (2,true) (byMove [
.cycle 25 7 false (1),
.cycle 16 4 false (0),
.cycle 29 1 false (1),
.cycle 0 19 true (0),
.cycle 25 7 false (1),
.last 14 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 7 12 true (2),
.last 15 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.cycle 16 4 false (0),
.last 19 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid10_part380_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid10_part380) = true := by rfl

def kid10_part381 : Audit := .cycle 8 4 true (4)
theorem kid10_part381_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid10_part381) = true := by rfl

def kid10_part382 : Audit := .cycle 1 11 true (1)
theorem kid10_part382_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid10_part382) = true := by rfl

def kid10_part383 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.last 15 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 7 14 true (3),
.cycle 10 4 true (4),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.last 13 (5,true),
.last 15 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part383_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid10_part383) = true := by rfl

def kid10_part384 : Audit := .cycle 0 12 true (0)
theorem kid10_part384_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid10_part384) = true := by rfl

def kid10_part385 : Audit := .cycle 7 4 true (3)
theorem kid10_part385_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid10_part385) = true := by rfl

def kid10_part386 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.last 14 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.last 14 (2,true),
.last 16 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.cycle 7 8 true (3),
.last 14 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part386_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid10_part386) = true := by rfl

def kid10_part387 : Audit := .cycle 7 8 true (3)
theorem kid10_part387_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid10_part387) = true := by rfl

def kid10_part388 : Audit := .split 12 (2,true) (byMove [
.last 15 (5,true),
.cycle 20 3 false (0),
.last 23 (5,true),
.cycle 10 6 true (3),
.last 15 (5,true),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 1 15 true (1),
.cycle 7 16 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 7 8 true (3),
.cycle 20 3 false (0),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 24 5 false (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
])
theorem kid10_part388_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid10_part388) = true := by rfl

def kid10_part389 : Audit := .cycle 8 6 true (3)
theorem kid10_part389_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid10_part389) = true := by rfl

def kid10_part390 : Audit := .cycle 23 1 false (5)
theorem kid10_part390_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid10_part390) = true := by rfl

def kid10_part391 : Audit := .split 12 (5,true) (byMove [
.cycle 8 9 true (3),
.cycle 24 3 false (2),
.last 13 (2,true),
.cycle 7 10 true (3),
.cycle 7 9 true (3),
.last 16 (2,true),
.cycle 8 6 true (3),
.cycle 1 15 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 16 (2,true),
.cycle 7 8 true (3),
.cycle 28 3 false (6),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 16 (2,true),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 7 11 true (3)
])
theorem kid10_part391_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid10_part391) = true := by rfl

def kid10_part392 : Audit := .split 13 (2,true) (byMove [
.last 16 (5,true),
.cycle 16 4 false (0),
.last 22 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 6 8 true (2),
.cycle 16 6 false (2),
.cycle 7 20 true (2),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 14 (5,true),
.cycle 7 10 true (2),
.cycle 16 4 false (0),
.cycle 7 12 true (1),
.cycle 7 10 true (2),
.cycle 7 10 true (2),
.last 14 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.last 14 (5,true)
])
theorem kid10_part392_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid10_part392) = true := by rfl

def kid10_part393 : Audit := .cycle 8 4 true (4)
theorem kid10_part393_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid10_part393) = true := by rfl

def kid10_part394 : Audit := .cycle 1 11 true (1)
theorem kid10_part394_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid10_part394) = true := by rfl

def kid10_part395 : Audit := .split 11 (2,true) (byMove [
.cycle 8 5 true (4),
.cycle 2 11 true (1),
.cycle 29 1 false (5),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 11 3 true (5),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.cycle 8 8 true (3),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part395_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid10_part395) = true := by rfl

def kid10_part396 : Audit := .cycle 0 12 true (0)
theorem kid10_part396_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid10_part396) = true := by rfl

def kid10_part397 : Audit := .cycle 7 4 true (3)
theorem kid10_part397_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid10_part397) = true := by rfl

def kid10_part398 : Audit := .split 11 (5,true) (byMove [
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 15 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.last 14 (2,true),
.cycle 6 6 true (2),
.cycle 10 2 true (4),
.last 12 (2,true),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.last 15 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part398_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid10_part398) = true := by rfl

def kid10_part374 : Audit := .split 10 (1,true) (byMove [(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398)])

theorem kid10_part374_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid10_part374) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid10_part375),(kid10_part376),(kid10_part377),(kid10_part378),(kid10_part379),(kid10_part380),(kid10_part381),(kid10_part382),(kid10_part383),(kid10_part384),(kid10_part385),(kid10_part386),(kid10_part387),(kid10_part388),(kid10_part389),(kid10_part390),(kid10_part391),(kid10_part392),(kid10_part393),(kid10_part394),(kid10_part395),(kid10_part396),(kid10_part397),(kid10_part398)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part375_checked

  · exact kid10_part381_checked

  · exact kid10_part387_checked

  · exact kid10_part393_checked

  · exact kid10_part376_checked

  · exact kid10_part382_checked

  · exact kid10_part388_checked

  · exact kid10_part394_checked

  · exact kid10_part377_checked

  · exact kid10_part383_checked

  · exact kid10_part389_checked

  · exact kid10_part395_checked

  · exact kid10_part378_checked

  · exact kid10_part384_checked

  · exact kid10_part390_checked

  · exact kid10_part396_checked

  · exact kid10_part379_checked

  · exact kid10_part385_checked

  · exact kid10_part391_checked

  · exact kid10_part397_checked

  · exact kid10_part380_checked

  · exact kid10_part386_checked

  · exact kid10_part392_checked

  · exact kid10_part398_checked

def kid10_part400 : Audit := .cycle 8 7 true (3)
theorem kid10_part400_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid10_part400) = true := by rfl

def kid10_part401 : Audit := .cycle 0 14 true (0)
theorem kid10_part401_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid10_part401) = true := by rfl

def kid10_part402 : Audit := .cycle 26 1 false (6)
theorem kid10_part402_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid10_part402) = true := by rfl

def kid10_part403 : Audit := .split 19 (5,true) (byMove [
.cycle 24 1 false (4),
.last 20 (1,true),
.cycle 21 1 false (3),
.cycle 0 21 true (0),
.cycle 24 1 false (4),
.cycle 0 24 true (0),
.cycle 0 20 true (0),
.cycle 16 21 true (2),
.cycle 31 1 false (7),
.cycle 28 1 false (6),
.cycle 18 8 true (4),
.cycle 0 23 true (0),
.cycle 25 1 false (5),
.last 20 (1,true),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 25 1 false (5),
.cycle 29 1 false (5),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 17 13 true (3),
.last 25 (1,true),
.last 24 (1,true)
])
theorem kid10_part403_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid10_part403) = true := by rfl

def kid10_part404 : Audit := .split 22 (5,true) (byMove [
.cycle 33 3 false (6),
.last 23 (1,true),
.cycle 23 3 false (1),
.last 25 (1,true),
.cycle 33 3 false (6),
.cycle 34 3 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 49, 1, 16, 1, 64],64⟩,
.last 23 (1,true),
.cycle 52 3 false (9),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[16, 64, 57, 1, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 64, 49, 1, 16, 16, 64],64⟩,
.cycle 0 29 true (0),
.cycle 28 3 false (7),
.last 23 (1,true),
.cycle 23 3 false (1),
.cycle 28 3 false (7),
.cycle 28 3 false (7),
.cycle 32 3 false (7),
.cycle 7 18 true (0),
.last 23 (1,true),
.cycle 23 11 true (2),
.cycle 5 18 true (0),
.cycle 7 18 true (0),
.cycle 25 5 true (4)
])
theorem kid10_part404_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid10_part404) = true := by rfl

def kid10_part405 : Audit := .split 15 (1,true) (byMove [
.cycle 8 9 true (2),
.cycle 1 16 true (1),
.cycle 0 20 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 7 16 true (2),
.cycle 3 13 true (1),
.last 27 (5,true),
.cycle 0 19 true (0),
.cycle 6 10 true (2),
.last 19 (5,true),
.cycle 10 6 true (2),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 11 true (2),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid10_part405_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid10_part405) = true := by rfl

def kid10_part406 : Audit := .cycle 8 4 true (4)
theorem kid10_part406_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid10_part406) = true := by rfl

def kid10_part407 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 8 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.last 13 (5,true),
.cycle 8 8 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part407_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid10_part407) = true := by rfl

def kid10_part408 : Audit := .cycle 33 1 false (11)
theorem kid10_part408_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid10_part408) = true := by rfl

def kid10_part409 : Audit := .cycle 0 12 true (0)
theorem kid10_part409_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid10_part409) = true := by rfl

def kid10_part410 : Audit := .cycle 7 4 true (3)
theorem kid10_part410_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid10_part410) = true := by rfl

def kid10_part411 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.last 13 (1,true),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.cycle 7 8 true (3),
.cycle 8 8 true (3),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part411_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid10_part411) = true := by rfl

def kid10_part412 : Audit := .split 12 (1,true) (byMove [
.last 15 (5,true),
.cycle 7 14 true (2),
.cycle 24 3 false (2),
.cycle 0 17 true (0),
.last 15 (5,true),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 7 16 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 7 8 true (3),
.cycle 7 12 true (2),
.cycle 28 3 false (6),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 13 (5,true),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.cycle 6 8 true (2),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 13 (5,true)
])
theorem kid10_part412_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid10_part412) = true := by rfl

def kid10_part413 : Audit := .split 13 (1,true) (byMove [
.last 20 (5,true),
.cycle 8 10 true (2),
.cycle 31 1 false (5),
.last 20 (5,true),
.last 22 (5,true),
.last 19 (5,true),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true),
.cycle 7 12 true (2),
.cycle 20 3 false (0),
.cycle 5 10 true (1),
.cycle 28 1 false (4),
.last 15 (5,true),
.cycle 7 12 true (1),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 12 2 true (3),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 14 (5,true)
])
theorem kid10_part413_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid10_part413) = true := by rfl

def kid10_part414 : Audit := .cycle 8 6 true (3)
theorem kid10_part414_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid10_part414) = true := by rfl

def kid10_part415 : Audit := .cycle 23 1 false (5)
theorem kid10_part415_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid10_part415) = true := by rfl

def kid10_part416 : Audit := .split 12 (5,true) (byMove [
.cycle 8 9 true (3),
.last 13 (1,true),
.cycle 24 3 false (2),
.last 15 (1,true),
.cycle 7 9 true (3),
.cycle 28 19 false (4),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 7 16 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 7 8 true (3),
.last 13 (1,true),
.cycle 28 3 false (6),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 7 12 true (1),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 7 8 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 7 11 true (3)
])
theorem kid10_part416_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid10_part416) = true := by rfl

def kid10_part417 : Audit := .cycle 5 8 true (1)
theorem kid10_part417_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid10_part417) = true := by rfl

def kid10_part418 : Audit := .cycle 8 4 true (4)
theorem kid10_part418_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid10_part418) = true := by rfl

def kid10_part419 : Audit := .split 11 (1,true) (byMove [
.cycle 8 5 true (4),
.cycle 1 12 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.cycle 26 5 false (2),
.cycle 10 2 true (4),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part419_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid10_part419) = true := by rfl

def kid10_part420 : Audit := .cycle 2 10 true (1)
theorem kid10_part420_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid10_part420) = true := by rfl

def kid10_part421 : Audit := .cycle 0 12 true (0)
theorem kid10_part421_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid10_part421) = true := by rfl

def kid10_part422 : Audit := .cycle 7 4 true (3)
theorem kid10_part422_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid10_part422) = true := by rfl

def kid10_part423 : Audit := .split 11 (5,true) (byMove [
.cycle 8 5 true (4),
.last 12 (1,true),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 0 16 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 0 15 true (0),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 10 2 true (4),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.cycle 5 10 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part423_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid10_part423) = true := by rfl

def kid10_part399 : Audit := .split 10 (2,true) (byMove [(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409),(kid10_part410),(kid10_part411),(kid10_part412),(kid10_part413),(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418),(kid10_part419),(kid10_part420),(kid10_part421),(kid10_part422),(kid10_part423)])

theorem kid10_part399_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid10_part399) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid10_part400),(kid10_part401),(kid10_part402),(kid10_part403),(kid10_part404),(kid10_part405),(kid10_part406),(kid10_part407),(kid10_part408),(kid10_part409),(kid10_part410),(kid10_part411),(kid10_part412),(kid10_part413),(kid10_part414),(kid10_part415),(kid10_part416),(kid10_part417),(kid10_part418),(kid10_part419),(kid10_part420),(kid10_part421),(kid10_part422),(kid10_part423)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part400_checked

  · exact kid10_part406_checked

  · exact kid10_part412_checked

  · exact kid10_part418_checked

  · exact kid10_part401_checked

  · exact kid10_part407_checked

  · exact kid10_part413_checked

  · exact kid10_part419_checked

  · exact kid10_part402_checked

  · exact kid10_part408_checked

  · exact kid10_part414_checked

  · exact kid10_part420_checked

  · exact kid10_part403_checked

  · exact kid10_part409_checked

  · exact kid10_part415_checked

  · exact kid10_part421_checked

  · exact kid10_part404_checked

  · exact kid10_part410_checked

  · exact kid10_part416_checked

  · exact kid10_part422_checked

  · exact kid10_part405_checked

  · exact kid10_part411_checked

  · exact kid10_part417_checked

  · exact kid10_part423_checked

def kid10_part424 : Audit := .cycle 8 4 true (4)
theorem kid10_part424_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid10_part424) = true := by rfl

def kid10_part425 : Audit := .cycle 7 4 true (3)
theorem kid10_part425_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid10_part425) = true := by rfl

def kid10_part427 : Audit := .split 13 (2,true) (byMove [
.cycle 8 7 true (3),
.last 14 (1,true),
.cycle 33 1 false (3),
.cycle 0 15 true (0),
.cycle 7 7 true (3),
.cycle 8 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 14 true (3),
.cycle 3 11 true (1),
.cycle 8 6 true (3),
.cycle 8 16 true (3),
.cycle 6 8 true (2),
.last 14 (1,true),
.cycle 5 12 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 8 11 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 8 9 true (3),
.cycle 8 13 true (3),
.cycle 8 12 true (3)
])
theorem kid10_part427_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid10_part427) = true := by rfl

def kid10_part428 : Audit := .cycle 0 14 true (0)
theorem kid10_part428_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid10_part428) = true := by rfl

def kid10_part429 : Audit := .cycle 26 1 false (6)
theorem kid10_part429_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid10_part429) = true := by rfl

def kid10_part430 : Audit := .cycle 0 21 true (0)
theorem kid10_part430_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid10_part430) = true := by rfl

def kid10_part431 : Audit := .cycle 33 3 false (6)
theorem kid10_part431_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid10_part431) = true := by rfl

def kid10_part432 : Audit := .cycle 15 1 false (-1)
theorem kid10_part432_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid10_part432) = true := by rfl

def kid10_part433 : Audit := .cycle 8 4 true (4)
theorem kid10_part433_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid10_part433) = true := by rfl

def kid10_part434 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 36 1 false (12),
.cycle 6 8 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.cycle 1 13 true (1),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part434_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid10_part434) = true := by rfl

def kid10_part435 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 25 1 false (5),
.cycle 8 4 true (4),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 26 1 false (8),
.last 13 (1,true),
.last 14 (1,true),
.cycle 0 14 true (0),
.cycle 26 1 false (6),
.cycle 7 14 true (3),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part435_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid10_part435) = true := by rfl

def kid10_part436 : Audit := .cycle 0 12 true (0)
theorem kid10_part436_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid10_part436) = true := by rfl

def kid10_part437 : Audit := .cycle 7 4 true (3)
theorem kid10_part437_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid10_part437) = true := by rfl

def kid10_part438 : Audit := .cycle 25 1 false (7)
theorem kid10_part438_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid10_part438) = true := by rfl

def kid10_part439 : Audit := .split 12 (1,true) (byMove [
.cycle 6 10 true (2),
.cycle 7 14 true (2),
.last 13 (2,true),
.cycle 0 17 true (0),
.cycle 6 10 true (2),
.cycle 24 3 false (2),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 7 15 true (3),
.cycle 7 8 true (3),
.last 15 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.cycle 28 3 false (6),
.cycle 8 6 true (3),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.cycle 6 8 true (2)
])
theorem kid10_part439_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid10_part439) = true := by rfl

def kid10_part440 : Audit := .split 12 (2,true) (byMove [
.last 16 (1,true),
.last 13 (1,true),
.last 24 (1,true),
.last 15 (1,true),
.last 16 (1,true),
.last 20 (1,true),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 7 16 true (3),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 19 (1,true),
.cycle 7 8 true (3),
.last 13 (1,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.cycle 7 8 true (3),
.last 20 (1,true),
.cycle 8 6 true (3),
.last 13 (1,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.cycle 7 6 true (3),
.last 14 (1,true)
])
theorem kid10_part440_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid10_part440) = true := by rfl

def kid10_part441 : Audit := .cycle 8 6 true (3)
theorem kid10_part441_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid10_part441) = true := by rfl

def kid10_part442 : Audit := .cycle 23 1 false (5)
theorem kid10_part442_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid10_part442) = true := by rfl

def kid10_part443 : Audit := .cycle 7 8 true (3)
theorem kid10_part443_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid10_part443) = true := by rfl

def kid10_part444 : Audit := .cycle 15 1 false (-1)
theorem kid10_part444_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid10_part444) = true := by rfl

def kid10_part445 : Audit := .cycle 8 4 true (4)
theorem kid10_part445_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid10_part445) = true := by rfl

def kid10_part446 : Audit := .split 11 (1,true) (byMove [
.cycle 8 5 true (4),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 1 16 true (1),
.cycle 6 6 true (2),
.last 14 (2,true),
.last 12 (2,true),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part446_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid10_part446) = true := by rfl

def kid10_part447 : Audit := .split 11 (2,true) (byMove [
.cycle 8 5 true (4),
.last 12 (1,true),
.cycle 29 1 false (5),
.cycle 0 13 true (0),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 12 true (3),
.cycle 3 9 true (1),
.cycle 8 4 true (4),
.cycle 2 15 true (1),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 8 8 true (3),
.cycle 8 6 true (4),
.cycle 7 6 true (3),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 8 7 true (4),
.cycle 8 4 true (4),
.cycle 9 3 true (4)
])
theorem kid10_part447_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid10_part447) = true := by rfl

def kid10_part448 : Audit := .cycle 0 12 true (0)
theorem kid10_part448_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid10_part448) = true := by rfl

def kid10_part449 : Audit := .cycle 7 4 true (3)
theorem kid10_part449_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid10_part449) = true := by rfl

def kid10_part450 : Audit := .cycle 9 3 true (4)
theorem kid10_part450_checked : zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid10_part450) = true := by rfl

def kid10_part426 : Audit := .split 10 (5,true) (byMove [(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437),(kid10_part438),(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450)])

theorem kid10_part426_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid10_part426) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid10_part427),(kid10_part428),(kid10_part429),(kid10_part430),(kid10_part431),(kid10_part432),(kid10_part433),(kid10_part434),(kid10_part435),(kid10_part436),(kid10_part437),(kid10_part438),(kid10_part439),(kid10_part440),(kid10_part441),(kid10_part442),(kid10_part443),(kid10_part444),(kid10_part445),(kid10_part446),(kid10_part447),(kid10_part448),(kid10_part449),(kid10_part450)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part427_checked

  · exact kid10_part433_checked

  · exact kid10_part439_checked

  · exact kid10_part445_checked

  · exact kid10_part428_checked

  · exact kid10_part434_checked

  · exact kid10_part440_checked

  · exact kid10_part446_checked

  · exact kid10_part429_checked

  · exact kid10_part435_checked

  · exact kid10_part441_checked

  · exact kid10_part447_checked

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

def kid10_part451 : Audit := .cycle 0 10 true (0)
theorem kid10_part451_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid10_part451) = true := by rfl

def kid10_part452 : Audit := .cycle 1 9 true (1)
theorem kid10_part452_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid10_part452) = true := by rfl

def kid10_part453 : Audit := .cycle 2 8 true (1)
theorem kid10_part453_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid10_part453) = true := by rfl

def kid10_part454 : Audit := .cycle 8 5 true (4)
theorem kid10_part454_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid10_part454) = true := by rfl

def kid10_part455 : Audit := .cycle 8 2 true (4)
theorem kid10_part455_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid10_part455) = true := by rfl

def kid10_part456 : Audit := .cycle 9 1 true (5)
theorem kid10_part456_checked : zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid10_part456) = true := by rfl

def kid10_part360 : Audit := .split 9 (5,false) (byMove [(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369),(kid10_part370),(kid10_part371),(kid10_part372),(kid10_part373),(kid10_part374),(kid10_part399),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part451),(kid10_part452),(kid10_part453),(kid10_part454),(kid10_part455),(kid10_part456)])

theorem kid10_part360_checked : zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (kid10_part360) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) 9 (5,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,true,4⟩) (4,false) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid10_part361),(kid10_part362),(kid10_part363),(kid10_part364),(kid10_part365),(kid10_part366),(kid10_part367),(kid10_part368),(kid10_part369),(kid10_part370),(kid10_part371),(kid10_part372),(kid10_part373),(kid10_part374),(kid10_part399),(kid10_part424),(kid10_part425),(kid10_part426),(kid10_part451),(kid10_part452),(kid10_part453),(kid10_part454),(kid10_part455),(kid10_part456)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part361_checked

  · exact kid10_part367_checked

  · exact kid10_part373_checked

  · exact kid10_part451_checked

  · exact kid10_part362_checked

  · exact kid10_part368_checked

  · exact kid10_part374_checked

  · exact kid10_part452_checked

  · exact kid10_part363_checked

  · exact kid10_part369_checked

  · exact kid10_part399_checked

  · exact kid10_part453_checked

  · exact kid10_part364_checked

  · exact kid10_part370_checked

  · exact kid10_part424_checked

  · exact kid10_part454_checked

  · exact kid10_part365_checked

  · exact kid10_part371_checked

  · exact kid10_part425_checked

  · exact kid10_part455_checked

  · exact kid10_part366_checked

  · exact kid10_part372_checked

  · exact kid10_part426_checked

  · exact kid10_part456_checked

def kid10 : Audit := .split 8 (4,false) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part6),(kid10_part79),(kid10_part80),(kid10_part81),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part133),(kid10_part182),(kid10_part255),(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360)])

theorem check10 : zipCheck 944 (child ⟨false,true,4⟩) (kid10) = true := by

  change (zipQueryOK 944 (child ⟨false,true,4⟩) 8 (4,false) && allMoves (fun mv => zipCheck 944 (refine (child ⟨false,true,4⟩) (4,false) (some mv)) (byMove [(kid10_part1),(kid10_part2),(kid10_part3),(kid10_part4),(kid10_part5),(kid10_part6),(kid10_part79),(kid10_part80),(kid10_part81),(kid10_part82),(kid10_part83),(kid10_part84),(kid10_part133),(kid10_part182),(kid10_part255),(kid10_part256),(kid10_part257),(kid10_part258),(kid10_part355),(kid10_part356),(kid10_part357),(kid10_part358),(kid10_part359),(kid10_part360)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid10_part1_checked

  · exact kid10_part79_checked

  · exact kid10_part133_checked

  · exact kid10_part355_checked

  · exact kid10_part2_checked

  · exact kid10_part80_checked

  · exact kid10_part182_checked

  · exact kid10_part356_checked

  · exact kid10_part3_checked

  · exact kid10_part81_checked

  · exact kid10_part255_checked

  · exact kid10_part357_checked

  · exact kid10_part4_checked

  · exact kid10_part82_checked

  · exact kid10_part256_checked

  · exact kid10_part358_checked

  · exact kid10_part5_checked

  · exact kid10_part83_checked

  · exact kid10_part257_checked

  · exact kid10_part359_checked

  · exact kid10_part6_checked

  · exact kid10_part84_checked

  · exact kid10_part258_checked

  · exact kid10_part360_checked

end BB6.Agent11Raw39B0RE
