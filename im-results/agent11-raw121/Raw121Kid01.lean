import Raw121Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid01_part2 : Audit := .cycle 0 13 false (4)
theorem kid01_part2_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part2) = true := by rfl

def kid01_part3 : Audit := .cycle 0 24 false (4)
theorem kid01_part3_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part3) = true := by rfl

def kid01_part4 : Audit := .split 11 (2,true) (byMove [
.cycle 14 1 false (0),
.cycle 0 13 false (4),
.cycle 14 1 false (0),
.cycle 0 15 false (4),
.cycle 0 15 false (4),
.split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 24 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 0 17 false (4),
.cycle 13 1 false (-1),
.cycle 38 1 false (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,false),
.cycle 20 1 false (0),
.cycle 0 15 false (4),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (0),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 0 15 false (4),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 22 1 false (0),
.cycle 11 3 true (1),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 25 false (5),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 37 1 false (1),
.cycle 0 15 true (0),
.cycle 12 1 true (2)
]),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 19 1 false (-1),
.cycle 54 1 false (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.last 31 (5,false),
.last 13 (5,false),
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 11 2 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 22 1 false (0),
.cycle 12 1 true (2)
])
])
theorem kid01_part4_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part4) = true := by rfl

def kid01_part5 : Audit := .cycle 15 1 false (-1)
theorem kid01_part5_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part5) = true := by rfl

def kid01_part6 : Audit := .cycle 0 29 false (4)
theorem kid01_part6_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part6) = true := by rfl

def kid01_part8 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 0 25 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 26 false (4),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 0 25 false (4),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 0 26 false (4),
.cycle 13 1 true (-1),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 0 18 false (4),
.cycle 14 1 false (-2),
.cycle 0 34 false (4),
.cycle 13 1 false (-1),
.cycle 0 28 false (4),
.cycle 1 13 false (4),
.cycle 0 24 false (4),
.cycle 12 7 false (1),
.cycle 0 16 false (4),
.cycle 13 1 true (-1)
])
theorem kid01_part8_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part8) = true := by rfl

def kid01_part9 : Audit := .cycle 0 13 false (4)
theorem kid01_part9_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part9) = true := by rfl

def kid01_part10 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 26 1 false (0),
.last 13 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 0 17 false (4),
.cycle 13 1 false (-1),
.last 37 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.last 19 (5,false),
.cycle 0 15 false (4),
.last 13 (5,false)
])
theorem kid01_part10_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part10) = true := by rfl

def kid01_part11 : Audit := .cycle 0 15 false (4)
theorem kid01_part11_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part11) = true := by rfl

def kid01_part12 : Audit := .cycle 0 15 false (4)
theorem kid01_part12_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part12) = true := by rfl

def kid01_part13 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 12 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 12 13 false (2),
.cycle 13 1 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 0 18 false (4),
.cycle 14 1 false (-2),
.cycle 11 21 false (2),
.cycle 13 1 false (-1),
.cycle 11 15 false (4),
.cycle 1 13 false (4),
.cycle 12 11 false (2),
.cycle 13 7 false (1),
.cycle 0 16 false (4),
.cycle 13 1 true (-1)
])
theorem kid01_part13_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part13) = true := by rfl

def kid01_part14 : Audit := .cycle 0 12 true (0)
theorem kid01_part14_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part14) = true := by rfl

def kid01_part15 : Audit := .cycle 1 11 true (1)
theorem kid01_part15_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part15) = true := by rfl

def kid01_part16 : Audit := .cycle 6 12 true (0)
theorem kid01_part16_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part16) = true := by rfl

def kid01_part17 : Audit := .cycle 21 1 false (1)
theorem kid01_part17_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part17) = true := by rfl

def kid01_part18 : Audit := .cycle 1 12 true (1)
theorem kid01_part18_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part18) = true := by rfl

def kid01_part19 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (-2),
.cycle 0 15 false (4),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 17 4 false (1),
.last 14 (2,true),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 25 false (5),
.cycle 17 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 27 7 false (3),
.cycle 0 15 true (0),
.cycle 12 1 true (2)
])
theorem kid01_part19_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part19) = true := by rfl

def kid01_part20 : Audit := .split 13 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[8, 20, 64, 16, 16, 20, 64],64⟩,
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 16 false (0),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.last 15 (2,true),
.cycle 0 18 true (-1),
.cycle 14 1 false (0),
.cycle 32 16 false (0),
.cycle 19 1 true (-1),
.cycle 12 4 false (0),
.last 15 (2,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 3, 3, 3],[128, 256, 8, 0, 32768, 1024, 128, 256, 32768, 1024, 32768, 1073741824, 33554432, 67108864, 2097152, 1024, 32768, 268435456, 524288, 1048576, 2097152, 4195328, 1075871744, 1077936128, 524288, 1048576, 2097152, 4194304, 32768, 1073741824, 1073741824],[32768, 256, 1073741824, 1024, 1024, 1024, 32768, 1024, 1073741824, 1024, 1024, 268435456, 1073741824, 256, 1073741824, 268435456, 268435456, 1024, 1075871744, 1078985728, 1073741824, 4194304, 4194304, 1347421184, 32768, 1073741824, 1073741824, 4194304, 4194304, 1073741824, 1073741824],1878816768⟩,
.cycle 14 1 false (-2),
.cycle 38 24 false (0),
.cycle 13 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[10, 20, 64, 16, 16, 20, 64],64⟩,
.last 15 (2,true),
.cycle 30 14 false (0),
.cycle 23 7 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[8, 20, 64, 16, 16, 20, 64],64⟩,
.cycle 15 12 false (1)
])
theorem kid01_part20_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part20) = true := by rfl

def kid01_part21 : Audit := .split 15 (2,true) (byMove [
.last 21 (5,false),
.last 18 (5,false),
.cycle 19 1 false (-1),
.last 20 (5,false),
.last 20 (5,false),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 14 13 true (0),
.last 30 (5,false),
.cycle 3 13 false (4),
.last 30 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.last 18 (5,false),
.last 35 (5,false),
.last 29 (5,false),
.last 29 (5,false),
.cycle 11 5 false (1),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 2],[128, 256, 8, 4195344, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 134217728, 1073741824, 8192, 16384, 32768, 4260880, 1207992328, 1073741824, 2, 4, 134217728, 16, 1073741824, 1073741824, 8192, 16384, 32768, 1024, 8, 1073741824, 1073741824],[1073741824, 1048576, 64, 1024, 1024, 262144, 2, 1073741824, 262144, 4194304, 4194304, 1, 1074274434, 1074807044, 4096, 65536, 65536, 1074008129, 128, 256, 1, 16, 16, 1073741824, 1073741824, 256, 4096, 65536, 65536, 64, 1073741824],2012216190⟩,
.last 78 (5,false),
.last 28 (5,false),
.cycle 7 11 false (4),
.last 25 (5,false),
.last 16 (5,false)
])
theorem kid01_part21_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part21) = true := by rfl

def kid01_part22 : Audit := .split 12 (2,true) (byMove [
.cycle 0 22 false (4),
.last 53 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 14 (5,false),
.cycle 0 14 true (0),
.cycle 15 1 false (3),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 16 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 21 (5,false),
.last 13 (5,false),
.cycle 0 19 false (4),
.last 15 (5,false),
.cycle 2 12 true (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part22_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part22) = true := by rfl

def kid01_part23 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 29 1 false (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 30 1 false (-4),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.cycle 29 1 false (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 30 1 false (-2),
.cycle 17 1 true (-1),
.cycle 15 4 false (1),
.last 19 (2,true),
.cycle 0 22 false (4),
.cycle 18 1 false (-2),
.cycle 42 1 false (-4),
.cycle 17 1 false (-1),
.cycle 36 1 false (-2),
.cycle 1 17 false (4),
.cycle 28 1 false (-2),
.cycle 12 7 false (2),
.cycle 0 20 false (4),
.cycle 17 1 true (-1)
])
theorem kid01_part23_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part23) = true := by rfl

def kid01_part24 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 23 24 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 24 24 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.cycle 23 24 false (3),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 24 24 false (2),
.cycle 17 1 true (-1),
.cycle 15 4 false (1),
.last 19 (2,true),
.cycle 0 22 false (4),
.cycle 18 1 false (-2),
.cycle 18 24 false (2),
.cycle 17 1 false (-1),
.cycle 18 24 false (4),
.cycle 1 17 false (4),
.cycle 22 24 false (2),
.cycle 13 7 false (2),
.cycle 0 20 false (4),
.cycle 17 1 true (-1)
])
theorem kid01_part24_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part24) = true := by rfl

def kid01_part25 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 0 23 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[24, 28, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 0 20 true (-1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 0 36 false (4),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 0 34 false (4),
.cycle 14 1 false (-2),
.cycle 6 78 false (4),
.cycle 13 1 false (-1),
.cycle 12 3 false (0),
.cycle 9 42 false (4),
.last 14 (2,true),
.cycle 22 7 false (0),
.cycle 0 28 false (4),
.cycle 11 3 false (1)
])
theorem kid01_part25_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part25) = true := by rfl

def kid01_part26 : Audit := .cycle 0 12 true (0)
theorem kid01_part26_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part26) = true := by rfl

def kid01_part27 : Audit := .cycle 1 11 true (1)
theorem kid01_part27_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part27) = true := by rfl

def kid01_part28 : Audit := .cycle 2 10 true (1)
theorem kid01_part28_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part28) = true := by rfl

def kid01_part29 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 false (4),
.cycle 14 18 false (3),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 14 19 false (3),
.cycle 25 1 false (-1),
.cycle 0 26 true (-1),
.cycle 14 18 true (-1),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 14 19 false (3),
.cycle 25 1 true (-1),
.cycle 23 4 false (1),
.last 27 (2,true),
.cycle 0 30 false (4),
.cycle 26 1 false (-2),
.cycle 7 39 false (4),
.cycle 25 1 false (-1),
.cycle 7 33 false (4),
.cycle 1 25 false (4),
.cycle 14 17 false (3),
.cycle 19 7 false (2),
.cycle 0 28 false (4),
.cycle 25 1 true (-1)
])
theorem kid01_part29_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part29) = true := by rfl

def kid01_part30 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 0 29 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 30 false (4),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 0 29 false (4),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 0 30 false (4),
.cycle 15 1 true (-1),
.cycle 13 4 false (1),
.last 17 (2,true),
.cycle 0 20 false (4),
.cycle 16 1 false (-2),
.cycle 0 40 false (4),
.cycle 15 1 false (-1),
.cycle 0 34 false (4),
.cycle 1 15 false (4),
.cycle 0 28 false (4),
.cycle 12 7 false (2),
.cycle 0 18 false (4),
.cycle 15 1 true (-1)
])
theorem kid01_part30_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part30) = true := by rfl

def kid01_part31 : Audit := .split 12 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 0 29 false (4),
.last 13 (2,true),
.cycle 18 1 false (-2),
.cycle 0 34 false (4),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 16 4 false (0),
.last 17 (2,true),
.last 13 (2,true),
.cycle 26 1 false (-2),
.cycle 6 39 false (4),
.cycle 11 3 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 0 24 false (4),
.cycle 12 1 true (2)
])
theorem kid01_part31_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part31) = true := by rfl

def kid01_part7 : Audit := .split 11 (5,true) (byMove [(kid01_part8),(kid01_part9),(kid01_part10),(kid01_part11),(kid01_part12),(kid01_part13),(kid01_part14),(kid01_part15),(kid01_part16),(kid01_part17),(kid01_part18),(kid01_part19),(kid01_part20),(kid01_part21),(kid01_part22),(kid01_part23),(kid01_part24),(kid01_part25),(kid01_part26),(kid01_part27),(kid01_part28),(kid01_part29),(kid01_part30),(kid01_part31)])

theorem kid01_part7_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part7) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part8),(kid01_part9),(kid01_part10),(kid01_part11),(kid01_part12),(kid01_part13),(kid01_part14),(kid01_part15),(kid01_part16),(kid01_part17),(kid01_part18),(kid01_part19),(kid01_part20),(kid01_part21),(kid01_part22),(kid01_part23),(kid01_part24),(kid01_part25),(kid01_part26),(kid01_part27),(kid01_part28),(kid01_part29),(kid01_part30),(kid01_part31)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part8_checked

  · exact kid01_part14_checked

  · exact kid01_part20_checked

  · exact kid01_part26_checked

  · exact kid01_part9_checked

  · exact kid01_part15_checked

  · exact kid01_part21_checked

  · exact kid01_part27_checked

  · exact kid01_part10_checked

  · exact kid01_part16_checked

  · exact kid01_part22_checked

  · exact kid01_part28_checked

  · exact kid01_part11_checked

  · exact kid01_part17_checked

  · exact kid01_part23_checked

  · exact kid01_part29_checked

  · exact kid01_part12_checked

  · exact kid01_part18_checked

  · exact kid01_part24_checked

  · exact kid01_part30_checked

  · exact kid01_part13_checked

  · exact kid01_part19_checked

  · exact kid01_part25_checked

  · exact kid01_part31_checked

def kid01_part32 : Audit := .cycle 0 11 true (0)
theorem kid01_part32_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part32) = true := by rfl

def kid01_part33 : Audit := .cycle 1 10 true (1)
theorem kid01_part33_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part33) = true := by rfl

def kid01_part34 : Audit := .cycle 6 11 true (1)
theorem kid01_part34_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part34) = true := by rfl

def kid01_part35 : Audit := .cycle 3 8 true (1)
theorem kid01_part35_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part35) = true := by rfl

def kid01_part36 : Audit := .cycle 1 11 true (1)
theorem kid01_part36_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part36) = true := by rfl

def kid01_part37 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 0 30 false (4),
.split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.cycle 0 15 false (4),
.last 14 (2,true),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 29 1 false (1),
.cycle 17 1 false (1),
.cycle 12 2 true (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.split 13 (2,true) (byMove [
.cycle 10 4 true (2),
.cycle 0 25 false (4),
.cycle 18 1 false (0),
.cycle 0 31 false (4),
.cycle 0 31 false (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 11 3 true (2),
.last 15 (5,true),
.cycle 17 9 false (2),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.last 20 (5,true)
]),
.cycle 0 16 true (0),
.cycle 4 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 64, 16, 16, 64, 64],64⟩,
.split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.cycle 53 1 false (-1),
.last 14 (2,true),
.cycle 53 1 false (-3),
.cycle 47 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 37 1 false (3),
.cycle 37 1 false (3),
.cycle 25 1 false (5),
.cycle 19 1 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 15 1 false (-1),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 14 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 0 14 true (0),
.cycle 11 1 true (3)
])
theorem kid01_part37_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part37) = true := by rfl

def kid01_part38 : Audit := .cycle 12 3 false (0)
theorem kid01_part38_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part38) = true := by rfl

def kid01_part39 : Audit := .split 14 (2,true) (byMove [
.cycle 12 3 false (0),
.cycle 0 39 false (4),
.cycle 17 1 false (-1),
.cycle 0 45 false (4),
.cycle 0 45 false (4),
.split 15 (5,true) (byMove [
.cycle 0 39 false (4),
.cycle 0 32 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 35 false (4),
.last 16 (5,false),
.cycle 0 20 true (-1),
.cycle 13 23 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.last 16 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.last 40 (5,false),
.cycle 16 1 false (-2),
.cycle 9 25 false (3),
.last 16 (5,false),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.cycle 6 15 false (4),
.cycle 11 9 false (1),
.cycle 0 45 false (4),
.last 16 (5,false)
]),
.cycle 0 20 true (-1),
.cycle 15 14 true (1),
.cycle 0 19 true (-1),
.cycle 6 13 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[16, 28, 16, 16, 16, 64, 64],96⟩,
.split 15 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 32, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[48, 28, 32, 16, 16, 64, 64],64⟩,
.cycle 6 15 false (4),
.cycle 11 9 false (1),
.cycle 0 45 false (4),
.last 17 (5,true),
.cycle 0 20 true (-1),
.cycle 0 17 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 32, 16, 16, 64, 64],64⟩,
.cycle 0 19 true (-1),
.cycle 0 19 true (-1),
.last 16 (5,true),
.cycle 9 16 false (3),
.last 18 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 1032, 4096, 4096],[32, 256, 32, 1024, 1024, 4096, 1056, 1032, 32, 1024, 1024, 4096, 4096],6144⟩,
.cycle 6 13 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[48, 28, 32, 16, 16, 64, 64],64⟩,
.last 17 (5,true),
.cycle 13 24 true (-1),
.cycle 1 20 true (-1),
.cycle 16 14 true (2),
.cycle 17 9 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[48, 28, 32, 16, 16, 64, 64],64⟩,
.last 16 (5,true)
]),
.cycle 12 3 false (0),
.cycle 11 8 false (1),
.cycle 11 9 false (1),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.split 15 (5,true) (byMove [
.cycle 12 8 false (0),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 2, 64],96⟩,
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.last 16 (5,false),
.cycle 12 4 true (-1),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.last 17 (5,false),
.far true 1 ⟨0,[0, 0],[3, 11, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 11, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.last 17 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 9 false (1),
.cycle 16 1 false (-2),
.cycle 24 11 false (0),
.last 16 (5,false),
.cycle 10 12 false (2),
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 17 (5,false)
]),
.cycle 9 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[2, 4, 2, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[20, 28, 4, 16, 16, 64, 64],96⟩,
.cycle 4 11 false (4),
.cycle 11 5 false (1),
.split 15 (5,false) (byMove [
.cycle 10 12 false (2),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 0 20 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 2, 64],[62, 30, 32, 16, 16, 64, 64],64⟩,
.cycle 6 18 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[48, 28, 32, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[48, 28, 32, 16, 16, 64, 64],64⟩,
.last 16 (5,true),
.last 21 (5,true),
.cycle 11 5 false (1),
.last 17 (5,true),
.cycle 5 11 false (4),
.cycle 6 11 false (4),
.last 16 (5,true),
.cycle 9 16 false (3),
.cycle 9 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 32, 16, 16, 64, 64],64⟩,
.cycle 8 9 false (4),
.cycle 7 9 false (4),
.last 16 (5,true)
])
])
theorem kid01_part39_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part39) = true := by rfl

def kid01_part40 : Audit := .split 11 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[28, 28, 28, 16, 16, 64, 64],96⟩,
.cycle 25 21 false (5),
.cycle 14 1 false (0),
.cycle 38 1 false (-2),
.cycle 6 39 false (5),
.split 12 (5,true) (byMove [
.last 34 (5,false),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 20 true (0),
.last 27 (5,false),
.cycle 0 17 true (0),
.cycle 13 1 false (1),
.cycle 0 19 true (0),
.last 13 (5,false),
.cycle 14 25 false (3),
.cycle 11 3 false (1),
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 4398046511104, 2147483648, 4294967296, 8, 268435456, 32768, 4398046511104, 8192, 16384, 32768, 272695296, 4398319239680, 4398046511104, 33554432, 67108864, 32768, 268435456, 4398046511104, 4398046511104, 524288, 1048576, 512, 4194304, 268435456, 4398046511104, 33554432, 67108864, 32768, 268435456, 512, 4398046511104, 8192, 16384, 32768, 0, 0, 4398046511104, 4398046511104],[17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 17179869184, 17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 17179869184, 4415499075584, 4398320304640, 4398319239680, 65536, 65536, 4415499075584, 4398046511104, 512, 512, 268435456, 268435456, 4398046511104, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 17179869184, 4398046511104, 512, 512, 268435456, 268435456, 4398046511104, 0, 0, 0, 65536, 65536, 0, 4398046511104],7118553349566⟩,
.cycle 13 1 false (-1),
.cycle 71 23 false (1),
.last 13 (5,false),
.last 17 (5,false),
.cycle 1 15 true (0),
.cycle 0 17 true (0),
.last 21 (5,false),
.last 38 (5,false),
.last 13 (5,false)
]),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 6 15 true (0),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 0 23 false (4),
.cycle 0 15 false (4),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 0 25 false (4),
.last 15 (5,false),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 25 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 23 true (0),
.cycle 0 15 true (0),
.last 13 (5,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[28, 28, 28, 16, 16, 64, 64],96⟩,
.cycle 54 35 false (3),
.cycle 0 31 false (4),
.cycle 19 1 false (-1),
.cycle 6 38 false (4),
.split 12 (5,true) (byMove [
.last 49 (5,false),
.cycle 56 21 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 49 23 false (3),
.last 13 (5,false),
.cycle 0 24 true (0),
.cycle 0 19 true (0),
.last 14 (5,false),
.cycle 0 22 true (0),
.cycle 0 22 true (0),
.last 15 (5,false),
.last 47 (5,false),
.cycle 11 3 false (1),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 23 (5,false),
.last 13 (5,false),
.last 15 (5,false),
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 4398046511104, 2147483648, 4294967296, 8, 268435456, 32768, 4398046511104, 8192, 16384, 32768, 272695296, 4398319239680, 4398046511104, 33554432, 67108864, 32768, 268435456, 4398046511104, 4398046511104, 524288, 1048576, 512, 4194304, 268435456, 4398046511104, 33554432, 67108864, 32768, 268435456, 512, 4398046511104, 8192, 16384, 32768, 0, 0, 4398046511104, 4398046511104],[17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 2147483648, 17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 2147483648, 4415500173824, 4398320304640, 4398320304640, 65536, 65536, 8192, 4398046511104, 512, 512, 268435456, 268435456, 33554432, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 524288, 4398046511104, 512, 512, 268435456, 268435456, 33554432, 0, 0, 0, 65536, 65536, 8192, 4398046511104],7118553349566⟩,
.cycle 11 2 true (0),
.last 19 (5,false),
.last 19 (5,false),
.last 15 (5,false)
]),
.cycle 10 2 true (1),
.cycle 0 21 false (4),
.cycle 2 11 true (1),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.split 12 (5,true) (byMove [
.cycle 0 21 false (4),
.cycle 0 19 false (4),
.last 14 (5,false),
.cycle 0 21 false (4),
.cycle 0 21 false (4),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 0 37 false (4),
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 4398046511104, 2147483648, 4294967296, 8, 268435456, 32768, 4398046511104, 8192, 16384, 32768, 272695296, 4398319239680, 4398046511104, 33554432, 67108864, 32768, 268435456, 4398046511104, 4398046511104, 524288, 1048576, 512, 4194304, 268435456, 4398046511104, 33554432, 67108864, 32768, 268435456, 512, 4398046511104, 8192, 16384, 32768, 0, 0, 4398046511104, 4398046511104],[17179869184, 67108864, 34359738368, 17179869184, 17179869184, 536870912, 17179869184, 67108864, 34359738368, 17179869184, 17179869184, 536870912, 4416044466176, 4398320304640, 131072, 65536, 65536, 4416044466176, 4398046511104, 512, 536870912, 268435456, 268435456, 4398046511104, 17179869184, 4398046511104, 8388608, 4194304, 4194304, 17179869184, 8388608, 512, 536870912, 268435456, 268435456, 8388608, 0, 0, 131072, 65536, 65536, 0, 4398046511104],7118553349566⟩,
.cycle 11 2 true (1),
.cycle 0 29 false (4),
.cycle 0 29 false (4),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 0 25 false (4),
.last 13 (5,false)
])
])
theorem kid01_part40_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part40) = true := by rfl

def kid01_part41 : Audit := .cycle 21 1 false (-1)
theorem kid01_part41_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part41) = true := by rfl

def kid01_part42 : Audit := .cycle 6 32 false (4)
theorem kid01_part42_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part42) = true := by rfl

def kid01_part44 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.last 43 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 2, 2147483648, 4294967296, 8, 268435456, 32768, 2, 8192, 16384, 32768, 272695296, 4398319239680, 8192, 33554432, 67108864, 32768, 268435456, 4398046511104, 8192, 524288, 1048576, 512, 4194304, 268435456, 128, 33554432, 67108864, 32768, 268435456, 512, 8192, 8192, 16384, 32768, 0, 0, 8192, 4398046511104],[67108864, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 67108864, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 4415500173824, 4398320304640, 4398046511104, 65536, 65536, 4398320304640, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 4398046511104, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 0, 0, 4398046511104, 65536, 65536, 0, 4398046511104],7118553349566⟩,
.last 14 (2,true),
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 8, 2147483648, 4294967296, 8, 268435456, 32768, 8, 8192, 16384, 32768, 272695296, 4398319239680, 32768, 33554432, 67108864, 32768, 268435456, 4398046511104, 32768, 524288, 1048576, 512, 4194304, 268435456, 512, 33554432, 67108864, 32768, 268435456, 512, 32768, 8192, 16384, 32768, 0, 0, 32768, 4398046511104],[17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 4415499075584, 4398320304640, 4398046511104, 65536, 65536, 4398320304640, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 4398046511104, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 0, 0, 4398046511104, 65536, 65536, 0, 4398046511104],7118016478654⟩,
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 16, 2147483648, 4294967296, 8, 268435456, 32768, 16, 8192, 16384, 32768, 272695296, 4398319239680, 65536, 33554432, 67108864, 32768, 268435456, 4398046511104, 65536, 524288, 1048576, 512, 4194304, 268435456, 1024, 33554432, 67108864, 32768, 268435456, 512, 65536, 8192, 16384, 32768, 0, 0, 65536, 4398046511104],[17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 17179869184, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 4415499075584, 4398320304640, 4398046511104, 65536, 65536, 4398320304640, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 4398046511104, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 0, 0, 4398046511104, 65536, 65536, 0, 4398046511104],7118553349566⟩,
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 32, 2147483648, 4294967296, 8, 268435456, 32768, 32, 8192, 16384, 32768, 272695296, 4398319239680, 131072, 33554432, 67108864, 32768, 268435456, 4398046511104, 131072, 524288, 1048576, 512, 4194304, 268435456, 2048, 33554432, 67108864, 32768, 268435456, 512, 131072, 8192, 16384, 32768, 0, 0, 131072, 4398046511104],[67108864, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 67108864, 67108864, 4398046511104, 17179869184, 17179869184, 67108864, 4415500173824, 4398320304640, 4398046511104, 65536, 65536, 4398320304640, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 17179869184, 4398046511104, 4398046511104, 4194304, 4194304, 4398046511104, 4398046511104, 512, 4398046511104, 268435456, 268435456, 512, 0, 0, 4398046511104, 65536, 65536, 0, 4398046511104],4884624962974⟩,
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 12 7 false (1),
.cycle 14 1 false (-2),
.last 32 (2,true),
.cycle 13 1 false (-1),
.last 18 (2,true),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 12 5 false (1),
.cycle 12 5 false (1),
.cycle 11 3 false (1)
])
theorem kid01_part44_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part44) = true := by rfl

def kid01_part45 : Audit := .cycle 25 21 false (5)
theorem kid01_part45_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part45) = true := by rfl

def kid01_part46 : Audit := .split 12 (2,true) (byMove [
.cycle 35 1 false (-1),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.last 16 (5,false),
.cycle 6 25 true (0),
.cycle 0 17 true (0),
.cycle 13 1 false (1),
.cycle 0 19 true (0),
.last 13 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.cycle 47 1 false (-1),
.cycle 13 1 false (-1),
.last 83 (5,false),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 1 14 true (0),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 39 1 false (-1),
.last 13 (5,false)
])
theorem kid01_part46_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part46) = true := by rfl

def kid01_part47 : Audit := .cycle 38 1 false (-2)
theorem kid01_part47_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part47) = true := by rfl

def kid01_part48 : Audit := .cycle 6 39 false (5)
theorem kid01_part48_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part48) = true := by rfl

def kid01_part49 : Audit := .split 13 (5,false) (byMove [
.cycle 0 30 false (4),
.cycle 6 26 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 6 34 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 15 false (4),
.cycle 17 1 true (1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 0 38 false (4),
.cycle 14 1 false (-2),
.cycle 33 21 false (-1),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 1 70 false (5),
.cycle 6 13 false (4),
.cycle 17 5 false (1),
.cycle 0 34 false (4),
.cycle 20 1 true (-2)
])
theorem kid01_part49_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part49) = true := by rfl

def kid01_part50 : Audit := .split 13 (5,false) (byMove [
.last 18 (2,true),
.cycle 27 25 false (5),
.last 14 (2,true),
.cycle 44 1 false (-2),
.cycle 6 45 false (5),
.cycle 18 1 false (0),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 14 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 14 4 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 12 18 false (3),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.cycle 17 3 false (1),
.last 14 (2,true),
.cycle 19 5 false (2),
.cycle 19 5 false (2),
.cycle 0 15 true (0)
])
theorem kid01_part50_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part50) = true := by rfl

def kid01_part51 : Audit := .cycle 0 13 true (0)
theorem kid01_part51_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part51) = true := by rfl

def kid01_part52 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 19 (5,false),
.cycle 0 15 false (4),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 21 (5,false),
.last 17 (5,false),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 27 25 false (5),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 19 (5,false),
.cycle 0 15 true (0),
.last 13 (5,false)
])
theorem kid01_part52_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part52) = true := by rfl

def kid01_part53 : Audit := .cycle 0 15 true (0)
theorem kid01_part53_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part53) = true := by rfl

def kid01_part54 : Audit := .cycle 0 15 true (0)
theorem kid01_part54_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part54) = true := by rfl

def kid01_part55 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (0),
.cycle 6 15 true (0),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 18 4 false (0),
.last 15 (2,true),
.cycle 0 18 true (0),
.cycle 6 12 true (0),
.cycle 0 20 true (0),
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 36 5 false (4),
.cycle 0 16 true (0),
.cycle 13 1 true (3)
])
theorem kid01_part55_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part55) = true := by rfl

def kid01_part56 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 91 25 false (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1032, 128, 256, 8, 1024, 1032, 1032, 4096],[1024, 256, 4096, 1024, 1024, 1032, 1024, 1032, 4096, 1024, 1024, 1024, 4096],4096⟩,
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.last 17 (2,true),
.last 14 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 8, 128, 256, 8, 1024, 1032, 8, 4096],[1024, 256, 4096, 1024, 1024, 1032, 1024, 1032, 4096, 1024, 1024, 1024, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 16, 128, 256, 8, 1024, 1032, 16, 4096],[1024, 256, 4096, 1024, 1024, 1032, 1024, 1032, 4096, 1024, 1024, 1024, 4096],4096⟩,
.cycle 12 5 false (0),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 6 11 false (4),
.cycle 14 1 false (-2),
.cycle 36 20 false (-2),
.cycle 13 1 false (-1),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.last 14 (2,true),
.cycle 5 9 false (4),
.cycle 6 9 false (4),
.cycle 11 3 false (1)
])
theorem kid01_part56_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part56) = true := by rfl

def kid01_part57 : Audit := .split 15 (2,true) (byMove [
.last 21 (5,false),
.last 18 (5,false),
.cycle 19 1 false (-1),
.last 20 (5,false),
.last 20 (5,false),
.cycle 11 5 false (1),
.last 17 (5,false),
.last 43 (5,false),
.last 43 (5,false),
.last 47 (5,false),
.last 47 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.last 18 (5,false),
.cycle 6 15 false (4),
.cycle 5 11 false (4),
.cycle 6 11 false (4),
.cycle 11 5 false (1),
.last 20 (5,false),
.cycle 9 7 false (3),
.last 39 (5,false),
.cycle 8 9 false (4),
.cycle 7 9 false (4),
.last 25 (5,false)
])
theorem kid01_part57_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part57) = true := by rfl

def kid01_part58 : Audit := .split 12 (2,true) (byMove [
.last 24 (5,false),
.last 20 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 39 (5,false),
.last 13 (5,false),
.last 14 (5,false),
.last 34 (5,false),
.cycle 16 1 false (4),
.last 18 (5,false),
.last 18 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.last 21 (5,false),
.last 27 (5,false),
.cycle 13 1 false (-1),
.last 29 (5,false),
.last 13 (5,false),
.last 29 (5,false),
.last 15 (5,false),
.cycle 2 13 true (0),
.last 25 (5,false),
.last 25 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part58_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part58) = true := by rfl

def kid01_part59 : Audit := .cycle 19 1 false (-1)
theorem kid01_part59_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part59) = true := by rfl

def kid01_part60 : Audit := .split 27 (5,false) (byMove [
.last 32 (2,true),
.cycle 6 49 false (4),
.last 28 (2,true),
.cycle 6 51 false (4),
.cycle 6 51 false (4),
.cycle 6 62 false (4),
.cycle 26 2 true (-1),
.cycle 6 36 false (4),
.last 28 (2,true),
.cycle 6 38 false (4),
.cycle 6 38 false (4),
.cycle 6 51 false (4),
.cycle 28 4 false (-2),
.last 31 (2,true),
.last 28 (2,true),
.cycle 13 16 false (3),
.cycle 12 16 false (3),
.cycle 6 47 false (4),
.cycle 10 18 false (3),
.cycle 16 12 false (2),
.last 28 (2,true),
.cycle 15 14 false (3),
.cycle 14 14 false (3),
.cycle 13 16 false (3)
])
theorem kid01_part60_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part60) = true := by rfl

def kid01_part61 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[16, 28, 64, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[16, 28, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 13 2 true (-1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 0 31 false (4),
.cycle 0 31 false (4),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 6 11 false (4),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[16, 28, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.last 14 (2,true),
.cycle 5 9 false (4),
.cycle 6 9 false (4),
.cycle 11 3 false (1)
])
theorem kid01_part61_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part61) = true := by rfl

def kid01_part62 : Audit := .cycle 10 2 true (1)
theorem kid01_part62_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part62) = true := by rfl

def kid01_part63 : Audit := .split 17 (5,false) (byMove [
.last 20 (2,true),
.cycle 9 26 false (3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 6 19 false (4),
.cycle 17 1 false (-1),
.cycle 16 2 true (-1),
.cycle 0 19 false (4),
.last 18 (2,true),
.cycle 0 21 false (4),
.cycle 0 21 false (4),
.cycle 1 18 true (-1),
.cycle 15 4 false (1),
.last 19 (2,true),
.cycle 15 7 false (1),
.cycle 18 1 false (-2),
.cycle 12 19 false (2),
.cycle 17 1 false (-1),
.cycle 13 5 false (1),
.cycle 15 3 false (1),
.last 18 (2,true),
.cycle 15 5 false (1),
.cycle 15 5 false (1),
.cycle 9 21 false (4)
])
theorem kid01_part63_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part63) = true := by rfl

def kid01_part64 : Audit := .split 12 (2,true) (byMove [
.last 17 (5,false),
.last 15 (5,false),
.cycle 16 1 false (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 17 (5,false),
.last 15 (5,false),
.last 31 (5,false),
.last 25 (5,false),
.last 25 (5,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.last 21 (5,false),
.last 13 (5,false)
])
theorem kid01_part64_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part64) = true := by rfl

def kid01_part65 : Audit := .split 21 (5,false) (byMove [
.last 24 (2,true),
.cycle 8 32 false (4),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 6 23 false (4),
.cycle 21 1 false (-1),
.cycle 20 2 true (-1),
.cycle 0 23 false (4),
.last 22 (2,true),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.cycle 18 8 true (-1),
.cycle 19 4 false (1),
.last 23 (2,true),
.cycle 18 7 false (2),
.cycle 22 1 false (-2),
.cycle 13 21 false (3),
.cycle 21 1 false (-1),
.cycle 15 7 false (2),
.cycle 19 3 false (1),
.last 22 (2,true),
.cycle 17 5 false (2),
.cycle 18 5 false (2),
.cycle 13 13 false (3)
])
theorem kid01_part65_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part65) = true := by rfl

def kid01_part66 : Audit := .split 21 (5,false) (byMove [
.last 24 (2,true),
.cycle 7 32 false (4),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 6 23 false (4),
.cycle 21 1 false (-1),
.cycle 20 2 true (-1),
.cycle 0 23 false (4),
.last 22 (2,true),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.cycle 19 4 false (1),
.last 23 (2,true),
.cycle 17 7 false (2),
.cycle 22 1 false (-2),
.cycle 12 21 false (3),
.cycle 21 1 false (-1),
.cycle 15 7 false (2),
.cycle 19 3 false (1),
.last 22 (2,true),
.cycle 18 5 false (2),
.cycle 17 5 false (2),
.cycle 18 5 false (2)
])
theorem kid01_part66_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part66) = true := by rfl

def kid01_part67 : Audit := .split 13 (5,false) (byMove [
.cycle 10 4 true (1),
.cycle 9 32 false (3),
.last 14 (2,true),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 11 5 true (1),
.last 23 (2,true),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.cycle 8 6 true (1),
.cycle 13 1 true (3)
])
theorem kid01_part67_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part67) = true := by rfl

def kid01_part43 : Audit := .split 11 (5,true) (byMove [(kid01_part44),(kid01_part45),(kid01_part46),(kid01_part47),(kid01_part48),(kid01_part49),(kid01_part50),(kid01_part51),(kid01_part52),(kid01_part53),(kid01_part54),(kid01_part55),(kid01_part56),(kid01_part57),(kid01_part58),(kid01_part59),(kid01_part60),(kid01_part61),(kid01_part62),(kid01_part63),(kid01_part64),(kid01_part65),(kid01_part66),(kid01_part67)])

theorem kid01_part43_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part43) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part44),(kid01_part45),(kid01_part46),(kid01_part47),(kid01_part48),(kid01_part49),(kid01_part50),(kid01_part51),(kid01_part52),(kid01_part53),(kid01_part54),(kid01_part55),(kid01_part56),(kid01_part57),(kid01_part58),(kid01_part59),(kid01_part60),(kid01_part61),(kid01_part62),(kid01_part63),(kid01_part64),(kid01_part65),(kid01_part66),(kid01_part67)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part44_checked

  · exact kid01_part50_checked

  · exact kid01_part56_checked

  · exact kid01_part62_checked

  · exact kid01_part45_checked

  · exact kid01_part51_checked

  · exact kid01_part57_checked

  · exact kid01_part63_checked

  · exact kid01_part46_checked

  · exact kid01_part52_checked

  · exact kid01_part58_checked

  · exact kid01_part64_checked

  · exact kid01_part47_checked

  · exact kid01_part53_checked

  · exact kid01_part59_checked

  · exact kid01_part65_checked

  · exact kid01_part48_checked

  · exact kid01_part54_checked

  · exact kid01_part60_checked

  · exact kid01_part66_checked

  · exact kid01_part49_checked

  · exact kid01_part55_checked

  · exact kid01_part61_checked

  · exact kid01_part67_checked

def kid01_part68 : Audit := .cycle 0 11 true (0)
theorem kid01_part68_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part68) = true := by rfl

def kid01_part69 : Audit := .cycle 1 10 true (1)
theorem kid01_part69_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part69) = true := by rfl

def kid01_part70 : Audit := .cycle 2 9 true (1)
theorem kid01_part70_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part70) = true := by rfl

def kid01_part71 : Audit := .cycle 7 6 true (2)
theorem kid01_part71_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part71) = true := by rfl

def kid01_part72 : Audit := .cycle 0 19 false (4)
theorem kid01_part72_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part72) = true := by rfl

def kid01_part73 : Audit := .split 11 (5,false) (byMove [
.cycle 10 2 true (2),
.cycle 0 19 false (4),
.split 12 (2,true) (byMove [
.cycle 0 19 false (4),
.cycle 0 30 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 35 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 14 (5,true),
.cycle 12 10 false (2),
.cycle 0 37 false (4),
.cycle 27 1 false (-1),
.cycle 6 40 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 25 false (4),
.cycle 11 2 true (2)
]),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.split 12 (5,true) (byMove [
.cycle 0 19 false (4),
.cycle 0 30 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 0 35 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.cycle 12 2 true (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 6 40 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 25 false (4),
.cycle 11 2 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.split 13 (5,true) (byMove [
.cycle 10 4 true (2),
.cycle 0 25 false (4),
.last 14 (2,true),
.cycle 0 31 false (4),
.cycle 0 31 false (4),
.cycle 15 8 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 9 7 true (2),
.cycle 12 2 true (2),
.last 27 (2,true),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 15 8 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 11 3 true (2)
]),
.split 21 (2,true) (byMove [
.cycle 13 9 false (2),
.cycle 15 7 false (1),
.cycle 25 1 false (-1),
.cycle 15 9 false (1),
.cycle 15 9 false (1),
.last 22 (5,true),
.last 23 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 6, 64],[32, 6, 2, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[32, 28, 8, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 16, 16, 16, 64, 64],64⟩,
.last 22 (5,true),
.last 23 (5,true),
.cycle 15 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 16, 16, 16, 64, 64],64⟩,
.last 22 (5,true),
.last 23 (5,true),
.cycle 9 13 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[32, 28, 8, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 16, 16, 16, 64, 64],64⟩,
.last 22 (5,true)
]),
.split 12 (2,true) (byMove [
.cycle 12 9 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 8, 16, 16, 64, 64],64⟩,
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 6 16 true (1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.last 13 (5,true),
.last 14 (5,true),
.cycle 12 10 false (2),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 10 3 true (2),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.last 21 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 64, 16, 16, 8, 64],64⟩,
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 13 (2,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 32 1 false (6),
.cycle 12 2 true (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.cycle 10 3 true (2),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 8 4 true (2),
.cycle 11 1 true (3)
])
theorem kid01_part73_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part73) = true := by rfl

def kid01_part1 : Audit := .split 10 (0,true) (byMove [(kid01_part2),(kid01_part3),(kid01_part4),(kid01_part5),(kid01_part6),(kid01_part7),(kid01_part32),(kid01_part33),(kid01_part34),(kid01_part35),(kid01_part36),(kid01_part37),(kid01_part38),(kid01_part39),(kid01_part40),(kid01_part41),(kid01_part42),(kid01_part43),(kid01_part68),(kid01_part69),(kid01_part70),(kid01_part71),(kid01_part72),(kid01_part73)])

theorem kid01_part1_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (kid01_part1) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) 10 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part2),(kid01_part3),(kid01_part4),(kid01_part5),(kid01_part6),(kid01_part7),(kid01_part32),(kid01_part33),(kid01_part34),(kid01_part35),(kid01_part36),(kid01_part37),(kid01_part38),(kid01_part39),(kid01_part40),(kid01_part41),(kid01_part42),(kid01_part43),(kid01_part68),(kid01_part69),(kid01_part70),(kid01_part71),(kid01_part72),(kid01_part73)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part2_checked

  · exact kid01_part32_checked

  · exact kid01_part38_checked

  · exact kid01_part68_checked

  · exact kid01_part3_checked

  · exact kid01_part33_checked

  · exact kid01_part39_checked

  · exact kid01_part69_checked

  · exact kid01_part4_checked

  · exact kid01_part34_checked

  · exact kid01_part40_checked

  · exact kid01_part70_checked

  · exact kid01_part5_checked

  · exact kid01_part35_checked

  · exact kid01_part41_checked

  · exact kid01_part71_checked

  · exact kid01_part6_checked

  · exact kid01_part36_checked

  · exact kid01_part42_checked

  · exact kid01_part72_checked

  · exact kid01_part7_checked

  · exact kid01_part37_checked

  · exact kid01_part43_checked

  · exact kid01_part73_checked

def kid01_part74 : Audit := .cycle 10 11 false (2)
theorem kid01_part74_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,1⟩)) (kid01_part74) = true := by rfl

def kid01_part76 : Audit := .split 11 (0,true) (byMove [
.cycle 0 13 false (4),
.cycle 14 1 false (0),
.cycle 0 13 false (4),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.last 24 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 16 false (4),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.last 29 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 23 (5,false),
.cycle 0 19 false (4),
.cycle 16 1 false (0),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (0),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 0 19 false (4),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 0 21 false (4),
.cycle 10 4 true (1),
.cycle 33 1 false (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 19 true (0),
.cycle 29 1 false (1),
.cycle 12 1 true (2)
]),
.cycle 2 20 false (4),
.cycle 14 1 false (0),
.cycle 10 5 false (2),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.last 28 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 14 (5,false),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.last 14 (5,false),
.cycle 2 20 false (4),
.last 16 (5,false),
.cycle 0 19 false (4),
.cycle 13 1 false (-1),
.last 41 (5,false),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 0 15 false (4),
.last 15 (5,false),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 25 false (4),
.cycle 0 15 false (4),
.split 12 (5,false) (byMove [
.cycle 11 2 true (1),
.cycle 0 15 false (4),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 14 (5,true),
.cycle 2 19 false (4),
.cycle 10 9 false (2),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 0 21 false (4),
.cycle 12 1 true (2)
])
])
theorem kid01_part76_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part76) = true := by rfl

def kid01_part77 : Audit := .cycle 25 1 false (-1)
theorem kid01_part77_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part77) = true := by rfl

def kid01_part78 : Audit := .cycle 14 1 false (0)
theorem kid01_part78_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part78) = true := by rfl

def kid01_part79 : Audit := .cycle 15 1 false (-1)
theorem kid01_part79_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part79) = true := by rfl

def kid01_part80 : Audit := .cycle 30 1 false (-2)
theorem kid01_part80_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part80) = true := by rfl

def kid01_part82 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 false (4),
.cycle 0 24 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 25 false (4),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 25 false (4),
.last 13 (5,false),
.last 16 (5,false),
.cycle 0 16 false (4),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 29 false (4),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 false (4),
.last 19 (5,false),
.cycle 16 1 false (0),
.last 13 (5,false)
])
theorem kid01_part82_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part82) = true := by rfl

def kid01_part83 : Audit := .cycle 14 1 false (0)
theorem kid01_part83_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part83) = true := by rfl

def kid01_part84 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 27 1 false (-3),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 26 1 false (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 27 1 false (-1),
.cycle 13 1 true (-1),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 31 1 false (-3),
.cycle 13 1 false (-1),
.cycle 29 1 false (-1),
.cycle 1 13 false (4),
.cycle 25 1 false (-1),
.cycle 12 7 false (1),
.cycle 17 1 false (-1),
.cycle 13 1 true (-1)
])
theorem kid01_part84_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part84) = true := by rfl

def kid01_part85 : Audit := .cycle 16 1 false (0)
theorem kid01_part85_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part85) = true := by rfl

def kid01_part86 : Audit := .cycle 16 1 false (0)
theorem kid01_part86_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part86) = true := by rfl

def kid01_part87 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 12 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 12 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 12 13 false (2),
.cycle 13 1 true (-1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 17 false (0),
.cycle 13 1 false (-1),
.cycle 11 15 false (4),
.cycle 1 13 false (4),
.cycle 12 11 false (2),
.cycle 13 7 false (1),
.cycle 17 1 false (-1),
.cycle 13 1 true (-1)
])
theorem kid01_part87_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part87) = true := by rfl

def kid01_part88 : Audit := .cycle 0 12 true (0)
theorem kid01_part88_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part88) = true := by rfl

def kid01_part89 : Audit := .cycle 1 11 true (1)
theorem kid01_part89_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part89) = true := by rfl

def kid01_part90 : Audit := .cycle 6 12 true (0)
theorem kid01_part90_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part90) = true := by rfl

def kid01_part91 : Audit := .cycle 21 1 false (1)
theorem kid01_part91_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part91) = true := by rfl

def kid01_part92 : Audit := .cycle 1 12 true (1)
theorem kid01_part92_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part92) = true := by rfl

def kid01_part93 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 17 4 false (1),
.cycle 10 4 true (1),
.cycle 33 1 false (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 17 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 27 7 false (3),
.cycle 29 1 false (1),
.cycle 12 1 true (2)
])
theorem kid01_part93_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part93) = true := by rfl

def kid01_part94 : Audit := .split 12 (0,true) (byMove [
.cycle 10 5 false (2),
.last 31 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.cycle 0 14 true (0),
.cycle 15 1 false (1),
.last 14 (5,false),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.last 17 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 21 (5,false),
.last 13 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part94_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part94) = true := by rfl

def kid01_part95 : Audit := .cycle 14 1 false (0)
theorem kid01_part95_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part95) = true := by rfl

def kid01_part96 : Audit := .split 13 (5,false) (byMove [
.cycle 2 18 false (4),
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 31 1 false (-3),
.cycle 13 1 false (-1),
.cycle 0 18 true (-1),
.cycle 22 1 false (0),
.cycle 19 1 false (1),
.cycle 14 1 false (0),
.cycle 35 1 false (-1),
.cycle 21 1 false (1),
.cycle 12 4 false (0),
.cycle 22 1 false (-2),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 35 1 false (-3),
.cycle 13 1 false (-1),
.cycle 23 1 false (-1),
.cycle 10 5 false (2),
.cycle 33 1 false (-1),
.cycle 27 1 false (-1),
.cycle 17 1 false (-1),
.cycle 23 1 false (-1)
])
theorem kid01_part96_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part96) = true := by rfl

def kid01_part97 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 29 1 false (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 30 1 false (-4),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.cycle 29 1 false (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 30 1 false (-2),
.cycle 17 1 true (-1),
.cycle 15 4 false (1),
.cycle 21 1 false (-3),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 34 1 false (-4),
.cycle 17 1 false (-1),
.cycle 36 1 false (-2),
.cycle 1 17 false (4),
.cycle 28 1 false (-2),
.cycle 12 7 false (2),
.cycle 21 1 false (-1),
.cycle 17 1 true (-1)
])
theorem kid01_part97_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part97) = true := by rfl

def kid01_part98 : Audit := .split 17 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 19 16 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 20 16 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1),
.cycle 19 16 false (3),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 20 16 false (2),
.cycle 17 1 true (-1),
.cycle 15 4 false (1),
.cycle 19 16 false (-1),
.cycle 23 1 false (-1),
.cycle 18 1 false (-2),
.cycle 18 16 false (0),
.cycle 17 1 false (-1),
.cycle 30 16 false (2),
.cycle 1 17 false (4),
.cycle 18 16 false (2),
.cycle 13 7 false (2),
.cycle 21 1 false (-1),
.cycle 17 1 true (-1)
])
theorem kid01_part98_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part98) = true := by rfl

def kid01_part99 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 24 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 24, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 37 1 false (-1),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 35 1 false (-3),
.cycle 14 1 false (-2),
.cycle 26 32 false (0),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 2 20 false (4),
.cycle 12 3 false (0),
.cycle 22 7 false (0),
.cycle 29 1 false (-3),
.cycle 11 3 false (1)
])
theorem kid01_part99_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part99) = true := by rfl

def kid01_part100 : Audit := .cycle 0 12 true (0)
theorem kid01_part100_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part100) = true := by rfl

def kid01_part101 : Audit := .cycle 1 11 true (1)
theorem kid01_part101_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part101) = true := by rfl

def kid01_part102 : Audit := .cycle 2 10 true (1)
theorem kid01_part102_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part102) = true := by rfl

def kid01_part103 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 false (4),
.cycle 14 18 false (3),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 14 19 false (3),
.cycle 25 1 false (-1),
.cycle 0 26 true (-1),
.cycle 14 18 true (-1),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 14 19 false (3),
.cycle 25 1 true (-1),
.cycle 23 4 false (1),
.cycle 17 10 false (2),
.cycle 31 1 false (-1),
.cycle 26 1 false (-2),
.cycle 14 23 false (3),
.cycle 25 1 false (-1),
.cycle 7 33 false (4),
.cycle 1 25 false (4),
.cycle 14 17 false (3),
.cycle 19 7 false (2),
.cycle 29 1 false (-1),
.cycle 25 1 true (-1)
])
theorem kid01_part103_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part103) = true := by rfl

def kid01_part104 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 30 1 false (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 31 1 false (-3),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 30 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 31 1 false (-1),
.cycle 15 1 true (-1),
.cycle 13 4 false (1),
.cycle 22 1 false (-2),
.cycle 21 1 false (-1),
.cycle 16 1 false (-2),
.cycle 35 1 false (-3),
.cycle 15 1 false (-1),
.cycle 35 1 false (-1),
.cycle 1 15 false (4),
.cycle 29 1 false (-1),
.cycle 12 7 false (2),
.cycle 19 1 false (-1),
.cycle 15 1 true (-1)
])
theorem kid01_part104_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part104) = true := by rfl

def kid01_part105 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 30 1 false (-2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 35 1 false (-3),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 13 (0,true),
.cycle 22 1 false (-2),
.cycle 23 1 false (-1),
.cycle 26 1 false (-2),
.cycle 13 23 false (3),
.cycle 11 3 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 25 1 false (-1),
.cycle 12 1 true (2)
])
theorem kid01_part105_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part105) = true := by rfl

def kid01_part81 : Audit := .split 11 (5,true) (byMove [(kid01_part82),(kid01_part83),(kid01_part84),(kid01_part85),(kid01_part86),(kid01_part87),(kid01_part88),(kid01_part89),(kid01_part90),(kid01_part91),(kid01_part92),(kid01_part93),(kid01_part94),(kid01_part95),(kid01_part96),(kid01_part97),(kid01_part98),(kid01_part99),(kid01_part100),(kid01_part101),(kid01_part102),(kid01_part103),(kid01_part104),(kid01_part105)])

theorem kid01_part81_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part81) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part82),(kid01_part83),(kid01_part84),(kid01_part85),(kid01_part86),(kid01_part87),(kid01_part88),(kid01_part89),(kid01_part90),(kid01_part91),(kid01_part92),(kid01_part93),(kid01_part94),(kid01_part95),(kid01_part96),(kid01_part97),(kid01_part98),(kid01_part99),(kid01_part100),(kid01_part101),(kid01_part102),(kid01_part103),(kid01_part104),(kid01_part105)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part82_checked

  · exact kid01_part88_checked

  · exact kid01_part94_checked

  · exact kid01_part100_checked

  · exact kid01_part83_checked

  · exact kid01_part89_checked

  · exact kid01_part95_checked

  · exact kid01_part101_checked

  · exact kid01_part84_checked

  · exact kid01_part90_checked

  · exact kid01_part96_checked

  · exact kid01_part102_checked

  · exact kid01_part85_checked

  · exact kid01_part91_checked

  · exact kid01_part97_checked

  · exact kid01_part103_checked

  · exact kid01_part86_checked

  · exact kid01_part92_checked

  · exact kid01_part98_checked

  · exact kid01_part104_checked

  · exact kid01_part87_checked

  · exact kid01_part93_checked

  · exact kid01_part99_checked

  · exact kid01_part105_checked

def kid01_part106 : Audit := .cycle 0 11 true (0)
theorem kid01_part106_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part106) = true := by rfl

def kid01_part107 : Audit := .cycle 1 10 true (1)
theorem kid01_part107_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part107) = true := by rfl

def kid01_part108 : Audit := .cycle 6 11 true (1)
theorem kid01_part108_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part108) = true := by rfl

def kid01_part109 : Audit := .cycle 3 8 true (1)
theorem kid01_part109_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part109) = true := by rfl

def kid01_part110 : Audit := .cycle 1 11 true (1)
theorem kid01_part110_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part110) = true := by rfl

def kid01_part111 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 31 1 false (-1),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 29 1 false (1),
.cycle 17 1 false (1),
.cycle 12 2 true (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 2 14 true (1),
.cycle 4 8 true (1),
.cycle 35 1 false (-1),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.last 14 (0,true),
.cycle 6 14 true (0),
.cycle 6 20 true (0),
.cycle 37 1 false (3),
.cycle 37 1 false (3),
.cycle 25 1 false (5),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 15 10 true (0),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 15 1 false (-1),
.last 14 (0,true),
.cycle 21 1 false (1),
.cycle 2 14 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 14 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 2 12 true (1),
.cycle 11 1 true (3)
])
theorem kid01_part111_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part111) = true := by rfl

def kid01_part112 : Audit := .split 11 (0,true) (byMove [
.cycle 2 17 false (4),
.cycle 14 1 false (0),
.cycle 12 3 false (0),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.split 12 (5,true) (byMove [
.cycle 2 17 false (4),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 13 3 false (2),
.last 16 (5,false),
.cycle 18 1 false (2),
.cycle 13 1 false (1),
.last 29 (5,false),
.last 13 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.last 29 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 10 4 true (0),
.last 27 (5,false),
.last 21 (5,false),
.cycle 16 1 false (0),
.last 13 (5,false)
]),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 17 3 false (1),
.cycle 29 1 false (1),
.cycle 29 1 false (1),
.split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 3 false (1),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 18 3 false (1),
.cycle 10 4 true (1),
.cycle 33 1 false (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 28 3 false (2),
.cycle 29 1 false (1),
.last 13 (5,false)
]),
.cycle 13 3 false (0),
.cycle 14 1 false (0),
.cycle 12 3 false (0),
.cycle 19 1 false (-1),
.cycle 16 12 false (2),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 32 1 false (-2),
.last 13 (5,false),
.last 14 (5,false),
.cycle 15 1 false (1),
.cycle 13 3 false (1),
.cycle 16 3 false (2),
.cycle 16 3 false (2),
.last 15 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.last 21 (5,false),
.cycle 13 1 false (-1),
.last 23 (5,false),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.last 15 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 15 (5,false)
]),
.cycle 0 13 true (0),
.cycle 15 3 false (1),
.cycle 10 2 true (1),
.cycle 19 3 false (1),
.cycle 19 3 false (1),
.split 12 (5,true) (byMove [
.last 14 (5,false),
.cycle 13 3 false (1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 15 3 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 11 2 true (1),
.cycle 13 3 false (1),
.cycle 16 3 false (0),
.cycle 23 3 false (1),
.cycle 23 3 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 19 3 false (1),
.last 13 (5,false)
])
])
theorem kid01_part112_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part112) = true := by rfl

def kid01_part113 : Audit := .cycle 17 1 false (-1)
theorem kid01_part113_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part113) = true := by rfl

def kid01_part114 : Audit := .cycle 32 1 false (0)
theorem kid01_part114_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part114) = true := by rfl

def kid01_part115 : Audit := .cycle 21 1 false (-1)
theorem kid01_part115_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part115) = true := by rfl

def kid01_part116 : Audit := .cycle 11 20 false (3)
theorem kid01_part116_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part116) = true := by rfl

def kid01_part118 : Audit := .split 12 (0,true) (byMove [
.cycle 2 17 false (4),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 17 false (2),
.last 13 (5,false),
.last 16 (5,false),
.cycle 10 8 true (0),
.cycle 18 1 false (2),
.cycle 13 1 false (1),
.cycle 10 21 false (3),
.last 13 (5,false),
.last 16 (5,false),
.cycle 10 8 false (2),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 21 false (2),
.last 13 (5,false),
.cycle 10 9 false (2),
.cycle 10 4 true (0),
.cycle 10 19 false (3),
.cycle 10 13 false (3),
.cycle 16 1 false (0),
.last 13 (5,false)
])
theorem kid01_part118_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part118) = true := by rfl

def kid01_part119 : Audit := .cycle 14 1 false (0)
theorem kid01_part119_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part119) = true := by rfl

def kid01_part120 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 30 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 12 2 true (-1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.cycle 12 7 false (1),
.cycle 14 1 false (-2),
.cycle 31 1 false (-3),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 3 false (0),
.cycle 17 1 false (-1),
.cycle 12 5 false (1),
.cycle 12 5 false (1),
.cycle 11 3 false (1)
])
theorem kid01_part120_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part120) = true := by rfl

def kid01_part121 : Audit := .cycle 16 1 false (0)
theorem kid01_part121_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part121) = true := by rfl

def kid01_part122 : Audit := .cycle 16 1 false (0)
theorem kid01_part122_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part122) = true := by rfl

def kid01_part123 : Audit := .split 13 (5,false) (byMove [
.cycle 0 30 false (4),
.cycle 6 26 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 10 6 true (-1),
.cycle 27 4 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 15 false (4),
.cycle 17 1 true (1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 19 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 17 false (0),
.cycle 13 1 false (-1),
.cycle 16 19 false (3),
.cycle 2 17 false (4),
.cycle 6 13 false (4),
.cycle 17 5 false (1),
.cycle 17 1 false (-1),
.cycle 20 1 true (-2)
])
theorem kid01_part123_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part123) = true := by rfl

def kid01_part124 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 19 (5,false),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 21 (5,false),
.cycle 10 4 true (1),
.cycle 33 1 false (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 19 (5,false),
.cycle 29 1 false (1),
.last 13 (5,false)
])
theorem kid01_part124_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part124) = true := by rfl

def kid01_part125 : Audit := .cycle 25 1 false (1)
theorem kid01_part125_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part125) = true := by rfl

def kid01_part126 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 20 1 false (2),
.last 14 (0,true),
.cycle 29 1 false (1),
.cycle 12 2 true (1),
.cycle 33 1 false (1),
.cycle 33 1 false (1),
.cycle 6 17 true (0),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 6 13 false (4),
.cycle 23 1 false (-1),
.cycle 12 18 false (3),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 17 3 false (1),
.cycle 10 4 true (1),
.cycle 19 5 false (2),
.cycle 19 5 false (2),
.cycle 6 15 true (1)
])
theorem kid01_part126_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part126) = true := by rfl

def kid01_part127 : Audit := .cycle 29 1 false (1)
theorem kid01_part127_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part127) = true := by rfl

def kid01_part128 : Audit := .cycle 29 1 false (1)
theorem kid01_part128_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part128) = true := by rfl

def kid01_part129 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 17 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (0),
.cycle 6 15 true (0),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.last 18 (0,true),
.cycle 10 5 true (1),
.cycle 6 18 true (0),
.cycle 6 12 true (0),
.cycle 2 18 true (1),
.cycle 20 1 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 36 5 false (4),
.cycle 6 16 true (0),
.cycle 13 1 true (3)
])
theorem kid01_part129_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part129) = true := by rfl

def kid01_part130 : Audit := .split 12 (0,true) (byMove [
.cycle 10 5 false (2),
.last 20 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 32 1 false (-2),
.last 13 (5,false),
.cycle 0 15 true (0),
.cycle 15 1 false (1),
.last 14 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 24 (5,false),
.cycle 13 1 false (-1),
.last 30 (5,false),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 15 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part130_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part130) = true := by rfl

def kid01_part131 : Audit := .cycle 14 1 false (0)
theorem kid01_part131_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part131) = true := by rfl

def kid01_part132 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 32 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 12 2 true (-1),
.cycle 32 1 false (0),
.cycle 32 1 false (0),
.cycle 36 1 false (0),
.cycle 12 4 false (0),
.cycle 6 26 false (4),
.cycle 6 11 false (4),
.cycle 14 1 false (-2),
.cycle 6 35 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 3 false (0),
.cycle 6 13 false (4),
.cycle 5 9 false (4),
.cycle 6 9 false (4),
.cycle 11 3 false (1)
])
theorem kid01_part132_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part132) = true := by rfl

def kid01_part133 : Audit := .cycle 19 1 false (-1)
theorem kid01_part133_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part133) = true := by rfl

def kid01_part134 : Audit := .split 27 (5,false) (byMove [
.last 28 (0,true),
.cycle 30 1 false (-2),
.cycle 31 1 false (-3),
.cycle 32 1 false (-2),
.cycle 32 1 false (-2),
.cycle 13 26 false (3),
.last 28 (0,true),
.cycle 13 20 false (3),
.cycle 26 2 true (-1),
.cycle 13 22 false (3),
.cycle 13 22 false (3),
.cycle 32 1 false (-2),
.last 28 (0,true),
.cycle 30 1 false (-2),
.cycle 6 27 false (4),
.cycle 13 16 false (3),
.cycle 12 16 false (3),
.cycle 42 1 false (-4),
.last 28 (0,true),
.cycle 16 12 false (2),
.cycle 10 18 false (3),
.cycle 15 14 false (3),
.cycle 14 14 false (3),
.cycle 13 16 false (3)
])
theorem kid01_part134_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part134) = true := by rfl

def kid01_part135 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 13 2 true (-1),
.cycle 32 1 false (0),
.cycle 32 1 false (0),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 6 11 false (4),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 13 3 false (0),
.cycle 12 3 false (0),
.cycle 5 9 false (4),
.cycle 6 9 false (4),
.cycle 11 3 false (1)
])
theorem kid01_part135_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part135) = true := by rfl

def kid01_part136 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.last 15 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 18 (5,false),
.last 15 (5,false),
.last 17 (5,false),
.last 25 (5,false),
.last 25 (5,false),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.last 21 (5,false),
.last 13 (5,false)
])
theorem kid01_part136_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part136) = true := by rfl

def kid01_part137 : Audit := .split 17 (5,false) (byMove [
.cycle 10 10 false (2),
.cycle 12 18 false (2),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 6 19 false (4),
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 20 1 false (0),
.cycle 16 2 true (-1),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 1 18 true (-1),
.cycle 15 4 false (1),
.cycle 13 6 false (1),
.cycle 15 7 false (1),
.cycle 18 1 false (-2),
.cycle 12 19 false (2),
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 15 3 false (1),
.cycle 13 5 false (1),
.cycle 15 5 false (1),
.cycle 15 5 false (1),
.cycle 9 21 false (4)
])
theorem kid01_part137_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part137) = true := by rfl

def kid01_part138 : Audit := .cycle 10 2 true (1)
theorem kid01_part138_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part138) = true := by rfl

def kid01_part139 : Audit := .split 21 (5,false) (byMove [
.cycle 10 14 false (3),
.cycle 13 20 false (3),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 6 23 false (4),
.cycle 21 1 false (-1),
.last 22 (0,true),
.cycle 24 1 false (0),
.cycle 20 2 true (-1),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 18 8 true (-1),
.cycle 19 4 false (1),
.cycle 13 14 false (3),
.cycle 18 7 false (2),
.cycle 22 1 false (-2),
.cycle 13 21 false (3),
.cycle 21 1 false (-1),
.last 22 (0,true),
.cycle 19 3 false (1),
.cycle 15 7 false (2),
.cycle 17 5 false (2),
.cycle 18 5 false (2),
.cycle 13 13 false (3)
])
theorem kid01_part139_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part139) = true := by rfl

def kid01_part140 : Audit := .split 21 (5,false) (byMove [
.cycle 10 14 false (3),
.cycle 12 20 false (3),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 6 23 false (4),
.cycle 21 1 false (-1),
.last 22 (0,true),
.cycle 24 1 false (0),
.cycle 20 2 true (-1),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 19 4 false (1),
.cycle 12 14 false (3),
.cycle 17 7 false (2),
.cycle 22 1 false (-2),
.cycle 12 21 false (3),
.cycle 21 1 false (-1),
.last 22 (0,true),
.cycle 19 3 false (1),
.cycle 15 7 false (2),
.cycle 18 5 false (2),
.cycle 17 5 false (2),
.cycle 18 5 false (2)
])
theorem kid01_part140_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part140) = true := by rfl

def kid01_part141 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 14 20 false (2),
.cycle 10 4 true (1),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.last 14 (0,true),
.cycle 11 14 false (3),
.cycle 11 5 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 11 3 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.cycle 8 6 true (1),
.cycle 13 1 true (3)
])
theorem kid01_part141_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part141) = true := by rfl

def kid01_part117 : Audit := .split 11 (5,true) (byMove [(kid01_part118),(kid01_part119),(kid01_part120),(kid01_part121),(kid01_part122),(kid01_part123),(kid01_part124),(kid01_part125),(kid01_part126),(kid01_part127),(kid01_part128),(kid01_part129),(kid01_part130),(kid01_part131),(kid01_part132),(kid01_part133),(kid01_part134),(kid01_part135),(kid01_part136),(kid01_part137),(kid01_part138),(kid01_part139),(kid01_part140),(kid01_part141)])

theorem kid01_part117_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part117) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part118),(kid01_part119),(kid01_part120),(kid01_part121),(kid01_part122),(kid01_part123),(kid01_part124),(kid01_part125),(kid01_part126),(kid01_part127),(kid01_part128),(kid01_part129),(kid01_part130),(kid01_part131),(kid01_part132),(kid01_part133),(kid01_part134),(kid01_part135),(kid01_part136),(kid01_part137),(kid01_part138),(kid01_part139),(kid01_part140),(kid01_part141)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part118_checked

  · exact kid01_part124_checked

  · exact kid01_part130_checked

  · exact kid01_part136_checked

  · exact kid01_part119_checked

  · exact kid01_part125_checked

  · exact kid01_part131_checked

  · exact kid01_part137_checked

  · exact kid01_part120_checked

  · exact kid01_part126_checked

  · exact kid01_part132_checked

  · exact kid01_part138_checked

  · exact kid01_part121_checked

  · exact kid01_part127_checked

  · exact kid01_part133_checked

  · exact kid01_part139_checked

  · exact kid01_part122_checked

  · exact kid01_part128_checked

  · exact kid01_part134_checked

  · exact kid01_part140_checked

  · exact kid01_part123_checked

  · exact kid01_part129_checked

  · exact kid01_part135_checked

  · exact kid01_part141_checked

def kid01_part142 : Audit := .cycle 0 11 true (0)
theorem kid01_part142_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part142) = true := by rfl

def kid01_part143 : Audit := .cycle 1 10 true (1)
theorem kid01_part143_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part143) = true := by rfl

def kid01_part144 : Audit := .cycle 2 9 true (1)
theorem kid01_part144_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part144) = true := by rfl

def kid01_part145 : Audit := .cycle 7 6 true (2)
theorem kid01_part145_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part145) = true := by rfl

def kid01_part146 : Audit := .cycle 20 1 false (0)
theorem kid01_part146_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part146) = true := by rfl

def kid01_part147 : Audit := .split 11 (5,false) (byMove [
.split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 31 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 36 1 false (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 14 5 false (0),
.cycle 23 1 false (-1),
.last 14 (5,true),
.cycle 27 1 false (-1),
.cycle 13 24 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 26 1 false (0),
.cycle 11 2 true (2)
]),
.cycle 20 1 false (0),
.cycle 10 2 true (2),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 31 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 36 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.last 13 (0,true),
.cycle 23 1 false (-1),
.cycle 12 2 true (1),
.cycle 27 1 false (-1),
.cycle 13 24 false (3),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 26 1 false (0),
.cycle 11 2 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 35 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 0 14 true (0),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.last 13 (5,true),
.cycle 14 5 false (0),
.last 19 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.cycle 20 1 false (0),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 26 1 false (0),
.cycle 10 4 true (2),
.cycle 32 1 false (0),
.cycle 32 1 false (0),
.cycle 23 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 2 17 true (1),
.last 14 (0,true),
.cycle 26 1 false (0),
.cycle 12 2 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 11 3 true (2)
]),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 35 1 false (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 2 12 true (1),
.cycle 10 3 true (2),
.cycle 2 14 true (1),
.cycle 2 14 true (1),
.cycle 32 1 false (6),
.last 13 (0,true),
.cycle 12 7 false (2),
.cycle 12 2 true (1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 10 3 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 3 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 8 4 true (2),
.cycle 11 1 true (3)
])
theorem kid01_part147_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part147) = true := by rfl

def kid01_part75 : Audit := .split 10 (2,true) (byMove [(kid01_part76),(kid01_part77),(kid01_part78),(kid01_part79),(kid01_part80),(kid01_part81),(kid01_part106),(kid01_part107),(kid01_part108),(kid01_part109),(kid01_part110),(kid01_part111),(kid01_part112),(kid01_part113),(kid01_part114),(kid01_part115),(kid01_part116),(kid01_part117),(kid01_part142),(kid01_part143),(kid01_part144),(kid01_part145),(kid01_part146),(kid01_part147)])

theorem kid01_part75_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (kid01_part75) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part76),(kid01_part77),(kid01_part78),(kid01_part79),(kid01_part80),(kid01_part81),(kid01_part106),(kid01_part107),(kid01_part108),(kid01_part109),(kid01_part110),(kid01_part111),(kid01_part112),(kid01_part113),(kid01_part114),(kid01_part115),(kid01_part116),(kid01_part117),(kid01_part142),(kid01_part143),(kid01_part144),(kid01_part145),(kid01_part146),(kid01_part147)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part76_checked

  · exact kid01_part106_checked

  · exact kid01_part112_checked

  · exact kid01_part142_checked

  · exact kid01_part77_checked

  · exact kid01_part107_checked

  · exact kid01_part113_checked

  · exact kid01_part143_checked

  · exact kid01_part78_checked

  · exact kid01_part108_checked

  · exact kid01_part114_checked

  · exact kid01_part144_checked

  · exact kid01_part79_checked

  · exact kid01_part109_checked

  · exact kid01_part115_checked

  · exact kid01_part145_checked

  · exact kid01_part80_checked

  · exact kid01_part110_checked

  · exact kid01_part116_checked

  · exact kid01_part146_checked

  · exact kid01_part81_checked

  · exact kid01_part111_checked

  · exact kid01_part117_checked

  · exact kid01_part147_checked

def kid01_part148 : Audit := .cycle 19 1 false (-1)
theorem kid01_part148_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,3⟩)) (kid01_part148) = true := by rfl

def kid01_part149 : Audit := .cycle 10 16 false (3)
theorem kid01_part149_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,4⟩)) (kid01_part149) = true := by rfl

def kid01_part152 : Audit := .cycle 0 13 false (4)
theorem kid01_part152_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part152) = true := by rfl

def kid01_part153 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 14 11 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 11 false (0),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 11 false (2),
.cycle 13 1 true (-1),
.cycle 0 17 false (4),
.last 15 (2,true),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 0 26 false (4),
.cycle 13 1 false (-1),
.cycle 0 28 false (4),
.cycle 1 13 false (4),
.cycle 14 11 false (2),
.cycle 0 20 false (4),
.cycle 12 3 false (0),
.cycle 13 1 true (-1)
])
theorem kid01_part153_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part153) = true := by rfl

def kid01_part154 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (4),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 26 1 false (0),
.last 13 (5,false),
.cycle 0 16 false (4),
.last 16 (5,false),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 0 19 false (4),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part154_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part154) = true := by rfl

def kid01_part155 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 27 1 false (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 28 1 false (-4),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 27 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 28 1 false (-2),
.cycle 15 1 true (-1),
.cycle 0 19 false (4),
.last 17 (2,true),
.cycle 12 5 false (1),
.cycle 16 1 false (-2),
.cycle 0 28 false (4),
.cycle 15 1 false (-1),
.cycle 0 32 false (4),
.cycle 1 15 false (4),
.cycle 26 1 false (-2),
.cycle 0 22 false (4),
.cycle 13 3 false (1),
.cycle 15 1 true (-1)
])
theorem kid01_part155_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part155) = true := by rfl

def kid01_part156 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 16 12 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 12 false (0),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 16 12 false (3),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 12 false (2),
.cycle 15 1 true (-1),
.cycle 0 19 false (4),
.last 17 (2,true),
.cycle 13 5 false (1),
.cycle 16 1 false (-2),
.cycle 0 28 false (4),
.cycle 15 1 false (-1),
.cycle 0 32 false (4),
.cycle 1 15 false (4),
.cycle 16 12 false (2),
.cycle 0 22 false (4),
.cycle 13 3 false (1),
.cycle 15 1 true (-1)
])
theorem kid01_part156_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part156) = true := by rfl

def kid01_part157 : Audit := .cycle 0 13 false (4)
theorem kid01_part157_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part157) = true := by rfl

def kid01_part158 : Audit := .cycle 0 12 true (0)
theorem kid01_part158_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part158) = true := by rfl

def kid01_part159 : Audit := .cycle 1 11 true (1)
theorem kid01_part159_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part159) = true := by rfl

def kid01_part160 : Audit := .cycle 6 12 true (0)
theorem kid01_part160_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part160) = true := by rfl

def kid01_part161 : Audit := .cycle 21 1 false (1)
theorem kid01_part161_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part161) = true := by rfl

def kid01_part162 : Audit := .cycle 1 12 true (1)
theorem kid01_part162_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part162) = true := by rfl

def kid01_part163 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 0 19 false (4),
.cycle 15 13 false (0),
.cycle 0 15 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 0 21 false (4),
.last 14 (2,true),
.last 18 (2,true),
.cycle 22 1 false (0),
.cycle 0 28 false (4),
.last 17 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 19 true (0),
.cycle 0 19 false (4),
.cycle 12 1 true (2)
])
theorem kid01_part163_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part163) = true := by rfl

def kid01_part164 : Audit := .split 22 (5,false) (byMove [
.cycle 11 12 false (2),
.cycle 0 25 false (4),
.last 23 (2,true),
.cycle 0 27 false (4),
.cycle 0 27 false (4),
.cycle 0 28 false (4),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 1, 8192, 16384, 8, 65536, 16384, 1, 8192, 16384, 8, 65536, 65536, 1, 262144],[65544, 128, 262144, 1024, 1024, 16384, 66560, 8, 262144, 65536, 65536, 65536, 65536, 65544, 262144, 65536, 65536, 81920, 262144],262144⟩,
.cycle 9 26 false (4),
.cycle 9 68 false (3),
.cycle 3 20 false (4),
.cycle 9 68 false (3),
.cycle 22 1 true (0),
.cycle 9 56 false (3),
.cycle 14 9 false (2),
.last 23 (2,true),
.cycle 0 32 false (4),
.cycle 0 32 false (4),
.cycle 9 74 false (3),
.cycle 32 112 false (4),
.cycle 9 42 false (4),
.cycle 9 66 false (3),
.cycle 7 18 false (4),
.cycle 0 30 false (4),
.cycle 22 1 true (0)
])
theorem kid01_part164_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part164) = true := by rfl

def kid01_part165 : Audit := .split 13 (5,false) (byMove [
.cycle 11 10 false (2),
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 27 (2,true),
.cycle 13 1 false (-1),
.cycle 0 17 false (4),
.last 15 (2,true),
.cycle 20 1 false (2),
.cycle 14 1 false (0),
.cycle 1 21 false (4),
.cycle 0 16 true (-1),
.last 63 (2,true),
.last 15 (2,true),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 0 26 false (4),
.cycle 13 1 false (-1),
.last 19 (2,true),
.last 15 (2,true),
.cycle 2 17 false (4),
.last 23 (2,true),
.cycle 12 3 false (0),
.cycle 10 5 false (2)
])
theorem kid01_part165_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part165) = true := by rfl

def kid01_part166 : Audit := .split 12 (2,true) (byMove [
.cycle 11 5 false (1),
.last 18 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 18 (5,false),
.last 14 (5,false),
.cycle 15 1 false (3),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 14 true (0),
.last 22 (5,false),
.last 16 (5,false),
.cycle 0 19 false (4),
.cycle 13 1 false (-1),
.last 45 (5,false),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 0 15 false (4),
.cycle 2 12 true (0),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.last 19 (5,false)
])
theorem kid01_part166_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part166) = true := by rfl

def kid01_part167 : Audit := .cycle 0 17 false (4)
theorem kid01_part167_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part167) = true := by rfl

def kid01_part168 : Audit := .cycle 0 17 false (4)
theorem kid01_part168_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part168) = true := by rfl

def kid01_part169 : Audit := .split 15 (2,true) (byMove [
.cycle 11 5 false (1),
.cycle 0 18 false (4),
.cycle 19 1 false (-1),
.cycle 0 20 false (4),
.cycle 0 20 false (4),
.last 18 (5,false),
.cycle 0 16 true (-1),
.last 27 (5,false),
.last 30 (5,false),
.cycle 3 13 false (4),
.last 30 (5,false),
.last 16 (5,false),
.cycle 11 5 false (1),
.last 24 (5,false),
.last 26 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 18 (5,false),
.last 32 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1212253184, 1073741824, 128, 256, 134217728, 1024, 4194304, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1073741824, 1073741824, 128, 1024, 1024, 1048576, 128, 134217728, 524288, 4194304, 4194304, 1073741824, 1074274304, 1073774592, 8192, 65536, 65536, 1073758464, 1073741824, 1073741824, 128, 1024, 1024, 1048576, 1073741824, 1073741824, 128, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.last 28 (5,false),
.cycle 7 11 false (4),
.last 20 (5,false),
.last 16 (5,false)
])
theorem kid01_part169_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part169) = true := by rfl

def kid01_part170 : Audit := .cycle 0 12 true (0)
theorem kid01_part170_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part170) = true := by rfl

def kid01_part171 : Audit := .cycle 1 11 true (1)
theorem kid01_part171_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part171) = true := by rfl

def kid01_part172 : Audit := .cycle 2 10 true (1)
theorem kid01_part172_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part172) = true := by rfl

def kid01_part173 : Audit := .cycle 0 25 false (4)
theorem kid01_part173_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part173) = true := by rfl

def kid01_part174 : Audit := .cycle 0 15 false (4)
theorem kid01_part174_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part174) = true := by rfl

def kid01_part175 : Audit := .split 12 (5,false) (byMove [
.cycle 11 2 true (1),
.cycle 0 15 false (4),
.last 13 (2,true),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.cycle 0 17 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 10 4 true (1),
.cycle 12 9 false (3),
.last 13 (2,true),
.cycle 0 25 false (4),
.cycle 0 25 false (4),
.last 19 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 0 21 false (4),
.cycle 12 1 true (2)
])
theorem kid01_part175_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part175) = true := by rfl

def kid01_part151 : Audit := .split 11 (0,true) (byMove [(kid01_part152),(kid01_part153),(kid01_part154),(kid01_part155),(kid01_part156),(kid01_part157),(kid01_part158),(kid01_part159),(kid01_part160),(kid01_part161),(kid01_part162),(kid01_part163),(kid01_part164),(kid01_part165),(kid01_part166),(kid01_part167),(kid01_part168),(kid01_part169),(kid01_part170),(kid01_part171),(kid01_part172),(kid01_part173),(kid01_part174),(kid01_part175)])

theorem kid01_part151_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part151) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part152),(kid01_part153),(kid01_part154),(kid01_part155),(kid01_part156),(kid01_part157),(kid01_part158),(kid01_part159),(kid01_part160),(kid01_part161),(kid01_part162),(kid01_part163),(kid01_part164),(kid01_part165),(kid01_part166),(kid01_part167),(kid01_part168),(kid01_part169),(kid01_part170),(kid01_part171),(kid01_part172),(kid01_part173),(kid01_part174),(kid01_part175)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part152_checked

  · exact kid01_part158_checked

  · exact kid01_part164_checked

  · exact kid01_part170_checked

  · exact kid01_part153_checked

  · exact kid01_part159_checked

  · exact kid01_part165_checked

  · exact kid01_part171_checked

  · exact kid01_part154_checked

  · exact kid01_part160_checked

  · exact kid01_part166_checked

  · exact kid01_part172_checked

  · exact kid01_part155_checked

  · exact kid01_part161_checked

  · exact kid01_part167_checked

  · exact kid01_part173_checked

  · exact kid01_part156_checked

  · exact kid01_part162_checked

  · exact kid01_part168_checked

  · exact kid01_part174_checked

  · exact kid01_part157_checked

  · exact kid01_part163_checked

  · exact kid01_part169_checked

  · exact kid01_part175_checked

def kid01_part176 : Audit := .split 24 (5,false) (byMove [
.cycle 0 25 false (4),
.cycle 13 12 false (2),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.cycle 13 13 false (2),
.cycle 24 1 false (-2),
.cycle 0 25 false (4),
.cycle 13 12 true (-2),
.cycle 26 1 false (0),
.cycle 25 1 false (-1),
.cycle 13 13 false (2),
.cycle 24 1 true (-2),
.cycle 11 15 false (2),
.split 26 (2,true) (byMove [
.last 27 (0,true),
.cycle 23 4 false (-1),
.cycle 29 1 false (-3),
.cycle 23 6 false (-1),
.cycle 23 6 false (-1),
.cycle 12 15 false (2),
.cycle 1 39 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 24, 64],64⟩,
.cycle 6 27 false (4),
.cycle 15 12 false (2),
.cycle 1 27 false (4),
.cycle 24 3 true (-3),
.last 27 (0,true),
.cycle 23 4 false (-1),
.cycle 11 21 false (2),
.cycle 11 19 false (2),
.cycle 11 19 false (2),
.cycle 23 11 false (-1),
.cycle 9 29 false (3),
.cycle 21 16 false (2),
.cycle 2 25 false (4),
.cycle 19 10 false (2),
.cycle 11 17 false (2),
.cycle 6 30 false (4)
]),
.cycle 23 5 false (-1),
.cycle 25 1 false (-3),
.cycle 11 24 false (2),
.cycle 24 1 false (-2),
.cycle 21 15 false (3),
.cycle 1 24 false (4),
.cycle 14 11 false (2),
.cycle 11 18 false (2),
.cycle 23 3 false (-1),
.cycle 24 1 true (-2)
])
theorem kid01_part176_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part176) = true := by rfl

def kid01_part178 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 false (4),
.cycle 0 24 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 25 false (4),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 25 false (4),
.last 13 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 false (4),
.cycle 20 1 false (0),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part178_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part178) = true := by rfl

def kid01_part179 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 14 11 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 15 11 false (0),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 11 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 11 false (2),
.cycle 13 1 true (-1),
.cycle 18 1 false (-2),
.cycle 11 4 false (1),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 27 1 false (-3),
.cycle 13 1 false (-1),
.cycle 29 1 false (-1),
.cycle 1 13 false (4),
.cycle 14 11 false (2),
.cycle 21 1 false (-1),
.cycle 12 3 false (0),
.cycle 13 1 true (-1)
])
theorem kid01_part179_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part179) = true := by rfl

def kid01_part180 : Audit := .cycle 14 1 false (0)
theorem kid01_part180_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part180) = true := by rfl

def kid01_part181 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 27 1 false (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 28 1 false (-4),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 27 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 28 1 false (-2),
.cycle 15 1 true (-1),
.cycle 20 1 false (-2),
.cycle 11 6 false (1),
.cycle 12 5 false (1),
.cycle 16 1 false (-2),
.cycle 29 1 false (-3),
.cycle 15 1 false (-1),
.cycle 33 1 false (-1),
.cycle 1 15 false (4),
.cycle 26 1 false (-2),
.cycle 23 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 true (-1)
])
theorem kid01_part181_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part181) = true := by rfl

def kid01_part182 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 16 12 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 12 false (0),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 16 12 false (3),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 12 false (2),
.cycle 15 1 true (-1),
.cycle 20 1 false (-2),
.cycle 11 6 false (1),
.cycle 13 5 false (1),
.cycle 16 1 false (-2),
.cycle 29 1 false (-3),
.cycle 15 1 false (-1),
.cycle 33 1 false (-1),
.cycle 1 15 false (4),
.cycle 16 12 false (2),
.cycle 23 1 false (-1),
.cycle 13 3 false (1),
.cycle 15 1 true (-1)
])
theorem kid01_part182_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part182) = true := by rfl

def kid01_part183 : Audit := .cycle 14 1 false (0)
theorem kid01_part183_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part183) = true := by rfl

def kid01_part184 : Audit := .cycle 0 12 true (0)
theorem kid01_part184_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part184) = true := by rfl

def kid01_part185 : Audit := .cycle 1 11 true (1)
theorem kid01_part185_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part185) = true := by rfl

def kid01_part186 : Audit := .cycle 6 12 true (0)
theorem kid01_part186_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part186) = true := by rfl

def kid01_part187 : Audit := .cycle 21 1 false (1)
theorem kid01_part187_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part187) = true := by rfl

def kid01_part188 : Audit := .cycle 1 12 true (1)
theorem kid01_part188_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part188) = true := by rfl

def kid01_part189 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 15 13 false (0),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 22 1 false (0),
.cycle 11 3 true (1),
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.cycle 29 1 false (-3),
.cycle 16 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 37 1 false (1),
.cycle 20 1 false (0),
.cycle 12 1 true (2)
])
theorem kid01_part189_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part189) = true := by rfl

def kid01_part190 : Audit := .split 12 (0,true) (byMove [
.last 24 (5,false),
.last 18 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 18 1 false (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 35 1 false (-3),
.last 13 (5,false),
.cycle 0 14 true (0),
.cycle 16 1 false (0),
.cycle 11 2 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1)
])
theorem kid01_part190_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part190) = true := by rfl

def kid01_part191 : Audit := .split 13 (5,false) (byMove [
.last 21 (0,true),
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 16 false (1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 11 4 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (0),
.cycle 1 21 false (4),
.cycle 17 1 false (1),
.cycle 18 1 false (-2),
.cycle 11 4 false (1),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 27 1 false (-3),
.cycle 13 1 false (-1),
.cycle 11 8 false (1),
.cycle 19 1 false (-1),
.cycle 2 17 false (4),
.cycle 11 12 false (2),
.cycle 12 3 false (0),
.cycle 10 5 false (2)
])
theorem kid01_part191_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part191) = true := by rfl

def kid01_part192 : Audit := .cycle 20 1 false (0)
theorem kid01_part192_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part192) = true := by rfl

def kid01_part193 : Audit := .cycle 18 1 false (0)
theorem kid01_part193_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part193) = true := by rfl

def kid01_part194 : Audit := .cycle 18 1 false (0)
theorem kid01_part194_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part194) = true := by rfl

def kid01_part195 : Audit := .cycle 14 1 false (0)
theorem kid01_part195_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part195) = true := by rfl

def kid01_part196 : Audit := .cycle 0 12 true (0)
theorem kid01_part196_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part196) = true := by rfl

def kid01_part197 : Audit := .cycle 1 11 true (1)
theorem kid01_part197_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part197) = true := by rfl

def kid01_part198 : Audit := .cycle 2 10 true (1)
theorem kid01_part198_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part198) = true := by rfl

def kid01_part199 : Audit := .cycle 26 1 false (0)
theorem kid01_part199_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part199) = true := by rfl

def kid01_part200 : Audit := .cycle 16 1 false (0)
theorem kid01_part200_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part200) = true := by rfl

def kid01_part201 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 13 (0,true),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 22 1 false (0),
.cycle 12 1 true (2)
])
theorem kid01_part201_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part201) = true := by rfl

def kid01_part177 : Audit := .split 11 (2,true) (byMove [(kid01_part178),(kid01_part179),(kid01_part180),(kid01_part181),(kid01_part182),(kid01_part183),(kid01_part184),(kid01_part185),(kid01_part186),(kid01_part187),(kid01_part188),(kid01_part189),(kid01_part190),(kid01_part191),(kid01_part192),(kid01_part193),(kid01_part194),(kid01_part195),(kid01_part196),(kid01_part197),(kid01_part198),(kid01_part199),(kid01_part200),(kid01_part201)])

theorem kid01_part177_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part177) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part178),(kid01_part179),(kid01_part180),(kid01_part181),(kid01_part182),(kid01_part183),(kid01_part184),(kid01_part185),(kid01_part186),(kid01_part187),(kid01_part188),(kid01_part189),(kid01_part190),(kid01_part191),(kid01_part192),(kid01_part193),(kid01_part194),(kid01_part195),(kid01_part196),(kid01_part197),(kid01_part198),(kid01_part199),(kid01_part200),(kid01_part201)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part178_checked

  · exact kid01_part184_checked

  · exact kid01_part190_checked

  · exact kid01_part196_checked

  · exact kid01_part179_checked

  · exact kid01_part185_checked

  · exact kid01_part191_checked

  · exact kid01_part197_checked

  · exact kid01_part180_checked

  · exact kid01_part186_checked

  · exact kid01_part192_checked

  · exact kid01_part198_checked

  · exact kid01_part181_checked

  · exact kid01_part187_checked

  · exact kid01_part193_checked

  · exact kid01_part199_checked

  · exact kid01_part182_checked

  · exact kid01_part188_checked

  · exact kid01_part194_checked

  · exact kid01_part200_checked

  · exact kid01_part183_checked

  · exact kid01_part189_checked

  · exact kid01_part195_checked

  · exact kid01_part201_checked

def kid01_part202 : Audit := .cycle 15 1 false (-1)
theorem kid01_part202_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part202) = true := by rfl

def kid01_part203 : Audit := .split 29 (5,false) (byMove [
.cycle 0 30 false (4),
.cycle 16 14 false (1),
.cycle 31 1 false (-3),
.cycle 30 1 false (-4),
.cycle 15 15 false (1),
.cycle 29 1 false (-3),
.cycle 0 30 false (4),
.cycle 16 14 true (-3),
.cycle 31 1 false (-1),
.cycle 30 1 false (-2),
.cycle 15 15 false (1),
.cycle 29 1 true (-3),
.cycle 13 18 false (1),
.split 31 (2,true) (byMove [
.last 32 (0,true),
.cycle 28 4 false (-2),
.cycle 34 1 false (-4),
.cycle 27 6 false (-1),
.cycle 26 6 false (-1),
.cycle 14 18 false (1),
.cycle 27 20 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 24, 64],64⟩,
.cycle 6 32 false (4),
.cycle 18 14 false (1),
.cycle 1 32 false (4),
.cycle 29 3 true (-4),
.last 32 (0,true),
.cycle 28 4 false (-2),
.cycle 11 24 false (2),
.cycle 11 22 false (2),
.cycle 11 22 false (2),
.cycle 6 34 false (4),
.cycle 7 36 false (4),
.cycle 22 20 false (1),
.cycle 2 30 false (4),
.cycle 22 12 false (1),
.cycle 12 20 false (2),
.cycle 13 20 false (1)
]),
.cycle 27 5 false (-1),
.cycle 30 1 false (-4),
.cycle 11 27 false (2),
.cycle 29 1 false (-3),
.cycle 22 19 false (2),
.cycle 1 29 false (4),
.cycle 17 13 false (1),
.cycle 11 21 false (2),
.cycle 27 3 false (-1),
.cycle 29 1 true (-3)
])
theorem kid01_part203_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part203) = true := by rfl

def kid01_part204 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 13 false (1),
.cycle 13 1 false (-1),
.cycle 0 14 true (-1),
.cycle 11 12 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 11 13 false (2),
.cycle 13 1 true (-1),
.cycle 12 4 false (0),
.split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 18 1 false (-2),
.cycle 13 6 false (-1),
.cycle 13 6 false (-1),
.cycle 12 4 false (0),
.cycle 28 8 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 28, 64],64⟩,
.cycle 6 16 false (4),
.cycle 11 12 false (1),
.cycle 1 16 false (4),
.cycle 13 3 true (-2),
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 12 10 false (0),
.cycle 12 8 false (0),
.cycle 12 8 false (0),
.cycle 12 4 false (0),
.cycle 10 18 false (4),
.cycle 10 16 false (3),
.cycle 2 14 false (4),
.cycle 11 10 false (1),
.cycle 12 6 false (0),
.cycle 12 6 false (0)
]),
.cycle 13 5 false (0),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 10 15 false (4),
.cycle 1 13 false (4),
.cycle 11 11 false (2),
.cycle 12 7 false (1),
.cycle 13 3 false (0),
.cycle 13 1 true (-1)
])
theorem kid01_part204_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part204) = true := by rfl

def kid01_part205 : Audit := .cycle 0 11 true (0)
theorem kid01_part205_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part205) = true := by rfl

def kid01_part206 : Audit := .cycle 1 10 true (1)
theorem kid01_part206_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part206) = true := by rfl

def kid01_part207 : Audit := .cycle 6 11 true (1)
theorem kid01_part207_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part207) = true := by rfl

def kid01_part208 : Audit := .cycle 3 8 true (1)
theorem kid01_part208_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part208) = true := by rfl

def kid01_part209 : Audit := .cycle 1 11 true (1)
theorem kid01_part209_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part209) = true := by rfl

def kid01_part210 : Audit := .split 11 (5,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 15 15 false (2),
.cycle 17 1 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.cycle 9 4 true (2),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 21 4 false (1),
.cycle 18 1 false (0),
.cycle 25 6 false (1),
.cycle 25 6 false (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 11 3 true (2),
.last 14 (0,true),
.cycle 21 4 false (1),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 5 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 10 true (2)
]),
.split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 18 5 false (0),
.cycle 20 1 false (0),
.cycle 18 5 false (1),
.cycle 19 5 false (1),
.cycle 26 5 false (3),
.last 18 (0,true),
.cycle 21 5 false (1),
.cycle 6 21 true (0),
.cycle 23 5 false (2),
.cycle 24 5 false (2),
.cycle 32 5 false (3),
.last 18 (0,true),
.cycle 18 5 false (0),
.cycle 39 5 false (2),
.cycle 31 1 false (-1),
.cycle 24 20 false (3),
.cycle 21 5 false (4),
.last 18 (0,true),
.cycle 29 5 false (2),
.cycle 2 17 true (1),
.cycle 33 5 false (2),
.cycle 33 5 false (2),
.cycle 10 8 true (1)
]),
.cycle 4 8 true (1),
.cycle 12 13 false (2),
.cycle 25 1 false (5),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 25 3 false (2),
.cycle 11 1 true (3)
])
theorem kid01_part210_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part210) = true := by rfl

def kid01_part212 : Audit := .split 19 (5,false) (byMove [
.cycle 0 22 false (4),
.cycle 20 3 false (0),
.last 20 (2,true),
.cycle 22 3 false (0),
.cycle 22 3 false (0),
.last 24 (2,true),
.cycle 0 20 true (-1),
.last 33 (2,true),
.cycle 22 15 false (4),
.cycle 3 17 false (4),
.cycle 26 15 false (4),
.cycle 19 1 true (1),
.cycle 11 9 false (3),
.cycle 20 3 false (0),
.last 20 (2,true),
.last 28 (2,true),
.last 28 (2,true),
.last 24 (2,true),
.cycle 0 74 false (6),
.cycle 0 70 false (5),
.cycle 24 15 false (4),
.cycle 7 15 false (4),
.last 26 (2,true),
.cycle 19 1 true (1)
])
theorem kid01_part212_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part212) = true := by rfl

def kid01_part213 : Audit := .split 13 (5,false) (byMove [
.cycle 27 3 false (-1),
.cycle 12 19 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 22 false (0),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 14 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 15 false (4),
.cycle 16 3 false (2),
.cycle 14 3 false (-1),
.last 15 (2,true),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 24 3 false (-2),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 25 21 false (5),
.cycle 6 13 false (4),
.cycle 18 3 false (0),
.cycle 12 3 false (0),
.cycle 18 3 false (0)
])
theorem kid01_part213_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part213) = true := by rfl

def kid01_part214 : Audit := .split 12 (2,true) (byMove [
.last 19 (5,false),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 13 3 false (2),
.cycle 6 25 true (0),
.last 17 (5,false),
.cycle 13 1 false (1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 1 14 true (0),
.last 17 (5,false),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part214_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part214) = true := by rfl

def kid01_part215 : Audit := .split 15 (5,false) (byMove [
.cycle 31 3 false (-1),
.cycle 27 1 false (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 28 1 false (-4),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 37 3 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.cycle 18 3 false (2),
.cycle 16 3 false (-1),
.last 17 (2,true),
.cycle 12 5 false (1),
.cycle 16 1 false (-2),
.cycle 26 3 false (-2),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 38 1 false (-2),
.cycle 6 15 false (4),
.cycle 20 3 false (0),
.cycle 13 3 false (1),
.cycle 22 3 false (0)
])
theorem kid01_part215_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part215) = true := by rfl

def kid01_part216 : Audit := .split 15 (5,false) (byMove [
.cycle 31 3 false (-1),
.cycle 6 28 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 29 false (4),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 6 36 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.cycle 18 3 false (2),
.cycle 16 3 false (-1),
.last 17 (2,true),
.cycle 13 5 false (1),
.cycle 16 1 false (-2),
.cycle 26 3 false (-2),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 6 39 false (5),
.cycle 6 15 false (4),
.cycle 20 3 false (0),
.cycle 13 3 false (1),
.cycle 22 3 false (0)
])
theorem kid01_part216_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part216) = true := by rfl

def kid01_part217 : Audit := .cycle 12 3 false (0)
theorem kid01_part217_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part217) = true := by rfl

def kid01_part218 : Audit := .cycle 0 13 true (0)
theorem kid01_part218_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part218) = true := by rfl

def kid01_part219 : Audit := .split 13 (5,false) (byMove [
.cycle 0 28 true (0),
.cycle 14 13 false (1),
.last 14 (2,true),
.cycle 18 1 false (-2),
.cycle 16 14 false (0),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1),
.cycle 17 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 17 3 false (1),
.cycle 17 3 false (1),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 27 3 false (1),
.cycle 15 3 false (1),
.cycle 13 1 true (1)
])
theorem kid01_part219_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part219) = true := by rfl

def kid01_part220 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 3 false (1),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 18 3 false (1),
.cycle 15 3 false (1),
.last 17 (5,false),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 28 3 false (2),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part220_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part220) = true := by rfl

def kid01_part221 : Audit := .split 15 (5,false) (byMove [
.cycle 17 1 false (1),
.cycle 16 15 false (1),
.last 16 (2,true),
.cycle 20 1 false (-2),
.cycle 17 16 false (1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (0),
.cycle 29 1 false (1),
.cycle 1 16 true (1),
.cycle 15 1 true (1),
.cycle 21 3 false (0),
.last 19 (2,true),
.last 16 (2,true),
.cycle 19 3 false (1),
.cycle 19 3 false (1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 31 3 false (1),
.cycle 17 3 false (1),
.cycle 15 1 true (1)
])
theorem kid01_part221_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part221) = true := by rfl

def kid01_part222 : Audit := .split 15 (5,false) (byMove [
.cycle 0 33 false (4),
.cycle 16 15 false (1),
.last 16 (2,true),
.cycle 20 1 false (-2),
.cycle 16 16 false (1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (0),
.cycle 29 1 false (1),
.cycle 1 16 true (1),
.cycle 15 1 true (1),
.cycle 21 3 false (0),
.last 19 (2,true),
.last 16 (2,true),
.cycle 19 3 false (1),
.cycle 19 3 false (1),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 31 3 false (1),
.cycle 17 3 false (1),
.cycle 15 1 true (1)
])
theorem kid01_part222_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part222) = true := by rfl

def kid01_part223 : Audit := .cycle 17 3 false (1)
theorem kid01_part223_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part223) = true := by rfl

def kid01_part224 : Audit := .cycle 13 3 false (0)
theorem kid01_part224_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part224) = true := by rfl

def kid01_part225 : Audit := .split 13 (5,false) (byMove [
.cycle 9 14 false (3),
.cycle 27 3 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 27 (2,true),
.cycle 13 1 false (-1),
.cycle 14 3 false (1),
.last 15 (2,true),
.cycle 18 3 false (2),
.cycle 14 1 false (0),
.last 27 (2,true),
.cycle 15 3 false (1),
.cycle 14 3 false (-1),
.last 15 (2,true),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 24 3 false (-2),
.cycle 13 1 false (-1),
.last 19 (2,true),
.last 15 (2,true),
.last 25 (2,true),
.cycle 6 11 false (4),
.cycle 12 3 false (0),
.cycle 10 5 false (2)
])
theorem kid01_part225_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part225) = true := by rfl

def kid01_part226 : Audit := .split 12 (2,true) (byMove [
.cycle 11 5 false (1),
.cycle 28 3 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 31 (5,false),
.last 13 (5,false),
.cycle 18 3 false (2),
.last 14 (5,false),
.cycle 16 1 false (4),
.cycle 16 3 false (2),
.cycle 16 3 false (2),
.cycle 13 3 false (1),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 25 3 false (1),
.cycle 13 1 false (-1),
.cycle 37 3 false (-1),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.cycle 2 13 true (0),
.cycle 23 3 false (1),
.cycle 23 3 false (1),
.cycle 27 3 false (1)
])
theorem kid01_part226_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part226) = true := by rfl

def kid01_part227 : Audit := .cycle 19 1 false (-1)
theorem kid01_part227_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part227) = true := by rfl

def kid01_part228 : Audit := .cycle 16 12 false (2)
theorem kid01_part228_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part228) = true := by rfl

def kid01_part229 : Audit := .cycle 12 3 false (0)
theorem kid01_part229_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part229) = true := by rfl

def kid01_part230 : Audit := .cycle 0 13 true (0)
theorem kid01_part230_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part230) = true := by rfl

def kid01_part231 : Audit := .cycle 15 3 false (1)
theorem kid01_part231_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part231) = true := by rfl

def kid01_part232 : Audit := .split 12 (2,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 3 false (1),
.cycle 16 1 false (0),
.cycle 15 3 false (1),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 11 2 true (1),
.cycle 13 3 false (1),
.cycle 29 3 false (1),
.cycle 23 3 false (1),
.cycle 23 3 false (1),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.cycle 19 3 false (1),
.last 13 (5,false)
])
theorem kid01_part232_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part232) = true := by rfl

def kid01_part233 : Audit := .cycle 19 3 false (1)
theorem kid01_part233_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part233) = true := by rfl

def kid01_part234 : Audit := .cycle 19 3 false (1)
theorem kid01_part234_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part234) = true := by rfl

def kid01_part235 : Audit := .cycle 10 2 true (1)
theorem kid01_part235_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part235) = true := by rfl

def kid01_part211 : Audit := .split 11 (0,true) (byMove [(kid01_part212),(kid01_part213),(kid01_part214),(kid01_part215),(kid01_part216),(kid01_part217),(kid01_part218),(kid01_part219),(kid01_part220),(kid01_part221),(kid01_part222),(kid01_part223),(kid01_part224),(kid01_part225),(kid01_part226),(kid01_part227),(kid01_part228),(kid01_part229),(kid01_part230),(kid01_part231),(kid01_part232),(kid01_part233),(kid01_part234),(kid01_part235)])

theorem kid01_part211_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part211) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part212),(kid01_part213),(kid01_part214),(kid01_part215),(kid01_part216),(kid01_part217),(kid01_part218),(kid01_part219),(kid01_part220),(kid01_part221),(kid01_part222),(kid01_part223),(kid01_part224),(kid01_part225),(kid01_part226),(kid01_part227),(kid01_part228),(kid01_part229),(kid01_part230),(kid01_part231),(kid01_part232),(kid01_part233),(kid01_part234),(kid01_part235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part212_checked

  · exact kid01_part218_checked

  · exact kid01_part224_checked

  · exact kid01_part230_checked

  · exact kid01_part213_checked

  · exact kid01_part219_checked

  · exact kid01_part225_checked

  · exact kid01_part231_checked

  · exact kid01_part214_checked

  · exact kid01_part220_checked

  · exact kid01_part226_checked

  · exact kid01_part232_checked

  · exact kid01_part215_checked

  · exact kid01_part221_checked

  · exact kid01_part227_checked

  · exact kid01_part233_checked

  · exact kid01_part216_checked

  · exact kid01_part222_checked

  · exact kid01_part228_checked

  · exact kid01_part234_checked

  · exact kid01_part217_checked

  · exact kid01_part223_checked

  · exact kid01_part229_checked

  · exact kid01_part235_checked

def kid01_part237 : Audit := .split 15 (0,true) (byMove [
.last 31 (5,false),
.last 27 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 28 (5,false),
.last 16 (5,false),
.cycle 0 20 true (-1),
.last 21 (5,false),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.last 16 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.last 20 (5,false),
.cycle 16 1 false (-2),
.last 22 (5,false),
.last 16 (5,false),
.last 36 (5,false),
.last 21 (5,false),
.cycle 6 15 false (4),
.cycle 11 9 false (1),
.last 18 (5,false),
.last 16 (5,false)
])
theorem kid01_part237_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part237) = true := by rfl

def kid01_part238 : Audit := .split 16 (5,false) (byMove [
.cycle 0 17 false (4),
.cycle 6 29 false (4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 13 false (-1),
.cycle 16 1 false (-2),
.cycle 0 106 false (6),
.cycle 6 17 false (4),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 1 37 false (4),
.cycle 24 1 true (0),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 15 5 false (-1),
.cycle 17 1 false (-3),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 35 20 false (3),
.cycle 1 39 false (4),
.cycle 2 31 false (4),
.cycle 11 10 false (1),
.cycle 15 3 false (-1),
.cycle 9 12 false (3)
])
theorem kid01_part238_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part238) = true := by rfl

def kid01_part239 : Audit := .cycle 17 1 false (-1)
theorem kid01_part239_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part239) = true := by rfl

def kid01_part240 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 false (4),
.cycle 6 31 false (4),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 13 false (-1),
.cycle 18 1 false (-2),
.cycle 0 118 false (6),
.cycle 6 19 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 1 39 false (4),
.cycle 28 1 true (0),
.cycle 11 9 false (1),
.cycle 13 6 false (0),
.cycle 15 5 false (0),
.cycle 19 1 false (-3),
.cycle 11 18 false (1),
.cycle 18 1 false (-2),
.cycle 37 24 false (3),
.cycle 1 45 false (4),
.cycle 2 33 false (4),
.cycle 11 12 false (1),
.cycle 16 3 false (0),
.cycle 9 14 false (3)
])
theorem kid01_part240_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part240) = true := by rfl

def kid01_part241 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 false (4),
.cycle 6 31 false (4),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 17 13 false (-1),
.cycle 18 1 false (-2),
.cycle 0 118 false (6),
.cycle 6 19 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 1 39 false (4),
.cycle 28 1 true (0),
.cycle 11 9 false (1),
.cycle 13 6 false (0),
.cycle 16 5 false (0),
.cycle 19 1 false (-3),
.cycle 11 18 false (1),
.cycle 18 1 false (-2),
.cycle 37 24 false (3),
.cycle 1 45 false (4),
.cycle 2 33 false (4),
.cycle 11 12 false (1),
.cycle 16 3 false (0),
.cycle 9 14 false (3)
])
theorem kid01_part241_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part241) = true := by rfl

def kid01_part242 : Audit := .cycle 12 3 false (0)
theorem kid01_part242_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part242) = true := by rfl

def kid01_part243 : Audit := .cycle 0 20 true (-1)
theorem kid01_part243_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part243) = true := by rfl

def kid01_part244 : Audit := .split 28 (5,false) (byMove [
.last 29 (0,true),
.cycle 6 45 false (6),
.cycle 117 1 false (-1),
.cycle 37 1 false (-3),
.cycle 35 13 false (-1),
.cycle 110 1 false (-4),
.cycle 15 17 true (1),
.cycle 15 14 true (1),
.cycle 13 63 true (-2),
.cycle 6 27 true (-1),
.cycle 13 63 true (-2),
.cycle 15 16 true (1),
.last 29 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 2, 16, 16, 2, 64],64⟩,
.cycle 38 5 false (0),
.cycle 143 1 false (-5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 28, 2, 16, 16, 18, 64],64⟩,
.cycle 36 1 false (-2),
.cycle 9 21 true (-1),
.cycle 15 14 true (1),
.cycle 13 55 true (-2),
.cycle 4 25 true (-1),
.cycle 125 3 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 36, 2, 16, 16, 2, 64],64⟩
])
theorem kid01_part244_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part244) = true := by rfl

def kid01_part245 : Audit := .split 19 (5,false) (byMove [
.last 42 (0,true),
.cycle 1 19 false (4),
.cycle 32 1 false (-2),
.cycle 6 28 false (4),
.cycle 21 13 false (-1),
.cycle 6 24 false (4),
.cycle 0 20 true (-1),
.cycle 6 34 true (-1),
.cycle 43 1 false (1),
.cycle 6 19 false (4),
.cycle 46 23 false (4),
.cycle 19 1 true (1),
.cycle 21 21 false (1),
.cycle 37 25 false (3),
.cycle 28 1 false (2),
.cycle 29 1 false (-3),
.cycle 6 37 false (4),
.cycle 79 1 false (-5),
.cycle 221 25 true (1),
.cycle 1 19 true (-1),
.cycle 40 19 false (4),
.cycle 39 9 false (1),
.cycle 6 28 false (4),
.cycle 19 1 true (1)
])
theorem kid01_part245_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part245) = true := by rfl

def kid01_part246 : Audit := .cycle 6 13 false (4)
theorem kid01_part246_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part246) = true := by rfl

def kid01_part247 : Audit := .split 21 (5,false) (byMove [
.last 22 (0,true),
.cycle 1 26 false (4),
.cycle 1 23 false (4),
.cycle 1 28 false (4),
.cycle 1 28 false (4),
.cycle 24 1 false (-2),
.cycle 0 22 true (-1),
.cycle 1 36 true (-1),
.cycle 43 1 false (1),
.cycle 3 19 false (4),
.cycle 28 23 false (4),
.cycle 21 1 true (1),
.last 22 (0,true),
.cycle 11 11 false (3),
.cycle 29 5 false (1),
.cycle 29 1 false (-3),
.cycle 1 43 false (4),
.cycle 24 1 false (-2),
.cycle 35 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 16, 16, 16, 16, 64],64⟩,
.cycle 26 19 false (4),
.cycle 7 17 false (4),
.cycle 25 3 false (-1),
.cycle 21 1 true (1)
])
theorem kid01_part247_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part247) = true := by rfl

def kid01_part248 : Audit := .split 15 (5,false) (byMove [
.last 44 (0,true),
.cycle 1 26 false (4),
.cycle 6 15 false (4),
.cycle 11 9 false (1),
.cycle 17 13 false (-1),
.cycle 12 5 false (1),
.last 16 (0,true),
.cycle 17 15 true (1),
.cycle 47 1 false (1),
.cycle 6 19 false (4),
.cycle 46 23 false (4),
.cycle 19 1 true (3),
.cycle 11 11 false (1),
.cycle 19 3 true (1),
.cycle 21 10 true (0),
.cycle 6 13 false (4),
.cycle 11 18 false (1),
.cycle 35 1 false (-3),
.last 16 (0,true),
.cycle 1 20 true (-1),
.cycle 14 55 true (-2),
.cycle 17 9 true (0),
.cycle 29 3 false (-1),
.cycle 10 16 false (2)
])
theorem kid01_part248_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part248) = true := by rfl

def kid01_part249 : Audit := .split 15 (0,true) (byMove [
.last 27 (5,false),
.last 21 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.last 16 (5,false),
.cycle 0 24 true (-1),
.last 17 (5,false),
.cycle 11 7 false (1),
.last 19 (5,false),
.last 19 (5,false),
.cycle 12 4 true (-1),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 9 false (1),
.cycle 16 1 false (-2),
.last 34 (5,false),
.last 16 (5,false),
.cycle 9 9 false (3),
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 18 (5,false)
])
theorem kid01_part249_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part249) = true := by rfl

def kid01_part250 : Audit := .split 16 (5,false) (byMove [
.last 24 (0,true),
.cycle 6 17 false (4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 15 13 false (-1),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 4 true (-2),
.cycle 23 1 false (1),
.cycle 17 1 false (-1),
.cycle 15 23 false (3),
.cycle 12 6 true (-2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 15 5 false (-1),
.cycle 17 1 false (-3),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.cycle 15 5 false (0),
.cycle 11 8 false (1),
.cycle 15 19 false (3),
.cycle 15 9 false (1),
.cycle 15 3 false (-1),
.cycle 10 8 false (2)
])
theorem kid01_part250_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part250) = true := by rfl

def kid01_part251 : Audit := .cycle 11 9 false (1)
theorem kid01_part251_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part251) = true := by rfl

def kid01_part252 : Audit := .cycle 11 7 false (1)
theorem kid01_part252_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part252) = true := by rfl

def kid01_part253 : Audit := .cycle 11 7 false (1)
theorem kid01_part253_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part253) = true := by rfl

def kid01_part254 : Audit := .cycle 12 3 false (0)
theorem kid01_part254_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part254) = true := by rfl

def kid01_part255 : Audit := .cycle 9 7 false (3)
theorem kid01_part255_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part255) = true := by rfl

def kid01_part256 : Audit := .split 32 (5,false) (byMove [
.last 40 (0,true),
.cycle 27 29 false (3),
.cycle 34 1 false (-2),
.cycle 33 1 false (-3),
.cycle 29 13 false (1),
.cycle 32 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 2, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 2, 16, 16, 2, 64],64⟩,
.cycle 39 1 false (1),
.cycle 33 1 false (-1),
.cycle 27 23 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 36, 2, 16, 16, 2, 64],64⟩,
.last 44 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 2, 16, 16, 2, 64],64⟩,
.cycle 31 5 false (-1),
.cycle 33 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 28, 2, 16, 16, 18, 64],64⟩,
.cycle 32 1 false (-2),
.cycle 29 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 2, 16, 16, 2, 64],64⟩,
.cycle 27 19 false (3),
.cycle 29 9 false (1),
.cycle 31 3 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 36, 2, 16, 16, 2, 64],64⟩
])
theorem kid01_part256_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part256) = true := by rfl

def kid01_part257 : Audit := .split 19 (5,false) (byMove [
.last 20 (0,true),
.cycle 2 22 false (4),
.cycle 2 19 false (4),
.cycle 2 24 false (4),
.cycle 2 24 false (4),
.cycle 22 1 false (-2),
.cycle 0 20 true (-1),
.cycle 2 32 true (-1),
.cycle 41 1 false (1),
.cycle 3 17 false (4),
.cycle 26 23 false (4),
.cycle 19 1 true (1),
.last 20 (0,true),
.cycle 11 9 false (3),
.cycle 33 5 false (-1),
.cycle 27 1 false (-3),
.cycle 2 39 false (4),
.cycle 22 1 false (-2),
.cycle 33 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 4, 16, 16, 20, 64],64⟩,
.cycle 24 19 false (4),
.cycle 7 15 false (4),
.cycle 23 3 false (-1),
.cycle 19 1 true (1)
])
theorem kid01_part257_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part257) = true := by rfl

def kid01_part258 : Audit := .cycle 4 11 false (4)
theorem kid01_part258_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part258) = true := by rfl

def kid01_part259 : Audit := .cycle 11 5 false (1)
theorem kid01_part259_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part259) = true := by rfl

def kid01_part260 : Audit := .split 15 (5,false) (byMove [
.last 16 (0,true),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.cycle 18 1 false (-2),
.last 16 (0,true),
.cycle 17 15 true (1),
.cycle 6 18 true (-1),
.cycle 3 17 false (4),
.cycle 26 23 false (4),
.cycle 19 1 true (3),
.last 16 (0,true),
.cycle 11 5 false (1),
.cycle 10 7 false (2),
.cycle 5 11 false (4),
.cycle 6 11 false (4),
.cycle 18 1 false (-2),
.last 16 (0,true),
.cycle 9 7 false (3),
.cycle 27 19 false (3),
.cycle 8 9 false (4),
.cycle 7 9 false (4),
.cycle 10 12 false (2)
])
theorem kid01_part260_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part260) = true := by rfl

def kid01_part236 : Audit := .split 14 (2,true) (byMove [(kid01_part237),(kid01_part238),(kid01_part239),(kid01_part240),(kid01_part241),(kid01_part242),(kid01_part243),(kid01_part244),(kid01_part245),(kid01_part246),(kid01_part247),(kid01_part248),(kid01_part249),(kid01_part250),(kid01_part251),(kid01_part252),(kid01_part253),(kid01_part254),(kid01_part255),(kid01_part256),(kid01_part257),(kid01_part258),(kid01_part259),(kid01_part260)])

theorem kid01_part236_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part236) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid01_part237),(kid01_part238),(kid01_part239),(kid01_part240),(kid01_part241),(kid01_part242),(kid01_part243),(kid01_part244),(kid01_part245),(kid01_part246),(kid01_part247),(kid01_part248),(kid01_part249),(kid01_part250),(kid01_part251),(kid01_part252),(kid01_part253),(kid01_part254),(kid01_part255),(kid01_part256),(kid01_part257),(kid01_part258),(kid01_part259),(kid01_part260)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part237_checked

  · exact kid01_part243_checked

  · exact kid01_part249_checked

  · exact kid01_part255_checked

  · exact kid01_part238_checked

  · exact kid01_part244_checked

  · exact kid01_part250_checked

  · exact kid01_part256_checked

  · exact kid01_part239_checked

  · exact kid01_part245_checked

  · exact kid01_part251_checked

  · exact kid01_part257_checked

  · exact kid01_part240_checked

  · exact kid01_part246_checked

  · exact kid01_part252_checked

  · exact kid01_part258_checked

  · exact kid01_part241_checked

  · exact kid01_part247_checked

  · exact kid01_part253_checked

  · exact kid01_part259_checked

  · exact kid01_part242_checked

  · exact kid01_part248_checked

  · exact kid01_part254_checked

  · exact kid01_part260_checked

def kid01_part262 : Audit := .split 12 (0,true) (byMove [
.last 19 (5,false),
.cycle 6 13 false (4),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 32 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.cycle 13 15 true (1),
.last 17 (5,false),
.cycle 13 1 false (1),
.last 19 (5,false),
.last 13 (5,false),
.last 20 (5,false),
.cycle 11 3 false (1),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 9 31 false (5),
.cycle 1 15 true (0),
.last 17 (5,false),
.cycle 16 11 false (3),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part262_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part262) = true := by rfl

def kid01_part263 : Audit := .split 13 (5,false) (byMove [
.cycle 0 34 false (4),
.cycle 12 19 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 22 false (0),
.cycle 13 1 false (-1),
.cycle 0 24 true (-1),
.cycle 14 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 15 false (4),
.cycle 21 1 true (1),
.cycle 12 8 false (0),
.cycle 11 4 false (1),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 12 17 false (0),
.cycle 13 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 28, 16, 16, 28, 64],64⟩,
.cycle 25 21 false (5),
.cycle 6 13 false (4),
.cycle 12 11 false (1),
.cycle 12 3 false (0),
.cycle 9 35 false (3)
])
theorem kid01_part263_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part263) = true := by rfl

def kid01_part264 : Audit := .cycle 14 1 false (0)
theorem kid01_part264_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part264) = true := by rfl

def kid01_part265 : Audit := .split 15 (5,false) (byMove [
.cycle 0 38 false (4),
.cycle 27 1 false (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 28 1 false (-4),
.cycle 15 1 false (-1),
.cycle 0 28 true (-1),
.cycle 6 44 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.cycle 23 1 true (1),
.cycle 12 8 false (1),
.cycle 11 6 false (1),
.cycle 12 5 false (1),
.cycle 16 1 false (-2),
.cycle 12 17 false (1),
.cycle 15 1 false (-1),
.cycle 24 1 false (-2),
.cycle 38 1 false (-2),
.cycle 6 15 false (4),
.cycle 12 11 false (1),
.cycle 13 3 false (1),
.cycle 39 1 false (-3)
])
theorem kid01_part265_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part265) = true := by rfl

def kid01_part266 : Audit := .split 15 (5,false) (byMove [
.cycle 0 38 false (4),
.cycle 6 28 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 29 false (4),
.cycle 15 1 false (-1),
.cycle 0 28 true (-1),
.cycle 6 36 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 6 17 false (4),
.cycle 23 1 true (1),
.cycle 13 8 false (1),
.cycle 11 6 false (1),
.cycle 13 5 false (1),
.cycle 16 1 false (-2),
.cycle 13 17 false (1),
.cycle 15 1 false (-1),
.cycle 6 25 false (4),
.cycle 6 39 false (5),
.cycle 6 15 false (4),
.cycle 13 11 false (1),
.cycle 13 3 false (1),
.cycle 6 40 false (4)
])
theorem kid01_part266_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part266) = true := by rfl

def kid01_part267 : Audit := .split 17 (5,false) (byMove [
.last 41 (0,true),
.cycle 6 30 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 13 false (0),
.cycle 17 1 false (-1),
.cycle 0 32 true (-1),
.cycle 19 20 true (1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 6 19 false (4),
.cycle 25 1 true (1),
.cycle 12 8 false (1),
.cycle 11 8 false (1),
.cycle 13 5 false (1),
.cycle 18 1 false (-2),
.cycle 12 17 false (1),
.cycle 17 1 false (-1),
.cycle 10 11 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 28, 16, 16, 28, 64],64⟩,
.cycle 6 17 false (4),
.cycle 12 11 false (1),
.cycle 15 3 false (1),
.cycle 10 16 false (2)
])
theorem kid01_part267_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part267) = true := by rfl

def kid01_part268 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 23 (5,false),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (0),
.cycle 6 12 true (0),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 25 (5,false),
.cycle 0 15 true (0),
.last 17 (5,false),
.cycle 22 1 false (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 23 (5,false),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part268_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part268) = true := by rfl

def kid01_part269 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 14 13 false (1),
.cycle 29 1 false (1),
.cycle 18 1 false (-2),
.cycle 16 14 false (0),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 13 1 true (1),
.last 14 (0,true),
.cycle 18 15 true (0),
.cycle 15 5 false (1),
.cycle 24 1 false (-2),
.cycle 12 17 false (2),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 21 11 false (2),
.cycle 19 3 false (1),
.cycle 13 1 true (1)
])
theorem kid01_part269_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part269) = true := by rfl

def kid01_part270 : Audit := .cycle 6 15 true (0)
theorem kid01_part270_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part270) = true := by rfl

def kid01_part271 : Audit := .split 15 (5,false) (byMove [
.last 16 (0,true),
.cycle 16 15 false (1),
.cycle 17 1 false (1),
.cycle 20 1 false (-2),
.cycle 17 16 false (1),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (0),
.cycle 29 1 false (1),
.cycle 1 16 true (1),
.cycle 15 1 true (1),
.last 16 (0,true),
.cycle 6 18 false (4),
.cycle 17 5 false (2),
.cycle 26 1 false (-2),
.cycle 12 17 false (3),
.cycle 27 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 23 11 false (2),
.cycle 21 3 false (1),
.cycle 15 1 true (1)
])
theorem kid01_part271_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part271) = true := by rfl

def kid01_part272 : Audit := .split 15 (5,false) (byMove [
.last 16 (0,true),
.cycle 16 15 false (1),
.cycle 34 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 16 false (1),
.cycle 21 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (0),
.cycle 29 1 false (1),
.cycle 1 16 true (1),
.cycle 15 1 true (1),
.last 16 (0,true),
.cycle 24 26 false (2),
.cycle 18 5 false (2),
.cycle 26 1 false (-2),
.cycle 13 17 false (3),
.cycle 27 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 24 11 false (2),
.cycle 21 3 false (1),
.cycle 15 1 true (1)
])
theorem kid01_part272_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part272) = true := by rfl

def kid01_part273 : Audit := .split 17 (5,false) (byMove [
.last 18 (0,true),
.cycle 18 17 false (1),
.cycle 21 1 false (1),
.cycle 22 1 false (-2),
.cycle 19 18 false (1),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (0),
.cycle 33 1 false (1),
.cycle 1 18 true (1),
.cycle 17 1 true (1),
.last 18 (0,true),
.cycle 32 23 false (1),
.cycle 20 5 false (2),
.cycle 28 1 false (-2),
.cycle 13 17 false (3),
.cycle 29 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 25 11 false (2),
.cycle 23 3 false (1),
.cycle 17 1 true (1)
])
theorem kid01_part273_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part273) = true := by rfl

def kid01_part274 : Audit := .split 12 (0,true) (byMove [
.last 30 (5,false),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 31 (5,false),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 14 (5,false),
.last 21 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 24 (5,false),
.last 20 (5,false),
.cycle 11 3 false (1),
.last 28 (5,false),
.cycle 13 1 false (-1),
.last 34 (5,false),
.last 13 (5,false),
.cycle 0 15 true (0),
.last 19 (5,false),
.cycle 11 2 true (0),
.last 26 (5,false),
.last 26 (5,false),
.last 22 (5,false)
])
theorem kid01_part274_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part274) = true := by rfl

def kid01_part275 : Audit := .split 13 (5,false) (byMove [
.last 27 (0,true),
.cycle 11 35 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 16 false (1),
.cycle 13 1 false (-1),
.cycle 15 10 true (-1),
.cycle 11 4 true (-1),
.cycle 26 1 false (2),
.cycle 14 1 false (0),
.cycle 1 27 false (4),
.cycle 26 1 true (0),
.cycle 12 8 false (0),
.cycle 11 4 false (1),
.cycle 12 5 false (0),
.cycle 14 1 false (-2),
.cycle 12 17 false (0),
.cycle 13 1 false (-1),
.cycle 11 8 false (1),
.cycle 54 35 false (3),
.cycle 2 23 false (4),
.cycle 6 11 false (4),
.cycle 12 3 false (0),
.cycle 10 5 false (2)
])
theorem kid01_part275_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part275) = true := by rfl

def kid01_part276 : Audit := .split 31 (5,false) (byMove [
.cycle 0 32 false (4),
.cycle 14 22 false (3),
.cycle 33 1 false (-1),
.cycle 32 1 false (-2),
.cycle 14 23 false (3),
.cycle 31 1 false (-1),
.cycle 0 32 true (-1),
.cycle 14 22 true (-1),
.cycle 33 1 false (1),
.cycle 32 1 false (0),
.cycle 14 23 false (3),
.cycle 31 1 true (-1),
.cycle 25 8 false (1),
.cycle 20 14 false (2),
.cycle 27 5 false (1),
.cycle 32 1 false (-2),
.cycle 23 17 false (2),
.cycle 31 1 false (-1),
.cycle 6 43 false (4),
.cycle 1 31 false (4),
.cycle 14 21 false (3),
.cycle 22 11 false (2),
.cycle 29 3 false (1),
.cycle 31 1 true (-1)
])
theorem kid01_part276_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part276) = true := by rfl

def kid01_part277 : Audit := .cycle 19 1 false (-1)
theorem kid01_part277_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part277) = true := by rfl

def kid01_part278 : Audit := .split 31 (5,false) (byMove [
.last 32 (0,true),
.cycle 13 26 false (3),
.cycle 27 8 false (1),
.cycle 36 1 false (-4),
.cycle 13 29 false (3),
.cycle 37 1 false (-3),
.cycle 6 52 false (4),
.cycle 20 26 true (-3),
.cycle 6 32 false (4),
.cycle 13 22 false (3),
.cycle 1 32 false (4),
.cycle 31 1 true (-1),
.last 32 (0,true),
.cycle 32 12 false (-2),
.cycle 18 14 false (2),
.cycle 42 1 false (-4),
.cycle 27 17 false (1),
.cycle 43 1 false (-3),
.cycle 6 46 false (4),
.cycle 6 38 false (4),
.cycle 2 30 false (4),
.cycle 14 20 false (3),
.cycle 37 3 false (-1),
.cycle 31 1 true (-1)
])
theorem kid01_part278_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part278) = true := by rfl

def kid01_part279 : Audit := .split 21 (5,false) (byMove [
.cycle 19 6 false (1),
.cycle 14 26 false (3),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 21 1 false (-1),
.last 22 (0,true),
.cycle 14 28 true (-1),
.cycle 20 2 true (-1),
.cycle 32 1 false (0),
.cycle 14 23 false (3),
.cycle 33 1 true (-1),
.cycle 21 8 false (-1),
.cycle 6 22 false (4),
.cycle 13 9 false (3),
.cycle 22 1 false (-2),
.cycle 6 29 false (4),
.cycle 21 1 false (-1),
.last 22 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 28, 16, 16, 28, 64],64⟩,
.cycle 11 11 false (3),
.cycle 16 7 false (3),
.cycle 15 7 false (3),
.cycle 19 3 false (1)
])
theorem kid01_part279_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part279) = true := by rfl

def kid01_part280 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.last 19 (5,false),
.cycle 0 14 true (0),
.last 21 (5,false),
.last 21 (5,false),
.last 21 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.last 22 (5,false),
.last 19 (5,false),
.cycle 11 2 true (1),
.last 29 (5,false),
.last 29 (5,false),
.last 37 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (1),
.last 25 (5,false),
.last 13 (5,false)
])
theorem kid01_part280_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part280) = true := by rfl

def kid01_part281 : Audit := .split 21 (5,false) (byMove [
.cycle 0 22 false (4),
.cycle 12 18 false (2),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.cycle 12 19 false (2),
.cycle 21 1 false (-1),
.cycle 0 22 true (-1),
.cycle 12 18 true (-1),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 12 19 false (2),
.cycle 21 1 true (-1),
.cycle 15 8 false (1),
.cycle 9 26 false (3),
.cycle 17 5 false (1),
.cycle 22 1 false (-2),
.cycle 15 17 false (1),
.cycle 21 1 false (-1),
.cycle 9 25 false (4),
.cycle 1 21 false (4),
.cycle 12 17 false (2),
.cycle 15 11 false (1),
.cycle 19 3 false (1),
.cycle 21 1 true (-1)
])
theorem kid01_part281_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part281) = true := by rfl

def kid01_part282 : Audit := .cycle 2 11 true (1)
theorem kid01_part282_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part282) = true := by rfl

def kid01_part283 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 false (4),
.cycle 13 20 false (3),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 13 21 false (3),
.cycle 25 1 false (-1),
.cycle 0 26 true (-1),
.cycle 13 20 true (-1),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 13 21 false (3),
.cycle 25 1 true (-1),
.cycle 19 8 false (1),
.cycle 13 18 false (3),
.cycle 21 5 false (1),
.cycle 26 1 false (-2),
.cycle 18 17 false (2),
.cycle 25 1 false (-1),
.cycle 8 31 false (4),
.cycle 1 25 false (4),
.cycle 13 19 false (3),
.cycle 18 11 false (2),
.cycle 23 3 false (1),
.cycle 25 1 true (-1)
])
theorem kid01_part283_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part283) = true := by rfl

def kid01_part284 : Audit := .split 25 (5,false) (byMove [
.cycle 0 26 false (4),
.cycle 12 20 false (3),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 12 21 false (3),
.cycle 25 1 false (-1),
.cycle 0 26 true (-1),
.cycle 12 20 true (-1),
.cycle 27 1 false (1),
.cycle 26 1 false (0),
.cycle 12 21 false (3),
.cycle 25 1 true (-1),
.cycle 19 8 false (1),
.cycle 18 10 false (2),
.cycle 21 5 false (1),
.cycle 26 1 false (-2),
.cycle 17 17 false (2),
.cycle 25 1 false (-1),
.cycle 7 31 false (4),
.cycle 1 25 false (4),
.cycle 12 19 false (3),
.cycle 17 11 false (2),
.cycle 23 3 false (1),
.cycle 25 1 true (-1)
])
theorem kid01_part284_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part284) = true := by rfl

def kid01_part285 : Audit := .cycle 10 2 true (1)
theorem kid01_part285_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part285) = true := by rfl

def kid01_part261 : Audit := .split 11 (2,true) (byMove [(kid01_part262),(kid01_part263),(kid01_part264),(kid01_part265),(kid01_part266),(kid01_part267),(kid01_part268),(kid01_part269),(kid01_part270),(kid01_part271),(kid01_part272),(kid01_part273),(kid01_part274),(kid01_part275),(kid01_part276),(kid01_part277),(kid01_part278),(kid01_part279),(kid01_part280),(kid01_part281),(kid01_part282),(kid01_part283),(kid01_part284),(kid01_part285)])

theorem kid01_part261_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part261) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part262),(kid01_part263),(kid01_part264),(kid01_part265),(kid01_part266),(kid01_part267),(kid01_part268),(kid01_part269),(kid01_part270),(kid01_part271),(kid01_part272),(kid01_part273),(kid01_part274),(kid01_part275),(kid01_part276),(kid01_part277),(kid01_part278),(kid01_part279),(kid01_part280),(kid01_part281),(kid01_part282),(kid01_part283),(kid01_part284),(kid01_part285)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part262_checked

  · exact kid01_part268_checked

  · exact kid01_part274_checked

  · exact kid01_part280_checked

  · exact kid01_part263_checked

  · exact kid01_part269_checked

  · exact kid01_part275_checked

  · exact kid01_part281_checked

  · exact kid01_part264_checked

  · exact kid01_part270_checked

  · exact kid01_part276_checked

  · exact kid01_part282_checked

  · exact kid01_part265_checked

  · exact kid01_part271_checked

  · exact kid01_part277_checked

  · exact kid01_part283_checked

  · exact kid01_part266_checked

  · exact kid01_part272_checked

  · exact kid01_part278_checked

  · exact kid01_part284_checked

  · exact kid01_part267_checked

  · exact kid01_part273_checked

  · exact kid01_part279_checked

  · exact kid01_part285_checked

def kid01_part286 : Audit := .cycle 21 1 false (-1)
theorem kid01_part286_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part286) = true := by rfl

def kid01_part287 : Audit := .split 27 (5,false) (byMove [
.split 28 (0,true) (byMove [
.cycle 0 29 false (4),
.cycle 11 23 false (3),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 11 24 false (3),
.cycle 0 30 false (4),
.cycle 0 29 false (4),
.cycle 11 23 false (3),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 11 24 false (3),
.cycle 0 30 false (4),
.cycle 19 11 false (1),
.last 30 (2,true),
.cycle 0 34 false (4),
.cycle 29 1 false (-3),
.cycle 21 8 false (1),
.last 32 (2,true),
.cycle 6 34 false (4),
.cycle 1 28 false (4),
.cycle 11 22 false (3),
.cycle 17 14 false (2),
.cycle 0 32 false (4),
.cycle 27 2 true (-2)
]),
.cycle 11 24 false (3),
.split 28 (2,true) (byMove [
.cycle 0 29 false (4),
.cycle 11 23 false (3),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 11 24 false (3),
.cycle 31 1 false (-3),
.cycle 0 29 false (4),
.cycle 11 23 false (3),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 11 24 false (3),
.cycle 31 1 false (-1),
.cycle 19 11 false (1),
.cycle 34 1 false (-4),
.cycle 35 1 false (-3),
.cycle 29 1 false (-3),
.cycle 21 8 false (1),
.cycle 31 1 false (-3),
.cycle 6 34 false (4),
.cycle 1 28 false (4),
.cycle 11 22 false (3),
.cycle 17 14 false (2),
.cycle 33 1 false (-3),
.cycle 27 2 true (-2)
]),
.cycle 32 1 false (-4),
.cycle 11 27 false (3),
.cycle 20 8 false (1),
.split 54 (2,true) (byMove [
.last 55 (0,true),
.cycle 19 36 false (4),
.cycle 58 1 false (-2),
.cycle 18 38 false (4),
.cycle 17 38 false (4),
.cycle 15 40 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 1, 16, 16, 17, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 2, 16, 16, 18, 64],64⟩,
.cycle 6 60 false (4),
.cycle 3 52 false (4),
.cycle 6 60 false (4),
.cycle 34 98 false (6),
.last 55 (0,true),
.cycle 47 20 false (1),
.cycle 11 48 false (4),
.cycle 12 44 false (4),
.cycle 11 44 false (4),
.cycle 11 46 false (4),
.cycle 6 70 false (5),
.cycle 6 64 false (4),
.cycle 6 58 false (4),
.cycle 7 50 false (4),
.cycle 13 42 false (4),
.cycle 34 70 false (6)
]),
.cycle 22 24 true (-3),
.cycle 6 28 false (4),
.cycle 11 20 false (3),
.cycle 1 28 false (4),
.cycle 27 1 true (-1),
.split 28 (0,true) (byMove [
.last 31 (2,true),
.cycle 22 7 false (1),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 6 30 false (4),
.cycle 19 12 false (1),
.cycle 0 30 true (-2),
.cycle 19 13 false (1),
.last 29 (2,true),
.cycle 19 15 false (1),
.cycle 19 15 false (1),
.cycle 20 9 false (1),
.cycle 19 11 false (1),
.last 30 (2,true),
.cycle 17 14 false (2),
.cycle 29 1 false (-3),
.cycle 19 22 false (1),
.cycle 19 12 false (1),
.cycle 6 40 false (4),
.cycle 19 10 false (1),
.last 29 (2,true),
.cycle 18 12 false (2),
.cycle 17 12 false (2),
.cycle 15 14 false (2)
]),
.split 31 (2,true) (byMove [
.last 32 (0,true),
.cycle 28 4 false (-2),
.cycle 34 1 false (-4),
.cycle 28 6 false (-2),
.cycle 28 6 false (-2),
.cycle 20 12 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 31, 64],[64, 30, 1, 16, 16, 17, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 16, 64],64⟩,
.cycle 6 44 false (4),
.cycle 6 30 false (4),
.cycle 19 20 false (1),
.cycle 18 18 false (2),
.last 32 (0,true),
.cycle 28 4 false (-2),
.cycle 17 18 false (2),
.cycle 17 16 false (2),
.cycle 16 16 false (2),
.cycle 28 14 false (-2),
.cycle 9 24 false (3),
.cycle 6 48 false (4),
.cycle 19 18 false (1),
.cycle 4 28 false (4),
.cycle 18 14 false (2),
.cycle 19 14 false (1)
]),
.split 28 (2,true) (byMove [
.last 32 (0,true),
.cycle 22 7 false (1),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 6 30 false (4),
.cycle 29 5 false (-2),
.last 29 (0,true),
.cycle 29 5 false (-1),
.cycle 31 1 false (1),
.cycle 29 5 false (0),
.cycle 30 5 false (0),
.cycle 20 9 false (1),
.cycle 19 11 false (1),
.cycle 31 5 false (-3),
.cycle 17 14 false (2),
.cycle 29 1 false (-3),
.cycle 37 5 false (-3),
.cycle 11 21 false (3),
.last 29 (0,true),
.cycle 19 10 false (1),
.cycle 2 28 false (4),
.cycle 18 12 false (2),
.cycle 17 12 false (2),
.cycle 15 14 false (2)
]),
.cycle 17 12 false (2),
.cycle 16 12 false (2),
.cycle 39 1 false (-5),
.cycle 6 38 false (4),
.cycle 6 32 false (4),
.cycle 2 26 false (4),
.cycle 12 18 false (3),
.cycle 18 10 false (2),
.cycle 27 1 true (-1)
])
theorem kid01_part287_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part287) = true := by rfl

def kid01_part289 : Audit := .split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 12 6 false (0),
.cycle 20 1 false (-2),
.cycle 12 8 false (0),
.cycle 12 8 false (0),
.cycle 11 6 false (1),
.last 17 (0,true),
.last 19 (0,true),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 4, 1024, 1024, 16384, 16777216, 32768, 16384, 1024, 1024, 16384, 16777216, 18907136, 16384, 4194304, 4194304, 17842176, 16777216, 18907136, 1048576, 4194304, 4194304, 17842176, 16777216],33503232⟩,
.last 23 (0,true),
.last 23 (0,true),
.last 19 (0,true),
.last 17 (0,true),
.cycle 12 6 false (0),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 18907136, 4194304, 4194304, 4194304, 20972544, 16777216, 23069696, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 0, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 18907136, 1024, 4194304, 4194304, 20972544, 16777216, 23069696, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 4194304, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 18907136, 4195328, 4194304, 4194304, 20972544, 16777216, 23069696, 20972544, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 11 6 false (1),
.last 17 (0,true),
.cycle 9 8 false (3),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 256, 1024, 1024, 256, 16777216, 32768, 256, 1024, 1024, 256, 16777216, 18907136, 1048576, 4194304, 4194304, 17826048, 16777216, 18907136, 1048576, 4194304, 4194304, 17826048, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 512, 1024, 1024, 512, 16777216, 1024, 512, 1024, 1024, 1024, 16777216, 18907136, 2097152, 4194304, 4194304, 18874880, 16777216, 23069696, 2097152, 4194304, 4194304, 23069696, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 32768, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 18907136, 4194304, 4194304, 4194304, 20972544, 16777216, 23069696, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 10 8 false (2)
])
theorem kid01_part289_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part289) = true := by rfl

def kid01_part290 : Audit := .cycle 22 22 false (0)
theorem kid01_part290_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part290) = true := by rfl

def kid01_part291 : Audit := .cycle 15 1 false (-1)
theorem kid01_part291_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part291) = true := by rfl

def kid01_part292 : Audit := .cycle 14 1 false (-2)
theorem kid01_part292_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part292) = true := by rfl

def kid01_part293 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 64, 16, 16, 16, 64],64⟩
theorem kid01_part293_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part293) = true := by rfl

def kid01_part294 : Audit := .cycle 13 1 false (-1)
theorem kid01_part294_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part294) = true := by rfl

def kid01_part295 : Audit := .split 14 (0,true) (byMove [
.last 17 (2,true),
.cycle 1 23 false (4),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 1, 8192, 16384, 8, 65536, 16384, 1, 8192, 16384, 8, 65536, 65544, 1, 262144],[65544, 128, 262144, 1024, 1024, 65544, 16384, 65544, 262144, 65536, 65536, 66560, 65544, 81928, 262144, 65536, 65536, 65536, 262144],262144⟩,
.last 24 (2,true),
.cycle 0 17 true (-1),
.cycle 0 37 true (-1),
.last 15 (2,true),
.cycle 22 1 false (2),
.cycle 0 40 true (-1),
.cycle 0 22 true (-1),
.cycle 12 5 false (0),
.last 16 (2,true),
.cycle 0 38 true (-1),
.cycle 15 1 false (-1),
.last 32 (2,true),
.cycle 13 2 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 1, 64],[1, 2, 64, 16, 16, 1, 64],64⟩,
.last 20 (2,true),
.last 15 (2,true),
.cycle 24 8 true (-1),
.cycle 0 32 true (-1),
.cycle 11 4 true (-1)
])
theorem kid01_part295_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part295) = true := by rfl

def kid01_part296 : Audit := .split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 24 18 true (1),
.cycle 20 1 false (0),
.cycle 24 20 true (1),
.cycle 25 20 true (1),
.cycle 26 20 true (1),
.last 18 (0,true),
.cycle 20 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 4, 16, 16, 28, 64],64⟩,
.cycle 24 14 true (1),
.cycle 1 38 true (-1),
.cycle 21 17 true (1),
.last 18 (0,true),
.cycle 14 4 true (-1),
.cycle 20 26 true (-1),
.cycle 18 24 true (-1),
.cycle 19 24 true (-1),
.cycle 12 6 true (-1),
.last 18 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 2, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 4, 16, 16, 28, 64],64⟩,
.cycle 19 12 true (-1),
.cycle 18 22 true (-1),
.cycle 10 8 true (-1)
])
theorem kid01_part296_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part296) = true := by rfl

def kid01_part297 : Audit := .split 14 (2,true) (byMove [
.last 18 (0,true),
.cycle 1 23 false (4),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 26 1 false (2),
.last 15 (0,true),
.cycle 23 1 false (3),
.cycle 18 1 false (4),
.cycle 22 1 false (2),
.cycle 41 1 false (3),
.cycle 23 1 false (5),
.cycle 12 5 false (0),
.cycle 51 1 false (1),
.cycle 39 1 false (1),
.cycle 15 1 false (-1),
.cycle 31 1 false (-1),
.cycle 13 2 true (-1),
.last 15 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 28, 2, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 8, 4, 16, 16, 4, 64],64⟩,
.cycle 24 8 true (-1),
.cycle 33 1 false (1),
.cycle 11 4 true (-1)
])
theorem kid01_part297_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part297) = true := by rfl

def kid01_part298 : Audit := .cycle 32 1 false (0)
theorem kid01_part298_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part298) = true := by rfl

def kid01_part299 : Audit := .cycle 15 23 false (3)
theorem kid01_part299_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part299) = true := by rfl

def kid01_part300 : Audit := .cycle 12 2 true (-1)
theorem kid01_part300_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part300) = true := by rfl

def kid01_part301 : Audit := .cycle 12 4 false (0)
theorem kid01_part301_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part301) = true := by rfl

def kid01_part302 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 18 1 false (-2),
.cycle 13 6 false (-1),
.cycle 13 6 false (-1),
.cycle 12 4 false (0),
.last 16 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 20, 64],[64, 24, 4, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 8, 16, 16, 16, 64],64⟩,
.cycle 38 20 false (-2),
.cycle 12 16 false (0),
.last 16 (0,true),
.cycle 13 4 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 12 4 false (0),
.last 16 (0,true),
.cycle 11 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 20, 64],[64, 24, 4, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 10 6 false (2)
])
theorem kid01_part302_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part302) = true := by rfl

def kid01_part303 : Audit := .cycle 6 11 false (4)
theorem kid01_part303_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part303) = true := by rfl

def kid01_part304 : Audit := .cycle 14 1 false (-2)
theorem kid01_part304_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part304) = true := by rfl

def kid01_part305 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 64, 16, 16, 16, 64],64⟩
theorem kid01_part305_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part305) = true := by rfl

def kid01_part306 : Audit := .cycle 13 1 false (-1)
theorem kid01_part306_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part306) = true := by rfl

def kid01_part307 : Audit := .split 14 (0,true) (byMove [
.cycle 0 29 false (4),
.last 19 (2,true),
.last 15 (2,true),
.last 21 (2,true),
.last 21 (2,true),
.cycle 12 3 false (0),
.cycle 0 17 true (-1),
.cycle 9 9 false (3),
.last 15 (2,true),
.cycle 3 19 false (4),
.cycle 52 96 false (5),
.cycle 12 26 true (-1),
.cycle 12 6 false (0),
.cycle 11 8 false (1),
.last 15 (2,true),
.cycle 6 11 false (4),
.cycle 6 11 false (4),
.cycle 12 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 1, 64],[1, 2, 64, 16, 16, 1, 64],64⟩,
.cycle 11 5 false (1),
.last 15 (2,true),
.cycle 7 9 false (4),
.cycle 6 9 false (4),
.cycle 10 5 false (2)
])
theorem kid01_part307_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part307) = true := by rfl

def kid01_part308 : Audit := .cycle 12 3 false (0)
theorem kid01_part308_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part308) = true := by rfl

def kid01_part309 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 12 3 false (0),
.last 15 (0,true),
.cycle 59 37 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 8, 4, 16, 16, 4, 64],64⟩,
.cycle 3 19 false (4),
.cycle 24 27 false (4),
.cycle 15 16 true (0),
.last 15 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 16, 16, 16, 16, 64],64⟩,
.cycle 6 13 false (4),
.cycle 6 11 false (4),
.cycle 6 11 false (4),
.cycle 12 3 false (0),
.last 15 (0,true),
.cycle 11 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 8, 4, 16, 16, 4, 64],64⟩,
.cycle 7 9 false (4),
.cycle 6 9 false (4),
.cycle 10 5 false (2)
])
theorem kid01_part309_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part309) = true := by rfl

def kid01_part310 : Audit := .cycle 5 9 false (4)
theorem kid01_part310_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part310) = true := by rfl

def kid01_part311 : Audit := .cycle 6 9 false (4)
theorem kid01_part311_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part311) = true := by rfl

def kid01_part312 : Audit := .cycle 11 3 false (1)
theorem kid01_part312_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part312) = true := by rfl

def kid01_part288 : Audit := .split 13 (5,false) (byMove [(kid01_part289),(kid01_part290),(kid01_part291),(kid01_part292),(kid01_part293),(kid01_part294),(kid01_part295),(kid01_part296),(kid01_part297),(kid01_part298),(kid01_part299),(kid01_part300),(kid01_part301),(kid01_part302),(kid01_part303),(kid01_part304),(kid01_part305),(kid01_part306),(kid01_part307),(kid01_part308),(kid01_part309),(kid01_part310),(kid01_part311),(kid01_part312)])

theorem kid01_part288_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part288) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) 13 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (5,false) (some mv)) (byMove [(kid01_part289),(kid01_part290),(kid01_part291),(kid01_part292),(kid01_part293),(kid01_part294),(kid01_part295),(kid01_part296),(kid01_part297),(kid01_part298),(kid01_part299),(kid01_part300),(kid01_part301),(kid01_part302),(kid01_part303),(kid01_part304),(kid01_part305),(kid01_part306),(kid01_part307),(kid01_part308),(kid01_part309),(kid01_part310),(kid01_part311),(kid01_part312)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid01_part294_checked

  · exact kid01_part300_checked

  · exact kid01_part306_checked

  · exact kid01_part312_checked

def kid01_part313 : Audit := .cycle 0 11 true (0)
theorem kid01_part313_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part313) = true := by rfl

def kid01_part314 : Audit := .cycle 1 10 true (1)
theorem kid01_part314_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part314) = true := by rfl

def kid01_part315 : Audit := .cycle 2 9 true (1)
theorem kid01_part315_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part315) = true := by rfl

def kid01_part316 : Audit := .cycle 7 6 true (2)
theorem kid01_part316_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part316) = true := by rfl

def kid01_part317 : Audit := .split 19 (5,false) (byMove [
.cycle 0 20 false (4),
.cycle 11 16 false (3),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 11 17 false (3),
.cycle 19 1 false (-1),
.cycle 0 20 true (-1),
.cycle 11 16 true (-1),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.cycle 11 17 false (3),
.cycle 19 1 true (-1),
.cycle 15 6 false (1),
.split 21 (2,true) (byMove [
.last 22 (0,true),
.cycle 18 4 false (0),
.cycle 24 1 false (-2),
.cycle 17 6 false (1),
.cycle 17 6 false (1),
.cycle 16 6 false (1),
.cycle 37 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 18, 64],[64, 28, 2, 16, 16, 16, 64],64⟩,
.cycle 6 22 false (4),
.cycle 11 16 false (3),
.cycle 1 22 false (4),
.cycle 19 3 true (-2),
.last 22 (0,true),
.cycle 18 4 false (0),
.cycle 14 12 false (2),
.cycle 14 10 false (2),
.cycle 14 10 false (2),
.cycle 14 10 false (2),
.cycle 8 28 false (4),
.cycle 8 24 false (4),
.cycle 2 20 false (4),
.cycle 11 14 false (3),
.cycle 14 8 false (2),
.cycle 15 8 false (1)
]),
.cycle 17 5 false (1),
.cycle 20 1 false (-2),
.cycle 14 15 false (2),
.cycle 19 1 false (-1),
.cycle 8 23 false (4),
.cycle 1 19 false (4),
.cycle 11 15 false (3),
.cycle 14 9 false (2),
.cycle 17 3 false (1),
.cycle 19 1 true (-1)
])
theorem kid01_part317_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part317) = true := by rfl

def kid01_part318 : Audit := .split 11 (5,false) (byMove [
.split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 0 31 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 0 36 false (4),
.cycle 0 20 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 14 5 false (0),
.last 18 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 25 8 false (1),
.cycle 10 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 26 false (4),
.cycle 11 2 true (2)
]),
.cycle 12 16 false (2),
.split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 32 1 false (-2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 37 1 false (-3),
.cycle 21 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 13 (0,true),
.cycle 22 1 false (-2),
.cycle 39 1 false (-1),
.cycle 27 1 false (-1),
.cycle 25 8 false (1),
.cycle 10 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 27 1 false (-1),
.cycle 11 2 true (2)
]),
.cycle 26 1 false (-2),
.cycle 12 21 false (3),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 11 1 true (3),
.split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 15 7 false (2),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 16 6 false (1),
.cycle 0 14 true (0),
.cycle 17 7 false (1),
.last 13 (2,true),
.cycle 21 9 false (2),
.cycle 21 9 false (2),
.cycle 10 3 true (2),
.cycle 14 5 false (0),
.last 18 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 10 5 true (1),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 10 3 true (2)
]),
.split 21 (2,true) (byMove [
.last 22 (0,true),
.cycle 18 4 false (0),
.cycle 24 1 false (-2),
.cycle 18 6 false (0),
.cycle 18 6 false (0),
.cycle 16 6 false (1),
.cycle 17 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 30, 64],[64, 30, 2, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 20, 64],[64, 28, 4, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 8, 16, 16, 32, 64],64⟩,
.cycle 32 18 false (2),
.cycle 30 18 false (3),
.last 22 (0,true),
.cycle 18 4 false (0),
.cycle 15 12 false (1),
.cycle 15 10 false (1),
.cycle 15 10 false (1),
.cycle 13 10 false (2),
.cycle 9 14 false (3),
.cycle 9 18 false (3),
.cycle 30 16 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 8, 16, 16, 32, 64],64⟩,
.cycle 15 8 false (1),
.cycle 14 8 false (2)
]),
.split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 15 7 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 19 5 false (0),
.last 13 (0,true),
.cycle 19 5 false (1),
.cycle 6 16 true (1),
.cycle 23 5 false (2),
.cycle 24 5 false (2),
.cycle 10 3 true (2),
.last 13 (0,true),
.cycle 19 5 false (-1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 10 5 true (1),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 10 3 true (2)
]),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.cycle 10 3 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 8 4 true (2),
.cycle 11 1 true (3)
])
theorem kid01_part318_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part318) = true := by rfl

def kid01_part150 : Audit := .split 10 (5,true) (byMove [(kid01_part151),(kid01_part176),(kid01_part177),(kid01_part202),(kid01_part203),(kid01_part204),(kid01_part205),(kid01_part206),(kid01_part207),(kid01_part208),(kid01_part209),(kid01_part210),(kid01_part211),(kid01_part236),(kid01_part261),(kid01_part286),(kid01_part287),(kid01_part288),(kid01_part313),(kid01_part314),(kid01_part315),(kid01_part316),(kid01_part317),(kid01_part318)])

theorem kid01_part150_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (kid01_part150) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part151),(kid01_part176),(kid01_part177),(kid01_part202),(kid01_part203),(kid01_part204),(kid01_part205),(kid01_part206),(kid01_part207),(kid01_part208),(kid01_part209),(kid01_part210),(kid01_part211),(kid01_part236),(kid01_part261),(kid01_part286),(kid01_part287),(kid01_part288),(kid01_part313),(kid01_part314),(kid01_part315),(kid01_part316),(kid01_part317),(kid01_part318)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part151_checked

  · exact kid01_part205_checked

  · exact kid01_part211_checked

  · exact kid01_part313_checked

  · exact kid01_part176_checked

  · exact kid01_part206_checked

  · exact kid01_part236_checked

  · exact kid01_part314_checked

  · exact kid01_part177_checked

  · exact kid01_part207_checked

  · exact kid01_part261_checked

  · exact kid01_part315_checked

  · exact kid01_part202_checked

  · exact kid01_part208_checked

  · exact kid01_part286_checked

  · exact kid01_part316_checked

  · exact kid01_part203_checked

  · exact kid01_part209_checked

  · exact kid01_part287_checked

  · exact kid01_part317_checked

  · exact kid01_part204_checked

  · exact kid01_part210_checked

  · exact kid01_part288_checked

  · exact kid01_part318_checked

def kid01_part319 : Audit := .cycle 0 10 true (0)
theorem kid01_part319_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,0⟩)) (kid01_part319) = true := by rfl

def kid01_part320 : Audit := .cycle 1 9 true (1)
theorem kid01_part320_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,1⟩)) (kid01_part320) = true := by rfl

def kid01_part321 : Audit := .cycle 6 10 true (2)
theorem kid01_part321_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,2⟩)) (kid01_part321) = true := by rfl

def kid01_part322 : Audit := .cycle 3 7 true (1)
theorem kid01_part322_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,3⟩)) (kid01_part322) = true := by rfl

def kid01_part323 : Audit := .cycle 1 10 true (1)
theorem kid01_part323_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,4⟩)) (kid01_part323) = true := by rfl

def kid01_part325 : Audit := .cycle 0 11 true (0)
theorem kid01_part325_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part325) = true := by rfl

def kid01_part326 : Audit := .cycle 1 10 true (1)
theorem kid01_part326_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part326) = true := by rfl

def kid01_part327 : Audit := .cycle 2 9 true (1)
theorem kid01_part327_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part327) = true := by rfl

def kid01_part328 : Audit := .cycle 7 6 true (2)
theorem kid01_part328_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part328) = true := by rfl

def kid01_part329 : Audit := .cycle 11 17 false (3)
theorem kid01_part329_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part329) = true := by rfl

def kid01_part330 : Audit := .split 12 (5,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 0 15 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 0 17 false (4),
.last 39 (2,true),
.cycle 0 16 true (0),
.last 14 (2,true),
.cycle 0 21 false (4),
.cycle 0 21 false (4),
.last 17 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 31 false (4),
.cycle 0 19 false (4),
.cycle 0 19 false (4)
]),
.cycle 30 1 false (0),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 17 1 false (1),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 20 1 false (0),
.cycle 20 1 false (0)
]),
.cycle 19 1 false (-1),
.cycle 35 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.split 13 (0,true) (byMove [
.last 28 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 14 5 false (1),
.cycle 0 15 true (0),
.cycle 16 5 false (2),
.last 14 (2,true),
.cycle 18 5 false (2),
.cycle 18 5 false (2),
.cycle 21 5 false (2),
.cycle 9 13 false (4),
.last 26 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 18 16 false (3),
.cycle 9 13 false (4),
.cycle 0 15 true (0),
.cycle 19 5 false (2),
.last 14 (2,true),
.cycle 23 5 false (2),
.cycle 23 5 false (2),
.cycle 12 2 true (1)
]),
.split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 24 1 false (0),
.cycle 20 1 false (0),
.cycle 28 1 false (0),
.cycle 28 1 false (0),
.cycle 19 3 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 17 true (1),
.cycle 3 14 true (1),
.cycle 1 17 true (1),
.cycle 21 5 false (2),
.last 17 (0,true),
.cycle 13 4 true (1),
.cycle 29 11 false (2),
.cycle 25 9 false (2),
.cycle 25 9 false (2),
.cycle 19 3 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (1),
.cycle 23 7 false (2),
.cycle 11 6 true (1)
]),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 14 (0,true),
.cycle 23 1 false (1),
.cycle 6 17 true (0),
.cycle 25 1 false (1),
.cycle 25 1 false (1),
.cycle 27 1 false (1),
.last 14 (0,true),
.cycle 28 1 false (2),
.cycle 37 1 false (1),
.cycle 23 1 false (-1),
.cycle 45 1 false (-1),
.cycle 25 1 false (-1),
.last 14 (0,true),
.cycle 27 1 false (1),
.cycle 2 13 true (1),
.cycle 31 1 false (1),
.cycle 31 1 false (1),
.cycle 12 2 true (1)
]),
.cycle 27 1 false (-1),
.cycle 24 10 false (2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 25 1 false (1),
.cycle 11 2 true (2)
])
theorem kid01_part330_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part330) = true := by rfl

def kid01_part331 : Audit := .cycle 0 11 true (0)
theorem kid01_part331_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part331) = true := by rfl

def kid01_part332 : Audit := .cycle 1 10 true (1)
theorem kid01_part332_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part332) = true := by rfl

def kid01_part333 : Audit := .cycle 6 13 true (2)
theorem kid01_part333_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part333) = true := by rfl

def kid01_part334 : Audit := .cycle 6 10 true (2)
theorem kid01_part334_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part334) = true := by rfl

def kid01_part335 : Audit := .cycle 1 11 true (1)
theorem kid01_part335_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part335) = true := by rfl

def kid01_part336 : Audit := .cycle 10 1 true (4)
theorem kid01_part336_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part336) = true := by rfl

def kid01_part337 : Audit := .cycle 9 3 true (3)
theorem kid01_part337_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part337) = true := by rfl

def kid01_part338 : Audit := .split 12 (2,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 14 23 false (3),
.cycle 0 17 false (4),
.cycle 35 1 false (-1),
.cycle 14 28 false (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.last 19 (5,true),
.last 15 (5,true),
.cycle 14 5 false (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 16 (5,true)
]),
.cycle 9 4 true (3),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 14 23 false (3),
.cycle 22 1 false (-2),
.cycle 35 1 false (-1),
.cycle 14 28 false (3),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 10 4 true (3),
.last 14 (0,true),
.cycle 25 3 false (1),
.cycle 17 8 true (-3),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 16 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 13 3 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 10 3 true (3),
.split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 6 27 true (-1),
.cycle 14 7 false (2),
.cycle 35 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 1024, 4096, 4096],[1024, 32, 32, 1024, 1024, 4096, 1024, 32, 1024, 1024, 1024, 4096, 4096],6144⟩,
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 9 5 true (3),
.cycle 9 7 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true),
.last 19 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 9 5 true (3),
.cycle 12 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (2),
.cycle 15 29 false (3),
.cycle 22 5 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 1 15 true (1),
.cycle 10 5 true (3),
.cycle 9 7 true (3),
.cycle 11 4 true (3),
.cycle 8 9 true (3),
.cycle 4 11 true (1),
.cycle 6 35 true (-1),
.cycle 22 5 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (3),
.cycle 13 3 true (3)
]),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 1024, 4096, 4096],[4096, 32, 1024, 1024, 1024, 4096, 4096, 32, 1024, 1024, 1024, 4096, 4096],6144⟩,
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 6 27 true (-1),
.cycle 22 1 false (-2),
.cycle 35 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 32, 16, 16, 16, 24, 64],64⟩,
.cycle 16 4 false (0),
.last 14 (0,true),
.cycle 9 5 true (3),
.cycle 35 5 false (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 10 5 true (3),
.last 14 (0,true),
.cycle 25 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 16 4 false (0),
.last 14 (0,true),
.cycle 9 5 true (3),
.cycle 12 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 14 3 true (4)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 22 9 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 1 16 true (1),
.cycle 10 6 true (3),
.cycle 9 8 true (3),
.cycle 11 5 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 6 16 true (2),
.cycle 27 6 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 13 3 true (4)
])
])
theorem kid01_part338_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part338) = true := by rfl

def kid01_part339 : Audit := .cycle 8 5 true (3)
theorem kid01_part339_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part339) = true := by rfl

def kid01_part340 : Audit := .cycle 4 7 true (1)
theorem kid01_part340_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part340) = true := by rfl

def kid01_part341 : Audit := .cycle 6 19 true (-1)
theorem kid01_part341_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part341) = true := by rfl

def kid01_part343 : Audit := .split 13 (0,true) (byMove [
.cycle 0 34 false (5),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 0 34 false (5),
.cycle 0 17 true (0),
.last 15 (2,true),
.last 24 (2,true),
.cycle 6 13 true (0),
.last 26 (2,true),
.last 19 (2,true),
.last 30 (2,true),
.last 28 (2,true),
.last 14 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.last 17 (2,true),
.cycle 0 17 true (0),
.last 15 (2,true),
.last 24 (2,true),
.cycle 6 11 true (1),
.last 21 (2,true),
.last 21 (2,true)
])
theorem kid01_part343_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part343) = true := by rfl

def kid01_part344 : Audit := .cycle 6 15 true (-1)
theorem kid01_part344_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part344) = true := by rfl

def kid01_part345 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 2 15 true (1),
.cycle 6 22 true (0),
.cycle 6 24 true (0),
.cycle 6 13 true (0),
.cycle 6 24 true (1),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 17 1 false (1),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 2 15 true (1),
.cycle 9 7 true (1),
.cycle 6 22 true (1),
.cycle 6 11 true (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0)
])
theorem kid01_part345_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part345) = true := by rfl

def kid01_part346 : Audit := .cycle 19 1 false (-1)
theorem kid01_part346_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part346) = true := by rfl

def kid01_part347 : Audit := .cycle 51 1 false (-1)
theorem kid01_part347_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part347) = true := by rfl

def kid01_part348 : Audit := .cycle 15 1 false (-1)
theorem kid01_part348_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part348) = true := by rfl

def kid01_part349 : Audit := .split 13 (0,true) (byMove [
.last 16 (2,true),
.cycle 7 20 true (2),
.cycle 6 13 true (1),
.cycle 32 1 false (0),
.cycle 6 21 false (4),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 1 23 true (1),
.last 14 (2,true),
.cycle 5 18 true (1),
.cycle 6 18 true (1),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 7 9 true (2),
.cycle 6 11 true (1),
.cycle 6 19 true (-1),
.cycle 20 1 false (0),
.cycle 0 15 true (0),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0)
])
theorem kid01_part349_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part349) = true := by rfl

def kid01_part350 : Audit := .cycle 1 14 true (1)
theorem kid01_part350_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part350) = true := by rfl

def kid01_part351 : Audit := .split 13 (2,true) (byMove [
.last 17 (0,true),
.cycle 7 20 true (2),
.cycle 6 13 true (1),
.cycle 32 1 false (0),
.cycle 6 21 false (4),
.cycle 20 1 false (0),
.last 14 (0,true),
.cycle 1 23 true (1),
.cycle 6 19 true (1),
.cycle 5 18 true (1),
.cycle 6 18 true (1),
.cycle 6 19 true (1),
.cycle 6 19 true (2),
.cycle 6 27 true (1),
.cycle 7 9 true (2),
.cycle 6 11 true (1),
.cycle 6 19 true (-1),
.cycle 20 1 false (0),
.last 14 (0,true),
.cycle 9 5 true (2),
.cycle 2 13 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 6 15 true (2)
])
theorem kid01_part351_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part351) = true := by rfl

def kid01_part352 : Audit := .cycle 7 7 true (2)
theorem kid01_part352_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part352) = true := by rfl

def kid01_part353 : Audit := .cycle 6 7 true (2)
theorem kid01_part353_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part353) = true := by rfl

def kid01_part354 : Audit := .cycle 37 1 false (7)
theorem kid01_part354_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part354) = true := by rfl

def kid01_part355 : Audit := .split 13 (0,true) (byMove [
.last 29 (2,true),
.cycle 15 1 false (1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 45 1 false (-3),
.cycle 0 17 true (0),
.cycle 9 11 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (1),
.cycle 9 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 9 17 true (0),
.last 14 (2,true),
.cycle 6 11 true (0),
.cycle 6 11 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 0 17 true (0),
.cycle 9 11 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (1),
.cycle 12 2 true (1)
])
theorem kid01_part355_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part355) = true := by rfl

def kid01_part356 : Audit := .split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 24 1 false (0),
.cycle 20 1 false (0),
.cycle 28 1 false (0),
.cycle 28 1 false (0),
.cycle 19 3 false (1),
.last 17 (0,true),
.cycle 1 20 true (1),
.cycle 6 23 true (1),
.cycle 14 9 true (1),
.cycle 14 9 true (1),
.cycle 10 13 true (1),
.last 17 (0,true),
.cycle 13 4 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 13 true (1),
.cycle 6 13 true (1),
.cycle 19 3 false (1),
.last 17 (0,true),
.cycle 1 20 true (1),
.cycle 2 17 true (1),
.cycle 7 11 true (1),
.cycle 6 11 true (1),
.cycle 17 11 true (2)
])
theorem kid01_part356_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part356) = true := by rfl

def kid01_part357 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.last 14 (0,true),
.cycle 5 20 true (1),
.cycle 6 23 true (0),
.cycle 5 9 true (1),
.cycle 6 9 true (1),
.cycle 5 11 true (1),
.last 14 (0,true),
.cycle 6 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 11 true (0),
.cycle 6 11 true (0),
.cycle 29 1 false (-1),
.last 14 (0,true),
.cycle 5 20 true (1),
.cycle 2 15 true (1),
.cycle 5 9 true (1),
.cycle 6 9 true (1),
.cycle 12 2 true (1)
])
theorem kid01_part357_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part357) = true := by rfl

def kid01_part358 : Audit := .cycle 6 9 true (1)
theorem kid01_part358_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part358) = true := by rfl

def kid01_part359 : Audit := .cycle 6 9 true (1)
theorem kid01_part359_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part359) = true := by rfl

def kid01_part360 : Audit := .cycle 15 1 false (-1)
theorem kid01_part360_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part360) = true := by rfl

def kid01_part361 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 25 1 false (1),
.last 14 (2,true),
.cycle 31 1 false (1),
.cycle 31 1 false (1),
.cycle 9 7 true (2),
.cycle 0 15 true (0),
.cycle 0 22 true (0),
.last 14 (2,true),
.cycle 7 16 true (2),
.cycle 6 16 true (2),
.cycle 0 15 true (0),
.cycle 15 41 true (-1),
.cycle 0 19 true (0),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 12 2 true (2),
.cycle 0 15 true (0),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 0 15 true (0)
])
theorem kid01_part361_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part361) = true := by rfl

def kid01_part362 : Audit := .cycle 1 14 true (1)
theorem kid01_part362_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part362) = true := by rfl

def kid01_part363 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 25 1 false (1),
.cycle 18 1 false (0),
.cycle 31 1 false (1),
.cycle 31 1 false (1),
.cycle 7 20 true (2),
.last 14 (0,true),
.cycle 2 20 true (1),
.cycle 6 17 true (2),
.cycle 7 16 true (2),
.cycle 6 16 true (2),
.cycle 2 13 true (1),
.last 14 (0,true),
.cycle 2 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 4, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 12 2 true (2),
.last 14 (0,true),
.cycle 9 5 true (2),
.cycle 2 13 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 2 13 true (1)
])
theorem kid01_part363_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part363) = true := by rfl

def kid01_part364 : Audit := .cycle 7 7 true (2)
theorem kid01_part364_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part364) = true := by rfl

def kid01_part365 : Audit := .cycle 6 7 true (2)
theorem kid01_part365_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part365) = true := by rfl

def kid01_part366 : Audit := .cycle 13 3 true (3)
theorem kid01_part366_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part366) = true := by rfl

def kid01_part342 : Audit := .split 12 (5,true) (byMove [(kid01_part343),(kid01_part344),(kid01_part345),(kid01_part346),(kid01_part347),(kid01_part348),(kid01_part349),(kid01_part350),(kid01_part351),(kid01_part352),(kid01_part353),(kid01_part354),(kid01_part355),(kid01_part356),(kid01_part357),(kid01_part358),(kid01_part359),(kid01_part360),(kid01_part361),(kid01_part362),(kid01_part363),(kid01_part364),(kid01_part365),(kid01_part366)])

theorem kid01_part342_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part342) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part343),(kid01_part344),(kid01_part345),(kid01_part346),(kid01_part347),(kid01_part348),(kid01_part349),(kid01_part350),(kid01_part351),(kid01_part352),(kid01_part353),(kid01_part354),(kid01_part355),(kid01_part356),(kid01_part357),(kid01_part358),(kid01_part359),(kid01_part360),(kid01_part361),(kid01_part362),(kid01_part363),(kid01_part364),(kid01_part365),(kid01_part366)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part343_checked

  · exact kid01_part349_checked

  · exact kid01_part355_checked

  · exact kid01_part361_checked

  · exact kid01_part344_checked

  · exact kid01_part350_checked

  · exact kid01_part356_checked

  · exact kid01_part362_checked

  · exact kid01_part345_checked

  · exact kid01_part351_checked

  · exact kid01_part357_checked

  · exact kid01_part363_checked

  · exact kid01_part346_checked

  · exact kid01_part352_checked

  · exact kid01_part358_checked

  · exact kid01_part364_checked

  · exact kid01_part347_checked

  · exact kid01_part353_checked

  · exact kid01_part359_checked

  · exact kid01_part365_checked

  · exact kid01_part348_checked

  · exact kid01_part354_checked

  · exact kid01_part360_checked

  · exact kid01_part366_checked

def kid01_part367 : Audit := .cycle 0 11 true (0)
theorem kid01_part367_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part367) = true := by rfl

def kid01_part368 : Audit := .cycle 1 10 true (1)
theorem kid01_part368_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part368) = true := by rfl

def kid01_part369 : Audit := .cycle 2 9 true (1)
theorem kid01_part369_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part369) = true := by rfl

def kid01_part370 : Audit := .cycle 7 6 true (3)
theorem kid01_part370_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part370) = true := by rfl

def kid01_part371 : Audit := .cycle 8 3 true (3)
theorem kid01_part371_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part371) = true := by rfl

def kid01_part372 : Audit := .cycle 10 1 true (4)
theorem kid01_part372_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part372) = true := by rfl

def kid01_part324 : Audit := .split 10 (5,false) (byMove [(kid01_part325),(kid01_part326),(kid01_part327),(kid01_part328),(kid01_part329),(kid01_part330),(kid01_part331),(kid01_part332),(kid01_part333),(kid01_part334),(kid01_part335),(kid01_part336),(kid01_part337),(kid01_part338),(kid01_part339),(kid01_part340),(kid01_part341),(kid01_part342),(kid01_part367),(kid01_part368),(kid01_part369),(kid01_part370),(kid01_part371),(kid01_part372)])

theorem kid01_part324_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (kid01_part324) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨false,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part325),(kid01_part326),(kid01_part327),(kid01_part328),(kid01_part329),(kid01_part330),(kid01_part331),(kid01_part332),(kid01_part333),(kid01_part334),(kid01_part335),(kid01_part336),(kid01_part337),(kid01_part338),(kid01_part339),(kid01_part340),(kid01_part341),(kid01_part342),(kid01_part367),(kid01_part368),(kid01_part369),(kid01_part370),(kid01_part371),(kid01_part372)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part325_checked

  · exact kid01_part331_checked

  · exact kid01_part337_checked

  · exact kid01_part367_checked

  · exact kid01_part326_checked

  · exact kid01_part332_checked

  · exact kid01_part338_checked

  · exact kid01_part368_checked

  · exact kid01_part327_checked

  · exact kid01_part333_checked

  · exact kid01_part339_checked

  · exact kid01_part369_checked

  · exact kid01_part328_checked

  · exact kid01_part334_checked

  · exact kid01_part340_checked

  · exact kid01_part370_checked

  · exact kid01_part329_checked

  · exact kid01_part335_checked

  · exact kid01_part341_checked

  · exact kid01_part371_checked

  · exact kid01_part330_checked

  · exact kid01_part336_checked

  · exact kid01_part342_checked

  · exact kid01_part372_checked

def kid01_part374 : Audit := .cycle 0 28 false (4)
theorem kid01_part374_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part374) = true := by rfl

def kid01_part375 : Audit := .cycle 11 12 false (2)
theorem kid01_part375_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part375) = true := by rfl

def kid01_part376 : Audit := .split 11 (2,true) (byMove [
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 14 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.split 12 (5,true) (byMove [
.cycle 29 1 false (-1),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.last 22 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.last 23 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.cycle 9 10 true (0),
.cycle 6 12 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 13 (5,false)
]),
.cycle 6 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (0),
.cycle 6 10 true (0),
.cycle 9 10 true (1),
.split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 9 10 true (1),
.cycle 6 12 true (0),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 6 14 true (0),
.cycle 6 16 true (0),
.cycle 6 21 true (0),
.cycle 6 18 true (0),
.cycle 6 18 true (0),
.last 13 (5,true),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 6 18 true (0),
.cycle 6 10 true (0),
.cycle 19 1 false (-1),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 6 14 true (0),
.cycle 2 13 true (1),
.cycle 6 16 true (0),
.cycle 6 16 true (0),
.last 13 (5,true)
]),
.cycle 14 1 false (0),
.cycle 17 1 false (-1),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.split 12 (5,true) (byMove [
.cycle 19 1 false (-1),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.cycle 15 1 false (1),
.cycle 18 1 false (0),
.last 14 (5,false),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.last 14 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,false),
.last 15 (5,false),
.cycle 16 1 false (0),
.cycle 11 2 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 14 (5,false)
]),
.cycle 9 4 true (1),
.cycle 1 13 true (1),
.cycle 9 8 true (1),
.cycle 4 8 true (1),
.cycle 16 1 false (0),
.split 12 (5,false) (byMove [
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 13 (5,true),
.cycle 2 12 true (1),
.cycle 9 6 true (1),
.cycle 6 15 true (1),
.cycle 9 8 true (1),
.cycle 9 8 true (1),
.last 13 (5,true),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.last 14 (5,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 0 16 true (0),
.cycle 9 4 true (1),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 13 (5,true)
])
])
theorem kid01_part376_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part376) = true := by rfl

def kid01_part377 : Audit := .cycle 15 1 false (-1)
theorem kid01_part377_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part377) = true := by rfl

def kid01_part378 : Audit := .cycle 6 16 false (4)
theorem kid01_part378_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part378) = true := by rfl

def kid01_part380 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 9 23 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 9 24 false (3),
.cycle 13 1 false (-1),
.cycle 9 12 true (-1),
.cycle 6 14 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 9 24 false (3),
.cycle 0 18 true (-1),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 12 8 false (0),
.cycle 14 1 false (-2),
.cycle 9 22 false (3),
.cycle 13 1 false (-1),
.cycle 0 26 false (4),
.cycle 0 28 false (4),
.cycle 9 22 false (3),
.cycle 9 27 false (3),
.cycle 12 6 false (0),
.cycle 0 22 false (4)
])
theorem kid01_part380_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part380) = true := by rfl

def kid01_part381 : Audit := .split 16 (5,false) (byMove [
.cycle 9 15 false (3),
.cycle 6 17 false (4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 6 29 false (4),
.cycle 16 1 false (-2),
.cycle 13 4 true (-2),
.last 18 (2,true),
.cycle 12 8 true (-2),
.cycle 17 1 false (-1),
.cycle 6 27 false (4),
.cycle 6 30 false (4),
.cycle 13 4 false (0),
.last 18 (2,true),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.cycle 6 27 false (4),
.cycle 16 1 false (-2),
.cycle 6 21 false (4),
.last 18 (2,true),
.cycle 6 25 false (4),
.cycle 6 25 false (4),
.cycle 12 6 false (0),
.cycle 14 5 false (0)
])
theorem kid01_part381_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part381) = true := by rfl

def kid01_part382 : Audit := .split 12 (2,true) (byMove [
.last 28 (5,false),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 23 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 20 (5,false),
.cycle 13 1 false (-1),
.cycle 24 1 false (-2),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 9 10 true (0),
.cycle 6 12 true (0),
.last 19 (5,false),
.last 18 (5,false),
.last 13 (5,false)
])
theorem kid01_part382_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part382) = true := by rfl

def kid01_part383 : Audit := .split 18 (5,false) (byMove [
.cycle 9 17 false (3),
.cycle 6 19 false (4),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 31 1 false (-5),
.cycle 18 1 false (-2),
.cycle 15 4 true (-2),
.last 20 (2,true),
.cycle 12 8 true (-2),
.cycle 19 1 false (-1),
.cycle 29 1 false (-3),
.cycle 21 1 false (-1),
.cycle 15 4 false (0),
.last 20 (2,true),
.cycle 12 8 false (1),
.cycle 19 1 false (-3),
.cycle 29 1 false (-5),
.cycle 18 1 false (-2),
.cycle 23 1 false (-3),
.last 20 (2,true),
.cycle 27 1 false (-3),
.cycle 27 1 false (-3),
.cycle 13 6 false (1),
.cycle 16 7 false (0)
])
theorem kid01_part383_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part383) = true := by rfl

def kid01_part384 : Audit := .split 18 (5,false) (byMove [
.cycle 9 17 false (3),
.cycle 6 19 false (4),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 19 12 false (-1),
.cycle 18 1 false (-2),
.cycle 15 4 true (-2),
.last 20 (2,true),
.cycle 13 8 true (-2),
.cycle 19 1 false (-1),
.cycle 26 12 false (0),
.cycle 20 12 false (1),
.cycle 15 4 false (0),
.last 20 (2,true),
.cycle 13 8 false (1),
.cycle 19 1 false (-3),
.cycle 26 12 false (-2),
.cycle 18 1 false (-2),
.cycle 20 12 false (0),
.last 20 (2,true),
.cycle 24 12 false (0),
.cycle 19 12 false (1),
.cycle 13 6 false (1),
.cycle 16 7 false (0)
])
theorem kid01_part384_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part384) = true := by rfl

def kid01_part385 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 12 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 9 12 true (-1),
.cycle 6 14 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 28 false (4),
.cycle 18 1 true (2),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 13 8 false (0),
.cycle 14 1 false (-2),
.cycle 12 11 false (0),
.cycle 13 1 false (-1),
.cycle 21 32 false (4),
.cycle 1 28 false (4),
.cycle 6 24 false (4),
.cycle 12 16 false (1),
.cycle 13 6 false (0),
.cycle 22 1 true (-2)
])
theorem kid01_part385_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part385) = true := by rfl

def kid01_part386 : Audit := .split 15 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 6 21 false (4),
.last 16 (2,true),
.cycle 23 1 false (-3),
.cycle 19 16 false (0),
.last 19 (2,true),
.cycle 12 4 true (1),
.last 17 (2,true),
.cycle 12 8 true (1),
.cycle 6 14 true (0),
.cycle 9 14 true (1),
.cycle 0 18 true (0),
.cycle 16 4 false (0),
.last 22 (2,true),
.last 16 (2,true),
.cycle 22 1 false (-2),
.cycle 19 14 false (1),
.cycle 18 1 false (0),
.cycle 9 8 true (1),
.last 17 (2,true),
.cycle 9 12 true (1),
.cycle 4 12 true (1),
.cycle 17 6 false (1),
.cycle 0 18 true (0)
])
theorem kid01_part386_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part386) = true := by rfl

def kid01_part387 : Audit := .split 13 (2,true) (byMove [
.last 15 (5,false),
.last 25 (5,false),
.cycle 29 1 false (1),
.last 29 (5,false),
.last 29 (5,false),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.last 15 (5,false),
.last 25 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.last 17 (5,false),
.last 14 (5,false)
])
theorem kid01_part387_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part387) = true := by rfl

def kid01_part388 : Audit := .split 19 (5,false) (byMove [
.cycle 0 22 false (4),
.cycle 6 25 false (4),
.last 20 (2,true),
.cycle 27 1 false (-3),
.cycle 21 20 false (1),
.cycle 22 1 false (2),
.cycle 16 4 true (1),
.last 21 (2,true),
.cycle 12 8 true (1),
.cycle 6 18 true (0),
.cycle 9 18 true (1),
.cycle 6 26 true (0),
.cycle 20 4 false (0),
.last 26 (2,true),
.last 20 (2,true),
.cycle 26 1 false (-2),
.cycle 23 18 false (1),
.last 21 (2,true),
.cycle 9 12 true (1),
.last 21 (2,true),
.cycle 9 16 true (1),
.cycle 4 16 true (1),
.cycle 21 6 false (1),
.cycle 6 22 true (1)
])
theorem kid01_part388_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part388) = true := by rfl

def kid01_part389 : Audit := .cycle 6 10 true (0)
theorem kid01_part389_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part389) = true := by rfl

def kid01_part390 : Audit := .cycle 9 10 true (1)
theorem kid01_part390_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part390) = true := by rfl

def kid01_part391 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.cycle 9 10 true (1),
.cycle 6 12 true (0),
.cycle 20 1 false (-2),
.cycle 6 33 false (4),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.last 19 (2,true),
.last 13 (2,true),
.cycle 6 18 true (0),
.cycle 9 18 true (1),
.cycle 14 1 true (4),
.cycle 17 4 false (1),
.last 14 (2,true),
.last 20 (2,true),
.cycle 6 10 true (0),
.cycle 16 26 false (0),
.cycle 18 1 false (4),
.cycle 0 16 true (0),
.last 17 (2,true),
.last 13 (2,true),
.cycle 4 14 true (1),
.cycle 19 6 false (1),
.cycle 14 1 true (4)
])
theorem kid01_part391_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part391) = true := by rfl

def kid01_part392 : Audit := .split 13 (5,false) (byMove [
.cycle 9 12 false (3),
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 16 false (0),
.cycle 13 1 false (-1),
.cycle 12 4 true (-1),
.last 15 (2,true),
.cycle 12 8 true (-1),
.cycle 14 1 false (0),
.cycle 12 14 false (2),
.cycle 12 6 true (-1),
.cycle 12 4 false (0),
.last 15 (2,true),
.cycle 12 8 false (0),
.cycle 14 1 false (-2),
.cycle 12 14 false (0),
.cycle 13 1 false (-1),
.cycle 12 8 false (1),
.last 15 (2,true),
.cycle 12 12 false (2),
.cycle 12 12 false (2),
.cycle 12 6 false (0),
.cycle 12 8 false (1)
])
theorem kid01_part392_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part392) = true := by rfl

def kid01_part393 : Audit := .split 16 (5,false) (byMove [
.last 29 (2,true),
.cycle 14 16 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.last 30 (2,true),
.cycle 16 1 false (-2),
.cycle 13 4 true (-2),
.last 18 (2,true),
.cycle 21 8 true (-1),
.cycle 17 1 false (-1),
.cycle 9 24 false (3),
.last 20 (2,true),
.cycle 13 4 false (0),
.last 18 (2,true),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.last 28 (2,true),
.cycle 16 1 false (-2),
.last 22 (2,true),
.last 18 (2,true),
.cycle 9 20 false (3),
.cycle 6 14 false (4),
.cycle 12 6 false (0),
.cycle 14 5 false (0)
])
theorem kid01_part393_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part393) = true := by rfl

def kid01_part394 : Audit := .split 12 (2,true) (byMove [
.last 25 (5,false),
.last 29 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.last 21 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.last 21 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 21 (5,false),
.last 13 (5,false),
.last 22 (5,false),
.last 15 (5,false),
.cycle 9 10 true (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part394_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part394) = true := by rfl

def kid01_part395 : Audit := .split 17 (5,false) (byMove [
.cycle 9 16 false (3),
.cycle 6 18 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 30 1 false (-4),
.cycle 17 1 false (-1),
.cycle 15 4 true (-1),
.last 19 (2,true),
.cycle 15 8 true (-1),
.cycle 18 1 false (0),
.cycle 28 1 false (-2),
.cycle 20 1 false (0),
.cycle 15 4 false (1),
.last 19 (2,true),
.cycle 15 8 false (1),
.cycle 18 1 false (-2),
.cycle 28 1 false (-4),
.cycle 17 1 false (-1),
.cycle 22 1 false (-2),
.last 19 (2,true),
.cycle 26 1 false (-2),
.cycle 26 1 false (-2),
.cycle 15 6 false (1),
.cycle 26 1 false (-2)
])
theorem kid01_part395_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part395) = true := by rfl

def kid01_part396 : Audit := .split 17 (5,false) (byMove [
.cycle 9 16 false (3),
.cycle 6 18 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 27 10 false (-1),
.cycle 17 1 false (-1),
.cycle 15 4 true (-1),
.last 19 (2,true),
.cycle 15 8 true (-1),
.cycle 18 1 false (0),
.cycle 18 10 false (2),
.cycle 19 10 false (2),
.cycle 15 4 false (1),
.last 19 (2,true),
.cycle 15 8 false (1),
.cycle 18 1 false (-2),
.cycle 18 10 false (0),
.cycle 17 1 false (-1),
.cycle 18 10 false (1),
.last 19 (2,true),
.cycle 18 10 false (2),
.cycle 23 10 false (1),
.cycle 15 6 false (1),
.cycle 23 10 false (1)
])
theorem kid01_part396_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part396) = true := by rfl

def kid01_part397 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 6 27 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[24, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 14 4 true (-1),
.last 20 (2,true),
.last 14 (2,true),
.cycle 20 1 false (0),
.cycle 17 18 false (2),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 27 8 false (-1),
.cycle 14 1 false (-2),
.cycle 29 26 false (-1),
.cycle 13 1 false (-1),
.cycle 12 3 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 15 14 false (2),
.cycle 23 6 false (-1),
.cycle 11 3 false (1)
])
theorem kid01_part397_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part397) = true := by rfl

def kid01_part398 : Audit := .cycle 9 4 true (1)
theorem kid01_part398_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part398) = true := by rfl

def kid01_part399 : Audit := .split 13 (2,true) (byMove [
.cycle 1 15 true (1),
.last 21 (5,false),
.cycle 18 1 false (0),
.last 25 (5,false),
.last 25 (5,false),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 10 4 true (1),
.last 21 (5,false),
.cycle 6 14 true (-1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 9 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.cycle 8 6 true (1),
.last 14 (5,false)
])
theorem kid01_part399_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part399) = true := by rfl

def kid01_part400 : Audit := .cycle 9 8 true (1)
theorem kid01_part400_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part400) = true := by rfl

def kid01_part401 : Audit := .cycle 4 8 true (1)
theorem kid01_part401_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part401) = true := by rfl

def kid01_part402 : Audit := .split 15 (5,false) (byMove [
.cycle 9 14 false (3),
.cycle 6 16 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 13 18 false (1),
.cycle 15 1 false (-1),
.cycle 13 4 true (-1),
.last 17 (2,true),
.cycle 13 8 true (-1),
.cycle 16 1 false (0),
.cycle 13 16 false (2),
.cycle 13 8 true (-1),
.cycle 13 4 false (1),
.last 17 (2,true),
.cycle 13 8 false (1),
.cycle 16 1 false (-2),
.cycle 13 16 false (1),
.cycle 15 1 false (-1),
.cycle 13 10 false (1),
.last 17 (2,true),
.cycle 13 14 false (2),
.cycle 13 14 false (2),
.cycle 13 6 false (1),
.cycle 13 12 false (2)
])
theorem kid01_part402_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part402) = true := by rfl

def kid01_part403 : Audit := .split 12 (5,false) (byMove [
.cycle 0 18 false (4),
.cycle 6 16 false (4),
.last 13 (2,true),
.cycle 18 1 false (-2),
.cycle 15 20 false (1),
.cycle 11 2 true (1),
.cycle 0 15 true (0),
.cycle 9 6 true (1),
.last 13 (2,true),
.cycle 9 8 true (1),
.cycle 9 8 true (1),
.cycle 14 1 true (4),
.cycle 16 4 false (0),
.last 17 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 14 3 true (2),
.cycle 0 16 true (0),
.cycle 9 4 true (1),
.last 13 (2,true),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 14 1 true (4)
])
theorem kid01_part403_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part403) = true := by rfl

def kid01_part379 : Audit := .split 11 (5,true) (byMove [(kid01_part380),(kid01_part381),(kid01_part382),(kid01_part383),(kid01_part384),(kid01_part385),(kid01_part386),(kid01_part387),(kid01_part388),(kid01_part389),(kid01_part390),(kid01_part391),(kid01_part392),(kid01_part393),(kid01_part394),(kid01_part395),(kid01_part396),(kid01_part397),(kid01_part398),(kid01_part399),(kid01_part400),(kid01_part401),(kid01_part402),(kid01_part403)])

theorem kid01_part379_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part379) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part380),(kid01_part381),(kid01_part382),(kid01_part383),(kid01_part384),(kid01_part385),(kid01_part386),(kid01_part387),(kid01_part388),(kid01_part389),(kid01_part390),(kid01_part391),(kid01_part392),(kid01_part393),(kid01_part394),(kid01_part395),(kid01_part396),(kid01_part397),(kid01_part398),(kid01_part399),(kid01_part400),(kid01_part401),(kid01_part402),(kid01_part403)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part380_checked

  · exact kid01_part386_checked

  · exact kid01_part392_checked

  · exact kid01_part398_checked

  · exact kid01_part381_checked

  · exact kid01_part387_checked

  · exact kid01_part393_checked

  · exact kid01_part399_checked

  · exact kid01_part382_checked

  · exact kid01_part388_checked

  · exact kid01_part394_checked

  · exact kid01_part400_checked

  · exact kid01_part383_checked

  · exact kid01_part389_checked

  · exact kid01_part395_checked

  · exact kid01_part401_checked

  · exact kid01_part384_checked

  · exact kid01_part390_checked

  · exact kid01_part396_checked

  · exact kid01_part402_checked

  · exact kid01_part385_checked

  · exact kid01_part391_checked

  · exact kid01_part397_checked

  · exact kid01_part403_checked

def kid01_part404 : Audit := .cycle 0 12 true (0)
theorem kid01_part404_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part404) = true := by rfl

def kid01_part405 : Audit := .cycle 9 4 true (2)
theorem kid01_part405_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part405) = true := by rfl

def kid01_part406 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 13 18 false (2),
.split 12 (5,false) (byMove [
.cycle 6 14 true (0),
.cycle 13 18 false (2),
.last 14 (5,true),
.cycle 19 1 false (-1),
.cycle 15 21 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 16 5 false (1),
.last 19 (5,true),
.last 14 (5,true),
.cycle 27 1 false (-1),
.cycle 16 18 false (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (1),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 11 3 true (3),
.cycle 9 9 true (2),
.cycle 6 11 true (1),
.cycle 9 11 true (2),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 9 7 true (2),
.cycle 12 1 true (4)
]),
.cycle 9 4 true (2),
.cycle 19 7 false (1),
.cycle 9 8 true (2),
.cycle 4 8 true (1),
.cycle 13 16 false (2),
.split 12 (5,false) (byMove [
.last 26 (5,true),
.cycle 13 16 false (2),
.last 14 (5,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 6 16 true (1),
.cycle 9 6 true (2),
.cycle 11 2 true (2),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.last 13 (5,true),
.cycle 16 5 false (1),
.last 19 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 6 14 true (2),
.cycle 9 4 true (2),
.last 14 (5,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 9 6 true (2),
.split 12 (5,false) (byMove [
.cycle 6 16 true (1),
.cycle 9 6 true (2),
.cycle 11 2 true (3),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.last 18 (5,true),
.last 14 (5,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part406_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part406) = true := by rfl

def kid01_part407 : Audit := .cycle 9 6 true (2)
theorem kid01_part407_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part407) = true := by rfl

def kid01_part408 : Audit := .cycle 9 6 true (2)
theorem kid01_part408_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part408) = true := by rfl

def kid01_part409 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 13 18 false (2),
.split 12 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 13 18 false (2),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 15 21 false (1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 16 5 false (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 16 18 false (2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (1),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 9 9 true (2),
.cycle 6 11 true (1),
.cycle 9 11 true (2),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 9 7 true (2),
.cycle 12 1 true (4)
]),
.cycle 9 4 true (2),
.split 13 (2,true) (byMove [
.last 15 (5,false),
.cycle 19 7 false (1),
.cycle 18 1 false (0),
.cycle 23 9 false (1),
.cycle 23 9 false (1),
.cycle 17 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 10 4 true (2),
.cycle 19 7 false (1),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 17 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.last 14 (5,false)
]),
.cycle 9 8 true (2),
.cycle 4 8 true (1),
.cycle 13 16 false (2),
.split 12 (5,false) (byMove [
.last 17 (2,true),
.cycle 13 16 false (2),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 9 6 true (2),
.last 13 (2,true),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.cycle 11 2 true (2),
.cycle 16 5 false (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 15 3 false (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 9 6 true (2),
.split 12 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 9 6 true (2),
.last 13 (2,true),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.cycle 15 5 true (2),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part409_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part409) = true := by rfl

def kid01_part410 : Audit := .cycle 12 3 false (0)
theorem kid01_part410_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part410) = true := by rfl

def kid01_part411 : Audit := .split 14 (2,true) (byMove [
.cycle 12 3 false (0),
.cycle 11 6 false (1),
.cycle 17 1 false (-1),
.cycle 11 8 false (1),
.cycle 11 8 false (1),
.split 15 (5,true) (byMove [
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 1, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 2, 64],96⟩,
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 18 false (1),
.last 16 (5,false),
.cycle 11 6 true (-1),
.cycle 11 26 true (-1),
.cycle 11 14 true (-1),
.cycle 16 1 false (0),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.last 16 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 10 false (1),
.cycle 16 1 false (-2),
.cycle 11 16 false (1),
.last 16 (5,false),
.cycle 11 10 false (1),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.cycle 11 8 false (1),
.last 16 (5,false)
]),
.cycle 0 24 true (-1),
.cycle 11 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[4, 4, 4, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[24, 16, 8, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.split 15 (5,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4096, 128, 256, 8, 1024, 8, 4096, 4096],[32, 256, 32, 1024, 1024, 256, 32, 256, 32, 1024, 1024, 4096, 4096],6176⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[48, 24, 32, 16, 16, 24, 64],96⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4096, 128, 256, 8, 1024, 0, 4096, 4096],[32, 1024, 32, 1024, 1024, 1024, 1024, 1024, 32, 1024, 1024, 4096, 4096],6176⟩,
.cycle 11 9 false (1),
.cycle 11 8 false (1),
.last 16 (5,false),
.cycle 0 20 true (-1),
.cycle 11 31 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 4, 32, 16, 16, 4, 64],96⟩,
.cycle 6 23 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.last 18 (5,false),
.cycle 11 10 false (1),
.last 24 (5,false),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.cycle 11 8 false (1),
.last 16 (5,false),
.cycle 11 12 false (2),
.cycle 1 25 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 4, 32, 16, 16, 4, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[48, 24, 32, 16, 16, 8, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.last 18 (5,false)
]),
.cycle 12 3 false (0),
.cycle 11 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.split 15 (5,true) (byMove [
.cycle 12 8 false (0),
.cycle 25 17 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.far true 1 ⟨0,[0, 0],[3, 19, 27, 8, 2, 64, 64],[2, 1, 32, 3, 3, 16, 64],96⟩,
.last 16 (5,false),
.cycle 12 4 true (-1),
.cycle 11 7 false (1),
.last 17 (5,false),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.last 20 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[12288, 12288, 32768, 512, 2, 262144, 159744, 159744, 192512, 32768, 128, 262144, 8192, 16384, 24576, 32768, 128, 262144, 262144],[128, 64, 2048, 64, 64, 256, 8192, 4096, 131072, 12288, 12288, 16384, 8192, 4096, 131072, 12288, 12288, 16384, 262144],462304⟩,
.cycle 16 1 false (-2),
.far true 1 ⟨0,[0, 0],[3, 19, 27, 8, 2, 64, 64],[2, 1, 32, 3, 3, 16, 64],96⟩,
.last 16 (5,false),
.cycle 11 8 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[2, 1, 32, 3, 3, 3, 64],96⟩,
.last 20 (5,false)
]),
.cycle 10 5 false (2),
.cycle 11 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[4, 4, 4, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[24, 16, 8, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.split 15 (5,true) (byMove [
.cycle 11 8 false (1),
.cycle 11 5 false (1),
.last 17 (5,false),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 18 (5,false),
.cycle 0 20 true (-1),
.cycle 9 9 false (3),
.cycle 6 18 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[48, 24, 32, 16, 16, 8, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.last 18 (5,false),
.cycle 11 8 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.last 18 (5,false),
.cycle 11 10 false (2),
.cycle 9 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 4, 32, 16, 16, 4, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[48, 24, 32, 16, 16, 8, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[48, 16, 32, 16, 16, 16, 64],96⟩,
.last 18 (5,false)
])
])
theorem kid01_part411_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part411) = true := by rfl

def kid01_part412 : Audit := .split 11 (2,true) (byMove [
.cycle 18 6 true (-2),
.cycle 14 6 true (-2),
.cycle 14 1 false (0),
.cycle 16 6 true (-2),
.cycle 16 6 true (-2),
.split 12 (5,true) (byMove [
.cycle 15 6 true (1),
.cycle 29 6 true (-3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.last 24 (5,false),
.last 30 (5,false),
.cycle 13 6 true (1),
.cycle 13 1 false (1),
.cycle 15 6 true (1),
.last 13 (5,false),
.cycle 14 6 true (-2),
.cycle 11 3 false (1),
.cycle 18 6 true (-2),
.cycle 13 1 false (-1),
.last 23 (5,false),
.last 13 (5,false),
.last 17 (5,false),
.cycle 1 18 true (0),
.cycle 13 6 true (1),
.cycle 6 10 true (0),
.cycle 16 6 true (-2),
.last 13 (5,false)
]),
.cycle 12 6 true (1),
.cycle 6 18 true (-1),
.cycle 6 18 true (0),
.cycle 12 6 true (1),
.cycle 13 6 true (1),
.split 12 (5,true) (byMove [
.last 16 (5,false),
.cycle 9 10 true (1),
.cycle 6 12 true (0),
.cycle 14 6 true (-1),
.cycle 16 6 true (-2),
.last 13 (5,false),
.cycle 19 6 true (1),
.cycle 15 6 true (1),
.last 14 (5,false),
.cycle 17 6 true (1),
.cycle 17 6 true (1),
.last 14 (5,false),
.cycle 6 18 true (-1),
.last 18 (5,false),
.cycle 13 6 true (1),
.cycle 6 10 true (0),
.cycle 16 6 true (-2),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 13 6 true (1),
.last 14 (5,false),
.cycle 14 6 true (1),
.cycle 13 6 true (1),
.last 14 (5,false)
]),
.cycle 6 10 true (-1),
.cycle 14 12 true (-2),
.cycle 6 10 true (-1),
.cycle 6 8 true (0),
.cycle 6 8 true (0),
.split 12 (5,true) (byMove [
.cycle 23 6 true (-3),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 29 6 true (-3),
.last 13 (5,false),
.last 22 (5,false),
.cycle 6 14 true (-1),
.last 14 (5,false),
.last 20 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.cycle 15 12 true (-2),
.cycle 11 3 false (1),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.cycle 28 6 true (-4),
.last 13 (5,false),
.last 15 (5,false),
.cycle 6 12 true (-1),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.last 16 (5,false)
]),
.cycle 10 2 true (1),
.cycle 6 14 true (-1),
.cycle 2 12 true (1),
.cycle 7 6 true (1),
.cycle 6 6 true (1),
.split 12 (5,true) (byMove [
.cycle 22 6 true (-2),
.cycle 13 6 true (-1),
.last 14 (5,false),
.cycle 14 6 true (-1),
.cycle 13 6 true (-1),
.last 15 (5,false),
.cycle 9 10 true (1),
.cycle 9 6 true (1),
.last 14 (5,false),
.cycle 9 8 true (1),
.cycle 9 8 true (1),
.last 14 (5,false),
.cycle 6 14 true (-1),
.cycle 6 12 true (-1),
.cycle 11 2 true (1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 0 16 true (0),
.cycle 9 4 true (1),
.last 14 (5,false),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 14 (5,false)
])
])
theorem kid01_part412_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part412) = true := by rfl

def kid01_part413 : Audit := .cycle 5 6 true (1)
theorem kid01_part413_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part413) = true := by rfl

def kid01_part414 : Audit := .cycle 6 6 true (1)
theorem kid01_part414_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part414) = true := by rfl

def kid01_part416 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.last 25 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.last 14 (2,true),
.cycle 18 6 true (-2),
.cycle 18 6 true (-2),
.last 27 (2,true),
.cycle 12 4 false (0),
.last 15 (2,true),
.last 31 (2,true),
.cycle 14 1 false (-2),
.cycle 6 19 false (4),
.cycle 13 1 false (-1),
.last 18 (2,true),
.cycle 12 3 false (0),
.last 14 (2,true),
.last 27 (2,true),
.last 27 (2,true),
.cycle 11 3 false (1)
])
theorem kid01_part416_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part416) = true := by rfl

def kid01_part417 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.cycle 12 13 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 14 17 false (1),
.cycle 16 1 false (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.last 17 (2,true),
.cycle 14 6 true (-2),
.cycle 14 6 true (-2),
.cycle 9 33 false (3),
.cycle 13 4 false (0),
.last 18 (2,true),
.last 33 (2,true),
.cycle 17 1 false (-3),
.cycle 14 29 false (1),
.cycle 16 1 false (-2),
.cycle 10 17 false (2),
.cycle 14 3 false (0),
.last 17 (2,true),
.cycle 7 25 false (4),
.cycle 6 25 false (4),
.cycle 11 6 false (1)
])
theorem kid01_part417_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part417) = true := by rfl

def kid01_part418 : Audit := .split 12 (2,true) (byMove [
.last 21 (5,false),
.last 31 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.last 16 (5,false),
.cycle 21 1 false (1),
.last 19 (5,false),
.cycle 13 1 false (1),
.last 21 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 20 (5,false),
.cycle 13 1 false (-1),
.cycle 24 1 false (-2),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 9 6 true (0),
.last 19 (5,false),
.cycle 6 10 true (0),
.last 18 (5,false),
.last 13 (5,false)
])
theorem kid01_part418_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part418) = true := by rfl

def kid01_part419 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 14 13 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 16 19 false (1),
.cycle 18 1 false (-2),
.cycle 17 2 true (-2),
.cycle 14 5 false (0),
.last 19 (2,true),
.cycle 16 6 true (-2),
.cycle 16 6 true (-2),
.cycle 20 1 false (-2),
.cycle 15 4 false (0),
.last 20 (2,true),
.cycle 27 1 false (-3),
.cycle 19 1 false (-3),
.cycle 16 17 false (1),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 16 3 false (0),
.last 19 (2,true),
.cycle 25 1 false (-3),
.cycle 25 1 false (-3),
.cycle 11 8 false (1)
])
theorem kid01_part419_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part419) = true := by rfl

def kid01_part420 : Audit := .split 18 (5,false) (byMove [
.last 21 (2,true),
.cycle 14 13 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 16 19 false (1),
.cycle 18 1 false (-2),
.cycle 17 2 true (-2),
.cycle 14 5 false (0),
.last 19 (2,true),
.cycle 16 6 true (-2),
.cycle 16 6 true (-2),
.cycle 6 21 false (4),
.cycle 15 4 false (0),
.last 20 (2,true),
.cycle 16 27 false (1),
.cycle 19 1 false (-3),
.cycle 13 16 false (1),
.cycle 18 1 false (-2),
.cycle 16 21 false (1),
.cycle 16 3 false (0),
.last 19 (2,true),
.cycle 16 25 false (1),
.cycle 16 25 false (1),
.cycle 11 8 false (1)
])
theorem kid01_part420_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part420) = true := by rfl

def kid01_part421 : Audit := .split 13 (5,false) (byMove [
.cycle 0 32 false (4),
.cycle 11 28 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.last 16 (2,true),
.last 29 (2,true),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 48 6 true (-2),
.cycle 20 1 true (2),
.cycle 13 4 false (-1),
.last 15 (2,true),
.cycle 12 17 false (0),
.cycle 14 1 false (-2),
.cycle 12 11 false (0),
.cycle 13 1 false (-1),
.last 16 (2,true),
.last 38 (2,true),
.last 47 (2,true),
.cycle 6 25 false (4),
.cycle 12 13 false (0),
.cycle 31 1 true (-3)
])
theorem kid01_part421_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part421) = true := by rfl

def kid01_part422 : Audit := .split 13 (5,false) (byMove [
.last 18 (2,true),
.cycle 12 13 false (2),
.last 14 (2,true),
.cycle 21 1 false (-3),
.cycle 18 21 false (1),
.cycle 18 1 false (0),
.cycle 12 2 true (1),
.cycle 19 5 false (1),
.last 14 (2,true),
.cycle 12 6 true (1),
.cycle 12 6 true (1),
.cycle 0 18 true (0),
.cycle 14 4 false (0),
.last 20 (2,true),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.cycle 17 3 false (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 0 18 true (0)
])
theorem kid01_part422_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part422) = true := by rfl

def kid01_part423 : Audit := .split 21 (5,false) (byMove [
.last 24 (2,true),
.cycle 39 13 false (1),
.cycle 23 1 false (-1),
.cycle 22 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 21 1 false (-1),
.cycle 20 2 true (-1),
.cycle 17 5 false (1),
.last 22 (2,true),
.cycle 6 18 true (-1),
.cycle 6 18 true (-1),
.cycle 16 6 true (-1),
.cycle 18 4 false (1),
.last 23 (2,true),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[131072, 131072, 32768, 512, 2, 256, 393216, 393216, 425984, 32768, 128, 16384, 131072, 262144, 147456, 32768, 128, 16384, 262144],[2048, 64, 262144, 64, 64, 16384, 131072, 4096, 262144, 135168, 135168, 409600, 131072, 4096, 262144, 131072, 131072, 131072, 262144],337376⟩,
.cycle 22 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 21 1 false (-1),
.cycle 15 7 false (1),
.cycle 19 3 false (1),
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 11 11 false (2)
])
theorem kid01_part423_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part423) = true := by rfl

def kid01_part424 : Audit := .split 12 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 9 10 true (1),
.cycle 6 12 true (0),
.last 19 (5,false),
.last 18 (5,false),
.last 13 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.cycle 6 18 true (0),
.last 19 (5,false),
.last 19 (5,false),
.cycle 6 18 true (0),
.last 21 (5,false),
.last 17 (5,false),
.last 19 (5,false),
.cycle 6 10 true (0),
.last 18 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 15 (5,false),
.cycle 2 12 true (1),
.last 17 (5,false),
.last 17 (5,false),
.cycle 6 14 true (1)
])
theorem kid01_part424_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part424) = true := by rfl

def kid01_part425 : Audit := .split 17 (5,false) (byMove [
.last 22 (2,true),
.cycle 12 13 false (4),
.last 18 (2,true),
.cycle 25 1 false (-3),
.cycle 22 25 false (1),
.cycle 19 1 false (1),
.cycle 16 2 true (1),
.cycle 33 5 false (3),
.last 18 (2,true),
.cycle 12 6 true (1),
.cycle 13 6 true (1),
.cycle 15 8 true (1),
.cycle 18 4 false (0),
.last 24 (2,true),
.last 18 (2,true),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 31 1 false (1),
.cycle 10 8 true (1),
.cycle 31 3 false (3),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 9 14 true (1)
])
theorem kid01_part425_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part425) = true := by rfl

def kid01_part426 : Audit := .split 17 (5,false) (byMove [
.last 22 (2,true),
.cycle 13 13 false (4),
.last 18 (2,true),
.cycle 25 1 false (-3),
.cycle 22 25 false (1),
.cycle 13 10 true (0),
.cycle 16 2 true (1),
.cycle 33 5 false (3),
.last 18 (2,true),
.cycle 13 6 true (1),
.cycle 12 6 true (1),
.cycle 15 8 true (1),
.cycle 18 4 false (0),
.last 24 (2,true),
.last 18 (2,true),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 31 1 false (1),
.cycle 10 8 true (1),
.cycle 31 3 false (3),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 9 14 true (1)
])
theorem kid01_part426_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part426) = true := by rfl

def kid01_part427 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (0),
.cycle 6 14 true (0),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 21 true (0),
.cycle 6 18 true (0),
.cycle 1 15 true (1),
.cycle 14 1 true (4),
.cycle 27 4 false (5),
.last 16 (2,true),
.cycle 5 19 true (1),
.cycle 6 15 true (0),
.cycle 9 13 true (1),
.cycle 23 1 false (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 16 true (1),
.cycle 6 15 true (1),
.cycle 14 1 true (4)
])
theorem kid01_part427_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part427) = true := by rfl

def kid01_part428 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 24 13 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 12 2 true (-1),
.cycle 12 5 false (0),
.last 14 (2,true),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 12 5 false (0),
.cycle 12 4 false (0),
.last 15 (2,true),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[135168, 135168, 32768, 512, 2, 256, 397312, 397312, 430080, 32768, 128, 16384, 131072, 262144, 147456, 32768, 128, 16384, 262144],[2048, 64, 262144, 64, 64, 64, 131072, 4096, 262144, 135168, 135168, 4096, 131072, 4096, 262144, 135168, 135168, 4096, 262144],337376⟩,
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 12 6 false (0),
.cycle 12 3 false (0),
.last 14 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 11 3 false (1)
])
theorem kid01_part428_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part428) = true := by rfl

def kid01_part429 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.cycle 28 13 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.proven (BB6.Agent11Raw121Pumps.M1358.table) (fun m hm => BB6.Agent11Raw121Pumps.M1358.never m hm),
.cycle 16 1 false (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.last 17 (2,true),
.cycle 14 12 true (-2),
.cycle 14 12 true (-2),
.last 19 (2,true),
.cycle 13 4 false (0),
.last 18 (2,true),
.last 32 (2,true),
.cycle 17 1 false (-3),
.last 34 (2,true),
.cycle 16 1 false (-2),
.last 20 (2,true),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 30 (2,true),
.last 30 (2,true),
.cycle 11 6 false (1)
])
theorem kid01_part429_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part429) = true := by rfl

def kid01_part430 : Audit := .split 12 (2,true) (byMove [
.last 24 (5,false),
.cycle 14 8 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 33 (5,false),
.last 13 (5,false),
.last 14 (5,false),
.last 17 (5,false),
.cycle 17 1 false (5),
.cycle 13 8 true (0),
.cycle 14 8 true (0),
.cycle 13 8 true (0),
.last 16 (5,false),
.last 19 (5,false),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.last 30 (5,false),
.last 13 (5,false),
.cycle 6 12 true (-1),
.last 15 (5,false),
.cycle 2 14 true (0),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.cycle 11 2 true (0)
])
theorem kid01_part430_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part430) = true := by rfl

def kid01_part431 : Audit := .cycle 6 8 true (0)
theorem kid01_part431_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part431) = true := by rfl

def kid01_part432 : Audit := .cycle 6 8 true (0)
theorem kid01_part432_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part432) = true := by rfl

def kid01_part433 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 25 13 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 13 2 true (-1),
.cycle 13 5 false (0),
.last 14 (2,true),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.last 15 (2,true),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[131072, 131072, 32768, 512, 2, 256, 393216, 393216, 425984, 32768, 128, 16384, 131072, 262144, 147456, 32768, 128, 16384, 262144],[2048, 64, 262144, 64, 64, 2048, 131072, 4096, 262144, 135168, 135168, 131072, 131072, 4096, 262144, 131072, 131072, 131072, 262144],337376⟩,
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.cycle 12 3 false (0),
.cycle 13 3 false (0),
.last 14 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 11 3 false (1)
])
theorem kid01_part433_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part433) = true := by rfl

def kid01_part434 : Audit := .cycle 10 2 true (1)
theorem kid01_part434_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part434) = true := by rfl

def kid01_part435 : Audit := .split 17 (5,false) (byMove [
.last 20 (2,true),
.cycle 31 13 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 17 1 false (-1),
.cycle 16 2 true (-1),
.cycle 15 5 false (1),
.last 18 (2,true),
.cycle 6 14 true (-1),
.cycle 6 14 true (-1),
.cycle 14 4 true (-1),
.cycle 15 4 false (1),
.last 19 (2,true),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[131072, 131072, 32768, 512, 2, 256, 393216, 393216, 425984, 32768, 128, 16384, 131072, 262144, 147456, 32768, 128, 16384, 262144],[2048, 64, 262144, 64, 64, 131072, 131072, 4096, 262144, 135168, 135168, 393216, 131072, 4096, 262144, 131072, 131072, 131072, 262144],337376⟩,
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 17 1 false (-1),
.cycle 13 5 false (1),
.cycle 15 3 false (1),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[16, 16, 64, 16, 16, 2, 64],64⟩,
.cycle 11 7 false (2)
])
theorem kid01_part435_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part435) = true := by rfl

def kid01_part436 : Audit := .split 12 (2,true) (byMove [
.last 17 (5,false),
.last 15 (5,false),
.cycle 16 1 false (0),
.last 17 (5,false),
.last 17 (5,false),
.cycle 9 10 true (1),
.last 14 (5,false),
.cycle 9 6 true (1),
.cycle 6 16 true (1),
.cycle 9 8 true (1),
.cycle 9 8 true (1),
.cycle 2 12 true (1),
.last 17 (5,false),
.last 15 (5,false),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 11 2 true (1),
.cycle 0 16 true (0),
.cycle 9 4 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 2 12 true (1)
])
theorem kid01_part436_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part436) = true := by rfl

def kid01_part437 : Audit := .cycle 7 6 true (1)
theorem kid01_part437_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part437) = true := by rfl

def kid01_part438 : Audit := .cycle 6 6 true (1)
theorem kid01_part438_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part438) = true := by rfl

def kid01_part439 : Audit := .split 14 (5,false) (byMove [
.cycle 12 4 true (2),
.cycle 9 6 true (1),
.last 15 (2,true),
.cycle 8 8 true (1),
.cycle 7 8 true (1),
.cycle 13 2 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (1),
.cycle 3 12 true (1),
.cycle 1 15 true (1),
.cycle 14 1 true (4),
.cycle 10 5 true (1),
.cycle 11 7 true (1),
.last 15 (2,true),
.cycle 7 9 true (1),
.cycle 6 9 true (1),
.cycle 12 3 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (1),
.cycle 8 7 true (1),
.cycle 14 1 true (4)
])
theorem kid01_part439_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part439) = true := by rfl

def kid01_part415 : Audit := .split 11 (5,true) (byMove [(kid01_part416),(kid01_part417),(kid01_part418),(kid01_part419),(kid01_part420),(kid01_part421),(kid01_part422),(kid01_part423),(kid01_part424),(kid01_part425),(kid01_part426),(kid01_part427),(kid01_part428),(kid01_part429),(kid01_part430),(kid01_part431),(kid01_part432),(kid01_part433),(kid01_part434),(kid01_part435),(kid01_part436),(kid01_part437),(kid01_part438),(kid01_part439)])

theorem kid01_part415_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part415) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part416),(kid01_part417),(kid01_part418),(kid01_part419),(kid01_part420),(kid01_part421),(kid01_part422),(kid01_part423),(kid01_part424),(kid01_part425),(kid01_part426),(kid01_part427),(kid01_part428),(kid01_part429),(kid01_part430),(kid01_part431),(kid01_part432),(kid01_part433),(kid01_part434),(kid01_part435),(kid01_part436),(kid01_part437),(kid01_part438),(kid01_part439)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part416_checked

  · exact kid01_part422_checked

  · exact kid01_part428_checked

  · exact kid01_part434_checked

  · exact kid01_part417_checked

  · exact kid01_part423_checked

  · exact kid01_part429_checked

  · exact kid01_part435_checked

  · exact kid01_part418_checked

  · exact kid01_part424_checked

  · exact kid01_part430_checked

  · exact kid01_part436_checked

  · exact kid01_part419_checked

  · exact kid01_part425_checked

  · exact kid01_part431_checked

  · exact kid01_part437_checked

  · exact kid01_part420_checked

  · exact kid01_part426_checked

  · exact kid01_part432_checked

  · exact kid01_part438_checked

  · exact kid01_part421_checked

  · exact kid01_part427_checked

  · exact kid01_part433_checked

  · exact kid01_part439_checked

def kid01_part440 : Audit := .cycle 0 12 true (0)
theorem kid01_part440_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part440) = true := by rfl

def kid01_part441 : Audit := .cycle 9 2 true (2)
theorem kid01_part441_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part441) = true := by rfl

def kid01_part442 : Audit := .split 11 (2,true) (byMove [
.cycle 2 11 true (1),
.cycle 15 5 false (1),
.cycle 16 1 false (0),
.cycle 19 7 false (1),
.cycle 19 7 false (1),
.split 12 (5,true) (byMove [
.cycle 2 12 true (1),
.cycle 13 18 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 15 21 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 16 5 false (1),
.cycle 15 3 false (1),
.cycle 13 9 false (1),
.cycle 27 1 false (-1),
.cycle 16 18 false (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (1),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 11 3 true (3),
.cycle 9 9 true (2),
.cycle 4 9 true (1),
.cycle 19 7 false (2),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 9 7 true (2),
.cycle 12 1 true (4)
]),
.cycle 10 2 true (2),
.cycle 15 5 false (1),
.cycle 6 12 true (-1),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.cycle 9 10 true (1),
.cycle 13 16 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 9 6 true (2),
.last 14 (5,false),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.last 14 (5,false),
.cycle 16 5 false (1),
.cycle 15 3 false (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 2 12 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 8 4 true (2),
.split 12 (5,false) (byMove [
.cycle 2 12 true (1),
.cycle 9 4 true (2),
.cycle 11 2 true (3),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.last 16 (5,true),
.last 14 (5,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part442_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part442) = true := by rfl

def kid01_part443 : Audit := .cycle 8 4 true (2)
theorem kid01_part443_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part443) = true := by rfl

def kid01_part444 : Audit := .cycle 7 4 true (2)
theorem kid01_part444_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part444) = true := by rfl

def kid01_part446 : Audit := .split 13 (5,false) (byMove [
.cycle 12 2 true (2),
.cycle 19 7 false (1),
.last 14 (2,true),
.cycle 23 9 false (1),
.cycle 23 9 false (1),
.cycle 0 21 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.cycle 10 4 true (2),
.cycle 19 7 false (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 23 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 13 1 true (3)
])
theorem kid01_part446_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part446) = true := by rfl

def kid01_part447 : Audit := .cycle 15 5 false (1)
theorem kid01_part447_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part447) = true := by rfl

def kid01_part448 : Audit := .split 12 (2,true) (byMove [
.last 14 (5,false),
.cycle 13 18 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 15 21 false (1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 16 5 false (1),
.cycle 13 8 false (1),
.cycle 29 9 false (1),
.cycle 27 1 false (-1),
.cycle 16 18 false (2),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (1),
.last 13 (5,false)
])
theorem kid01_part448_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part448) = true := by rfl

def kid01_part449 : Audit := .cycle 19 7 false (1)
theorem kid01_part449_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part449) = true := by rfl

def kid01_part450 : Audit := .cycle 19 7 false (1)
theorem kid01_part450_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part450) = true := by rfl

def kid01_part451 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 12 14 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 12 15 false (2),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 12 14 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 15 false (2),
.cycle 15 1 true (-1),
.cycle 13 6 false (1),
.last 17 (2,true),
.cycle 13 10 false (1),
.cycle 16 1 false (-2),
.cycle 12 13 false (2),
.cycle 15 1 false (-1),
.cycle 11 17 false (4),
.cycle 1 15 false (4),
.cycle 12 13 false (2),
.cycle 13 9 false (1),
.cycle 13 8 false (1),
.cycle 15 1 true (-1)
])
theorem kid01_part451_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part451) = true := by rfl

def kid01_part452 : Audit := .cycle 0 12 true (0)
theorem kid01_part452_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part452) = true := by rfl

def kid01_part453 : Audit := .cycle 1 11 true (1)
theorem kid01_part453_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part453) = true := by rfl

def kid01_part454 : Audit := .cycle 6 12 true (2)
theorem kid01_part454_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part454) = true := by rfl

def kid01_part455 : Audit := .cycle 3 9 true (1)
theorem kid01_part455_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part455) = true := by rfl

def kid01_part456 : Audit := .cycle 1 12 true (1)
theorem kid01_part456_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part456) = true := by rfl

def kid01_part457 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 19 7 false (2),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 9 9 true (2),
.cycle 4 9 true (1),
.cycle 19 7 false (2),
.cycle 39 1 false (7),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 9 7 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part457_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part457) = true := by rfl

def kid01_part458 : Audit := .cycle 10 2 true (2)
theorem kid01_part458_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part458) = true := by rfl

def kid01_part459 : Audit := .cycle 15 5 false (1)
theorem kid01_part459_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part459) = true := by rfl

def kid01_part460 : Audit := .split 12 (2,true) (byMove [
.last 14 (5,false),
.cycle 13 16 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 15 (5,false),
.last 14 (5,false),
.cycle 9 6 true (2),
.cycle 6 16 true (1),
.cycle 9 8 true (2),
.cycle 9 8 true (2),
.cycle 9 10 true (2),
.cycle 16 5 false (1),
.cycle 13 8 false (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (2)
])
theorem kid01_part460_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part460) = true := by rfl

def kid01_part461 : Audit := .cycle 7 6 true (2)
theorem kid01_part461_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part461) = true := by rfl

def kid01_part462 : Audit := .cycle 6 6 true (2)
theorem kid01_part462_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part462) = true := by rfl

def kid01_part463 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 27 17 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[32, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.cycle 13 4 true (-1),
.cycle 13 7 false (1),
.last 16 (2,true),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.cycle 14 2 true (-1),
.cycle 13 6 false (1),
.last 17 (2,true),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2048, 2048, 512, 512, 2, 256, 2048, 262144, 2304, 512, 8192, 256, 264192, 264192, 512, 512, 8192, 256, 262144],[262144, 64, 262144, 64, 64, 2048, 2048, 64, 262144, 2048, 2048, 2048, 262144, 64, 262144, 64, 64, 2048, 262144],341120⟩,
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.cycle 12 5 false (2),
.cycle 13 5 false (1),
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[32, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 3 false (1)
])
theorem kid01_part463_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part463) = true := by rfl

def kid01_part464 : Audit := .cycle 0 12 true (0)
theorem kid01_part464_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part464) = true := by rfl

def kid01_part465 : Audit := .cycle 1 11 true (1)
theorem kid01_part465_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part465) = true := by rfl

def kid01_part466 : Audit := .cycle 2 10 true (1)
theorem kid01_part466_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part466) = true := by rfl

def kid01_part467 : Audit := .cycle 7 7 true (2)
theorem kid01_part467_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part467) = true := by rfl

def kid01_part468 : Audit := .cycle 8 4 true (2)
theorem kid01_part468_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part468) = true := by rfl

def kid01_part469 : Audit := .split 12 (5,false) (byMove [
.cycle 12 2 true (3),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 10 3 true (2),
.cycle 11 5 true (2),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part469_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part469) = true := by rfl

def kid01_part445 : Audit := .split 11 (5,true) (byMove [(kid01_part446),(kid01_part447),(kid01_part448),(kid01_part449),(kid01_part450),(kid01_part451),(kid01_part452),(kid01_part453),(kid01_part454),(kid01_part455),(kid01_part456),(kid01_part457),(kid01_part458),(kid01_part459),(kid01_part460),(kid01_part461),(kid01_part462),(kid01_part463),(kid01_part464),(kid01_part465),(kid01_part466),(kid01_part467),(kid01_part468),(kid01_part469)])

theorem kid01_part445_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part445) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part446),(kid01_part447),(kid01_part448),(kid01_part449),(kid01_part450),(kid01_part451),(kid01_part452),(kid01_part453),(kid01_part454),(kid01_part455),(kid01_part456),(kid01_part457),(kid01_part458),(kid01_part459),(kid01_part460),(kid01_part461),(kid01_part462),(kid01_part463),(kid01_part464),(kid01_part465),(kid01_part466),(kid01_part467),(kid01_part468),(kid01_part469)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part446_checked

  · exact kid01_part452_checked

  · exact kid01_part458_checked

  · exact kid01_part464_checked

  · exact kid01_part447_checked

  · exact kid01_part453_checked

  · exact kid01_part459_checked

  · exact kid01_part465_checked

  · exact kid01_part448_checked

  · exact kid01_part454_checked

  · exact kid01_part460_checked

  · exact kid01_part466_checked

  · exact kid01_part449_checked

  · exact kid01_part455_checked

  · exact kid01_part461_checked

  · exact kid01_part467_checked

  · exact kid01_part450_checked

  · exact kid01_part456_checked

  · exact kid01_part462_checked

  · exact kid01_part468_checked

  · exact kid01_part451_checked

  · exact kid01_part457_checked

  · exact kid01_part463_checked

  · exact kid01_part469_checked

def kid01_part373 : Audit := .split 10 (0,true) (byMove [(kid01_part374),(kid01_part375),(kid01_part376),(kid01_part377),(kid01_part378),(kid01_part379),(kid01_part404),(kid01_part405),(kid01_part406),(kid01_part407),(kid01_part408),(kid01_part409),(kid01_part410),(kid01_part411),(kid01_part412),(kid01_part413),(kid01_part414),(kid01_part415),(kid01_part440),(kid01_part441),(kid01_part442),(kid01_part443),(kid01_part444),(kid01_part445)])

theorem kid01_part373_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (kid01_part373) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) 10 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part374),(kid01_part375),(kid01_part376),(kid01_part377),(kid01_part378),(kid01_part379),(kid01_part404),(kid01_part405),(kid01_part406),(kid01_part407),(kid01_part408),(kid01_part409),(kid01_part410),(kid01_part411),(kid01_part412),(kid01_part413),(kid01_part414),(kid01_part415),(kid01_part440),(kid01_part441),(kid01_part442),(kid01_part443),(kid01_part444),(kid01_part445)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part374_checked

  · exact kid01_part404_checked

  · exact kid01_part410_checked

  · exact kid01_part440_checked

  · exact kid01_part375_checked

  · exact kid01_part405_checked

  · exact kid01_part411_checked

  · exact kid01_part441_checked

  · exact kid01_part376_checked

  · exact kid01_part406_checked

  · exact kid01_part412_checked

  · exact kid01_part442_checked

  · exact kid01_part377_checked

  · exact kid01_part407_checked

  · exact kid01_part413_checked

  · exact kid01_part443_checked

  · exact kid01_part378_checked

  · exact kid01_part408_checked

  · exact kid01_part414_checked

  · exact kid01_part444_checked

  · exact kid01_part379_checked

  · exact kid01_part409_checked

  · exact kid01_part415_checked

  · exact kid01_part445_checked

def kid01_part471 : Audit := .split 15 (0,true) (byMove [
.cycle 0 31 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[8, 20, 20, 16, 16, 64, 64],96⟩,
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 10 15 false (2),
.split 16 (5,false) (byMove [
.far true 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 128, 512, 512, 2, 1, 128, 8388640, 8388640, 512, 8192, 4096, 16777216, 16777216, 512, 512, 524288, 262144, 16777216, 128, 512, 512, 2, 1, 16777216],[32, 128, 1, 128, 128, 16777216, 131072, 128, 4096, 128, 128, 16777216, 8388608, 128, 262144, 128, 128, 16777216, 32, 128, 1, 128, 128, 16777216, 16777216],17185792⟩,
.cycle 10 15 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 10 16 false (2),
.cycle 16 1 false (-2),
.last 21 (5,true),
.last 29 (5,true),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far true 4 ⟨0,[0, 1, 2, 1, 1, 3, 3, 3],[128, 128, 512, 512, 2, 128, 17301632, 2208, 2099360, 512, 8192, 2208, 16777344, 17301632, 512, 2097152, 128, 17301632, 17301504, 25821184, 27918336, 2097152, 524288, 25821184, 16777216],[32, 128, 1, 128, 128, 16777216, 131072, 128, 4096, 128, 128, 16777216, 2048, 524288, 64, 524288, 524288, 16777216, 8388608, 524288, 262144, 524288, 524288, 16777216, 16777216],31339584⟩,
.last 19 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.last 26 (5,true),
.cycle 16 1 false (-2),
.last 21 (5,true),
.last 29 (5,true),
.far true 4 ⟨0,[0, 1, 2, 1, 1, 3, 3, 3],[128, 128, 512, 512, 2, 128, 17301632, 2208, 2099360, 512, 8192, 2208, 16777344, 17301632, 512, 2097152, 128, 17301632, 17301504, 25821184, 27918336, 2097152, 524288, 25821184, 16777216],[32, 128, 1, 128, 128, 16777216, 131072, 128, 4096, 128, 128, 16777216, 2048, 524288, 64, 524288, 524288, 16777216, 8388608, 524288, 262144, 524288, 524288, 16777216, 16777216],31339584⟩,
.cycle 11 10 false (1),
.cycle 12 6 false (0),
.last 19 (5,true)
]),
.cycle 11 6 true (-1),
.cycle 16 20 true (0),
.cycle 44 1 false (4),
.cycle 16 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[16, 28, 28, 16, 16, 64, 64],96⟩,
.split 16 (5,false) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[32, 28, 28, 16, 16, 64, 64],64⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[32, 28, 28, 16, 16, 64, 64],64⟩,
.cycle 16 1 false (0),
.last 18 (5,true),
.cycle 17 25 true (0),
.cycle 0 24 true (-1),
.cycle 44 1 false (4),
.cycle 18 32 true (0),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 6 14 true (-1),
.cycle 17 1 false (-1),
.cycle 28 16 false (0),
.cycle 16 1 false (0),
.last 18 (5,true),
.cycle 11 6 true (-1),
.cycle 17 20 true (0),
.cycle 5 12 true (-1),
.cycle 6 12 true (-1),
.last 17 (5,true)
]),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-2),
.cycle 11 17 false (1),
.split 16 (5,false) (byMove [
.last 21 (5,true),
.last 25 (5,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 6 18 false (4),
.cycle 16 1 false (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.last 31 (5,true),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 11 10 false (1),
.cycle 17 1 false (-3),
.last 28 (5,true),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.cycle 11 8 false (1),
.cycle 11 8 false (1),
.last 17 (5,true)
]),
.cycle 10 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[2, 4, 4, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[4, 28, 12, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[8, 20, 20, 16, 16, 64, 64],96⟩,
.cycle 12 5 false (0),
.split 16 (5,false) (byMove [
.cycle 15 2 true (-1),
.cycle 12 5 false (0),
.cycle 0 39 false (4),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.last 17 (5,true),
.last 18 (5,true),
.cycle 17 25 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[32, 28, 12, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 20, 16, 16, 64, 64],64⟩,
.last 17 (5,true),
.last 18 (5,true),
.cycle 12 5 false (0),
.cycle 14 9 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 20, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 20, 16, 16, 64, 64],64⟩,
.last 17 (5,true),
.last 18 (5,true),
.cycle 10 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[32, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[32, 28, 12, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[32, 20, 20, 16, 16, 64, 64],64⟩,
.last 17 (5,true)
])
])
theorem kid01_part471_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part471) = true := by rfl

def kid01_part472 : Audit := .cycle 12 3 false (0)
theorem kid01_part472_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part472) = true := by rfl

def kid01_part473 : Audit := .cycle 17 1 false (-1)
theorem kid01_part473_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part473) = true := by rfl

def kid01_part474 : Audit := .cycle 12 5 false (0)
theorem kid01_part474_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part474) = true := by rfl

def kid01_part475 : Audit := .cycle 12 5 false (0)
theorem kid01_part475_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part475) = true := by rfl

def kid01_part476 : Audit := .split 15 (5,true) (byMove [
.split 29 (0,true) (byMove [
.cycle 0 31 false (4),
.cycle 0 34 false (4),
.last 31 (5,false),
.cycle 0 36 false (4),
.cycle 0 36 false (4),
.cycle 0 31 false (4),
.cycle 0 40 true (-2),
.cycle 30 35 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4096, 128, 256, 8, 1024, 1024, 4096, 4096],[4, 1032, 4096, 1024, 1024, 256, 4, 1024, 1032, 1024, 1024, 8, 4096],6176⟩,
.cycle 24 24 false (2),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[3, 2, 32, 2, 2, 1, 64],96⟩,
.last 30 (5,false),
.cycle 24 19 false (2),
.cycle 25 14 false (1),
.last 31 (5,false),
.cycle 25 18 false (1),
.cycle 25 18 false (1),
.last 36 (5,false),
.far true 1 ⟨0,[0, 0],[2, 3, 11, 8, 2, 64, 64],[2, 2, 32, 2, 2, 1, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 3, 11, 8, 2, 64, 64],[2, 2, 32, 2, 2, 1, 64],96⟩,
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[3, 2, 32, 2, 2, 1, 64],96⟩,
.cycle 24 22 false (2),
.cycle 25 16 false (1),
.last 30 (5,false)
]),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 10 15 false (2),
.split 16 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[34, 34, 42, 8, 2, 1, 64],[64, 2, 32, 2, 2, 32, 64],64⟩,
.cycle 10 15 false (2),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 10 16 false (2),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 30, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 2, 64],[64, 28, 28, 16, 16, 28, 64],64⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 26 1 true (2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.cycle 15 11 false (-1),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 1, 64],[64, 30, 30, 16, 16, 30, 64],64⟩,
.cycle 1 31 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 11 10 false (1),
.cycle 12 6 false (0),
.cycle 49 1 true (-5)
]),
.cycle 11 6 true (-1),
.cycle 16 20 true (0),
.cycle 44 1 false (4),
.cycle 16 1 false (0),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩,
.split 16 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.cycle 16 1 false (0),
.last 17 (0,true),
.cycle 17 25 true (0),
.cycle 32 1 false (4),
.cycle 44 1 false (4),
.cycle 18 32 true (0),
.cycle 20 1 true (4),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 6 14 true (-1),
.cycle 17 1 false (-1),
.cycle 28 16 false (0),
.cycle 16 1 false (0),
.last 17 (0,true),
.cycle 11 6 true (-1),
.cycle 17 20 true (0),
.cycle 5 12 true (-1),
.cycle 6 12 true (-1),
.cycle 20 1 true (4)
]),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 12 7 false (0),
.cycle 16 1 false (-2),
.cycle 11 17 false (1),
.split 16 (5,false) (byMove [
.cycle 15 6 false (-1),
.cycle 21 12 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 6 18 false (4),
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 12 5 false (0),
.cycle 20 1 false (0),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.cycle 15 2 true (-2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 11 10 false (1),
.cycle 17 1 false (-3),
.cycle 23 15 false (-1),
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.cycle 11 8 false (1),
.cycle 11 8 false (1),
.cycle 15 3 false (-1)
]),
.cycle 10 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 12 5 false (0),
.split 16 (5,false) (byMove [
.last 17 (0,true),
.cycle 12 5 false (0),
.cycle 20 1 false (-2),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.cycle 15 2 true (-1),
.last 17 (0,true),
.cycle 17 25 true (0),
.cycle 6 31 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.cycle 20 1 true (4),
.last 17 (0,true),
.cycle 12 5 false (0),
.cycle 12 10 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.cycle 20 3 true (2),
.last 17 (0,true),
.cycle 10 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 28, 12, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 24, 24, 16, 16, 32, 64],64⟩,
.cycle 20 1 true (4)
])
])
theorem kid01_part476_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part476) = true := by rfl

def kid01_part477 : Audit := .split 15 (0,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 64, 64],[30, 31, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 64, 64],[30, 31, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 14, 64, 64],[18, 19, 1, 16, 16, 64, 64],96⟩,
.cycle 11 9 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 64, 64],[30, 31, 1, 16, 16, 64, 64],96⟩,
.split 16 (5,false) (byMove [
.cycle 0 19 false (4),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 0 24 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 8, 64],[32, 2, 10, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[32, 2, 18, 2, 2, 64, 64],64⟩,
.last 17 (5,true),
.cycle 0 31 true (-1),
.cycle 0 38 true (-1),
.cycle 6 27 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 10, 64],[32, 2, 10, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.last 18 (5,true),
.cycle 11 9 false (1),
.cycle 12 5 false (1),
.far true 1 ⟨0,[0, 0],[14, 14, 14, 8, 2, 4, 64],[32, 2, 14, 2, 2, 64, 64],64⟩,
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.last 17 (5,true),
.cycle 9 9 false (3),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.cycle 11 7 false (1),
.last 18 (5,true)
]),
.cycle 0 18 true (-1),
.cycle 0 37 true (-1),
.cycle 0 48 true (-2),
.cycle 6 23 true (-1),
.cycle 0 44 true (-1),
.split 16 (5,true) (byMove [
.cycle 0 20 true (-1),
.cycle 0 24 true (-1),
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 128, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[32, 1, 1, 1024, 1024, 4194304, 32, 32, 1, 65536, 65536, 128, 32, 4194304, 1, 4194304, 4194304, 128, 32, 4194304, 1, 4194304, 4194304, 128, 16777216],25365024⟩,
.cycle 10 13 false (2),
.far false 8 ⟨0,[0, 6, 0, 6, 0, 6, 2, 3, 4, 4, 1, 7, 2, 5, 2, 3],[137438953472, 274877906944, 8, 4194304, 32768, 281474976710656, 137438953472, 274877906944, 8, 4194304, 32768, 281474976710656, 137438953472, 274877906944, 8, 70368748371968, 33280, 281474976710656, 524288, 1048576, 32768, 4194304, 0, 281474976710656, 33554432, 67108864, 134217728, 268435456, 281475480027136, 281474976710656, 8796093022208, 17592186044416, 512, 70368744177664, 281474976710656, 281474976710656, 2147483648, 4294967296, 32768, 17179869184, 137438953472, 281474976710656, 524288, 1048576, 32768, 4194304, 0, 281474976710656, 281474976710656],[32, 4096, 1, 1099511627776, 1099511627776, 70368748371968, 32, 4096, 1, 1099511627776, 1099511627776, 281474976710656, 32, 4160, 1, 1099511627776, 1099511627776, 4294967296, 131072, 4194304, 4096, 4194304, 4194304, 0, 536870912, 281476033675264, 16777216, 268435456, 268435456, 281475480027136, 2048, 70368748371968, 64, 70368744177664, 70368744177664, 281474976710656, 131072, 32, 4096, 17179869184, 17179869184, 137438953472, 131072, 4194304, 4096, 4194304, 4194304, 0, 281474976710656],425013849229344⟩,
.last 17 (5,false),
.last 18 (5,false),
.cycle 0 20 true (-1),
.cycle 0 18 true (-1),
.cycle 0 22 true (-1),
.cycle 0 22 true (-1),
.last 18 (5,false),
.last 30 (5,false),
.last 20 (5,false),
.last 26 (5,false),
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 128, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[32, 1, 1, 1024, 1024, 4194304, 32, 32, 1, 65536, 65536, 65536, 32, 4194304, 1, 4194304, 4194304, 4194304, 32, 4194304, 1, 4194304, 4194304, 4194304, 16777216],25365024⟩,
.last 28 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.cycle 0 18 true (-1),
.last 24 (5,false),
.last 24 (5,false),
.last 18 (5,false)
]),
.cycle 10 7 false (2),
.cycle 0 24 true (-1),
.cycle 0 42 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[16, 17, 1, 16, 16, 64, 64],96⟩,
.cycle 11 16 false (1),
.split 16 (5,false) (byMove [
.last 30 (5,true),
.cycle 11 16 false (1),
.cycle 11 8 true (-1),
.cycle 11 20 false (1),
.cycle 11 20 false (1),
.last 17 (5,true),
.cycle 15 2 true (0),
.cycle 0 30 true (-1),
.cycle 0 24 true (-1),
.cycle 0 42 true (-1),
.cycle 0 42 true (-1),
.last 17 (5,true),
.cycle 11 9 false (1),
.cycle 12 5 false (1),
.far true 1 ⟨0,[0, 0],[14, 14, 14, 8, 2, 4, 64],[32, 2, 14, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 8, 64],[32, 2, 10, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[32, 2, 18, 2, 2, 64, 64],64⟩,
.last 17 (5,true),
.last 18 (5,true),
.cycle 10 7 false (2),
.cycle 0 24 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[32, 2, 2, 2, 2, 64, 64],64⟩,
.last 17 (5,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[1, 1, 1, 16, 16, 64, 64],96⟩,
.cycle 1 25 true (-1),
.cycle 0 32 true (-1),
.cycle 26 9 true (1),
.cycle 0 36 true (-1),
.split 16 (5,true) (byMove [
.last 18 (5,false),
.last 26 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.last 28 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.cycle 0 20 true (-1),
.cycle 0 18 true (-1),
.cycle 0 22 true (-1),
.cycle 0 22 true (-1),
.last 18 (5,false),
.cycle 15 2 true (1),
.last 26 (5,false),
.last 22 (5,false),
.last 36 (5,false),
.last 36 (5,false),
.last 18 (5,false),
.last 18 (5,false),
.cycle 10 31 true (-1),
.cycle 0 18 true (-1),
.cycle 18 11 true (0),
.last 32 (5,false),
.last 18 (5,false)
])
])
theorem kid01_part477_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part477) = true := by rfl

def kid01_part478 : Audit := .cycle 15 19 true (0)
theorem kid01_part478_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part478) = true := by rfl

def kid01_part479 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 4, 4, 16, 16, 64, 64],96⟩
theorem kid01_part479_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part479) = true := by rfl

def kid01_part480 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[64, 24, 8, 16, 16, 64, 64],96⟩
theorem kid01_part480_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part480) = true := by rfl

def kid01_part481 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 16, 16, 16, 16, 64, 64],96⟩
theorem kid01_part481_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part481) = true := by rfl

def kid01_part483 : Audit := .split 50 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 4, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 8, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.cycle 28 23 false (6),
.last 53 (0,true),
.cycle 0 51 true (-2),
.cycle 44 18 true (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 10, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 10, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.cycle 44 19 true (2),
.cycle 50 1 true (6),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.cycle 48 3 true (4),
.cycle 48 7 true (4),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 8, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.cycle 28 23 false (6),
.last 53 (0,true),
.cycle 40 25 true (0),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.cycle 44 17 true (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 2, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.cycle 48 5 true (4),
.cycle 50 1 true (6)
])
theorem kid01_part483_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part483) = true := by rfl

def kid01_part484 : Audit := .far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[524288, 128, 2097152, 512, 2, 1073741824, 524288, 1074274432, 1074274432, 2097152, 8192, 1073741824, 1074274432, 1074274432, 1074307712, 32768, 8192, 1073741824, 128, 524288, 524288, 512, 33554432, 1073741824, 128, 128, 2097152, 512, 2, 1073741824, 1073741824],[1073741824, 128, 1073741824, 128, 128, 2, 1073741824, 524288, 128, 524288, 524288, 8192, 1073741824, 8192, 1074274432, 8192, 8192, 8192, 1073741824, 128, 1074274432, 128, 128, 33554432, 1073741824, 128, 1073741824, 128, 128, 2, 1073741824],1942453682⟩
theorem kid01_part484_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part484) = true := by rfl

def kid01_part485 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[262144, 32, 32, 1024, 1024, 65536, 262144, 65536, 32, 65536, 65536, 262144, 262144, 65536, 32, 65536, 65536, 262144, 262144],396320⟩
theorem kid01_part485_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part485) = true := by rfl

def kid01_part486 : Audit := .cycle 11 9 false (1)
theorem kid01_part486_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part486) = true := by rfl

def kid01_part487 : Audit := .split 20 (5,false) (byMove [
.cycle 8 24 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.cycle 10 18 false (2),
.cycle 11 14 false (1),
.cycle 16 5 false (0),
.cycle 10 22 false (2),
.cycle 0 43 true (-2),
.cycle 26 22 true (0),
.cycle 124 110 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.cycle 33 26 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 32, 64],[64, 56, 32, 16, 16, 56, 64],64⟩,
.cycle 10 12 false (2),
.cycle 10 18 false (2),
.cycle 34 28 false (2),
.cycle 10 16 false (2),
.cycle 16 5 false (0),
.cycle 9 26 false (3),
.cycle 22 30 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 2, 64],[64, 62, 32, 16, 16, 30, 64],64⟩,
.cycle 31 24 false (1),
.cycle 29 20 false (1),
.cycle 30 24 false (2),
.cycle 49 24 false (1)
])
theorem kid01_part487_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part487) = true := by rfl

def kid01_part488 : Audit := .split 16 (5,false) (byMove [
.last 17 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.cycle 20 1 false (0),
.cycle 11 16 false (1),
.cycle 18 5 false (0),
.cycle 18 1 false (-2),
.cycle 0 31 true (-1),
.cycle 20 18 true (2),
.cycle 6 27 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.cycle 22 1 true (2),
.last 17 (0,true),
.cycle 12 5 false (1),
.cycle 107 7 true (-4),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.cycle 18 1 false (-2),
.cycle 9 9 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 2, 64],[64, 62, 32, 16, 16, 30, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 4, 64],[64, 60, 32, 16, 16, 28, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.cycle 11 7 false (1),
.cycle 33 1 true (-3)
])
theorem kid01_part488_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part488) = true := by rfl

def kid01_part489 : Audit := .split 16 (0,true) (byMove [
.last 20 (5,false),
.last 24 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 128, 262144, 262144],[65536, 32, 32, 1024, 1024, 1, 262144, 1, 32, 65536, 65536, 1, 262144, 65536, 32, 65536, 65536, 1, 262144],396320⟩,
.cycle 10 13 false (2),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 1, 2, 3],[128, 256, 8, 4194304, 32768, 16777216, 524288, 1048576, 32768, 4194304, 16777216, 16777216, 128, 256, 8, 4194304, 32768, 16777216, 524288, 1048576, 32768, 4194304, 128, 16777216, 16777216],[4194304, 131072, 32, 1024, 1024, 1, 16777216, 1, 131072, 4194304, 4194304, 4096, 17825792, 131072, 32, 1024, 1024, 1, 128, 4194304, 131072, 4194304, 4194304, 4096, 16777216],25300000⟩,
.last 17 (5,false),
.cycle 0 18 true (-1),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.cycle 0 18 true (-1),
.cycle 0 30 true (-1),
.cycle 0 20 true (-1),
.cycle 0 26 true (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 128, 262144, 262144],[65536, 32, 32, 1024, 1024, 1, 65536, 1, 32, 65536, 65536, 1, 65536, 65536, 32, 65536, 65536, 1, 262144],396320⟩,
.cycle 0 28 true (-1),
.last 17 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8320, 262144, 262144],[64, 32, 32, 1024, 1024, 1, 4096, 1, 32, 65536, 65536, 1, 4096, 4160, 32, 65536, 65536, 1, 262144],396320⟩,
.cycle 0 22 true (-1),
.last 18 (5,false),
.cycle 0 24 true (-1),
.cycle 0 24 true (-1),
.cycle 0 18 true (-1)
])
theorem kid01_part489_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part489) = true := by rfl

def kid01_part490 : Audit := .split 37 (5,false) (byMove [
.cycle 30 25 true (3),
.cycle 1 37 true (-1),
.cycle 21 17 true (3),
.cycle 16 27 true (1),
.cycle 16 29 true (1),
.cycle 19 20 true (3),
.cycle 0 38 true (-1),
.cycle 20 18 true (3),
.cycle 30 27 true (3),
.cycle 6 37 true (-1),
.cycle 20 19 true (3),
.cycle 37 1 true (7),
.cycle 28 11 true (3),
.cycle 35 3 true (5),
.cycle 34 7 true (5),
.cycle 23 15 true (3),
.cycle 17 32 true (1),
.cycle 15 24 true (1),
.cycle 30 25 true (3),
.cycle 1 37 true (-1),
.cycle 21 17 true (3),
.cycle 16 27 true (1),
.cycle 34 5 true (5),
.cycle 37 1 true (7)
])
theorem kid01_part490_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part490) = true := by rfl

def kid01_part491 : Audit := .split 48 (5,false) (byMove [
.cycle 0 49 true (-2),
.cycle 45 16 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 45 17 true (3),
.cycle 58 1 false (0),
.cycle 0 49 true (-2),
.cycle 45 16 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 45 17 true (3),
.cycle 48 1 true (6),
.cycle 43 29 true (1),
.cycle 47 3 true (5),
.cycle 47 7 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 66 1 false (8),
.cycle 43 21 true (1),
.cycle 1 48 true (-2),
.cycle 45 15 true (3),
.cycle 43 32 true (1),
.cycle 47 5 true (5),
.cycle 48 1 true (6)
])
theorem kid01_part491_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part491) = true := by rfl

def kid01_part492 : Audit := .cycle 6 23 true (-1)
theorem kid01_part492_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part492) = true := by rfl

def kid01_part493 : Audit := .split 44 (5,false) (byMove [
.cycle 30 33 true (2),
.cycle 1 44 true (-1),
.cycle 26 19 true (2),
.cycle 17 30 true (1),
.cycle 50 50 false (4),
.cycle 23 23 true (2),
.cycle 0 45 true (-1),
.cycle 25 20 true (2),
.cycle 30 35 true (2),
.cycle 6 44 true (-1),
.cycle 24 21 true (2),
.cycle 44 1 true (6),
.cycle 33 13 true (2),
.cycle 42 3 true (4),
.cycle 40 7 true (4),
.cycle 28 17 true (2),
.cycle 86 117 true (-3),
.cycle 15 31 true (1),
.cycle 30 33 true (2),
.cycle 1 44 true (-1),
.cycle 26 19 true (2),
.cycle 17 30 true (1),
.cycle 40 5 true (4),
.cycle 44 1 true (6)
])
theorem kid01_part493_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part493) = true := by rfl

def kid01_part494 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 16 17 true (1),
.cycle 24 1 false (0),
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 16 17 true (2),
.cycle 18 1 true (4),
.cycle 17 7 true (2),
.cycle 18 3 true (3),
.cycle 18 7 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 65 32 true (3),
.cycle 29 1 false (5),
.cycle 15 21 true (1),
.cycle 1 18 true (-1),
.cycle 16 15 true (2),
.cycle 17 10 true (3),
.cycle 18 5 true (3),
.cycle 18 1 true (4)
])
theorem kid01_part494_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part494) = true := by rfl

def kid01_part495 : Audit := .cycle 10 7 false (2)
theorem kid01_part495_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part495) = true := by rfl

def kid01_part496 : Audit := .split 24 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 8 17 false (4),
.cycle 10 17 false (4),
.cycle 0 25 true (-1),
.cycle 16 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 16 21 true (0),
.cycle 24 1 true (4),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.cycle 22 3 true (2),
.cycle 22 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 8 17 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 13 29 true (-1),
.cycle 1 24 true (-1),
.cycle 16 19 true (0),
.cycle 19 12 true (1),
.cycle 22 5 true (2),
.cycle 24 1 true (4)
])
theorem kid01_part496_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part496) = true := by rfl

def kid01_part497 : Audit := .split 42 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 10, 2, 2, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 8 35 false (4),
.cycle 68 9 false (1),
.cycle 0 43 true (-1),
.cycle 17 30 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 17 31 true (0),
.cycle 42 1 true (4),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 10, 2, 2, 4, 64],64⟩,
.cycle 40 3 true (2),
.cycle 36 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 8 35 false (4),
.cycle 14 31 true (0),
.cycle 6 57 true (-1),
.cycle 1 42 true (-1),
.cycle 17 29 true (0),
.cycle 28 16 true (1),
.cycle 38 5 true (2),
.cycle 42 1 true (4)
])
theorem kid01_part497_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part497) = true := by rfl

def kid01_part498 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[262144, 32, 32, 1024, 1024, 65536, 262144, 65536, 32, 65536, 65536, 65536, 262144, 65536, 32, 65536, 65536, 65536, 262144],396320⟩
theorem kid01_part498_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part498) = true := by rfl

def kid01_part499 : Audit := .split 20 (5,false) (byMove [
.cycle 10 16 false (2),
.cycle 28 22 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 11 14 false (1),
.cycle 16 5 false (0),
.cycle 11 26 false (1),
.last 21 (0,true),
.cycle 21 32 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 30 24 false (2),
.cycle 10 12 false (2),
.cycle 11 14 false (1),
.cycle 29 20 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 16 5 false (0),
.cycle 35 28 false (1),
.last 21 (0,true),
.cycle 11 16 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 27 18 false (1),
.cycle 27 18 false (1),
.cycle 29 20 false (1)
])
theorem kid01_part499_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part499) = true := by rfl

def kid01_part500 : Audit := .split 16 (5,false) (byMove [
.last 17 (0,true),
.cycle 28 22 false (2),
.cycle 20 1 false (0),
.cycle 11 16 false (1),
.cycle 18 5 false (0),
.cycle 18 1 false (-2),
.last 17 (0,true),
.cycle 17 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 18 31 true (0),
.cycle 15 2 true (0),
.last 17 (0,true),
.cycle 12 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 18 1 false (-2),
.last 17 (0,true),
.cycle 10 7 false (2),
.cycle 17 19 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 18 3 false (0)
])
theorem kid01_part500_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part500) = true := by rfl

def kid01_part501 : Audit := .split 16 (0,true) (byMove [
.last 26 (5,false),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.cycle 10 37 true (-1),
.cycle 0 18 true (-1),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 38 (5,false),
.cycle 10 9 false (2),
.cycle 12 32 true (-1),
.cycle 14 26 true (0),
.cycle 6 50 true (-1),
.cycle 6 50 true (-1),
.cycle 15 2 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[64, 32, 32, 1024, 1024, 64, 4096, 64, 32, 65536, 65536, 4096, 4096, 4096, 32, 65536, 65536, 4096, 262144],396320⟩,
.cycle 10 31 true (-1),
.last 18 (5,false),
.cycle 18 11 true (0),
.cycle 6 44 true (-1),
.last 42 (5,false)
])
theorem kid01_part501_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part501) = true := by rfl

def kid01_part502 : Audit := .cycle 1 25 true (-1)
theorem kid01_part502_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part502) = true := by rfl

def kid01_part503 : Audit := .split 32 (5,false) (byMove [
.cycle 29 21 true (3),
.cycle 1 32 true (-1),
.cycle 18 15 true (2),
.cycle 16 24 true (2),
.cycle 38 40 false (4),
.cycle 17 17 true (2),
.cycle 0 33 true (-1),
.cycle 18 16 true (2),
.cycle 29 23 true (3),
.cycle 6 32 true (-1),
.cycle 18 17 true (2),
.cycle 32 1 true (6),
.cycle 25 9 true (2),
.cycle 31 3 true (5),
.cycle 31 7 true (5),
.cycle 20 13 true (2),
.cycle 70 79 true (-2),
.cycle 15 19 true (1),
.cycle 29 21 true (3),
.cycle 1 32 true (-1),
.cycle 18 15 true (2),
.cycle 16 24 true (2),
.cycle 31 5 true (5),
.cycle 32 1 true (6)
])
theorem kid01_part503_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part503) = true := by rfl

def kid01_part504 : Audit := .cycle 26 9 true (1)
theorem kid01_part504_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part504) = true := by rfl

def kid01_part505 : Audit := .split 36 (5,false) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 8 29 false (4),
.cycle 8 31 false (4),
.cycle 0 37 true (-1),
.cycle 16 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 16 27 true (0),
.cycle 36 1 true (4),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.cycle 34 3 true (2),
.cycle 32 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 8 29 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 6 49 true (-1),
.cycle 1 36 true (-1),
.cycle 16 25 true (0),
.cycle 25 14 true (1),
.cycle 32 5 true (2),
.cycle 36 1 true (4)
])
theorem kid01_part505_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part505) = true := by rfl

def kid01_part506 : Audit := .split 18 (5,false) (byMove [
.last 19 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 2 19 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 8 35 false (4),
.cycle 17 2 true (3),
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 18 1 true (4),
.last 19 (0,true),
.cycle 10 9 true (-1),
.cycle 17 3 true (3),
.cycle 7 13 true (-1),
.cycle 6 13 true (-1),
.cycle 16 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 2, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 8 11 true (-1),
.cycle 18 1 true (4)
])
theorem kid01_part506_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part506) = true := by rfl

def kid01_part482 : Audit := .split 15 (5,true) (byMove [(kid01_part483),(kid01_part484),(kid01_part485),(kid01_part486),(kid01_part487),(kid01_part488),(kid01_part489),(kid01_part490),(kid01_part491),(kid01_part492),(kid01_part493),(kid01_part494),(kid01_part495),(kid01_part496),(kid01_part497),(kid01_part498),(kid01_part499),(kid01_part500),(kid01_part501),(kid01_part502),(kid01_part503),(kid01_part504),(kid01_part505),(kid01_part506)])

theorem kid01_part482_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part482) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part483),(kid01_part484),(kid01_part485),(kid01_part486),(kid01_part487),(kid01_part488),(kid01_part489),(kid01_part490),(kid01_part491),(kid01_part492),(kid01_part493),(kid01_part494),(kid01_part495),(kid01_part496),(kid01_part497),(kid01_part498),(kid01_part499),(kid01_part500),(kid01_part501),(kid01_part502),(kid01_part503),(kid01_part504),(kid01_part505),(kid01_part506)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid01_part486_checked

  · exact kid01_part492_checked

  · exact kid01_part498_checked

  · exact kid01_part504_checked

  · exact kid01_part487_checked

  · exact kid01_part493_checked

  · exact kid01_part499_checked

  · exact kid01_part505_checked

  · exact kid01_part488_checked

  · exact kid01_part494_checked

  · exact kid01_part500_checked

  · exact kid01_part506_checked

def kid01_part507 : Audit := .split 15 (0,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[28, 16, 16, 16, 16, 64, 64],96⟩,
.cycle 26 12 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[24, 16, 16, 16, 16, 64, 64],96⟩,
.split 16 (5,false) (byMove [
.last 32 (5,true),
.far true 4 ⟨0,[0, 1, 2, 1, 1, 3, 3, 3],[128, 128, 512, 512, 2, 2, 17301632, 131200, 2228352, 512, 8192, 8192, 16777344, 17301632, 512, 2097152, 128, 128, 17301504, 25690112, 27787264, 2097152, 524288, 524288, 16777216],[32, 128, 64, 128, 128, 16777216, 131072, 128, 64, 128, 128, 16777216, 2048, 524288, 262144, 524288, 524288, 16777216, 8388608, 524288, 262144, 524288, 524288, 16777216, 16777216],31210560⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 10 16 false (2),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 4 true (-2),
.cycle 6 14 true (-2),
.cycle 17 1 false (-1),
.last 32 (5,true),
.last 18 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.last 26 (5,true),
.cycle 16 1 false (-2),
.cycle 10 8 false (2),
.last 20 (5,true),
.last 30 (5,true),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 8192, 32768, 512, 2, 8192, 270336, 272384, 305152, 32768, 128, 8192, 8192, 2048, 2048, 32768, 128, 8192, 262144],[32, 128, 64, 128, 128, 262144, 2048, 8192, 4096, 8192, 8192, 262144, 2048, 8192, 4096, 8192, 8192, 262144, 262144],329152⟩,
.cycle 12 6 false (0),
.last 18 (5,true)
]),
.cycle 0 20 true (-1),
.cycle 12 4 true (-1),
.cycle 11 7 false (1),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.split 16 (5,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4096, 128, 256, 8, 1024, 8, 4096, 4096],[32, 256, 256, 1024, 1024, 256, 32, 256, 256, 1024, 1024, 4096, 4096],6176⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[32, 24, 24, 16, 16, 24, 64],96⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[32, 24, 24, 16, 16, 24, 64],96⟩,
.last 17 (5,false),
.last 20 (5,false),
.cycle 17 25 true (0),
.cycle 11 8 true (-1),
.cycle 44 1 false (4),
.cycle 18 32 true (0),
.last 20 (5,false),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 6 14 true (-1),
.cycle 17 1 false (-1),
.cycle 28 16 false (0),
.last 17 (5,false),
.last 20 (5,false),
.cycle 11 6 true (-1),
.cycle 17 20 true (0),
.cycle 5 12 true (-1),
.cycle 6 12 true (-1),
.last 20 (5,false)
]),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.split 16 (5,false) (byMove [
.last 21 (5,true),
.last 33 (5,true),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.far true 4 ⟨0,[0, 1, 2, 1, 1, 3, 3, 3],[128, 128, 512, 512, 2, 16, 17301632, 2176, 2099328, 512, 8192, 65536, 16777344, 17301632, 512, 2097152, 128, 1024, 17301504, 25690112, 27787264, 2097152, 524288, 4194304, 16777216],[2048, 128, 64, 128, 128, 16777216, 2048, 128, 64, 128, 128, 16777216, 8388608, 524288, 262144, 524288, 524288, 16777216, 8388608, 524288, 262144, 524288, 524288, 16777216, 16777216],31339584⟩,
.cycle 16 1 false (-2),
.cycle 15 2 true (-2),
.cycle 12 5 false (0),
.cycle 11 8 false (1),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 8192, 32768, 512, 2, 32768, 270336, 401408, 434176, 32768, 128, 434176, 8192, 131072, 131072, 32768, 128, 131072, 262144],[2048, 128, 64, 128, 128, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 262144],331200⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 8192, 32768, 512, 2, 8192, 270336, 401408, 434176, 32768, 128, 401408, 8192, 131072, 131072, 32768, 128, 131072, 262144],[2048, 128, 64, 128, 128, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 262144],331200⟩,
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 1],[8192, 128, 32768, 512, 2, 256, 270464, 401536, 434816, 32768, 128, 16384, 128, 2048, 2048, 512, 128, 256, 262144],[2048, 128, 64, 128, 128, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 2048, 128, 64, 128, 128, 262144, 262144],464370⟩,
.cycle 17 1 false (-3),
.last 36 (5,true),
.cycle 16 1 false (-2),
.last 18 (5,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 8192, 32768, 512, 2, 8192, 270336, 401408, 434176, 32768, 128, 8192, 8192, 131072, 131072, 32768, 128, 8192, 262144],[2048, 128, 64, 128, 128, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 262144],329152⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 1],[8192, 128, 32768, 512, 2, 128, 270464, 401536, 434816, 32768, 128, 8192, 128, 2048, 2048, 512, 128, 128, 262144],[2048, 128, 64, 128, 128, 262144, 131072, 8192, 4096, 8192, 8192, 262144, 2048, 128, 64, 128, 128, 262144, 262144],464370⟩,
.last 17 (5,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[1, 1, 1, 16, 16, 64, 64],96⟩,
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[8, 16, 16, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[16, 16, 16, 16, 16, 64, 64],96⟩,
.split 16 (5,true) (byMove [
.last 18 (5,false),
.cycle 12 5 false (0),
.cycle 11 8 false (1),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.last 18 (5,false),
.last 20 (5,false),
.cycle 17 25 true (0),
.cycle 10 9 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[32, 24, 24, 16, 16, 8, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 16, 16, 16, 16, 16, 64],96⟩,
.last 20 (5,false),
.cycle 15 2 true (-1),
.cycle 12 5 false (0),
.cycle 11 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 16, 16, 16, 16, 16, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 16, 16, 16, 16, 16, 64],96⟩,
.last 18 (5,false),
.last 20 (5,false),
.cycle 10 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 4, 4, 16, 16, 4, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[32, 24, 24, 16, 16, 8, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[32, 16, 16, 16, 16, 16, 64],96⟩,
.last 20 (5,false)
])
])
theorem kid01_part507_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part507) = true := by rfl

def kid01_part508 : Audit := .cycle 12 3 false (0)
theorem kid01_part508_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part508) = true := by rfl

def kid01_part509 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 16, 16, 16, 16, 64, 64],96⟩
theorem kid01_part509_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part509) = true := by rfl

def kid01_part510 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 16, 16, 16, 16, 64, 64],96⟩
theorem kid01_part510_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part510) = true := by rfl

def kid01_part511 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 16, 16, 16, 16, 64, 64],96⟩
theorem kid01_part511_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part511) = true := by rfl

def kid01_part513 : Audit := .split 20 (0,true) (byMove [
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 2, 64, 64],[1, 2, 32, 2, 2, 1, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 3, 11, 8, 2, 64, 64],[2, 2, 32, 2, 2, 1, 64],96⟩,
.cycle 22 1 false (-2),
.cycle 21 1 false (-3),
.cycle 10 20 false (2),
.last 21 (5,false),
.cycle 11 11 false (1),
.cycle 13 8 true (-2),
.cycle 6 18 true (-2),
.cycle 21 1 false (-1),
.cycle 17 16 true (-2),
.last 21 (5,false),
.cycle 11 11 false (1),
.cycle 13 8 false (0),
.cycle 12 12 false (0),
.cycle 21 1 false (-3),
.cycle 17 10 false (0),
.last 21 (5,false),
.cycle 10 12 false (2),
.cycle 17 4 true (-2),
.cycle 17 14 true (-2),
.far true 1 ⟨0,[0, 0],[2, 3, 11, 8, 2, 64, 64],[2, 2, 32, 2, 2, 1, 64],96⟩,
.cycle 12 10 false (0),
.last 21 (5,false)
])
theorem kid01_part513_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part513) = true := by rfl

def kid01_part514 : Audit := .cycle 26 12 false (0)
theorem kid01_part514_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part514) = true := by rfl

def kid01_part515 : Audit := .cycle 17 1 false (-1)
theorem kid01_part515_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part515) = true := by rfl

def kid01_part516 : Audit := .cycle 16 1 false (-2)
theorem kid01_part516_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part516) = true := by rfl

def kid01_part517 : Audit := .far true 1 ⟨0,[0, 0],[2, 18, 26, 8, 2, 64, 64],[64, 2, 32, 2, 2, 16, 64],96⟩
theorem kid01_part517_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part517) = true := by rfl

def kid01_part518 : Audit := .split 16 (5,false) (byMove [
.cycle 0 35 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 24, 64],64⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 10 16 false (2),
.cycle 16 1 false (-2),
.cycle 11 7 false (1),
.cycle 13 4 true (-2),
.cycle 6 14 true (-2),
.cycle 17 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 24, 64],64⟩,
.cycle 28 1 true (2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 12 8 false (0),
.cycle 17 1 false (-3),
.cycle 15 11 false (-1),
.cycle 16 1 false (-2),
.cycle 10 8 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 28, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 24, 64],64⟩,
.cycle 12 6 false (0),
.cycle 60 1 true (-6)
])
theorem kid01_part518_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part518) = true := by rfl

def kid01_part519 : Audit := .split 16 (0,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[1, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[16, 2, 32, 2, 2, 2, 64],96⟩,
.last 17 (5,false),
.cycle 0 20 true (-1),
.cycle 17 25 true (0),
.last 18 (5,false),
.cycle 44 1 false (4),
.cycle 18 32 true (0),
.cycle 0 20 true (-1),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 6 14 true (-1),
.cycle 17 1 false (-1),
.cycle 28 16 false (0),
.last 17 (5,false),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 11 6 true (-1),
.cycle 17 20 true (0),
.cycle 5 12 true (-1),
.cycle 6 12 true (-1),
.cycle 0 20 true (-1)
])
theorem kid01_part519_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part519) = true := by rfl

def kid01_part520 : Audit := .cycle 12 4 true (-1)
theorem kid01_part520_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part520) = true := by rfl

def kid01_part521 : Audit := .split 17 (5,false) (byMove [
.last 24 (0,true),
.cycle 28 16 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 12 6 true (-1),
.cycle 16 2 true (-1),
.cycle 6 14 true (-1),
.cycle 6 14 true (-1),
.cycle 29 1 false (5),
.cycle 11 8 false (1),
.cycle 13 5 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 11 7 false (1),
.cycle 14 4 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 4, 4, 16, 16, 4, 64],64⟩
])
theorem kid01_part521_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part521) = true := by rfl

def kid01_part522 : Audit := .cycle 6 12 true (-1)
theorem kid01_part522_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part522) = true := by rfl

def kid01_part523 : Audit := .cycle 6 12 true (-1)
theorem kid01_part523_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part523) = true := by rfl

def kid01_part524 : Audit := .split 20 (5,false) (byMove [
.cycle 0 21 true (-1),
.cycle 16 18 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 16 19 true (0),
.cycle 20 1 false (4),
.cycle 0 21 true (-1),
.cycle 16 18 true (0),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 16 19 true (0),
.cycle 20 1 true (4),
.cycle 17 9 true (1),
.cycle 18 5 true (2),
.cycle 18 9 true (2),
.cycle 21 1 false (3),
.cycle 18 11 true (2),
.cycle 20 1 false (4),
.cycle 15 23 true (-1),
.cycle 1 20 true (-1),
.cycle 16 17 true (0),
.cycle 17 12 true (1),
.cycle 18 7 true (2),
.cycle 20 1 true (4)
])
theorem kid01_part524_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part524) = true := by rfl

def kid01_part525 : Audit := .cycle 11 6 false (1)
theorem kid01_part525_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part525) = true := by rfl

def kid01_part526 : Audit := .cycle 13 3 false (0)
theorem kid01_part526_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part526) = true := by rfl

def kid01_part527 : Audit := .far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[8192, 8192, 32768, 512, 2, 262144, 155648, 155648, 188416, 32768, 128, 262144, 8192, 16384, 16384, 32768, 128, 262144, 262144],[262144, 128, 2048, 128, 128, 256, 262144, 8192, 131072, 8192, 8192, 16384, 262144, 8192, 131072, 8192, 8192, 16384, 262144],462304⟩
theorem kid01_part527_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part527) = true := by rfl

def kid01_part528 : Audit := .cycle 16 1 false (-2)
theorem kid01_part528_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part528) = true := by rfl

def kid01_part529 : Audit := .far true 1 ⟨0,[0, 0],[2, 18, 26, 8, 2, 64, 64],[64, 2, 32, 2, 2, 16, 64],96⟩
theorem kid01_part529_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part529) = true := by rfl

def kid01_part530 : Audit := .split 16 (5,false) (byMove [
.cycle 15 6 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 12 5 false (0),
.cycle 16 2 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 2 true (-2),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 17 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (-1)
])
theorem kid01_part530_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part530) = true := by rfl

def kid01_part531 : Audit := .split 16 (0,true) (byMove [
.cycle 0 35 false (4),
.cycle 12 5 false (0),
.last 18 (5,false),
.cycle 12 7 false (0),
.cycle 12 7 false (0),
.cycle 10 9 false (2),
.cycle 0 20 true (-1),
.cycle 17 25 true (0),
.last 18 (5,false),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[10, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.last 42 (5,false),
.cycle 11 8 false (1),
.cycle 12 5 false (0),
.last 18 (5,false),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[8, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[16, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 15 2 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.cycle 10 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[2, 2, 32, 2, 2, 2, 64],96⟩,
.last 50 (5,false)
])
theorem kid01_part531_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part531) = true := by rfl

def kid01_part532 : Audit := .cycle 11 5 false (1)
theorem kid01_part532_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part532) = true := by rfl

def kid01_part533 : Audit := .cycle 14 2 true (-1)
theorem kid01_part533_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part533) = true := by rfl

def kid01_part534 : Audit := .far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩
theorem kid01_part534_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part534) = true := by rfl

def kid01_part535 : Audit := .far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[64, 2, 32, 2, 2, 2, 64],96⟩
theorem kid01_part535_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part535) = true := by rfl

def kid01_part536 : Audit := .split 20 (5,false) (byMove [
.last 21 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 18 4 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 19 2 true (3),
.cycle 0 21 true (-1),
.cycle 16 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 20 1 true (4),
.last 21 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 17 5 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 18 3 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 64, 128, 256, 8, 1024, 64, 64, 4096],[4096, 2048, 4096, 1024, 1024, 2048, 4096, 2048, 2048, 1024, 1024, 2048, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 2, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 20 1 true (4)
])
theorem kid01_part536_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part536) = true := by rfl

def kid01_part512 : Audit := .split 15 (5,true) (byMove [(kid01_part513),(kid01_part514),(kid01_part515),(kid01_part516),(kid01_part517),(kid01_part518),(kid01_part519),(kid01_part520),(kid01_part521),(kid01_part522),(kid01_part523),(kid01_part524),(kid01_part525),(kid01_part526),(kid01_part527),(kid01_part528),(kid01_part529),(kid01_part530),(kid01_part531),(kid01_part532),(kid01_part533),(kid01_part534),(kid01_part535),(kid01_part536)])

theorem kid01_part512_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part512) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part513),(kid01_part514),(kid01_part515),(kid01_part516),(kid01_part517),(kid01_part518),(kid01_part519),(kid01_part520),(kid01_part521),(kid01_part522),(kid01_part523),(kid01_part524),(kid01_part525),(kid01_part526),(kid01_part527),(kid01_part528),(kid01_part529),(kid01_part530),(kid01_part531),(kid01_part532),(kid01_part533),(kid01_part534),(kid01_part535),(kid01_part536)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid01_part516_checked

  · exact kid01_part522_checked

  · exact kid01_part528_checked

  · exact kid01_part534_checked

  · exact kid01_part517_checked

  · exact kid01_part523_checked

  · exact kid01_part529_checked

  · exact kid01_part535_checked

  · exact kid01_part518_checked

  · exact kid01_part524_checked

  · exact kid01_part530_checked

  · exact kid01_part536_checked

def kid01_part537 : Audit := .split 15 (0,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 64, 64],[30, 31, 1, 16, 16, 64, 64],96⟩,
.cycle 11 5 false (1),
.cycle 9 9 false (3),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.split 16 (5,true) (byMove [
.last 18 (5,false),
.cycle 9 16 false (3),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 2, 64, 64],[32, 2, 6, 2, 2, 4, 64],96⟩,
.cycle 8 20 false (4),
.cycle 7 20 false (4),
.last 18 (5,false),
.cycle 0 31 true (-1),
.cycle 13 44 true (-1),
.cycle 6 27 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 10, 2, 2, 10, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.last 17 (5,false),
.last 18 (5,false),
.cycle 12 5 false (1),
.cycle 9 51 false (3),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.last 18 (5,false),
.cycle 9 9 false (3),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.cycle 11 7 false (1),
.last 17 (5,false)
]),
.cycle 0 18 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 14, 64, 64],[2, 3, 1, 16, 16, 64, 64],96⟩,
.cycle 6 18 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 26, 64, 64],[8, 25, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[16, 17, 1, 16, 16, 64, 64],96⟩,
.split 16 (5,true) (byMove [
.far false 7 ⟨0,[0, 6, 4, 4, 3, 5, 4, 4, 4, 4, 0, 6, 1, 2],[137438953472, 274877906944, 8, 1116691562496, 512, 4398046511104, 33554432, 67108864, 134217728, 17179869184, 2097152, 4398046511104, 2147483648, 4294967296, 2097152, 17179869184, 4398046511104, 4398046511104, 33554432, 67108864, 134217728, 1099511627776, 8, 4398046511104, 33554432, 67108864, 134217728, 1116959997952, 4535655342088, 4398046511104, 137438953472, 274877906944, 8, 1099511627776, 512, 4398046511104, 8192, 16384, 512, 65536, 2147483648, 4398046511104, 4398046511104],[32, 4096, 68719476736, 1099511627776, 1099511627776, 16384, 536870912, 1073741824, 16777216, 268435456, 268435456, 4294967296, 8388608, 274877906944, 1073741824, 17179869184, 17179869184, 4398046511104, 536870912, 68719476736, 16777216, 268435456, 268435456, 274877906944, 536870912, 4472755472416, 16777216, 268435456, 268435456, 4398113619968, 32, 4096, 68719476736, 1099511627776, 1099511627776, 4398046511104, 2048, 8388608, 4096, 65536, 65536, 4398046511104, 4398046511104],7255271352812⟩,
.last 151 (5,false),
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[32, 266240, 64, 1024, 1024, 4194304, 32, 32, 4096, 65536, 65536, 8192, 32, 4194304, 262144, 4194304, 4194304, 524288, 32, 4194304, 262144, 4194304, 4194304, 524288, 16777216],25365024⟩,
.cycle 10 11 false (2),
.last 23 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.cycle 39 15 true (4),
.last 38 (5,false),
.last 77 (5,false),
.cycle 42 16 true (4),
.last 18 (5,false),
.cycle 9 9 false (3),
.last 20 (5,false),
.last 26 (5,false),
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[32, 266240, 64, 1024, 1024, 4194304, 32, 32, 4096, 65536, 65536, 65536, 32, 4194304, 262144, 4194304, 4194304, 4194304, 32, 4194304, 262144, 4194304, 4194304, 4194304, 16777216],25365024⟩,
.last 23 (5,false),
.last 17 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.cycle 37 14 true (5),
.last 24 (5,false),
.last 24 (5,false),
.last 18 (5,false)
]),
.cycle 11 8 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[16, 17, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[17, 17, 1, 16, 16, 64, 64],96⟩,
.split 16 (5,true) (byMove [
.last 18 (5,false),
.cycle 9 12 false (3),
.cycle 10 9 false (2),
.cycle 9 14 false (3),
.cycle 9 14 false (3),
.last 18 (5,false),
.last 18 (5,false),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.cycle 14 28 true (0),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 10, 2, 2, 10, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.last 20 (5,false),
.last 18 (5,false),
.cycle 12 5 false (1),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 2, 64, 64],[32, 2, 6, 2, 2, 4, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 10, 2, 2, 8, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 18, 2, 2, 16, 64],96⟩,
.last 18 (5,false),
.cycle 15 2 true (0),
.cycle 10 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 64, 64],[32, 2, 2, 2, 2, 2, 64],96⟩,
.last 20 (5,false)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[1, 1, 1, 16, 16, 64, 64],96⟩,
.cycle 9 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[4, 5, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 26, 64, 64],[8, 25, 1, 16, 16, 64, 64],96⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 64, 64],[16, 17, 1, 16, 16, 64, 64],96⟩,
.split 16 (5,true) (byMove [
.last 18 (5,false),
.cycle 10 7 false (2),
.cycle 9 11 false (3),
.cycle 10 9 false (2),
.cycle 10 9 false (2),
.last 20 (5,false),
.last 18 (5,false),
.cycle 47 15 true (4),
.last 38 (5,false),
.last 137 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 4, 4, 2, 0, 4, 4],[128, 256, 8, 4195344, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 2, 1073741824, 33554432, 67108864, 134217728, 1040, 32776, 1073741824, 2, 4, 32768, 16, 1073741824, 1073741824, 33554432, 67108864, 134217728, 272630800, 1242071176, 1073741824, 1073741824],[2048, 263168, 64, 1024, 1024, 16, 8388608, 4194336, 262144, 4194304, 4194304, 65536, 536870912, 65, 16777216, 268435456, 268435456, 268435456, 32, 16, 1, 16, 16, 65536, 536870912, 830539776, 16777216, 268435456, 268435456, 268435456, 1073741824],2144041580⟩,
.last 18 (5,false),
.cycle 15 2 true (1),
.cycle 10 7 false (2),
.last 22 (5,false),
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[2048, 266240, 64, 1024, 1024, 4194304, 131072, 8388608, 4096, 65536, 65536, 65536, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 16777216],25365024⟩,
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[2048, 266240, 64, 1024, 1024, 20972544, 131072, 8388608, 4096, 65536, 65536, 65536, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 16777216],25365024⟩,
.last 20 (5,false),
.last 18 (5,false),
.cycle 9 9 false (3),
.far false 5 ⟨0,[0, 1, 2, 3, 4, 4, 2, 0, 4, 4],[128, 256, 8, 4195344, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 2, 1073741824, 33554432, 67108864, 134217728, 1040, 32776, 1073741824, 2, 4, 32768, 16, 1073741824, 1073741824, 33554432, 67108864, 134217728, 272630800, 1242071176, 1073741824, 1073741824],[2048, 262144, 64, 1024, 1024, 256, 8388608, 32, 262144, 4194304, 4194304, 1048576, 536870912, 65, 16777216, 268435456, 268435456, 67108864, 32, 256, 1, 16, 16, 4, 536870912, 630196293, 16777216, 268435456, 268435456, 67108864, 1073741824],2144041580⟩,
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 4194304, 16777216, 16777216],[2048, 266240, 64, 1024, 1024, 512, 131072, 8388608, 4096, 65536, 65536, 32768, 8388608, 2097152, 262144, 4194304, 4194304, 2097152, 8388608, 4194304, 262144, 4194304, 4194304, 2097152, 16777216],25365024⟩,
.far false 4 ⟨0,[0, 1, 0, 2, 0, 3, 0, 3],[128, 256, 8, 4194304, 8, 16777216, 8192, 16384, 8, 65536, 524288, 16777216, 524288, 1048576, 8, 4194304, 16777216, 16777216, 524288, 1048576, 8, 4194304, 0, 16777216, 16777216],[2048, 266240, 64, 1024, 1024, 1024, 131072, 8388608, 4096, 65536, 65536, 65536, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 8388608, 4194304, 262144, 4194304, 4194304, 4194304, 16777216],25365024⟩,
.last 18 (5,false)
])
])
theorem kid01_part537_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part537) = true := by rfl

def kid01_part538 : Audit := .cycle 10 5 false (2)
theorem kid01_part538_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part538) = true := by rfl

def kid01_part539 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 4, 4, 16, 16, 64, 64],96⟩
theorem kid01_part539_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part539) = true := by rfl

def kid01_part540 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 64, 64],[64, 24, 8, 16, 16, 64, 64],96⟩
theorem kid01_part540_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part540) = true := by rfl

def kid01_part541 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 64, 64],[64, 16, 16, 16, 16, 64, 64],96⟩
theorem kid01_part541_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part541) = true := by rfl

def kid01_part543 : Audit := .split 16 (0,true) (byMove [
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[16384, 131072, 2048, 1024, 1024, 16384, 8, 65536, 131072, 65536, 65536, 8, 65536, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 0, 4, 2, 3],[128, 256, 8, 272629760, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 272695296, 1073774600, 1073741824, 33554432, 67108864, 8, 268435456, 0, 1073741824, 524288, 1048576, 32768, 4194304, 0, 1073741824, 1073741824],[1073741824, 8388608, 2048, 1024, 1024, 1048576, 8, 272629760, 8388608, 4194304, 4194304, 1073741824, 1073774600, 1958952960, 131072, 65536, 65536, 1413562368, 1073741824, 272629760, 536870912, 268435456, 268435456, 272629760, 0, 272629760, 8388608, 4194304, 4194304, 1073741824, 1073741824],1703673202⟩,
.cycle 0 31 true (-1),
.last 38 (5,false),
.cycle 6 27 true (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[8, 131072, 2048, 1024, 1024, 16384, 8, 65536, 131072, 65536, 65536, 65536, 8, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[524288, 128, 2097152, 512, 2, 1073741824, 524288, 1074274432, 1074274432, 2097152, 8192, 1073741824, 1074274432, 1074274432, 1074307712, 32768, 8192, 1073741824, 128, 524288, 524288, 512, 33554432, 1073741824, 128, 128, 2097152, 512, 2, 1073741824, 1073741824],[128, 128, 1073741824, 128, 128, 1, 1074274432, 524288, 128, 524288, 524288, 4096, 1074274432, 8192, 1074274432, 8192, 8192, 4096, 524288, 128, 1074274432, 128, 128, 16777216, 128, 128, 1073741824, 128, 128, 1, 1073741824],1942453682⟩,
.last 17 (5,false),
.cycle 11 8 false (1),
.cycle 12 5 false (1),
.last 26 (5,false),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.last 21 (5,false),
.cycle 9 9 false (3),
.last 50 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1212253184, 1073741824, 128, 256, 134217728, 1024, 4194304, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[256, 8388608, 2048, 1024, 1024, 1048576, 1048576, 138412032, 8388608, 4194304, 4194304, 32768, 16384, 147049728, 131072, 65536, 65536, 49408, 256, 1024, 2048, 1024, 1024, 134217728, 256, 8388608, 2048, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[512, 131072, 2048, 1024, 1024, 16384, 32768, 65536, 131072, 65536, 65536, 65536, 32768, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.cycle 11 7 false (1),
.last 17 (5,false)
])
theorem kid01_part543_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part543) = true := by rfl

def kid01_part544 : Audit := .cycle 11 5 false (1)
theorem kid01_part544_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part544) = true := by rfl

def kid01_part545 : Audit := .split 17 (5,false) (byMove [
.last 18 (0,true),
.cycle 11 7 false (1),
.cycle 16 2 true (0),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.cycle 23 1 false (-1),
.last 18 (0,true),
.cycle 22 20 true (2),
.cycle 6 22 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.last 18 (0,true),
.cycle 11 7 false (1),
.cycle 14 4 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 23 1 false (-1),
.last 18 (0,true),
.cycle 9 9 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 52, 32, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 8, 64],[64, 56, 32, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 23 1 true (3)
])
theorem kid01_part545_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part545) = true := by rfl

def kid01_part546 : Audit := .cycle 11 7 false (1)
theorem kid01_part546_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part546) = true := by rfl

def kid01_part547 : Audit := .cycle 11 7 false (1)
theorem kid01_part547_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part547) = true := by rfl

def kid01_part548 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 false (4),
.cycle 10 17 false (2),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 10 18 false (2),
.cycle 18 1 false (-2),
.cycle 0 35 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 2, 64],[64, 62, 32, 16, 16, 30, 64],64⟩,
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 10 18 false (2),
.cycle 26 1 true (2),
.cycle 11 9 false (1),
.cycle 11 11 false (1),
.cycle 14 12 false (1),
.cycle 19 1 false (-3),
.cycle 6 22 false (4),
.cycle 18 1 false (-2),
.cycle 25 39 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 30, 2, 64],[64, 62, 32, 16, 16, 30, 64],64⟩,
.cycle 10 16 false (2),
.cycle 11 12 false (1),
.cycle 10 15 false (2),
.cycle 40 1 true (-4)
])
theorem kid01_part548_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part548) = true := by rfl

def kid01_part549 : Audit := .split 16 (0,true) (byMove [
.last 20 (5,false),
.last 24 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 128, 262144, 262144],[65536, 131072, 2048, 1024, 1024, 1, 262144, 1, 131072, 65536, 65536, 1, 262144, 65536, 131072, 65536, 65536, 1, 262144],396320⟩,
.cycle 10 11 false (2),
.last 26 (5,false),
.last 17 (5,false),
.cycle 0 18 true (-1),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.cycle 0 18 true (-1),
.cycle 9 9 false (3),
.cycle 0 20 true (-1),
.cycle 0 26 true (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 128, 262144, 262144],[65536, 131072, 2048, 1024, 1024, 1, 65536, 1, 131072, 65536, 65536, 1, 65536, 65536, 131072, 65536, 65536, 1, 262144],396320⟩,
.cycle 8 22 false (4),
.last 17 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8320, 262144, 262144],[64, 131072, 2048, 1024, 1024, 1, 4096, 1, 131072, 65536, 65536, 1, 4096, 4160, 131072, 65536, 65536, 1, 262144],396320⟩,
.cycle 0 22 true (-1),
.last 18 (5,false),
.cycle 0 24 true (-1),
.cycle 0 24 true (-1),
.cycle 0 18 true (-1)
])
theorem kid01_part549_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part549) = true := by rfl

def kid01_part550 : Audit := .split 37 (5,false) (byMove [
.last 38 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 12, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 36 2 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 12, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 28, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 19 19 true (3),
.cycle 0 38 true (-1),
.cycle 20 18 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 8, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 16, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 37 1 true (7),
.last 38 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 46, 34, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 18 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 16, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 62, 50, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 33 5 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 13, 1, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 14, 2, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 8, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 16, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 37 1 true (7)
])
theorem kid01_part550_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part550) = true := by rfl

def kid01_part551 : Audit := .cycle 6 18 true (-1)
theorem kid01_part551_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part551) = true := by rfl

def kid01_part552 : Audit := .far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1212253184, 1073741824, 128, 256, 134217728, 1024, 4194304, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1073741824, 8388608, 2048, 1024, 1024, 8, 1073741824, 138412032, 8388608, 4194304, 4194304, 32768, 1073741824, 231424, 131072, 65536, 65536, 32768, 1073741824, 1024, 2048, 1024, 1024, 134217728, 1073741824, 8388608, 2048, 1024, 1024, 8, 1073741824],1990983038⟩
theorem kid01_part552_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part552) = true := by rfl

def kid01_part553 : Audit := .split 72 (5,false) (byMove [
.last 73 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 71 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 58 20 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 72 1 true (6),
.last 73 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 66 7 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 2, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 72 1 true (6)
])
theorem kid01_part553_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part553) = true := by rfl

def kid01_part554 : Audit := .split 18 (5,false) (byMove [
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 56 38 true (2),
.cycle 26 1 false (0),
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 16 17 true (2),
.cycle 18 1 true (4),
.cycle 9 18 true (-1),
.cycle 16 10 true (2),
.cycle 17 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 6 22 true (-1),
.cycle 40 1 false (6),
.cycle 15 21 true (1),
.cycle 1 18 true (-1),
.cycle 16 15 true (2),
.cycle 17 10 true (3),
.cycle 16 14 true (2),
.cycle 18 1 true (4)
])
theorem kid01_part554_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part554) = true := by rfl

def kid01_part555 : Audit := .split 16 (0,true) (byMove [
.cycle 0 35 false (4),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.cycle 11 8 false (1),
.cycle 0 20 true (-1),
.last 30 (5,false),
.last 24 (5,false),
.last 42 (5,false),
.last 42 (5,false),
.cycle 10 9 false (2),
.cycle 11 8 false (1),
.cycle 12 5 false (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[1024, 131072, 2048, 1024, 1024, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[65536, 131072, 2048, 1024, 1024, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[263168, 131072, 2048, 1024, 1024, 65536, 65536, 65536, 131072, 65536, 65536, 327680, 65536, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.cycle 11 8 false (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[64, 131072, 2048, 1024, 1024, 4096, 4096, 4096, 131072, 65536, 65536, 4096, 4096, 4096, 131072, 65536, 65536, 4096, 262144],396320⟩,
.cycle 10 7 false (2),
.last 24 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[512, 131072, 2048, 1024, 1024, 65536, 32768, 65536, 131072, 65536, 65536, 65536, 32768, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[1024, 131072, 2048, 1024, 1024, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩,
.cycle 15 2 true (0)
])
theorem kid01_part555_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part555) = true := by rfl

def kid01_part556 : Audit := .cycle 11 5 false (1)
theorem kid01_part556_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part556) = true := by rfl

def kid01_part557 : Audit := .cycle 14 2 true (0)
theorem kid01_part557_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part557) = true := by rfl

def kid01_part558 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[262144, 131072, 2048, 1024, 1024, 65536, 262144, 65536, 131072, 65536, 65536, 65536, 262144, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩
theorem kid01_part558_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part558) = true := by rfl

def kid01_part559 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[262144, 131072, 2048, 1024, 1024, 263168, 262144, 65536, 131072, 65536, 65536, 65536, 262144, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩
theorem kid01_part559_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part559) = true := by rfl

def kid01_part560 : Audit := .split 18 (5,false) (byMove [
.cycle 15 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 12 7 false (1),
.cycle 16 4 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 17 2 true (-2),
.cycle 11 9 false (1),
.cycle 13 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 19 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 11 8 false (1),
.cycle 14 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 16 3 false (0)
])
theorem kid01_part560_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part560) = true := by rfl

def kid01_part561 : Audit := .split 16 (0,true) (byMove [
.cycle 0 20 false (4),
.cycle 10 7 false (2),
.last 18 (5,false),
.cycle 10 9 false (2),
.cycle 10 9 false (2),
.cycle 9 11 false (3),
.cycle 0 18 true (-1),
.last 20 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 38 (5,false),
.cycle 11 10 false (2),
.cycle 10 7 false (2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[1024, 131072, 2048, 1024, 1024, 64, 4096, 4096, 131072, 65536, 65536, 4096, 4096, 4096, 131072, 65536, 65536, 4096, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[65536, 131072, 2048, 1024, 1024, 64, 65536, 4096, 131072, 65536, 65536, 4096, 65536, 65536, 131072, 65536, 65536, 4096, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[328704, 131072, 2048, 1024, 1024, 64, 65536, 4096, 131072, 65536, 65536, 4096, 65536, 65536, 131072, 65536, 65536, 4096, 262144],396320⟩,
.cycle 15 2 true (1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[64, 131072, 2048, 1024, 1024, 64, 4096, 4096, 131072, 65536, 65536, 4096, 4096, 4096, 131072, 65536, 65536, 4096, 262144],396320⟩,
.cycle 9 9 false (3),
.last 18 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 73728, 262144, 262144],[512, 131072, 2048, 1024, 1024, 64, 32768, 4096, 131072, 65536, 65536, 4096, 32768, 98304, 131072, 65536, 65536, 4096, 262144],396320⟩,
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 8192, 262144, 262144],[1024, 131072, 2048, 1024, 1024, 64, 65536, 4096, 131072, 65536, 65536, 4096, 65536, 65536, 131072, 65536, 65536, 4096, 262144],396320⟩,
.last 46 (5,false)
])
theorem kid01_part561_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part561) = true := by rfl

def kid01_part562 : Audit := .cycle 9 7 false (3)
theorem kid01_part562_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part562) = true := by rfl

def kid01_part563 : Audit := .split 40 (5,false) (byMove [
.last 41 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 39 2 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 37 16 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 40 1 true (6),
.last 41 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 44, 36, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 20, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 38 3 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 2, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.cycle 40 1 true (6)
])
theorem kid01_part563_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part563) = true := by rfl

def kid01_part564 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 65536, 262144, 262144],[262144, 131072, 2048, 1024, 1024, 512, 262144, 32768, 131072, 65536, 65536, 32768, 262144, 65536, 131072, 65536, 65536, 32768, 262144],396320⟩
theorem kid01_part564_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part564) = true := by rfl

def kid01_part565 : Audit := .far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[262144, 131072, 2048, 1024, 1024, 1024, 262144, 65536, 131072, 65536, 65536, 65536, 262144, 65536, 131072, 65536, 65536, 65536, 262144],396320⟩
theorem kid01_part565_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part565) = true := by rfl

def kid01_part566 : Audit := .split 18 (5,false) (byMove [
.last 19 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 18 2 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 17 2 true (3),
.cycle 0 19 true (-1),
.cycle 16 16 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 18 1 true (4),
.last 19 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 17 3 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 16 3 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 2, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 18 1 true (4)
])
theorem kid01_part566_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part566) = true := by rfl

def kid01_part542 : Audit := .split 15 (5,true) (byMove [(kid01_part543),(kid01_part544),(kid01_part545),(kid01_part546),(kid01_part547),(kid01_part548),(kid01_part549),(kid01_part550),(kid01_part551),(kid01_part552),(kid01_part553),(kid01_part554),(kid01_part555),(kid01_part556),(kid01_part557),(kid01_part558),(kid01_part559),(kid01_part560),(kid01_part561),(kid01_part562),(kid01_part563),(kid01_part564),(kid01_part565),(kid01_part566)])

theorem kid01_part542_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part542) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part543),(kid01_part544),(kid01_part545),(kid01_part546),(kid01_part547),(kid01_part548),(kid01_part549),(kid01_part550),(kid01_part551),(kid01_part552),(kid01_part553),(kid01_part554),(kid01_part555),(kid01_part556),(kid01_part557),(kid01_part558),(kid01_part559),(kid01_part560),(kid01_part561),(kid01_part562),(kid01_part563),(kid01_part564),(kid01_part565),(kid01_part566)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid01_part546_checked

  · exact kid01_part552_checked

  · exact kid01_part558_checked

  · exact kid01_part564_checked

  · exact kid01_part547_checked

  · exact kid01_part553_checked

  · exact kid01_part559_checked

  · exact kid01_part565_checked

  · exact kid01_part548_checked

  · exact kid01_part554_checked

  · exact kid01_part560_checked

  · exact kid01_part566_checked

def kid01_part470 : Audit := .split 14 (2,true) (byMove [(kid01_part471),(kid01_part472),(kid01_part473),(kid01_part474),(kid01_part475),(kid01_part476),(kid01_part477),(kid01_part478),(kid01_part479),(kid01_part480),(kid01_part481),(kid01_part482),(kid01_part507),(kid01_part508),(kid01_part509),(kid01_part510),(kid01_part511),(kid01_part512),(kid01_part537),(kid01_part538),(kid01_part539),(kid01_part540),(kid01_part541),(kid01_part542)])

theorem kid01_part470_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (kid01_part470) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid01_part471),(kid01_part472),(kid01_part473),(kid01_part474),(kid01_part475),(kid01_part476),(kid01_part477),(kid01_part478),(kid01_part479),(kid01_part480),(kid01_part481),(kid01_part482),(kid01_part507),(kid01_part508),(kid01_part509),(kid01_part510),(kid01_part511),(kid01_part512),(kid01_part537),(kid01_part538),(kid01_part539),(kid01_part540),(kid01_part541),(kid01_part542)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part471_checked

  · exact kid01_part477_checked

  · exact kid01_part507_checked

  · exact kid01_part537_checked

  · exact kid01_part472_checked

  · exact kid01_part478_checked

  · exact kid01_part508_checked

  · exact kid01_part538_checked

  · exact kid01_part473_checked

  · exact kid01_part479_checked

  · exact kid01_part509_checked

  · exact kid01_part539_checked

  · exact kid01_part474_checked

  · exact kid01_part480_checked

  · exact kid01_part510_checked

  · exact kid01_part540_checked

  · exact kid01_part475_checked

  · exact kid01_part481_checked

  · exact kid01_part511_checked

  · exact kid01_part541_checked

  · exact kid01_part476_checked

  · exact kid01_part482_checked

  · exact kid01_part512_checked

  · exact kid01_part542_checked

def kid01_part568 : Audit := .split 11 (0,true) (byMove [
.cycle 0 28 false (4),
.cycle 12 4 true (-1),
.cycle 29 1 false (-1),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.split 12 (5,true) (byMove [
.last 28 (5,false),
.last 24 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.cycle 10 8 false (2),
.last 16 (5,false),
.cycle 13 4 true (-1),
.cycle 13 1 false (-1),
.cycle 15 4 true (-1),
.last 13 (5,false),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.cycle 10 11 false (2),
.cycle 13 4 true (-1),
.last 13 (5,false)
]),
.cycle 0 19 true (0),
.cycle 1 14 true (1),
.cycle 12 4 true (2),
.cycle 6 10 true (0),
.cycle 14 4 true (2),
.split 12 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.cycle 10 11 false (2),
.cycle 13 4 true (-1),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 13 (5,true),
.cycle 10 13 false (2),
.cycle 10 4 true (1),
.cycle 24 4 true (2),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 1 19 true (1),
.cycle 2 14 true (1),
.cycle 14 11 true (1),
.cycle 22 4 true (2),
.last 13 (5,true)
]),
.cycle 10 8 false (2),
.cycle 10 11 false (2),
.cycle 10 5 false (2),
.cycle 10 9 false (2),
.cycle 10 9 false (2),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.cycle 14 4 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 14 (5,false),
.cycle 13 4 true (0),
.cycle 16 4 true (2),
.cycle 13 4 true (0),
.cycle 14 4 true (0),
.last 14 (5,false),
.cycle 10 8 false (2),
.last 16 (5,false),
.cycle 10 11 false (2),
.cycle 13 1 false (-1),
.last 33 (5,false),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 10 7 false (2),
.last 15 (5,false),
.cycle 10 9 false (2),
.cycle 10 9 false (2),
.last 14 (5,false)
]),
.cycle 9 4 true (1),
.cycle 1 14 true (1),
.cycle 12 4 true (2),
.cycle 4 8 true (1),
.cycle 10 7 false (2),
.split 12 (5,false) (byMove [
.cycle 11 2 true (1),
.cycle 10 7 false (2),
.cycle 0 38 false (4),
.cycle 10 9 false (2),
.cycle 10 9 false (2),
.last 13 (5,true),
.cycle 0 15 true (0),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 13 (5,true),
.last 14 (5,true),
.cycle 10 7 false (2),
.cycle 10 9 false (2),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 0 15 true (0),
.cycle 9 4 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 13 (5,true)
])
])
theorem kid01_part568_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part568) = true := by rfl

def kid01_part569 : Audit := .cycle 14 4 true (0)
theorem kid01_part569_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part569) = true := by rfl

def kid01_part570 : Audit := .cycle 14 1 false (0)
theorem kid01_part570_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part570) = true := by rfl

def kid01_part571 : Audit := .cycle 15 1 false (-1)
theorem kid01_part571_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part571) = true := by rfl

def kid01_part572 : Audit := .cycle 6 16 false (4)
theorem kid01_part572_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part572) = true := by rfl

def kid01_part574 : Audit := .split 12 (0,true) (byMove [
.cycle 0 28 false (4),
.cycle 26 4 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 27 4 true (-1),
.last 13 (5,false),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.last 16 (5,false),
.cycle 0 16 false (4),
.cycle 13 4 true (-1),
.cycle 13 1 false (-1),
.cycle 15 4 true (-1),
.last 13 (5,false),
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.last 19 (5,false),
.cycle 13 4 true (-1),
.last 13 (5,false)
])
theorem kid01_part574_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part574) = true := by rfl

def kid01_part575 : Audit := .cycle 12 4 true (-1)
theorem kid01_part575_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part575) = true := by rfl

def kid01_part576 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 26 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 27 1 false (-3),
.cycle 13 1 false (-1),
.cycle 16 4 true (2),
.cycle 6 14 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 27 1 false (-1),
.cycle 19 1 false (3),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.cycle 14 4 true (-2),
.cycle 14 1 false (-2),
.cycle 16 4 true (-2),
.cycle 13 1 false (-1),
.cycle 16 4 true (2),
.cycle 29 1 false (-1),
.cycle 25 1 false (-1),
.cycle 30 1 false (-2),
.cycle 14 4 true (-2),
.cycle 23 1 false (-1)
])
theorem kid01_part576_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part576) = true := by rfl

def kid01_part577 : Audit := .cycle 12 4 true (-1)
theorem kid01_part577_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part577) = true := by rfl

def kid01_part578 : Audit := .cycle 13 4 true (-1)
theorem kid01_part578_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part578) = true := by rfl

def kid01_part579 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 12 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 16 4 true (2),
.cycle 6 14 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 28 false (4),
.cycle 18 1 true (2),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 14 4 true (-2),
.cycle 14 1 false (-2),
.cycle 16 4 true (-2),
.cycle 13 1 false (-1),
.cycle 16 4 true (2),
.cycle 1 28 false (4),
.cycle 6 24 false (4),
.cycle 12 16 false (1),
.cycle 14 4 true (-2),
.cycle 22 1 true (-2)
])
theorem kid01_part579_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part579) = true := by rfl

def kid01_part580 : Audit := .split 15 (5,false) (byMove [
.last 16 (0,true),
.cycle 16 4 true (-1),
.cycle 19 1 false (-1),
.cycle 16 4 true (-1),
.cycle 17 4 true (-1),
.cycle 0 21 true (0),
.cycle 12 4 true (1),
.cycle 0 19 true (0),
.cycle 16 4 true (2),
.cycle 6 14 true (0),
.cycle 18 4 true (2),
.cycle 0 18 true (0),
.last 16 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 30, 64],[64, 30, 30, 16, 16, 1, 64],64⟩,
.cycle 18 4 true (-2),
.cycle 22 1 false (-2),
.cycle 24 4 true (-2),
.last 17 (0,true),
.cycle 9 8 true (1),
.cycle 0 19 true (0),
.cycle 16 4 true (2),
.cycle 4 12 true (1),
.cycle 20 4 true (-2),
.cycle 0 18 true (0)
])
theorem kid01_part580_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part580) = true := by rfl

def kid01_part581 : Audit := .cycle 1 14 true (1)
theorem kid01_part581_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part581) = true := by rfl

def kid01_part582 : Audit := .cycle 12 4 true (2)
theorem kid01_part582_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part582) = true := by rfl

def kid01_part583 : Audit := .cycle 6 10 true (0)
theorem kid01_part583_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part583) = true := by rfl

def kid01_part584 : Audit := .cycle 14 4 true (2)
theorem kid01_part584_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part584) = true := by rfl

def kid01_part585 : Audit := .split 12 (5,false) (byMove [
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.cycle 20 1 false (-2),
.cycle 13 4 true (-1),
.cycle 15 1 false (1),
.last 13 (0,true),
.cycle 13 4 true (2),
.cycle 6 17 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 14 1 true (4),
.cycle 17 4 false (1),
.cycle 10 4 true (1),
.cycle 22 4 true (-2),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.cycle 18 1 false (4),
.last 13 (0,true),
.cycle 1 19 true (1),
.cycle 2 14 true (1),
.cycle 4 14 true (1),
.cycle 22 4 true (-2),
.cycle 14 1 true (4)
])
theorem kid01_part585_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part585) = true := by rfl

def kid01_part586 : Audit := .split 12 (0,true) (byMove [
.cycle 10 5 false (2),
.cycle 14 4 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 17 (5,false),
.cycle 13 4 true (0),
.last 14 (5,false),
.cycle 13 4 true (0),
.cycle 14 4 true (0),
.last 17 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.last 19 (5,false),
.cycle 13 1 false (-1),
.last 21 (5,false),
.last 13 (5,false),
.cycle 9 6 true (0),
.last 15 (5,false),
.last 18 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.cycle 11 2 true (0)
])
theorem kid01_part586_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part586) = true := by rfl

def kid01_part587 : Audit := .split 19 (5,false) (byMove [
.cycle 22 4 true (0),
.cycle 6 20 false (4),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 30 3 false (-2),
.cycle 19 1 false (-1),
.cycle 17 4 true (-1),
.cycle 20 3 false (1),
.cycle 20 4 true (0),
.cycle 20 1 false (0),
.cycle 22 4 true (0),
.cycle 21 3 false (1),
.cycle 17 4 false (1),
.cycle 20 3 false (-1),
.cycle 20 4 true (-2),
.cycle 20 1 false (-2),
.cycle 22 4 true (-2),
.cycle 19 1 false (-1),
.cycle 22 3 false (0),
.cycle 10 11 false (2),
.cycle 20 4 true (0),
.cycle 26 3 false (0),
.cycle 20 4 true (-2),
.cycle 17 5 false (1)
])
theorem kid01_part587_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part587) = true := by rfl

def kid01_part588 : Audit := .split 13 (5,false) (byMove [
.cycle 16 4 true (0),
.cycle 6 14 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 26 4 true (-4),
.cycle 13 1 false (-1),
.cycle 12 4 true (-1),
.cycle 17 4 true (-1),
.cycle 14 4 true (0),
.cycle 14 1 false (0),
.cycle 16 4 true (0),
.cycle 16 4 true (0),
.cycle 12 4 false (0),
.cycle 17 4 true (-3),
.cycle 14 4 true (-2),
.cycle 14 1 false (-2),
.cycle 16 4 true (-2),
.cycle 13 1 false (-1),
.cycle 18 4 true (-2),
.cycle 10 5 false (2),
.cycle 14 4 true (0),
.cycle 22 4 true (-2),
.cycle 14 4 true (-2),
.cycle 18 4 true (-2)
])
theorem kid01_part588_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part588) = true := by rfl

def kid01_part589 : Audit := .split 17 (5,false) (byMove [
.cycle 20 4 true (0),
.cycle 6 18 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 30 1 false (-4),
.cycle 17 1 false (-1),
.cycle 15 4 true (-1),
.cycle 21 1 false (-1),
.cycle 18 4 true (0),
.cycle 18 1 false (0),
.cycle 20 4 true (0),
.cycle 20 1 false (0),
.cycle 15 4 false (1),
.cycle 21 1 false (-3),
.cycle 18 4 true (-2),
.cycle 18 1 false (-2),
.cycle 20 4 true (-2),
.cycle 17 1 false (-1),
.cycle 22 1 false (-2),
.cycle 10 9 false (2),
.cycle 18 4 true (0),
.cycle 26 1 false (-2),
.cycle 18 4 true (-2),
.cycle 26 1 false (-2)
])
theorem kid01_part589_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part589) = true := by rfl

def kid01_part590 : Audit := .split 17 (5,false) (byMove [
.cycle 20 4 true (0),
.cycle 6 18 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 32 4 true (-4),
.cycle 17 1 false (-1),
.cycle 15 4 true (-1),
.cycle 23 4 true (-1),
.cycle 18 4 true (0),
.cycle 18 1 false (0),
.cycle 20 4 true (0),
.cycle 22 4 true (0),
.cycle 15 4 false (1),
.cycle 23 4 true (-3),
.cycle 18 4 true (-2),
.cycle 18 1 false (-2),
.cycle 20 4 true (-2),
.cycle 17 1 false (-1),
.cycle 24 4 true (-2),
.cycle 10 9 false (2),
.cycle 18 4 true (0),
.cycle 28 4 true (-2),
.cycle 18 4 true (-2),
.cycle 28 4 true (-2)
])
theorem kid01_part590_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part590) = true := by rfl

def kid01_part591 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 22 4 true (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 24, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 26 4 true (-1),
.cycle 16 4 true (0),
.cycle 20 1 false (0),
.cycle 22 4 true (0),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 30 4 true (-4),
.cycle 14 1 false (-2),
.cycle 50 4 true (-8),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 10 8 false (2),
.cycle 12 3 false (0),
.cycle 15 14 false (2),
.cycle 26 4 true (-4),
.cycle 11 3 false (1)
])
theorem kid01_part591_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part591) = true := by rfl

def kid01_part592 : Audit := .cycle 9 4 true (1)
theorem kid01_part592_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part592) = true := by rfl

def kid01_part593 : Audit := .cycle 1 14 true (1)
theorem kid01_part593_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part593) = true := by rfl

def kid01_part594 : Audit := .cycle 12 4 true (2)
theorem kid01_part594_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part594) = true := by rfl

def kid01_part595 : Audit := .cycle 4 8 true (1)
theorem kid01_part595_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part595) = true := by rfl

def kid01_part596 : Audit := .split 15 (5,false) (byMove [
.cycle 18 4 true (0),
.cycle 6 16 false (4),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 28 4 true (-4),
.cycle 15 1 false (-1),
.cycle 13 4 true (-1),
.cycle 19 4 true (-1),
.cycle 16 4 true (0),
.cycle 16 1 false (0),
.cycle 18 4 true (0),
.cycle 18 4 true (0),
.cycle 13 4 false (1),
.cycle 19 4 true (-3),
.cycle 16 4 true (-2),
.cycle 16 1 false (-2),
.cycle 18 4 true (-2),
.cycle 15 1 false (-1),
.cycle 20 4 true (-2),
.cycle 10 7 false (2),
.cycle 16 4 true (0),
.cycle 24 4 true (-2),
.cycle 16 4 true (-2),
.cycle 22 4 true (-2)
])
theorem kid01_part596_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part596) = true := by rfl

def kid01_part597 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 6 16 false (4),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 32 4 true (-4),
.cycle 11 2 true (1),
.last 13 (0,true),
.cycle 13 4 true (2),
.cycle 6 15 true (1),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 14 1 true (4),
.last 13 (0,true),
.cycle 13 12 false (1),
.cycle 18 4 true (-2),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 14 3 true (2),
.last 13 (0,true),
.cycle 9 4 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 14 1 true (4)
])
theorem kid01_part597_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part597) = true := by rfl

def kid01_part573 : Audit := .split 11 (5,true) (byMove [(kid01_part574),(kid01_part575),(kid01_part576),(kid01_part577),(kid01_part578),(kid01_part579),(kid01_part580),(kid01_part581),(kid01_part582),(kid01_part583),(kid01_part584),(kid01_part585),(kid01_part586),(kid01_part587),(kid01_part588),(kid01_part589),(kid01_part590),(kid01_part591),(kid01_part592),(kid01_part593),(kid01_part594),(kid01_part595),(kid01_part596),(kid01_part597)])

theorem kid01_part573_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part573) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part574),(kid01_part575),(kid01_part576),(kid01_part577),(kid01_part578),(kid01_part579),(kid01_part580),(kid01_part581),(kid01_part582),(kid01_part583),(kid01_part584),(kid01_part585),(kid01_part586),(kid01_part587),(kid01_part588),(kid01_part589),(kid01_part590),(kid01_part591),(kid01_part592),(kid01_part593),(kid01_part594),(kid01_part595),(kid01_part596),(kid01_part597)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part574_checked

  · exact kid01_part580_checked

  · exact kid01_part586_checked

  · exact kid01_part592_checked

  · exact kid01_part575_checked

  · exact kid01_part581_checked

  · exact kid01_part587_checked

  · exact kid01_part593_checked

  · exact kid01_part576_checked

  · exact kid01_part582_checked

  · exact kid01_part588_checked

  · exact kid01_part594_checked

  · exact kid01_part577_checked

  · exact kid01_part583_checked

  · exact kid01_part589_checked

  · exact kid01_part595_checked

  · exact kid01_part578_checked

  · exact kid01_part584_checked

  · exact kid01_part590_checked

  · exact kid01_part596_checked

  · exact kid01_part579_checked

  · exact kid01_part585_checked

  · exact kid01_part591_checked

  · exact kid01_part597_checked

def kid01_part598 : Audit := .split 11 (0,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 28 4 true (-2),
.split 12 (5,false) (byMove [
.last 14 (5,true),
.cycle 29 4 true (-2),
.cycle 0 14 true (0),
.cycle 19 1 false (-1),
.cycle 33 4 true (-3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 14 (5,true),
.cycle 0 26 true (-1),
.cycle 19 4 true (-1),
.cycle 27 1 false (-1),
.cycle 29 4 true (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 0 15 true (0),
.cycle 13 4 true (3),
.cycle 6 11 true (1),
.cycle 15 4 true (3),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 4 true (3),
.cycle 12 1 true (4)
]),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 12 4 true (2),
.cycle 4 8 true (1),
.cycle 18 4 true (0),
.split 12 (5,false) (byMove [
.last 14 (5,true),
.cycle 18 4 true (0),
.cycle 6 18 true (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 11 2 true (2),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 13 (5,true),
.last 14 (5,true),
.cycle 18 16 true (-2),
.cycle 6 16 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.last 14 (5,true),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 12 4 true (2),
.split 12 (5,false) (byMove [
.cycle 11 2 true (3),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 14 (5,true),
.cycle 7 9 true (2),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part598_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part598) = true := by rfl

def kid01_part599 : Audit := .cycle 11 4 true (2)
theorem kid01_part599_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part599) = true := by rfl

def kid01_part600 : Audit := .cycle 6 14 true (1)
theorem kid01_part600_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part600) = true := by rfl

def kid01_part601 : Audit := .cycle 11 4 true (2)
theorem kid01_part601_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part601) = true := by rfl

def kid01_part602 : Audit := .cycle 12 4 true (2)
theorem kid01_part602_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part602) = true := by rfl

def kid01_part603 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 26 1 false (0),
.cycle 28 4 true (-2),
.split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 29 4 true (-2),
.cycle 29 1 false (1),
.cycle 19 1 false (-1),
.cycle 33 4 true (-3),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 13 (0,true),
.cycle 10 11 false (3),
.cycle 19 4 true (-1),
.cycle 27 1 false (-1),
.cycle 29 4 true (-1),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.cycle 12 1 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 14 true (1),
.cycle 6 11 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 12 3 true (3),
.cycle 13 4 true (3),
.cycle 6 11 true (1),
.cycle 15 4 true (3),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 4 true (3),
.cycle 12 1 true (4)
]),
.cycle 9 4 true (2),
.split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (2),
.cycle 29 4 true (-1),
.cycle 35 5 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 1 15 true (1),
.cycle 14 1 true (4),
.cycle 9 7 true (2),
.cycle 12 3 true (2),
.cycle 15 4 true (3),
.cycle 4 11 true (1),
.cycle 29 4 true (-1),
.cycle 10 17 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (2),
.cycle 15 4 true (3),
.cycle 14 1 true (4)
]),
.cycle 12 4 true (2),
.cycle 4 8 true (1),
.cycle 18 4 true (0),
.split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 18 4 true (0),
.cycle 6 14 true (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 13 4 true (2),
.cycle 6 19 true (1),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 11 2 true (2),
.last 13 (0,true),
.cycle 18 16 true (-2),
.cycle 6 16 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 2 13 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 15 3 false (1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 12 4 true (2),
.split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 13 4 true (2),
.cycle 6 15 true (1),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 13 (0,true),
.cycle 7 9 true (2),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part603_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part603) = true := by rfl

def kid01_part604 : Audit := .split 11 (0,true) (byMove [
.cycle 0 43 false (4),
.cycle 12 4 true (-1),
.cycle 12 3 false (0),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.split 12 (5,true) (byMove [
.last 36 (5,false),
.cycle 27 4 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 13 3 false (2),
.last 16 (5,false),
.cycle 17 3 false (3),
.cycle 13 1 false (1),
.last 25 (5,false),
.last 13 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 13 4 true (-1),
.cycle 13 1 false (-1),
.cycle 15 4 true (-1),
.last 13 (5,false),
.last 17 (5,false),
.cycle 10 4 true (0),
.last 23 (5,false),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.last 13 (5,false)
]),
.cycle 0 14 true (0),
.cycle 37 3 false (3),
.cycle 17 3 false (1),
.cycle 31 3 false (3),
.cycle 31 3 false (3),
.split 12 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.cycle 17 3 false (1),
.cycle 13 4 true (-1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 22 3 false (2),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 14 (5,false),
.cycle 18 3 false (1),
.cycle 10 4 true (1),
.cycle 37 3 false (3),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.last 13 (5,false),
.last 14 (5,false),
.cycle 20 3 false (2),
.cycle 2 14 true (1),
.cycle 31 3 false (3),
.cycle 31 3 false (3),
.last 14 (5,false)
]),
.cycle 13 3 false (0),
.cycle 6 10 true (-1),
.cycle 12 3 false (0),
.cycle 6 8 true (0),
.cycle 6 8 true (0),
.split 12 (5,true) (byMove [
.cycle 10 5 false (2),
.last 22 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 31 3 false (-1),
.last 13 (5,false),
.last 14 (5,false),
.last 22 (5,false),
.cycle 13 3 false (1),
.last 20 (5,false),
.last 20 (5,false),
.last 16 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.cycle 25 4 true (-3),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.last 15 (5,false),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.last 16 (5,false)
]),
.cycle 0 14 true (0),
.cycle 15 3 false (1),
.cycle 10 2 true (1),
.cycle 7 6 true (1),
.cycle 6 6 true (1),
.split 12 (5,true) (byMove [
.last 14 (5,false),
.cycle 13 3 false (1),
.cycle 16 3 false (0),
.cycle 15 3 false (1),
.cycle 15 3 false (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 9 6 true (1),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 14 (5,false),
.cycle 11 2 true (1),
.cycle 13 3 false (1),
.cycle 16 3 false (0),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.last 14 (5,false),
.cycle 9 4 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 14 (5,false)
])
])
theorem kid01_part604_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part604) = true := by rfl

def kid01_part605 : Audit := .cycle 14 12 true (-2)
theorem kid01_part605_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part605) = true := by rfl

def kid01_part606 : Audit := .cycle 6 10 true (-1)
theorem kid01_part606_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part606) = true := by rfl

def kid01_part607 : Audit := .cycle 5 6 true (1)
theorem kid01_part607_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part607) = true := by rfl

def kid01_part608 : Audit := .cycle 6 6 true (1)
theorem kid01_part608_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part608) = true := by rfl

def kid01_part610 : Audit := .split 12 (0,true) (byMove [
.last 21 (5,false),
.cycle 27 4 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 10 17 false (2),
.last 13 (5,false),
.last 16 (5,false),
.cycle 10 8 true (0),
.last 19 (5,false),
.cycle 13 1 false (1),
.last 21 (5,false),
.last 13 (5,false),
.last 16 (5,false),
.cycle 10 8 false (2),
.cycle 13 4 true (-1),
.cycle 13 1 false (-1),
.cycle 15 4 true (-1),
.last 13 (5,false),
.cycle 10 9 false (2),
.cycle 10 4 true (0),
.last 19 (5,false),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.last 13 (5,false)
])
theorem kid01_part610_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part610) = true := by rfl

def kid01_part611 : Audit := .cycle 12 4 true (-1)
theorem kid01_part611_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part611) = true := by rfl

def kid01_part612 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 15 4 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 14 4 true (-1),
.cycle 12 2 true (-1),
.cycle 14 4 true (-1),
.cycle 15 4 true (-1),
.cycle 16 1 false (0),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.cycle 30 1 false (-2),
.cycle 14 1 false (-2),
.cycle 6 19 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 3 false (0),
.cycle 17 1 false (-1),
.cycle 26 1 false (-2),
.cycle 26 1 false (-2),
.cycle 11 3 false (1)
])
theorem kid01_part612_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part612) = true := by rfl

def kid01_part613 : Audit := .cycle 12 4 true (-1)
theorem kid01_part613_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part613) = true := by rfl

def kid01_part614 : Audit := .cycle 13 4 true (-1)
theorem kid01_part614_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part614) = true := by rfl

def kid01_part615 : Audit := .split 13 (5,false) (byMove [
.cycle 0 32 false (4),
.cycle 11 28 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 12 13 false (0),
.cycle 13 1 false (-1),
.cycle 10 6 true (-1),
.cycle 15 8 true (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 48 6 true (-2),
.cycle 20 1 true (2),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.cycle 14 4 true (-2),
.cycle 14 1 false (-2),
.cycle 16 4 true (-2),
.cycle 13 1 false (-1),
.last 30 (0,true),
.cycle 1 43 false (4),
.cycle 10 37 false (4),
.cycle 6 25 false (4),
.cycle 14 4 true (-2),
.cycle 31 1 true (-3)
])
theorem kid01_part615_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part615) = true := by rfl

def kid01_part616 : Audit := .split 12 (0,true) (byMove [
.cycle 0 18 true (0),
.cycle 14 4 true (2),
.cycle 6 12 true (0),
.last 19 (5,false),
.cycle 13 4 true (-1),
.last 13 (5,false),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 0 14 true (0),
.last 21 (5,false),
.cycle 10 4 true (1),
.last 19 (5,false),
.cycle 6 10 true (0),
.cycle 13 4 true (-1),
.last 13 (5,false),
.cycle 0 14 true (0),
.last 15 (5,false),
.cycle 2 14 true (1),
.last 17 (5,false),
.last 17 (5,false),
.cycle 0 14 true (0)
])
theorem kid01_part616_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part616) = true := by rfl

def kid01_part617 : Audit := .split 19 (5,false) (byMove [
.last 20 (0,true),
.cycle 20 4 true (-1),
.cycle 23 1 false (-1),
.cycle 20 4 true (-1),
.cycle 21 4 true (-1),
.cycle 31 1 false (1),
.last 20 (0,true),
.cycle 12 8 true (1),
.cycle 18 2 true (1),
.cycle 14 6 true (1),
.cycle 15 6 true (1),
.cycle 21 4 true (2),
.last 20 (0,true),
.cycle 6 18 true (-1),
.cycle 6 40 true (-2),
.cycle 6 16 true (0),
.cycle 6 16 true (0),
.cycle 37 1 false (1),
.last 20 (0,true),
.cycle 37 3 false (3),
.cycle 10 10 true (1),
.cycle 7 14 true (1),
.cycle 6 14 true (1),
.cycle 21 4 true (2)
])
theorem kid01_part617_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part617) = true := by rfl

def kid01_part618 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 14 4 true (-1),
.cycle 17 1 false (-1),
.cycle 14 4 true (-1),
.cycle 15 4 true (-1),
.cycle 21 1 false (1),
.last 14 (0,true),
.cycle 12 8 true (1),
.cycle 12 2 true (1),
.cycle 12 6 true (1),
.cycle 12 6 true (1),
.cycle 6 22 true (0),
.last 14 (0,true),
.cycle 6 12 true (-1),
.cycle 14 16 true (-2),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 17 3 false (1),
.cycle 10 4 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 6 18 true (1)
])
theorem kid01_part618_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part618) = true := by rfl

def kid01_part619 : Audit := .split 17 (5,false) (byMove [
.last 18 (0,true),
.cycle 18 4 true (-1),
.cycle 21 1 false (-1),
.cycle 18 4 true (-1),
.cycle 19 4 true (-1),
.cycle 19 1 false (1),
.last 18 (0,true),
.cycle 12 8 true (1),
.cycle 16 2 true (1),
.cycle 12 6 true (1),
.cycle 13 6 true (1),
.cycle 19 4 true (2),
.last 18 (0,true),
.cycle 6 16 true (-1),
.cycle 6 34 true (-2),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 31 1 false (1),
.last 18 (0,true),
.cycle 31 3 false (3),
.cycle 10 8 true (1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 19 4 true (2)
])
theorem kid01_part619_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part619) = true := by rfl

def kid01_part620 : Audit := .split 17 (5,false) (byMove [
.last 18 (0,true),
.cycle 18 4 true (-1),
.cycle 21 1 false (-1),
.cycle 18 4 true (-1),
.cycle 19 4 true (-1),
.cycle 13 10 true (0),
.last 18 (0,true),
.cycle 13 8 true (1),
.cycle 16 2 true (1),
.cycle 13 6 true (1),
.cycle 12 6 true (1),
.cycle 20 4 true (2),
.last 18 (0,true),
.cycle 6 16 true (-1),
.cycle 6 34 true (-2),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 31 1 false (1),
.last 18 (0,true),
.cycle 31 3 false (3),
.cycle 10 8 true (1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 20 4 true (2)
])
theorem kid01_part620_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part620) = true := by rfl

def kid01_part621 : Audit := .split 14 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (0),
.cycle 6 14 true (0),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 21 true (0),
.cycle 6 18 true (0),
.cycle 1 15 true (1),
.cycle 14 1 true (4),
.cycle 27 4 false (5),
.cycle 12 5 true (2),
.cycle 15 4 true (3),
.cycle 6 15 true (0),
.cycle 17 4 true (3),
.cycle 23 1 false (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 16 true (1),
.cycle 15 4 true (3),
.cycle 14 1 true (4)
])
theorem kid01_part621_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part621) = true := by rfl

def kid01_part622 : Audit := .split 12 (0,true) (byMove [
.cycle 10 5 false (2),
.last 29 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 33 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 25 (5,false),
.last 14 (5,false),
.last 23 (5,false),
.last 23 (5,false),
.last 17 (5,false),
.last 16 (5,false),
.last 19 (5,false),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.cycle 25 4 true (-3),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 15 (5,false),
.last 18 (5,false),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.cycle 11 2 true (0)
])
theorem kid01_part622_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part622) = true := by rfl

def kid01_part623 : Audit := .cycle 6 10 true (-1)
theorem kid01_part623_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part623) = true := by rfl

def kid01_part624 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 26 4 true (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 19 16 true (-4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 6 12 true (-1),
.cycle 12 2 true (-1),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 6 12 true (-1),
.cycle 12 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 14 12 true (-2),
.cycle 14 1 false (-2),
.cycle 16 12 true (-2),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 3 false (0),
.cycle 14 12 true (-2),
.cycle 15 12 true (-2),
.cycle 14 12 true (-2),
.cycle 11 3 false (1)
])
theorem kid01_part624_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part624) = true := by rfl

def kid01_part625 : Audit := .cycle 6 8 true (0)
theorem kid01_part625_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part625) = true := by rfl

def kid01_part626 : Audit := .cycle 6 8 true (0)
theorem kid01_part626_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part626) = true := by rfl

def kid01_part627 : Audit := .split 13 (5,false) (byMove [
.cycle 10 6 false (2),
.cycle 26 4 true (-3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 6 12 true (-1),
.cycle 13 2 true (-1),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 12 2 true (-1),
.cycle 13 4 false (-1),
.cycle 12 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 13 3 false (0),
.cycle 12 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 11 3 false (1)
])
theorem kid01_part627_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part627) = true := by rfl

def kid01_part628 : Audit := .split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.last 15 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.last 17 (5,false),
.cycle 9 6 true (1),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 0 14 true (0),
.last 18 (5,false),
.last 15 (5,false),
.last 17 (5,false),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 11 2 true (1),
.cycle 0 14 true (0),
.cycle 9 4 true (1),
.cycle 2 14 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 0 14 true (0)
])
theorem kid01_part628_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part628) = true := by rfl

def kid01_part629 : Audit := .split 17 (5,false) (byMove [
.cycle 10 10 false (2),
.cycle 34 4 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 6 16 true (-1),
.cycle 16 2 true (-1),
.cycle 6 14 true (-1),
.cycle 6 14 true (-1),
.cycle 14 4 true (-1),
.cycle 15 4 false (1),
.cycle 13 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 18 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 15 3 false (1),
.cycle 13 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 11 7 false (2)
])
theorem kid01_part629_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part629) = true := by rfl

def kid01_part630 : Audit := .cycle 10 2 true (1)
theorem kid01_part630_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part630) = true := by rfl

def kid01_part631 : Audit := .cycle 7 6 true (1)
theorem kid01_part631_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part631) = true := by rfl

def kid01_part632 : Audit := .cycle 6 6 true (1)
theorem kid01_part632_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part632) = true := by rfl

def kid01_part633 : Audit := .split 14 (5,false) (byMove [
.last 15 (0,true),
.cycle 9 6 true (1),
.cycle 12 4 true (2),
.cycle 8 8 true (1),
.cycle 7 8 true (1),
.cycle 13 2 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (1),
.cycle 3 12 true (1),
.cycle 1 15 true (1),
.cycle 14 1 true (4),
.last 15 (0,true),
.cycle 11 7 true (1),
.cycle 10 5 true (1),
.cycle 7 9 true (1),
.cycle 6 9 true (1),
.cycle 12 3 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (1),
.cycle 8 7 true (1),
.cycle 14 1 true (4)
])
theorem kid01_part633_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part633) = true := by rfl

def kid01_part609 : Audit := .split 11 (5,true) (byMove [(kid01_part610),(kid01_part611),(kid01_part612),(kid01_part613),(kid01_part614),(kid01_part615),(kid01_part616),(kid01_part617),(kid01_part618),(kid01_part619),(kid01_part620),(kid01_part621),(kid01_part622),(kid01_part623),(kid01_part624),(kid01_part625),(kid01_part626),(kid01_part627),(kid01_part628),(kid01_part629),(kid01_part630),(kid01_part631),(kid01_part632),(kid01_part633)])

theorem kid01_part609_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part609) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part610),(kid01_part611),(kid01_part612),(kid01_part613),(kid01_part614),(kid01_part615),(kid01_part616),(kid01_part617),(kid01_part618),(kid01_part619),(kid01_part620),(kid01_part621),(kid01_part622),(kid01_part623),(kid01_part624),(kid01_part625),(kid01_part626),(kid01_part627),(kid01_part628),(kid01_part629),(kid01_part630),(kid01_part631),(kid01_part632),(kid01_part633)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part610_checked

  · exact kid01_part616_checked

  · exact kid01_part622_checked

  · exact kid01_part628_checked

  · exact kid01_part611_checked

  · exact kid01_part617_checked

  · exact kid01_part623_checked

  · exact kid01_part629_checked

  · exact kid01_part612_checked

  · exact kid01_part618_checked

  · exact kid01_part624_checked

  · exact kid01_part630_checked

  · exact kid01_part613_checked

  · exact kid01_part619_checked

  · exact kid01_part625_checked

  · exact kid01_part631_checked

  · exact kid01_part614_checked

  · exact kid01_part620_checked

  · exact kid01_part626_checked

  · exact kid01_part632_checked

  · exact kid01_part615_checked

  · exact kid01_part621_checked

  · exact kid01_part627_checked

  · exact kid01_part633_checked

def kid01_part634 : Audit := .split 11 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 18 4 true (-1),
.cycle 0 13 true (0),
.cycle 22 4 true (-1),
.cycle 23 4 true (-1),
.split 12 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 29 4 true (-2),
.cycle 0 14 true (0),
.cycle 19 1 false (-1),
.cycle 33 4 true (-3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 13 5 false (1),
.cycle 9 11 false (3),
.cycle 19 4 true (-1),
.cycle 27 1 false (-1),
.cycle 29 4 true (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.last 13 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 0 15 true (0),
.cycle 13 4 true (3),
.cycle 4 9 true (1),
.cycle 23 4 true (-1),
.last 14 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 4 true (3),
.cycle 12 1 true (4)
]),
.cycle 13 5 false (1),
.cycle 6 16 true (-1),
.cycle 10 2 true (2),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.last 26 (5,false),
.cycle 18 4 true (0),
.cycle 9 6 true (1),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 15 (5,false),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.last 14 (5,false),
.cycle 13 5 false (1),
.cycle 18 16 true (-2),
.cycle 6 16 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 11 2 true (2),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 14 (5,false)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (2),
.cycle 8 4 true (2),
.split 12 (5,false) (byMove [
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.cycle 0 14 true (0),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 14 (5,true),
.last 16 (5,true),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
])
theorem kid01_part634_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part634) = true := by rfl

def kid01_part635 : Audit := .cycle 9 2 true (2)
theorem kid01_part635_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part635) = true := by rfl

def kid01_part636 : Audit := .cycle 2 10 true (1)
theorem kid01_part636_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part636) = true := by rfl

def kid01_part637 : Audit := .cycle 8 4 true (2)
theorem kid01_part637_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part637) = true := by rfl

def kid01_part638 : Audit := .cycle 7 4 true (2)
theorem kid01_part638_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part638) = true := by rfl

def kid01_part640 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 29 4 true (-2),
.last 14 (5,false),
.cycle 19 1 false (-1),
.cycle 33 4 true (-3),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 14 5 false (0),
.last 19 (5,false),
.cycle 19 4 true (-1),
.cycle 27 1 false (-1),
.cycle 29 4 true (-1),
.last 15 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.last 13 (5,false)
])
theorem kid01_part640_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part640) = true := by rfl

def kid01_part641 : Audit := .cycle 18 4 true (-1)
theorem kid01_part641_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part641) = true := by rfl

def kid01_part642 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 24 4 true (-1),
.cycle 12 2 true (2),
.cycle 28 4 true (-1),
.cycle 29 4 true (-1),
.cycle 22 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 1 true (3),
.last 14 (0,true),
.cycle 6 22 true (-1),
.cycle 10 4 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 22 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 13 1 true (3)
])
theorem kid01_part642_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part642) = true := by rfl

def kid01_part643 : Audit := .cycle 22 4 true (-1)
theorem kid01_part643_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part643) = true := by rfl

def kid01_part644 : Audit := .cycle 23 4 true (-1)
theorem kid01_part644_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part644) = true := by rfl

def kid01_part645 : Audit := .split 15 (5,false) (byMove [
.cycle 0 16 false (4),
.cycle 12 14 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 12 15 false (2),
.cycle 15 1 false (-1),
.cycle 0 16 true (-1),
.cycle 12 14 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 15 false (2),
.cycle 15 1 true (-1),
.cycle 13 6 false (1),
.cycle 13 8 false (1),
.cycle 16 4 true (-2),
.cycle 16 1 false (-2),
.cycle 18 4 true (-2),
.cycle 15 1 false (-1),
.cycle 11 17 false (4),
.cycle 1 15 false (4),
.cycle 12 13 false (2),
.cycle 13 9 false (1),
.cycle 16 4 true (-2),
.cycle 15 1 true (-1)
])
theorem kid01_part645_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part645) = true := by rfl

def kid01_part646 : Audit := .cycle 0 12 true (0)
theorem kid01_part646_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part646) = true := by rfl

def kid01_part647 : Audit := .cycle 1 11 true (1)
theorem kid01_part647_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part647) = true := by rfl

def kid01_part648 : Audit := .cycle 6 12 true (2)
theorem kid01_part648_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part648) = true := by rfl

def kid01_part649 : Audit := .cycle 3 9 true (1)
theorem kid01_part649_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part649) = true := by rfl

def kid01_part650 : Audit := .cycle 1 12 true (1)
theorem kid01_part650_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part650) = true := by rfl

def kid01_part651 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 23 4 true (-1),
.cycle 21 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 11 8 true (3),
.cycle 13 4 true (3),
.cycle 4 9 true (1),
.cycle 23 4 true (-1),
.cycle 39 1 false (7),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 4 true (3),
.cycle 12 1 true (4)
])
theorem kid01_part651_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part651) = true := by rfl

def kid01_part652 : Audit := .split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 18 4 true (0),
.last 14 (5,false),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 13 4 true (2),
.last 14 (5,false),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 9 6 true (2),
.cycle 14 5 false (0),
.cycle 18 16 true (-2),
.cycle 6 16 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 15 (5,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 14 (5,false),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (2)
])
theorem kid01_part652_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part652) = true := by rfl

def kid01_part653 : Audit := .cycle 6 16 true (-1)
theorem kid01_part653_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part653) = true := by rfl

def kid01_part654 : Audit := .cycle 10 2 true (2)
theorem kid01_part654_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part654) = true := by rfl

def kid01_part655 : Audit := .cycle 7 6 true (2)
theorem kid01_part655_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part655) = true := by rfl

def kid01_part656 : Audit := .cycle 6 6 true (2)
theorem kid01_part656_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part656) = true := by rfl

def kid01_part657 : Audit := .split 15 (5,false) (byMove [
.cycle 10 8 false (3),
.cycle 30 4 true (-3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 6 14 true (-1),
.cycle 13 4 true (-1),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.cycle 14 2 true (-1),
.cycle 13 6 false (1),
.cycle 12 6 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.cycle 16 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 13 5 false (1),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.cycle 13 3 false (1)
])
theorem kid01_part657_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part657) = true := by rfl

def kid01_part658 : Audit := .cycle 0 12 true (0)
theorem kid01_part658_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part658) = true := by rfl

def kid01_part659 : Audit := .cycle 1 11 true (1)
theorem kid01_part659_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part659) = true := by rfl

def kid01_part660 : Audit := .cycle 2 10 true (1)
theorem kid01_part660_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part660) = true := by rfl

def kid01_part661 : Audit := .cycle 7 7 true (2)
theorem kid01_part661_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part661) = true := by rfl

def kid01_part662 : Audit := .cycle 8 4 true (2)
theorem kid01_part662_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part662) = true := by rfl

def kid01_part663 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 12 2 true (3),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 13 (0,true),
.cycle 11 5 true (2),
.cycle 10 3 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part663_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part663) = true := by rfl

def kid01_part639 : Audit := .split 11 (5,true) (byMove [(kid01_part640),(kid01_part641),(kid01_part642),(kid01_part643),(kid01_part644),(kid01_part645),(kid01_part646),(kid01_part647),(kid01_part648),(kid01_part649),(kid01_part650),(kid01_part651),(kid01_part652),(kid01_part653),(kid01_part654),(kid01_part655),(kid01_part656),(kid01_part657),(kid01_part658),(kid01_part659),(kid01_part660),(kid01_part661),(kid01_part662),(kid01_part663)])

theorem kid01_part639_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part639) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid01_part640),(kid01_part641),(kid01_part642),(kid01_part643),(kid01_part644),(kid01_part645),(kid01_part646),(kid01_part647),(kid01_part648),(kid01_part649),(kid01_part650),(kid01_part651),(kid01_part652),(kid01_part653),(kid01_part654),(kid01_part655),(kid01_part656),(kid01_part657),(kid01_part658),(kid01_part659),(kid01_part660),(kid01_part661),(kid01_part662),(kid01_part663)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part640_checked

  · exact kid01_part646_checked

  · exact kid01_part652_checked

  · exact kid01_part658_checked

  · exact kid01_part641_checked

  · exact kid01_part647_checked

  · exact kid01_part653_checked

  · exact kid01_part659_checked

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

def kid01_part567 : Audit := .split 10 (2,true) (byMove [(kid01_part568),(kid01_part569),(kid01_part570),(kid01_part571),(kid01_part572),(kid01_part573),(kid01_part598),(kid01_part599),(kid01_part600),(kid01_part601),(kid01_part602),(kid01_part603),(kid01_part604),(kid01_part605),(kid01_part606),(kid01_part607),(kid01_part608),(kid01_part609),(kid01_part634),(kid01_part635),(kid01_part636),(kid01_part637),(kid01_part638),(kid01_part639)])

theorem kid01_part567_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (kid01_part567) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part568),(kid01_part569),(kid01_part570),(kid01_part571),(kid01_part572),(kid01_part573),(kid01_part598),(kid01_part599),(kid01_part600),(kid01_part601),(kid01_part602),(kid01_part603),(kid01_part604),(kid01_part605),(kid01_part606),(kid01_part607),(kid01_part608),(kid01_part609),(kid01_part634),(kid01_part635),(kid01_part636),(kid01_part637),(kid01_part638),(kid01_part639)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part568_checked

  · exact kid01_part598_checked

  · exact kid01_part604_checked

  · exact kid01_part634_checked

  · exact kid01_part569_checked

  · exact kid01_part599_checked

  · exact kid01_part605_checked

  · exact kid01_part635_checked

  · exact kid01_part570_checked

  · exact kid01_part600_checked

  · exact kid01_part606_checked

  · exact kid01_part636_checked

  · exact kid01_part571_checked

  · exact kid01_part601_checked

  · exact kid01_part607_checked

  · exact kid01_part637_checked

  · exact kid01_part572_checked

  · exact kid01_part602_checked

  · exact kid01_part608_checked

  · exact kid01_part638_checked

  · exact kid01_part573_checked

  · exact kid01_part603_checked

  · exact kid01_part609_checked

  · exact kid01_part639_checked

def kid01_part664 : Audit := .cycle 7 4 true (2)
theorem kid01_part664_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,3⟩)) (kid01_part664) = true := by rfl

def kid01_part665 : Audit := .cycle 6 4 true (2)
theorem kid01_part665_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,4⟩)) (kid01_part665) = true := by rfl

def kid01_part668 : Audit := .cycle 0 28 false (4)
theorem kid01_part668_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part668) = true := by rfl

def kid01_part669 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 12 8 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.cycle 6 26 false (4),
.cycle 12 2 true (-1),
.last 14 (2,true),
.cycle 12 4 true (-1),
.cycle 12 4 true (-1),
.last 32 (2,true),
.last 19 (2,true),
.last 15 (2,true),
.last 22 (2,true),
.cycle 14 1 false (-2),
.last 24 (2,true),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.last 18 (2,true),
.last 14 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.cycle 6 27 false (4)
])
theorem kid01_part669_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part669) = true := by rfl

def kid01_part670 : Audit := .split 12 (2,true) (byMove [
.cycle 29 1 false (-1),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.cycle 11 8 false (1),
.last 16 (5,false),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 6 12 true (0),
.cycle 39 1 false (-1),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part670_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part670) = true := by rfl

def kid01_part671 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 14 2 true (-1),
.last 16 (2,true),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.last 36 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.last 24 (2,true),
.cycle 16 1 false (-2),
.last 26 (2,true),
.cycle 15 1 false (-1),
.cycle 11 5 false (1),
.last 20 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 18 1 false (-2)
])
theorem kid01_part671_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part671) = true := by rfl

def kid01_part672 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.cycle 16 12 false (1),
.cycle 14 2 true (-1),
.last 16 (2,true),
.cycle 13 4 true (-1),
.cycle 12 4 true (-1),
.last 36 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.last 24 (2,true),
.cycle 16 1 false (-2),
.last 26 (2,true),
.cycle 15 1 false (-1),
.cycle 11 5 false (1),
.last 20 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 16 12 false (0)
])
theorem kid01_part672_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part672) = true := by rfl

def kid01_part673 : Audit := .split 28 (5,false) (byMove [
.cycle 0 29 false (4),
.cycle 26 12 false (0),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.cycle 26 13 false (0),
.cycle 28 1 false (-2),
.cycle 13 16 true (-2),
.cycle 45 2 true (0),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 6 43 false (4),
.cycle 0 34 true (-2),
.last 34 (2,true),
.last 30 (2,true),
.last 42 (2,true),
.cycle 29 1 false (-3),
.cycle 26 15 false (0),
.cycle 28 1 false (-2),
.cycle 0 45 false (4),
.cycle 1 28 false (4),
.cycle 6 39 false (4),
.last 37 (2,true),
.last 38 (2,true),
.cycle 39 1 true (-3)
])
theorem kid01_part673_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part673) = true := by rfl

def kid01_part674 : Audit := .split 17 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 22 5 false (2),
.cycle 22 1 false (0),
.cycle 24 7 false (2),
.cycle 24 7 false (2),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (1),
.cycle 3 15 true (1),
.cycle 1 18 true (1),
.last 18 (5,false),
.cycle 0 20 true (0),
.cycle 22 5 false (2),
.cycle 6 18 true (-1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 10 8 true (1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (1),
.cycle 8 10 true (1),
.last 18 (5,false)
])
theorem kid01_part674_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part674) = true := by rfl

def kid01_part675 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 15 (5,false),
.cycle 29 1 false (1),
.last 17 (5,false),
.last 17 (5,false),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.last 16 (5,false),
.last 15 (5,false),
.cycle 6 24 true (-1),
.cycle 7 16 true (1),
.cycle 6 16 true (1),
.cycle 10 8 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.cycle 8 12 true (1),
.last 14 (5,false)
])
theorem kid01_part675_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part675) = true := by rfl

def kid01_part676 : Audit := .split 16 (5,false) (byMove [
.last 19 (2,true),
.last 27 (2,true),
.cycle 6 16 true (0),
.last 25 (2,true),
.cycle 6 21 false (4),
.cycle 41 1 false (1),
.cycle 6 22 true (0),
.cycle 15 2 true (2),
.last 17 (2,true),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 0 18 true (0),
.last 29 (2,true),
.last 18 (2,true),
.last 25 (2,true),
.cycle 6 14 true (0),
.last 30 (2,true),
.last 21 (2,true),
.cycle 6 18 true (1),
.last 21 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.cycle 6 21 true (0)
])
theorem kid01_part676_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part676) = true := by rfl

def kid01_part677 : Audit := .cycle 6 10 true (0)
theorem kid01_part677_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part677) = true := by rfl

def kid01_part678 : Audit := .split 18 (5,false) (byMove [
.cycle 11 8 true (1),
.last 23 (2,true),
.last 19 (2,true),
.last 25 (2,true),
.last 25 (2,true),
.cycle 6 22 true (0),
.cycle 1 20 true (1),
.cycle 17 2 true (2),
.last 19 (2,true),
.cycle 15 4 true (2),
.cycle 16 4 true (2),
.cycle 0 20 true (0),
.last 27 (2,true),
.last 23 (2,true),
.last 19 (2,true),
.cycle 5 14 true (1),
.cycle 6 14 true (1),
.last 31 (2,true),
.cycle 1 20 true (1),
.cycle 9 10 true (1),
.last 19 (2,true),
.cycle 8 12 true (1),
.cycle 7 12 true (1),
.cycle 1 21 true (1)
])
theorem kid01_part678_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part678) = true := by rfl

def kid01_part679 : Audit := .split 12 (5,false) (byMove [
.last 15 (2,true),
.last 23 (2,true),
.cycle 6 12 true (0),
.last 21 (2,true),
.cycle 6 17 false (4),
.cycle 32 1 false (0),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 13 (2,true),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 0 14 true (0),
.last 23 (2,true),
.last 14 (2,true),
.last 21 (2,true),
.cycle 6 10 true (0),
.last 26 (2,true),
.last 17 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.last 13 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.cycle 15 1 true (3)
])
theorem kid01_part679_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part679) = true := by rfl

def kid01_part680 : Audit := .split 18 (2,true) (byMove [
.cycle 11 8 false (1),
.cycle 14 5 false (0),
.cycle 22 1 false (-2),
.cycle 14 7 false (0),
.cycle 14 7 false (0),
.cycle 12 8 false (0),
.cycle 9 12 false (3),
.last 20 (5,false),
.last 24 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 26 (5,false),
.cycle 11 8 false (1),
.cycle 14 5 false (0),
.cycle 6 18 false (4),
.cycle 5 14 false (4),
.cycle 6 14 false (4),
.cycle 12 8 false (0),
.cycle 11 10 false (1),
.cycle 9 10 false (3),
.last 24 (5,false),
.cycle 8 12 false (4),
.cycle 7 12 false (4),
.cycle 11 10 false (1)
])
theorem kid01_part680_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part680) = true := by rfl

def kid01_part681 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.last 23 (2,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 32 (2,true),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 12 2 true (-1),
.last 14 (2,true),
.last 21 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.last 19 (2,true),
.last 15 (2,true),
.last 23 (2,true),
.cycle 14 1 false (-2),
.last 25 (2,true),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.last 18 (2,true),
.last 14 (2,true),
.last 21 (2,true),
.last 21 (2,true),
.last 17 (2,true)
])
theorem kid01_part681_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part681) = true := by rfl

def kid01_part682 : Audit := .split 12 (2,true) (byMove [
.cycle 11 5 false (1),
.last 18 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.last 18 (5,false),
.last 14 (5,false),
.last 18 (5,false),
.last 16 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.cycle 11 8 false (1),
.last 16 (5,false),
.last 36 (5,false),
.cycle 13 1 false (-1),
.cycle 6 18 false (4),
.last 13 (5,false),
.cycle 11 2 true (0),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1208008960, 1073741824, 128, 256, 134217728, 1024, 1048576, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1024, 1073741824, 128, 1024, 1024, 1048576, 128, 128, 524288, 4194304, 4194304, 1073741824, 1074340864, 1074340864, 8192, 65536, 65536, 1208008960, 1073741824, 1073741824, 128, 1024, 1024, 1048576, 1024, 1073741824, 128, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.last 18 (5,false),
.last 38 (5,false),
.last 28 (5,false),
.last 19 (5,false)
])
theorem kid01_part682_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part682) = true := by rfl

def kid01_part683 : Audit := .split 19 (2,true) (byMove [
.cycle 11 9 false (2),
.cycle 15 5 false (1),
.cycle 23 1 false (-1),
.cycle 14 7 false (2),
.cycle 13 7 false (2),
.cycle 22 1 false (-2),
.cycle 0 26 true (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 256, 262144, 262144],[65536, 262144, 2, 1024, 1024, 16384, 65536, 2, 2, 65536, 65536, 256, 65536, 2, 2, 65536, 65536, 256, 262144],396320⟩,
.last 24 (5,false),
.cycle 36 1 false (-2),
.last 26 (5,false),
.last 20 (5,false),
.cycle 28 1 false (-2),
.cycle 15 5 false (1),
.cycle 30 1 false (-2),
.cycle 26 1 false (-2),
.cycle 26 1 false (-2),
.cycle 22 1 false (-2),
.cycle 30 1 false (-2),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 16384, 262144, 262144],[65536, 262144, 128, 1024, 1024, 16384, 65536, 8192, 8192, 65536, 65536, 16384, 65536, 8192, 8192, 65536, 65536, 16384, 262144],396320⟩,
.last 24 (5,false),
.cycle 34 1 false (-2),
.cycle 24 1 false (-2),
.last 20 (5,false)
])
theorem kid01_part683_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part683) = true := by rfl

def kid01_part684 : Audit := .split 19 (2,true) (byMove [
.cycle 11 9 false (2),
.cycle 15 5 false (1),
.cycle 23 1 false (-1),
.cycle 14 7 false (2),
.cycle 13 7 false (2),
.last 28 (5,false),
.cycle 0 26 true (-1),
.last 35 (5,false),
.last 24 (5,false),
.last 42 (5,false),
.last 26 (5,false),
.last 20 (5,false),
.last 34 (5,false),
.cycle 15 5 false (1),
.last 36 (5,false),
.last 32 (5,false),
.last 32 (5,false),
.last 28 (5,false),
.last 36 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1209057536, 1073741824, 8192, 16384, 32768, 4260864, 1209057536, 1073741824, 128, 256, 134217728, 1024, 1048576, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[65536, 1073741824, 128, 1024, 1024, 1048576, 4194304, 128, 524288, 4194304, 4194304, 1209057536, 1074340992, 1074340992, 8192, 65536, 65536, 1209057536, 1024, 1074340992, 128, 1024, 1024, 1048576, 128, 1073741824, 128, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.last 24 (5,false),
.last 40 (5,false),
.last 30 (5,false),
.last 20 (5,false)
])
theorem kid01_part684_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part684) = true := by rfl

def kid01_part685 : Audit := .split 15 (2,true) (byMove [
.cycle 11 5 false (1),
.cycle 12 5 false (1),
.cycle 19 1 false (-1),
.cycle 12 7 false (1),
.cycle 12 7 false (1),
.last 18 (5,false),
.cycle 0 22 true (-1),
.last 29 (5,false),
.last 20 (5,false),
.last 28 (5,false),
.last 22 (5,false),
.last 16 (5,false),
.cycle 11 5 false (1),
.cycle 12 5 false (1),
.last 26 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 18 (5,false),
.last 22 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1208008960, 1073741824, 128, 256, 134217728, 1024, 1048576, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1073741824, 1073741824, 128, 1024, 1024, 1048576, 128, 128, 524288, 4194304, 4194304, 1073741824, 1074274304, 1074274304, 8192, 65536, 65536, 1073758464, 1073741824, 1073741824, 128, 1024, 1024, 1048576, 1073741824, 1073741824, 128, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.last 20 (5,false),
.last 26 (5,false),
.last 20 (5,false),
.last 16 (5,false)
])
theorem kid01_part685_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part685) = true := by rfl

def kid01_part686 : Audit := .cycle 9 4 true (1)
theorem kid01_part686_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part686) = true := by rfl

def kid01_part687 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 17 5 false (2),
.cycle 18 1 false (0),
.cycle 19 7 false (2),
.cycle 19 7 false (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (1),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 9 6 true (1),
.cycle 17 5 false (2),
.cycle 6 14 true (-1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (1),
.cycle 8 6 true (1),
.last 14 (5,false)
])
theorem kid01_part687_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part687) = true := by rfl

def kid01_part688 : Audit := .split 16 (5,false) (byMove [
.cycle 11 6 true (1),
.last 21 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.cycle 6 18 true (0),
.cycle 2 16 true (1),
.cycle 15 2 true (2),
.last 17 (2,true),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 0 18 true (0),
.last 18 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 6 12 true (1),
.last 27 (2,true),
.cycle 2 16 true (1),
.cycle 9 8 true (1),
.last 17 (2,true),
.cycle 8 10 true (1),
.cycle 7 10 true (1),
.cycle 2 17 true (1)
])
theorem kid01_part688_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part688) = true := by rfl

def kid01_part689 : Audit := .cycle 4 8 true (1)
theorem kid01_part689_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part689) = true := by rfl

def kid01_part690 : Audit := .split 17 (2,true) (byMove [
.cycle 11 7 false (2),
.cycle 13 5 false (1),
.cycle 21 1 false (-1),
.cycle 12 7 false (2),
.cycle 12 7 false (2),
.last 22 (5,false),
.cycle 0 24 true (-1),
.last 33 (5,false),
.last 22 (5,false),
.last 34 (5,false),
.last 24 (5,false),
.last 18 (5,false),
.last 26 (5,false),
.cycle 13 5 false (1),
.last 30 (5,false),
.last 26 (5,false),
.last 26 (5,false),
.last 22 (5,false),
.last 28 (5,false),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1208008960, 1073741824, 128, 256, 134217728, 1024, 1048576, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1024, 1073741824, 128, 1024, 1024, 1048576, 4194304, 128, 524288, 4194304, 4194304, 1073741824, 65536, 1074340864, 8192, 65536, 65536, 1208008960, 1024, 1073741824, 128, 1024, 1024, 1048576, 1024, 1073741824, 128, 1024, 1024, 1048576, 1073741824],1990983038⟩,
.last 22 (5,false),
.last 32 (5,false),
.last 24 (5,false),
.last 18 (5,false)
])
theorem kid01_part690_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part690) = true := by rfl

def kid01_part691 : Audit := .split 12 (5,false) (byMove [
.cycle 11 2 true (1),
.last 17 (2,true),
.last 13 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.cycle 0 38 false (4),
.cycle 0 15 true (0),
.cycle 12 2 true (2),
.last 13 (2,true),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 0 14 true (0),
.cycle 10 4 true (1),
.last 17 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 19 (2,true),
.cycle 0 15 true (0),
.cycle 9 4 true (1),
.last 13 (2,true),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 15 1 true (3)
])
theorem kid01_part691_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part691) = true := by rfl

def kid01_part667 : Audit := .split 11 (0,true) (byMove [(kid01_part668),(kid01_part669),(kid01_part670),(kid01_part671),(kid01_part672),(kid01_part673),(kid01_part674),(kid01_part675),(kid01_part676),(kid01_part677),(kid01_part678),(kid01_part679),(kid01_part680),(kid01_part681),(kid01_part682),(kid01_part683),(kid01_part684),(kid01_part685),(kid01_part686),(kid01_part687),(kid01_part688),(kid01_part689),(kid01_part690),(kid01_part691)])

theorem kid01_part667_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part667) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part668),(kid01_part669),(kid01_part670),(kid01_part671),(kid01_part672),(kid01_part673),(kid01_part674),(kid01_part675),(kid01_part676),(kid01_part677),(kid01_part678),(kid01_part679),(kid01_part680),(kid01_part681),(kid01_part682),(kid01_part683),(kid01_part684),(kid01_part685),(kid01_part686),(kid01_part687),(kid01_part688),(kid01_part689),(kid01_part690),(kid01_part691)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part668_checked

  · exact kid01_part674_checked

  · exact kid01_part680_checked

  · exact kid01_part686_checked

  · exact kid01_part669_checked

  · exact kid01_part675_checked

  · exact kid01_part681_checked

  · exact kid01_part687_checked

  · exact kid01_part670_checked

  · exact kid01_part676_checked

  · exact kid01_part682_checked

  · exact kid01_part688_checked

  · exact kid01_part671_checked

  · exact kid01_part677_checked

  · exact kid01_part683_checked

  · exact kid01_part689_checked

  · exact kid01_part672_checked

  · exact kid01_part678_checked

  · exact kid01_part684_checked

  · exact kid01_part690_checked

  · exact kid01_part673_checked

  · exact kid01_part679_checked

  · exact kid01_part685_checked

  · exact kid01_part691_checked

def kid01_part693 : Audit := .split 19 (0,true) (byMove [
.last 47 (2,true),
.cycle 6 20 false (4),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.last 35 (2,true),
.last 39 (2,true),
.cycle 11 10 true (-1),
.last 21 (2,true),
.last 27 (2,true),
.cycle 20 1 false (0),
.cycle 13 8 true (-1),
.last 23 (2,true),
.cycle 11 10 false (2),
.last 21 (2,true),
.last 27 (2,true),
.cycle 20 1 false (-2),
.cycle 13 8 false (2),
.last 23 (2,true),
.last 27 (2,true),
.last 21 (2,true),
.cycle 14 6 true (-1),
.last 31 (2,true),
.last 25 (2,true),
.cycle 18 2 true (-1)
])
theorem kid01_part693_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part693) = true := by rfl

def kid01_part694 : Audit := .cycle 13 8 false (2)
theorem kid01_part694_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part694) = true := by rfl

def kid01_part695 : Audit := .split 19 (2,true) (byMove [
.last 28 (0,true),
.cycle 6 20 false (4),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 34 1 false (-4),
.cycle 22 1 false (-2),
.cycle 11 10 true (-1),
.cycle 17 17 true (-1),
.cycle 26 1 false (0),
.cycle 20 1 false (0),
.cycle 13 8 true (-1),
.cycle 22 1 false (0),
.cycle 11 10 false (2),
.cycle 25 1 false (-3),
.cycle 26 1 false (-2),
.cycle 20 1 false (-2),
.cycle 13 8 false (2),
.cycle 22 1 false (-2),
.cycle 26 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 20, 64],[64, 18, 2, 16, 16, 12, 64],64⟩,
.cycle 14 6 true (-1),
.cycle 30 1 false (-2),
.cycle 24 1 false (-2),
.cycle 18 2 true (-1)
])
theorem kid01_part695_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part695) = true := by rfl

def kid01_part696 : Audit := .cycle 23 1 false (-3)
theorem kid01_part696_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part696) = true := by rfl

def kid01_part697 : Audit := .cycle 6 24 false (4)
theorem kid01_part697_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part697) = true := by rfl

def kid01_part698 : Audit := .cycle 6 20 false (4)
theorem kid01_part698_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part698) = true := by rfl

def kid01_part699 : Audit := .split 19 (0,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 1, 64],[28, 28, 64, 16, 16, 24, 64],64⟩,
.cycle 6 36 false (4),
.cycle 33 1 false (-1),
.cycle 11 13 false (2),
.cycle 21 14 false (0),
.last 23 (2,true),
.cycle 0 30 true (-1),
.last 21 (2,true),
.cycle 69 1 false (7),
.cycle 36 1 false (0),
.cycle 17 22 true (0),
.cycle 0 23 true (-1),
.cycle 11 16 false (2),
.last 21 (2,true),
.cycle 14 6 true (0),
.cycle 30 1 false (-2),
.cycle 13 12 false (2),
.cycle 18 2 true (0),
.cycle 17 6 true (0),
.last 21 (2,true),
.cycle 17 18 true (0),
.cycle 17 10 true (0),
.cycle 16 4 true (0),
.cycle 0 23 true (-1)
])
theorem kid01_part699_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part699) = true := by rfl

def kid01_part700 : Audit := .cycle 17 2 true (0)
theorem kid01_part700_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part700) = true := by rfl

def kid01_part701 : Audit := .split 19 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4, 128, 256, 8, 1024, 8, 4, 4096],[4096, 256, 256, 1024, 1024, 8, 4096, 1024, 4096, 1024, 1024, 8, 4096],4096⟩,
.cycle 6 36 false (4),
.cycle 33 1 false (-1),
.cycle 11 13 false (2),
.cycle 21 14 false (0),
.cycle 40 1 false (0),
.cycle 0 30 true (-1),
.cycle 17 15 true (0),
.cycle 69 1 false (7),
.cycle 36 1 false (0),
.cycle 17 22 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 12, 64],64⟩,
.cycle 11 16 false (2),
.cycle 42 5 false (-2),
.cycle 14 6 true (0),
.cycle 30 1 false (-2),
.cycle 13 12 false (2),
.cycle 18 2 true (0),
.cycle 17 6 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 18, 2, 16, 16, 12, 64],64⟩,
.cycle 17 18 true (0),
.cycle 17 10 true (0),
.cycle 16 4 true (0),
.cycle 6 23 true (-1)
])
theorem kid01_part701_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part701) = true := by rfl

def kid01_part702 : Audit := .cycle 15 4 true (0)
theorem kid01_part702_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part702) = true := by rfl

def kid01_part703 : Audit := .cycle 16 4 true (0)
theorem kid01_part703_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part703) = true := by rfl

def kid01_part704 : Audit := .cycle 6 36 false (4)
theorem kid01_part704_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part704) = true := by rfl

def kid01_part705 : Audit := .split 19 (0,true) (byMove [
.last 22 (2,true),
.cycle 20 19 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 35 21 false (-2),
.cycle 11 11 false (2),
.cycle 0 34 true (-1),
.cycle 17 16 false (2),
.last 20 (2,true),
.cycle 11 12 true (-1),
.cycle 11 12 true (-1),
.cycle 12 8 true (-1),
.cycle 17 14 false (2),
.last 21 (2,true),
.last 46 (2,true),
.cycle 20 1 false (-2),
.cycle 17 12 false (2),
.cycle 17 34 false (2),
.cycle 9 42 false (3),
.cycle 20 21 false (2),
.last 20 (2,true),
.cycle 7 38 false (4),
.cycle 6 38 false (4),
.cycle 10 30 false (2)
])
theorem kid01_part705_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part705) = true := by rfl

def kid01_part706 : Audit := .split 22 (2,true) (byMove [
.last 23 (0,true),
.cycle 19 4 false (-1),
.cycle 25 1 false (-3),
.cycle 19 6 false (-1),
.cycle 19 6 false (-1),
.cycle 9 28 false (3),
.last 23 (0,true),
.cycle 17 6 false (1),
.cycle 98 40 true (0),
.cycle 17 12 false (2),
.cycle 17 12 false (2),
.cycle 57 18 false (-1),
.last 23 (0,true),
.cycle 19 4 false (-1),
.cycle 33 12 false (-1),
.cycle 31 10 false (-1),
.cycle 31 10 false (-1),
.cycle 17 34 false (2),
.last 23 (0,true),
.cycle 19 6 false (-1),
.cycle 43 16 false (0),
.cycle 29 8 false (-1),
.cycle 29 8 false (-1),
.cycle 10 13 false (2)
])
theorem kid01_part706_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part706) = true := by rfl

def kid01_part707 : Audit := .split 19 (2,true) (byMove [
.last 23 (0,true),
.cycle 11 29 false (2),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 11 30 false (2),
.cycle 11 19 false (2),
.last 20 (0,true),
.cycle 11 24 false (2),
.cycle 43 1 false (5),
.cycle 11 12 true (-1),
.cycle 11 12 true (-1),
.cycle 12 8 true (-1),
.cycle 17 14 false (2),
.cycle 11 30 false (2),
.cycle 11 22 false (2),
.cycle 20 1 false (-2),
.cycle 17 12 false (2),
.cycle 6 18 false (4),
.last 20 (0,true),
.cycle 11 33 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 8, 64],64⟩,
.cycle 11 20 false (2),
.cycle 11 20 false (2),
.cycle 11 16 false (2)
])
theorem kid01_part707_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part707) = true := by rfl

def kid01_part708 : Audit := .cycle 27 1 false (-3)
theorem kid01_part708_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part708) = true := by rfl

def kid01_part709 : Audit := .cycle 6 36 false (4)
theorem kid01_part709_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part709) = true := by rfl

def kid01_part710 : Audit := .cycle 35 1 false (-3)
theorem kid01_part710_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part710) = true := by rfl

def kid01_part711 : Audit := .split 19 (0,true) (byMove [
.cycle 0 22 false (4),
.cycle 11 9 false (2),
.last 20 (2,true),
.cycle 11 11 false (2),
.cycle 11 11 false (2),
.cycle 20 14 false (0),
.cycle 0 30 true (-1),
.last 21 (2,true),
.cycle 6 26 true (-1),
.cycle 6 32 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[16, 16, 64, 16, 16, 8, 64],64⟩,
.cycle 18 21 true (0),
.cycle 17 16 false (2),
.cycle 38 3 false (-2),
.last 20 (2,true),
.cycle 11 20 false (2),
.cycle 11 20 false (2),
.cycle 12 12 false (2),
.cycle 9 20 false (3),
.last 21 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[4, 20, 64, 16, 16, 8, 64],64⟩,
.cycle 4 28 false (4),
.cycle 11 16 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 9, 1, 64],[32, 48, 64, 16, 16, 9, 64],64⟩
])
theorem kid01_part711_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part711) = true := by rfl

def kid01_part712 : Audit := .cycle 11 12 false (2)
theorem kid01_part712_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part712) = true := by rfl

def kid01_part713 : Audit := .split 19 (2,true) (byMove [
.last 20 (0,true),
.cycle 11 9 false (2),
.cycle 23 1 false (-1),
.cycle 11 11 false (2),
.cycle 11 11 false (2),
.cycle 20 14 false (0),
.cycle 0 30 true (-1),
.cycle 17 15 true (0),
.cycle 6 26 true (-1),
.cycle 6 32 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.cycle 17 15 true (0),
.last 20 (0,true),
.cycle 38 3 false (-2),
.cycle 11 26 false (2),
.cycle 11 20 false (2),
.cycle 11 20 false (2),
.cycle 12 12 false (2),
.cycle 9 20 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 18, 2, 16, 16, 12, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 20, 4, 16, 16, 8, 64],64⟩,
.cycle 4 28 false (4),
.cycle 11 16 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 48, 32, 16, 16, 12, 64],64⟩
])
theorem kid01_part713_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part713) = true := by rfl

def kid01_part714 : Audit := .cycle 11 16 false (2)
theorem kid01_part714_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part714) = true := by rfl

def kid01_part715 : Audit := .cycle 11 16 false (2)
theorem kid01_part715_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part715) = true := by rfl

def kid01_part716 : Audit := .cycle 10 9 false (2)
theorem kid01_part716_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part716) = true := by rfl

def kid01_part692 : Audit := .split 18 (5,false) (byMove [(kid01_part693),(kid01_part694),(kid01_part695),(kid01_part696),(kid01_part697),(kid01_part698),(kid01_part699),(kid01_part700),(kid01_part701),(kid01_part702),(kid01_part703),(kid01_part704),(kid01_part705),(kid01_part706),(kid01_part707),(kid01_part708),(kid01_part709),(kid01_part710),(kid01_part711),(kid01_part712),(kid01_part713),(kid01_part714),(kid01_part715),(kid01_part716)])

theorem kid01_part692_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part692) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) 18 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (5,false) (some mv)) (byMove [(kid01_part693),(kid01_part694),(kid01_part695),(kid01_part696),(kid01_part697),(kid01_part698),(kid01_part699),(kid01_part700),(kid01_part701),(kid01_part702),(kid01_part703),(kid01_part704),(kid01_part705),(kid01_part706),(kid01_part707),(kid01_part708),(kid01_part709),(kid01_part710),(kid01_part711),(kid01_part712),(kid01_part713),(kid01_part714),(kid01_part715),(kid01_part716)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part693_checked

  · exact kid01_part699_checked

  · exact kid01_part705_checked

  · exact kid01_part711_checked

  · exact kid01_part694_checked

  · exact kid01_part700_checked

  · exact kid01_part706_checked

  · exact kid01_part712_checked

  · exact kid01_part695_checked

  · exact kid01_part701_checked

  · exact kid01_part707_checked

  · exact kid01_part713_checked

  · exact kid01_part696_checked

  · exact kid01_part702_checked

  · exact kid01_part708_checked

  · exact kid01_part714_checked

  · exact kid01_part697_checked

  · exact kid01_part703_checked

  · exact kid01_part709_checked

  · exact kid01_part715_checked

  · exact kid01_part698_checked

  · exact kid01_part704_checked

  · exact kid01_part710_checked

  · exact kid01_part716_checked

def kid01_part718 : Audit := .split 12 (0,true) (byMove [
.cycle 0 28 false (4),
.last 30 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 31 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.last 18 (5,false),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 6 14 true (0),
.last 13 (5,false),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 0 17 true (0),
.last 18 (5,false),
.cycle 6 12 true (0),
.cycle 20 1 false (0),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part718_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part718) = true := by rfl

def kid01_part719 : Audit := .split 13 (5,false) (byMove [
.cycle 20 1 false (-2),
.cycle 12 8 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (-1),
.cycle 6 26 false (4),
.cycle 12 4 true (-1),
.cycle 12 4 true (-1),
.cycle 16 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 4 false (1),
.cycle 21 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 21 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 6 27 false (4)
])
theorem kid01_part719_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part719) = true := by rfl

def kid01_part720 : Audit := .cycle 14 1 false (0)
theorem kid01_part720_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part720) = true := by rfl

def kid01_part721 : Audit := .split 15 (5,false) (byMove [
.cycle 24 1 false (-2),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 14 2 true (-1),
.cycle 17 1 false (-1),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.cycle 18 1 false (0),
.cycle 20 1 false (-2),
.cycle 11 6 false (1),
.cycle 23 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 23 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 11 5 false (1),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 18 1 false (-2)
])
theorem kid01_part721_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part721) = true := by rfl

def kid01_part722 : Audit := .split 15 (5,false) (byMove [
.cycle 24 1 false (-2),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 14 2 true (-1),
.cycle 16 12 false (1),
.cycle 13 4 true (-1),
.cycle 12 4 true (-1),
.cycle 18 1 false (0),
.cycle 20 1 false (-2),
.cycle 11 6 false (1),
.cycle 23 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 23 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 11 5 false (1),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 16 12 false (0)
])
theorem kid01_part722_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part722) = true := by rfl

def kid01_part723 : Audit := .cycle 14 1 false (0)
theorem kid01_part723_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part723) = true := by rfl

def kid01_part724 : Audit := .cycle 6 14 true (0)
theorem kid01_part724_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part724) = true := by rfl

def kid01_part725 : Audit := .cycle 1 13 true (1)
theorem kid01_part725_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part725) = true := by rfl

def kid01_part726 : Audit := .split 16 (5,false) (byMove [
.cycle 6 20 true (1),
.cycle 26 1 false (0),
.cycle 6 16 true (0),
.cycle 24 1 false (0),
.cycle 6 21 false (4),
.cycle 20 1 false (0),
.last 17 (0,true),
.cycle 15 2 true (2),
.cycle 6 22 true (0),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 6 18 true (0),
.cycle 28 1 false (2),
.cycle 6 22 true (1),
.cycle 6 22 true (0),
.cycle 6 14 true (0),
.cycle 6 27 false (4),
.cycle 20 1 false (0),
.last 17 (0,true),
.cycle 6 18 true (0),
.cycle 6 18 true (1),
.cycle 6 20 true (0),
.cycle 6 20 true (0),
.cycle 6 21 true (0)
])
theorem kid01_part726_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part726) = true := by rfl

def kid01_part727 : Audit := .cycle 6 10 true (0)
theorem kid01_part727_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part727) = true := by rfl

def kid01_part728 : Audit := .split 18 (5,false) (byMove [
.last 19 (0,true),
.cycle 22 1 false (0),
.cycle 11 8 true (1),
.cycle 24 1 false (0),
.cycle 24 1 false (0),
.cycle 6 22 true (0),
.last 19 (0,true),
.cycle 17 2 true (2),
.cycle 1 20 true (1),
.cycle 15 4 true (2),
.cycle 16 4 true (2),
.cycle 2 18 true (1),
.last 19 (0,true),
.cycle 22 1 false (0),
.cycle 6 24 true (0),
.cycle 5 14 true (1),
.cycle 6 14 true (1),
.cycle 6 28 true (0),
.last 19 (0,true),
.cycle 9 10 true (1),
.cycle 1 20 true (1),
.cycle 8 12 true (1),
.cycle 7 12 true (1),
.cycle 1 21 true (1)
])
theorem kid01_part728_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part728) = true := by rfl

def kid01_part729 : Audit := .split 12 (5,false) (byMove [
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 6 12 true (0),
.cycle 20 1 false (0),
.cycle 6 17 false (4),
.cycle 16 1 false (0),
.last 13 (0,true),
.cycle 12 2 true (2),
.cycle 6 21 true (0),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 6 14 true (0),
.cycle 22 1 false (0),
.cycle 2 14 true (1),
.cycle 6 18 true (0),
.cycle 6 10 true (0),
.cycle 6 23 false (4),
.cycle 16 1 false (0),
.last 13 (0,true),
.cycle 6 14 true (0),
.cycle 2 13 true (1),
.cycle 6 16 true (0),
.cycle 6 16 true (0),
.cycle 15 1 true (3)
])
theorem kid01_part729_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part729) = true := by rfl

def kid01_part730 : Audit := .split 12 (0,true) (byMove [
.last 24 (5,false),
.last 18 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 14 false (4),
.last 13 (5,false),
.cycle 18 1 false (2),
.last 14 (5,false),
.cycle 18 1 false (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 15 1 false (1),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 20 1 false (0),
.cycle 13 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,false),
.cycle 9 6 true (0),
.cycle 16 1 false (0),
.cycle 11 2 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 19 1 false (-1)
])
theorem kid01_part730_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part730) = true := by rfl

def kid01_part731 : Audit := .split 13 (5,false) (byMove [
.cycle 20 1 false (-2),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 31 1 false (-3),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (-1),
.cycle 11 5 false (1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 4 false (1),
.cycle 11 12 false (2),
.cycle 14 1 false (-2),
.cycle 29 1 false (-3),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 11 10 false (2),
.cycle 11 10 false (2),
.cycle 11 6 false (1)
])
theorem kid01_part731_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part731) = true := by rfl

def kid01_part732 : Audit := .cycle 20 1 false (0)
theorem kid01_part732_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part732) = true := by rfl

def kid01_part733 : Audit := .cycle 18 1 false (0)
theorem kid01_part733_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part733) = true := by rfl

def kid01_part734 : Audit := .cycle 18 1 false (0)
theorem kid01_part734_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part734) = true := by rfl

def kid01_part735 : Audit := .cycle 14 1 false (0)
theorem kid01_part735_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part735) = true := by rfl

def kid01_part736 : Audit := .cycle 9 4 true (1)
theorem kid01_part736_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part736) = true := by rfl

def kid01_part737 : Audit := .cycle 1 13 true (1)
theorem kid01_part737_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part737) = true := by rfl

def kid01_part738 : Audit := .split 16 (5,false) (byMove [
.last 17 (0,true),
.cycle 20 1 false (0),
.cycle 11 6 true (1),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 6 18 true (0),
.last 17 (0,true),
.cycle 15 2 true (2),
.cycle 2 16 true (1),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 2 16 true (1),
.last 17 (0,true),
.cycle 20 1 false (0),
.cycle 2 18 true (1),
.cycle 5 12 true (1),
.cycle 6 12 true (1),
.cycle 6 24 true (0),
.last 17 (0,true),
.cycle 9 8 true (1),
.cycle 2 16 true (1),
.cycle 8 10 true (1),
.cycle 7 10 true (1),
.cycle 2 17 true (1)
])
theorem kid01_part738_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part738) = true := by rfl

def kid01_part739 : Audit := .cycle 4 8 true (1)
theorem kid01_part739_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part739) = true := by rfl

def kid01_part740 : Audit := .cycle 16 1 false (0)
theorem kid01_part740_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part740) = true := by rfl

def kid01_part741 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 16 1 false (0),
.cycle 11 2 true (1),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.last 13 (0,true),
.cycle 12 2 true (2),
.cycle 6 15 true (1),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 2 12 true (1),
.last 13 (0,true),
.cycle 16 1 false (0),
.cycle 10 4 true (1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 18 1 false (0),
.last 13 (0,true),
.cycle 9 4 true (1),
.cycle 2 13 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.cycle 15 1 true (3)
])
theorem kid01_part741_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part741) = true := by rfl

def kid01_part717 : Audit := .split 11 (2,true) (byMove [(kid01_part718),(kid01_part719),(kid01_part720),(kid01_part721),(kid01_part722),(kid01_part723),(kid01_part724),(kid01_part725),(kid01_part726),(kid01_part727),(kid01_part728),(kid01_part729),(kid01_part730),(kid01_part731),(kid01_part732),(kid01_part733),(kid01_part734),(kid01_part735),(kid01_part736),(kid01_part737),(kid01_part738),(kid01_part739),(kid01_part740),(kid01_part741)])

theorem kid01_part717_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part717) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part718),(kid01_part719),(kid01_part720),(kid01_part721),(kid01_part722),(kid01_part723),(kid01_part724),(kid01_part725),(kid01_part726),(kid01_part727),(kid01_part728),(kid01_part729),(kid01_part730),(kid01_part731),(kid01_part732),(kid01_part733),(kid01_part734),(kid01_part735),(kid01_part736),(kid01_part737),(kid01_part738),(kid01_part739),(kid01_part740),(kid01_part741)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part718_checked

  · exact kid01_part724_checked

  · exact kid01_part730_checked

  · exact kid01_part736_checked

  · exact kid01_part719_checked

  · exact kid01_part725_checked

  · exact kid01_part731_checked

  · exact kid01_part737_checked

  · exact kid01_part720_checked

  · exact kid01_part726_checked

  · exact kid01_part732_checked

  · exact kid01_part738_checked

  · exact kid01_part721_checked

  · exact kid01_part727_checked

  · exact kid01_part733_checked

  · exact kid01_part739_checked

  · exact kid01_part722_checked

  · exact kid01_part728_checked

  · exact kid01_part734_checked

  · exact kid01_part740_checked

  · exact kid01_part723_checked

  · exact kid01_part729_checked

  · exact kid01_part735_checked

  · exact kid01_part741_checked

def kid01_part742 : Audit := .cycle 15 1 false (-1)
theorem kid01_part742_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part742) = true := by rfl

def kid01_part743 : Audit := .cycle 6 16 false (4)
theorem kid01_part743_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part743) = true := by rfl

def kid01_part744 : Audit := .split 13 (5,false) (byMove [
.cycle 0 14 false (4),
.cycle 11 12 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 11 13 false (1),
.cycle 13 1 false (-1),
.split 21 (0,true) (byMove [
.far false 7 ⟨0,[0, 5, 0, 5, 2, 2, 2, 4, 1, 3, 2, 4, 2, 2],[2147483648, 4294967296, 8, 272629760, 32768, 1, 2147483648, 4294967296, 8, 268435456, 32768, 1, 8192, 16384, 32768, 272695296, 4398319239680, 4096, 33554432, 67108864, 32768, 268435456, 4398046511104, 4096, 524288, 1048576, 512, 4194304, 512, 64, 33554432, 67108864, 32768, 268435456, 512, 4096, 8192, 16384, 32768, 0, 0, 4096, 4398046511104],[67108864, 67108864, 4398046511104, 17179869184, 17179869184, 2147483648, 67108864, 67108864, 4398046511104, 17179869184, 17179869184, 2147483648, 4398320304640, 4415500173824, 4398046511104, 65536, 65536, 4398319264256, 512, 17179869184, 4398046511104, 268435456, 268435456, 268435456, 268435456, 4398050705408, 4398046511104, 4194304, 4194304, 512, 512, 0, 4398046511104, 268435456, 268435456, 67108864, 0, 0, 4398046511104, 65536, 65536, 0, 4398046511104],7118016476574⟩,
.cycle 27 16 true (-1),
.cycle 2 20 true (-1),
.last 32 (2,true),
.cycle 23 4 true (-1),
.cycle 0 23 true (-1),
.cycle 0 22 true (-1),
.last 36 (2,true),
.far false 8 ⟨0,[0, 6, 0, 6, 0, 6, 2, 3, 4, 4, 1, 7, 2, 5, 2, 3],[137438953472, 274877906944, 8, 4194304, 32768, 1, 137438953472, 274877906944, 8, 4194304, 32768, 1, 137438953472, 274877906944, 8, 70368748371968, 33280, 1, 524288, 1048576, 32768, 4194304, 8, 4096, 33554432, 67108864, 134217728, 268435456, 281475110928384, 16777216, 8796093022208, 17592186044416, 512, 70368744177664, 0, 64, 2147483648, 4294967296, 32768, 17179869184, 8, 4096, 524288, 1048576, 32768, 4194304, 281474976710656, 4096, 281474976710656],[4, 4, 281474976710656, 1099511627776, 1099511627776, 137438953472, 4, 4, 281474976710656, 1099511627776, 1099511627776, 137438953472, 4, 4, 281474976710656, 1099511627776, 1099511627776, 137438953472, 16384, 1099515822080, 281474976710656, 4194304, 4194304, 4194312, 67108864, 281475312254976, 281474976710656, 268435456, 268435456, 281475480027136, 256, 281474976710656, 281474976710656, 70368744177664, 70368744177664, 512, 16384, 0, 281474976710656, 17179869184, 17179869184, 4294967296, 16384, 1099511627776, 281474976710656, 4194304, 4194304, 4194304, 281474976710656],382986513917074⟩,
.cycle 23 16 true (-1),
.last 37 (2,true),
.cycle 0 23 true (-1),
.cycle 9 14 true (-1),
.last 23 (2,true),
.cycle 16 6 true (2),
.cycle 4 18 true (-1),
.cycle 23 4 true (-1),
.cycle 20 2 true (2),
.cycle 28 16 true (2),
.cycle 1 21 true (-1),
.last 35 (2,true),
.cycle 26 4 true (2),
.cycle 18 4 true (2),
.cycle 0 23 true (-1)
]),
.cycle 6 14 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 6 28 false (4),
.cycle 18 1 true (2),
.cycle 12 4 false (0),
.split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 18 1 false (-2),
.cycle 13 6 false (-1),
.cycle 13 6 false (-1),
.cycle 12 4 false (0),
.last 30 (0,true),
.cycle 29 6 false (-1),
.cycle 6 16 false (4),
.cycle 11 12 false (1),
.cycle 1 16 false (4),
.cycle 9 18 false (3),
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 12 10 false (0),
.cycle 12 8 false (0),
.cycle 12 8 false (0),
.cycle 12 4 false (0),
.cycle 39 16 false (1),
.cycle 27 16 false (1),
.cycle 2 14 false (4),
.cycle 11 10 false (1),
.cycle 12 6 false (0),
.cycle 12 6 false (0)
]),
.cycle 12 12 false (0),
.cycle 14 1 false (-2),
.cycle 11 15 false (1),
.cycle 13 1 false (-1),
.split 21 (0,true) (byMove [
.cycle 0 26 false (4),
.cycle 9 13 false (4),
.last 22 (2,true),
.cycle 8 15 false (4),
.cycle 7 15 false (4),
.cycle 22 32 false (3),
.cycle 0 22 true (-1),
.last 36 (2,true),
.cycle 33 32 false (3),
.cycle 25 32 false (5),
.cycle 33 32 false (3),
.cycle 53 32 false (3),
.last 37 (2,true),
.cycle 37 32 false (3),
.last 22 (2,true),
.cycle 23 32 false (4),
.cycle 22 32 false (4),
.cycle 22 32 false (4),
.cycle 35 32 false (3),
.cycle 33 32 false (3),
.cycle 31 32 false (3),
.cycle 24 32 false (5),
.cycle 22 32 false (4),
.cycle 37 32 false (3)
]),
.cycle 1 28 false (4),
.cycle 6 24 false (4),
.cycle 11 16 false (1),
.cycle 12 8 false (0),
.cycle 22 1 true (-2)
])
theorem kid01_part744_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part744) = true := by rfl

def kid01_part746 : Audit := .cycle 0 12 true (0)
theorem kid01_part746_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part746) = true := by rfl

def kid01_part747 : Audit := .cycle 1 11 true (1)
theorem kid01_part747_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part747) = true := by rfl

def kid01_part748 : Audit := .cycle 2 10 true (1)
theorem kid01_part748_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part748) = true := by rfl

def kid01_part749 : Audit := .cycle 26 1 false (0)
theorem kid01_part749_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part749) = true := by rfl

def kid01_part750 : Audit := .split 30 (5,false) (byMove [
.last 33 (2,true),
.cycle 29 8 false (0),
.cycle 32 1 false (-2),
.cycle 31 1 false (-3),
.cycle 6 32 false (4),
.cycle 30 1 false (-2),
.cycle 15 16 false (2),
.cycle 29 2 true (-2),
.last 31 (2,true),
.cycle 28 4 true (-2),
.cycle 28 4 true (-2),
.cycle 0 32 true (-2),
.cycle 6 36 false (4),
.last 32 (2,true),
.cycle 12 22 false (2),
.cycle 31 1 false (-3),
.cycle 1 40 false (4),
.cycle 30 1 false (-2),
.cycle 28 5 false (0),
.cycle 13 18 false (2),
.last 31 (2,true),
.cycle 12 20 false (2),
.cycle 12 20 false (2),
.cycle 1 48 false (4)
])
theorem kid01_part750_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part750) = true := by rfl

def kid01_part751 : Audit := .split 12 (5,false) (byMove [
.cycle 0 15 true (0),
.cycle 28 8 false (0),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 37 false (4),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.cycle 15 5 false (2),
.last 18 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 13 22 false (3),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 18 9 false (2),
.cycle 12 1 true (2)
])
theorem kid01_part751_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part751) = true := by rfl

def kid01_part752 : Audit := .cycle 0 12 true (0)
theorem kid01_part752_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part752) = true := by rfl

def kid01_part753 : Audit := .cycle 1 11 true (1)
theorem kid01_part753_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part753) = true := by rfl

def kid01_part754 : Audit := .cycle 6 14 true (1)
theorem kid01_part754_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part754) = true := by rfl

def kid01_part755 : Audit := .cycle 6 11 true (1)
theorem kid01_part755_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part755) = true := by rfl

def kid01_part756 : Audit := .cycle 1 12 true (1)
theorem kid01_part756_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part756) = true := by rfl

def kid01_part757 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 7 13 true (2),
.cycle 6 11 true (1),
.cycle 6 15 true (2),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 9 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part757_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part757) = true := by rfl

def kid01_part758 : Audit := .cycle 9 4 true (2)
theorem kid01_part758_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part758) = true := by rfl

def kid01_part759 : Audit := .split 13 (2,true) (byMove [
.cycle 17 3 false (1),
.last 25 (5,false),
.cycle 18 1 false (0),
.last 31 (5,false),
.last 31 (5,false),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 14 (5,false),
.cycle 17 3 false (1),
.last 25 (5,false),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.last 14 (5,false)
])
theorem kid01_part759_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part759) = true := by rfl

def kid01_part760 : Audit := .split 16 (5,false) (byMove [
.last 18 (2,true),
.cycle 23 8 false (2),
.last 17 (2,true),
.cycle 27 1 false (-1),
.cycle 6 28 false (4),
.last 31 (2,true),
.cycle 11 6 true (2),
.cycle 15 2 true (2),
.last 17 (2,true),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 0 18 true (0),
.last 18 (2,true),
.last 36 (2,true),
.last 17 (2,true),
.cycle 5 12 true (1),
.cycle 6 12 true (1),
.cycle 60 1 false (2),
.last 18 (2,true),
.cycle 9 8 true (2),
.last 17 (2,true),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.cycle 0 18 true (0)
])
theorem kid01_part760_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part760) = true := by rfl

def kid01_part761 : Audit := .cycle 4 8 true (1)
theorem kid01_part761_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part761) = true := by rfl

def kid01_part762 : Audit := .split 22 (5,false) (byMove [
.cycle 15 8 false (2),
.cycle 17 8 false (2),
.last 23 (2,true),
.cycle 27 1 false (-3),
.cycle 6 28 false (4),
.cycle 13 12 true (-1),
.cycle 15 12 false (2),
.cycle 21 2 true (0),
.last 23 (2,true),
.cycle 19 4 true (0),
.cycle 20 4 true (0),
.cycle 0 36 true (-1),
.cycle 20 14 false (2),
.last 26 (2,true),
.last 23 (2,true),
.cycle 33 1 false (-3),
.cycle 6 44 false (4),
.cycle 45 1 false (-3),
.cycle 12 24 false (2),
.cycle 13 16 false (2),
.last 23 (2,true),
.cycle 12 20 false (2),
.cycle 12 20 false (2),
.cycle 0 36 true (-1)
])
theorem kid01_part762_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part762) = true := by rfl

def kid01_part763 : Audit := .split 12 (5,false) (byMove [
.last 19 (2,true),
.cycle 16 8 false (2),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 23 (2,true),
.cycle 11 2 true (2),
.cycle 12 2 true (2),
.last 13 (2,true),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 0 14 true (0),
.cycle 14 5 false (1),
.last 18 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 18 1 false (0),
.cycle 10 4 true (2),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0)
])
theorem kid01_part763_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part763) = true := by rfl

def kid01_part764 : Audit := .cycle 0 12 true (0)
theorem kid01_part764_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part764) = true := by rfl

def kid01_part765 : Audit := .cycle 1 11 true (1)
theorem kid01_part765_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part765) = true := by rfl

def kid01_part766 : Audit := .cycle 2 10 true (1)
theorem kid01_part766_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part766) = true := by rfl

def kid01_part767 : Audit := .cycle 7 7 true (2)
theorem kid01_part767_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part767) = true := by rfl

def kid01_part768 : Audit := .split 14 (5,false) (byMove [
.last 25 (2,true),
.cycle 19 8 false (2),
.last 15 (2,true),
.cycle 23 1 false (-1),
.cycle 6 24 false (4),
.last 27 (2,true),
.cycle 11 4 true (2),
.cycle 13 2 true (2),
.last 15 (2,true),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 0 16 true (0),
.cycle 6 10 true (1),
.last 30 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (1),
.cycle 46 1 false (2),
.cycle 8 8 true (2),
.cycle 9 6 true (2),
.last 15 (2,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 0 16 true (0)
])
theorem kid01_part768_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part768) = true := by rfl

def kid01_part769 : Audit := .split 12 (5,false) (byMove [
.cycle 11 2 true (3),
.cycle 18 8 false (2),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 6 28 false (4),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part769_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part769) = true := by rfl

def kid01_part745 : Audit := .split 11 (0,true) (byMove [(kid01_part746),(kid01_part747),(kid01_part748),(kid01_part749),(kid01_part750),(kid01_part751),(kid01_part752),(kid01_part753),(kid01_part754),(kid01_part755),(kid01_part756),(kid01_part757),(kid01_part758),(kid01_part759),(kid01_part760),(kid01_part761),(kid01_part762),(kid01_part763),(kid01_part764),(kid01_part765),(kid01_part766),(kid01_part767),(kid01_part768),(kid01_part769)])

theorem kid01_part745_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part745) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some mv)) (byMove [(kid01_part746),(kid01_part747),(kid01_part748),(kid01_part749),(kid01_part750),(kid01_part751),(kid01_part752),(kid01_part753),(kid01_part754),(kid01_part755),(kid01_part756),(kid01_part757),(kid01_part758),(kid01_part759),(kid01_part760),(kid01_part761),(kid01_part762),(kid01_part763),(kid01_part764),(kid01_part765),(kid01_part766),(kid01_part767),(kid01_part768),(kid01_part769)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part746_checked

  · exact kid01_part752_checked

  · exact kid01_part758_checked

  · exact kid01_part764_checked

  · exact kid01_part747_checked

  · exact kid01_part753_checked

  · exact kid01_part759_checked

  · exact kid01_part765_checked

  · exact kid01_part748_checked

  · exact kid01_part754_checked

  · exact kid01_part760_checked

  · exact kid01_part766_checked

  · exact kid01_part749_checked

  · exact kid01_part755_checked

  · exact kid01_part761_checked

  · exact kid01_part767_checked

  · exact kid01_part750_checked

  · exact kid01_part756_checked

  · exact kid01_part762_checked

  · exact kid01_part768_checked

  · exact kid01_part751_checked

  · exact kid01_part757_checked

  · exact kid01_part763_checked

  · exact kid01_part769_checked

def kid01_part771 : Audit := .split 13 (0,true) (byMove [
.cycle 0 32 false (4),
.last 18 (2,true),
.last 14 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.cycle 0 49 false (4),
.last 21 (2,true),
.last 15 (2,true),
.last 21 (2,true),
.cycle 6 12 true (0),
.cycle 11 8 true (1),
.last 17 (2,true),
.last 22 (2,true),
.last 18 (2,true),
.last 14 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.last 19 (2,true),
.cycle 9 6 true (1),
.last 15 (2,true),
.cycle 11 6 true (1),
.cycle 4 10 true (1),
.last 21 (2,true),
.cycle 12 2 true (1)
])
theorem kid01_part771_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part771) = true := by rfl

def kid01_part772 : Audit := .cycle 15 8 false (2)
theorem kid01_part772_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part772) = true := by rfl

def kid01_part773 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 24 1 false (0),
.cycle 6 18 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (0),
.cycle 6 12 true (0),
.cycle 11 8 true (1),
.cycle 6 14 true (0),
.last 14 (0,true),
.cycle 17 1 false (-1),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 18 1 false (0),
.cycle 9 6 true (1),
.cycle 1 15 true (1),
.cycle 11 6 true (1),
.cycle 4 10 true (1),
.cycle 20 1 false (0),
.cycle 12 2 true (1)
])
theorem kid01_part773_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part773) = true := by rfl

def kid01_part774 : Audit := .cycle 19 1 false (-1)
theorem kid01_part774_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part774) = true := by rfl

def kid01_part775 : Audit := .cycle 6 20 false (4)
theorem kid01_part775_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part775) = true := by rfl

def kid01_part776 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 22 1 false (0),
.cycle 33 1 false (1),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (1),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 1 18 true (1),
.last 16 (0,true),
.cycle 22 1 false (0),
.cycle 44 1 false (2),
.cycle 40 1 false (2),
.cycle 40 1 false (2),
.cycle 32 1 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (1),
.cycle 36 1 false (2),
.cycle 1 17 true (1)
])
theorem kid01_part776_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part776) = true := by rfl

def kid01_part777 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 17 18 false (2),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 9 6 true (2),
.last 15 (2,true),
.cycle 11 6 true (2),
.cycle 4 10 true (1),
.cycle 17 12 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 11 4 true (2),
.cycle 0 15 true (0)
])
theorem kid01_part777_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part777) = true := by rfl

def kid01_part778 : Audit := .cycle 11 2 true (2)
theorem kid01_part778_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part778) = true := by rfl

def kid01_part779 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 17 18 false (2),
.cycle 6 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 1 14 true (1),
.cycle 6 19 true (1),
.cycle 9 6 true (2),
.cycle 25 5 false (1),
.cycle 11 6 true (2),
.cycle 4 10 true (1),
.cycle 17 12 false (2),
.cycle 12 2 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 11 4 true (2),
.cycle 6 15 true (2)
])
theorem kid01_part779_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part779) = true := by rfl

def kid01_part780 : Audit := .cycle 11 4 true (2)
theorem kid01_part780_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part780) = true := by rfl

def kid01_part781 : Audit := .cycle 11 4 true (2)
theorem kid01_part781_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part781) = true := by rfl

def kid01_part782 : Audit := .cycle 1 13 true (1)
theorem kid01_part782_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part782) = true := by rfl

def kid01_part783 : Audit := .split 13 (0,true) (byMove [
.last 46 (2,true),
.cycle 14 5 false (0),
.last 14 (2,true),
.cycle 16 5 false (0),
.cycle 16 5 false (0),
.last 16 (2,true),
.cycle 0 16 true (0),
.cycle 17 5 false (1),
.last 14 (2,true),
.cycle 39 5 false (3),
.cycle 39 5 false (3),
.cycle 23 5 false (2),
.cycle 15 5 false (0),
.cycle 14 5 false (0),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 14 5 false (1),
.cycle 0 16 true (0),
.cycle 19 5 false (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1)
])
theorem kid01_part783_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part783) = true := by rfl

def kid01_part784 : Audit := .split 18 (2,true) (byMove [
.last 19 (0,true),
.cycle 15 4 false (1),
.cycle 21 1 false (-1),
.cycle 15 6 false (1),
.cycle 15 6 false (1),
.cycle 15 26 true (-1),
.last 19 (0,true),
.cycle 15 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 15 27 true (-1),
.last 19 (0,true),
.cycle 15 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 14 5 false (1),
.last 19 (0,true),
.cycle 15 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 10 9 false (3)
])
theorem kid01_part784_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part784) = true := by rfl

def kid01_part785 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 14 8 true (-2),
.cycle 16 1 false (0),
.cycle 16 8 true (-2),
.cycle 16 8 true (-2),
.cycle 38 8 true (0),
.last 14 (0,true),
.cycle 6 16 true (-1),
.cycle 6 20 true (0),
.cycle 14 8 true (1),
.cycle 15 8 true (1),
.cycle 14 8 true (1),
.last 14 (0,true),
.cycle 14 16 true (-2),
.cycle 6 12 true (-1),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 6 14 true (-1),
.last 14 (0,true),
.cycle 6 20 true (-1),
.cycle 2 14 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1)
])
theorem kid01_part785_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part785) = true := by rfl

def kid01_part786 : Audit := .cycle 5 8 true (1)
theorem kid01_part786_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part786) = true := by rfl

def kid01_part787 : Audit := .cycle 6 8 true (1)
theorem kid01_part787_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part787) = true := by rfl

def kid01_part788 : Audit := .cycle 18 1 false (0)
theorem kid01_part788_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part788) = true := by rfl

def kid01_part789 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 21 3 false (1),
.last 14 (2,true),
.cycle 25 5 false (1),
.cycle 25 5 false (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 15 7 false (1),
.cycle 21 3 false (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 0 15 true (0)
])
theorem kid01_part789_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part789) = true := by rfl

def kid01_part790 : Audit := .cycle 9 4 true (2)
theorem kid01_part790_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part790) = true := by rfl

def kid01_part791 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 21 3 false (1),
.cycle 18 1 false (0),
.cycle 25 5 false (1),
.cycle 25 5 false (1),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 14 (0,true),
.cycle 21 3 false (1),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 2 13 true (1)
])
theorem kid01_part791_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part791) = true := by rfl

def kid01_part792 : Audit := .cycle 8 6 true (2)
theorem kid01_part792_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part792) = true := by rfl

def kid01_part793 : Audit := .cycle 7 6 true (2)
theorem kid01_part793_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part793) = true := by rfl

def kid01_part794 : Audit := .cycle 1 13 true (1)
theorem kid01_part794_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part794) = true := by rfl

def kid01_part770 : Audit := .split 12 (5,false) (byMove [(kid01_part771),(kid01_part772),(kid01_part773),(kid01_part774),(kid01_part775),(kid01_part776),(kid01_part777),(kid01_part778),(kid01_part779),(kid01_part780),(kid01_part781),(kid01_part782),(kid01_part783),(kid01_part784),(kid01_part785),(kid01_part786),(kid01_part787),(kid01_part788),(kid01_part789),(kid01_part790),(kid01_part791),(kid01_part792),(kid01_part793),(kid01_part794)])

theorem kid01_part770_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part770) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) 12 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (5,false) (some mv)) (byMove [(kid01_part771),(kid01_part772),(kid01_part773),(kid01_part774),(kid01_part775),(kid01_part776),(kid01_part777),(kid01_part778),(kid01_part779),(kid01_part780),(kid01_part781),(kid01_part782),(kid01_part783),(kid01_part784),(kid01_part785),(kid01_part786),(kid01_part787),(kid01_part788),(kid01_part789),(kid01_part790),(kid01_part791),(kid01_part792),(kid01_part793),(kid01_part794)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid01_part774_checked

  · exact kid01_part780_checked

  · exact kid01_part786_checked

  · exact kid01_part792_checked

  · exact kid01_part775_checked

  · exact kid01_part781_checked

  · exact kid01_part787_checked

  · exact kid01_part793_checked

  · exact kid01_part776_checked

  · exact kid01_part782_checked

  · exact kid01_part788_checked

  · exact kid01_part794_checked

def kid01_part796 : Audit := .cycle 0 12 true (0)
theorem kid01_part796_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part796) = true := by rfl

def kid01_part797 : Audit := .cycle 1 11 true (1)
theorem kid01_part797_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part797) = true := by rfl

def kid01_part798 : Audit := .cycle 2 10 true (1)
theorem kid01_part798_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part798) = true := by rfl

def kid01_part799 : Audit := .cycle 26 1 false (0)
theorem kid01_part799_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part799) = true := by rfl

def kid01_part800 : Audit := .split 30 (5,false) (byMove [
.cycle 12 23 false (2),
.cycle 29 8 false (0),
.cycle 32 1 false (-2),
.cycle 31 1 false (-3),
.cycle 6 32 false (4),
.cycle 30 1 false (-2),
.last 31 (0,true),
.cycle 29 2 true (-2),
.cycle 15 16 false (2),
.cycle 28 4 true (-2),
.cycle 28 4 true (-2),
.cycle 33 1 false (1),
.cycle 6 36 false (4),
.cycle 28 6 false (0),
.cycle 12 22 false (2),
.cycle 31 1 false (-3),
.cycle 1 40 false (4),
.cycle 30 1 false (-2),
.last 31 (0,true),
.cycle 13 18 false (2),
.cycle 28 5 false (0),
.cycle 12 20 false (2),
.cycle 12 20 false (2),
.cycle 6 32 false (4)
])
theorem kid01_part800_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part800) = true := by rfl

def kid01_part801 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 28 8 false (0),
.cycle 16 1 false (2),
.cycle 19 1 false (-1),
.cycle 6 37 false (4),
.cycle 6 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (2),
.last 13 (0,true),
.cycle 21 1 false (1),
.cycle 15 13 false (3),
.cycle 27 1 false (-1),
.cycle 13 22 false (3),
.cycle 18 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 18 9 false (2),
.cycle 12 1 true (2)
])
theorem kid01_part801_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part801) = true := by rfl

def kid01_part802 : Audit := .cycle 0 12 true (0)
theorem kid01_part802_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part802) = true := by rfl

def kid01_part803 : Audit := .cycle 1 11 true (1)
theorem kid01_part803_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part803) = true := by rfl

def kid01_part804 : Audit := .cycle 6 14 true (1)
theorem kid01_part804_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part804) = true := by rfl

def kid01_part805 : Audit := .cycle 6 11 true (1)
theorem kid01_part805_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part805) = true := by rfl

def kid01_part806 : Audit := .cycle 1 12 true (1)
theorem kid01_part806_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part806) = true := by rfl

def kid01_part807 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 6 16 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 11 3 true (3),
.cycle 7 13 true (2),
.cycle 6 11 true (1),
.cycle 6 15 true (2),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 9 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part807_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part807) = true := by rfl

def kid01_part808 : Audit := .cycle 9 4 true (2)
theorem kid01_part808_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part808) = true := by rfl

def kid01_part809 : Audit := .split 25 (5,false) (byMove [
.cycle 17 10 false (2),
.cycle 48 8 false (0),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 24 2 true (-1),
.cycle 21 5 false (1),
.cycle 6 22 true (-1),
.cycle 6 22 true (-1),
.cycle 20 6 true (-1),
.cycle 19 8 false (1),
.cycle 22 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 26 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 19 7 false (1),
.cycle 23 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 15 11 false (2)
])
theorem kid01_part809_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part809) = true := by rfl

def kid01_part810 : Audit := .split 16 (5,false) (byMove [
.last 17 (0,true),
.cycle 23 8 false (2),
.cycle 32 1 false (0),
.cycle 27 1 false (-1),
.cycle 6 28 false (4),
.cycle 26 1 false (2),
.last 17 (0,true),
.cycle 15 2 true (2),
.cycle 11 6 true (2),
.cycle 13 4 true (2),
.cycle 14 4 true (2),
.cycle 6 20 true (1),
.last 17 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 6 16 true (-1),
.cycle 5 12 true (1),
.cycle 6 12 true (1),
.cycle 60 1 false (2),
.last 17 (0,true),
.cycle 9 8 true (2),
.cycle 6 18 true (-1),
.cycle 8 10 true (2),
.cycle 7 10 true (2),
.cycle 6 18 true (2)
])
theorem kid01_part810_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part810) = true := by rfl

def kid01_part811 : Audit := .cycle 4 8 true (1)
theorem kid01_part811_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part811) = true := by rfl

def kid01_part812 : Audit := .split 22 (5,false) (byMove [
.last 23 (0,true),
.cycle 17 8 false (2),
.cycle 15 8 false (2),
.cycle 27 1 false (-3),
.cycle 6 28 false (4),
.cycle 28 1 false (0),
.last 23 (0,true),
.cycle 21 2 true (0),
.cycle 15 12 false (2),
.cycle 19 4 true (0),
.cycle 20 4 true (0),
.cycle 79 1 false (7),
.last 23 (0,true),
.cycle 36 12 false (0),
.cycle 20 14 false (2),
.cycle 33 1 false (-3),
.cycle 6 44 false (4),
.cycle 45 1 false (-3),
.last 23 (0,true),
.cycle 13 16 false (2),
.cycle 12 24 false (2),
.cycle 12 20 false (2),
.cycle 12 20 false (2),
.cycle 6 30 true (-1)
])
theorem kid01_part812_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part812) = true := by rfl

def kid01_part813 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 16 8 false (2),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 22 1 false (2),
.last 13 (0,true),
.cycle 12 2 true (2),
.cycle 11 2 true (2),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 6 16 true (1),
.last 13 (0,true),
.cycle 14 5 false (1),
.cycle 6 14 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 18 1 false (0),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 10 4 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 6 14 true (2)
])
theorem kid01_part813_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part813) = true := by rfl

def kid01_part814 : Audit := .cycle 0 12 true (0)
theorem kid01_part814_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part814) = true := by rfl

def kid01_part815 : Audit := .cycle 1 11 true (1)
theorem kid01_part815_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part815) = true := by rfl

def kid01_part816 : Audit := .cycle 2 10 true (1)
theorem kid01_part816_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part816) = true := by rfl

def kid01_part817 : Audit := .cycle 7 7 true (2)
theorem kid01_part817_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part817) = true := by rfl

def kid01_part818 : Audit := .split 14 (5,false) (byMove [
.last 15 (0,true),
.cycle 19 8 false (2),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 6 24 false (4),
.cycle 24 1 false (2),
.last 15 (0,true),
.cycle 13 2 true (2),
.cycle 11 4 true (2),
.cycle 12 4 true (2),
.cycle 12 4 true (2),
.cycle 6 18 true (1),
.last 15 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 6 10 true (1),
.cycle 5 10 true (1),
.cycle 6 10 true (1),
.cycle 46 1 false (2),
.last 15 (0,true),
.cycle 9 6 true (2),
.cycle 8 8 true (2),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 6 16 true (2)
])
theorem kid01_part818_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part818) = true := by rfl

def kid01_part819 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 18 8 false (2),
.cycle 11 2 true (3),
.cycle 27 1 false (-1),
.cycle 6 28 false (4),
.cycle 6 16 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 13 (0,true),
.cycle 6 21 true (0),
.cycle 6 15 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part819_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part819) = true := by rfl

def kid01_part795 : Audit := .split 11 (2,true) (byMove [(kid01_part796),(kid01_part797),(kid01_part798),(kid01_part799),(kid01_part800),(kid01_part801),(kid01_part802),(kid01_part803),(kid01_part804),(kid01_part805),(kid01_part806),(kid01_part807),(kid01_part808),(kid01_part809),(kid01_part810),(kid01_part811),(kid01_part812),(kid01_part813),(kid01_part814),(kid01_part815),(kid01_part816),(kid01_part817),(kid01_part818),(kid01_part819)])

theorem kid01_part795_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part795) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid01_part796),(kid01_part797),(kid01_part798),(kid01_part799),(kid01_part800),(kid01_part801),(kid01_part802),(kid01_part803),(kid01_part804),(kid01_part805),(kid01_part806),(kid01_part807),(kid01_part808),(kid01_part809),(kid01_part810),(kid01_part811),(kid01_part812),(kid01_part813),(kid01_part814),(kid01_part815),(kid01_part816),(kid01_part817),(kid01_part818),(kid01_part819)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part796_checked

  · exact kid01_part802_checked

  · exact kid01_part808_checked

  · exact kid01_part814_checked

  · exact kid01_part797_checked

  · exact kid01_part803_checked

  · exact kid01_part809_checked

  · exact kid01_part815_checked

  · exact kid01_part798_checked

  · exact kid01_part804_checked

  · exact kid01_part810_checked

  · exact kid01_part816_checked

  · exact kid01_part799_checked

  · exact kid01_part805_checked

  · exact kid01_part811_checked

  · exact kid01_part817_checked

  · exact kid01_part800_checked

  · exact kid01_part806_checked

  · exact kid01_part812_checked

  · exact kid01_part818_checked

  · exact kid01_part801_checked

  · exact kid01_part807_checked

  · exact kid01_part813_checked

  · exact kid01_part819_checked

def kid01_part821 : Audit := .split 15 (0,true) (byMove [
.cycle 0 36 false (4),
.last 20 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 17 1 false (1),
.last 25 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.cycle 6 14 true (0),
.cycle 11 8 true (1),
.last 19 (2,true),
.last 31 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.last 27 (2,true),
.last 27 (2,true),
.last 23 (2,true),
.cycle 9 8 true (1),
.last 17 (2,true),
.cycle 11 6 true (1),
.cycle 4 12 true (1),
.last 25 (2,true),
.cycle 14 2 true (1)
])
theorem kid01_part821_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part821) = true := by rfl

def kid01_part822 : Audit := .cycle 19 8 false (2)
theorem kid01_part822_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part822) = true := by rfl

def kid01_part823 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 17 1 false (1),
.cycle 6 22 true (0),
.cycle 1 17 true (1),
.cycle 6 20 true (0),
.cycle 6 14 true (0),
.cycle 11 8 true (1),
.cycle 6 16 true (0),
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 28 1 false (0),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 22 1 false (0),
.cycle 9 8 true (1),
.cycle 1 17 true (1),
.cycle 11 6 true (1),
.cycle 4 12 true (1),
.cycle 24 1 false (0),
.cycle 14 2 true (1)
])
theorem kid01_part823_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part823) = true := by rfl

def kid01_part824 : Audit := .cycle 23 1 false (-1)
theorem kid01_part824_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part824) = true := by rfl

def kid01_part825 : Audit := .cycle 6 24 false (4)
theorem kid01_part825_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part825) = true := by rfl

def kid01_part826 : Audit := .cycle 6 14 true (0)
theorem kid01_part826_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part826) = true := by rfl

def kid01_part827 : Audit := .split 15 (0,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 38 1 false (0),
.cycle 20 20 false (2),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (1),
.cycle 6 15 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 9 8 true (2),
.last 17 (2,true),
.cycle 11 6 true (2),
.cycle 4 12 true (1),
.cycle 20 12 false (2),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 12 4 true (2),
.cycle 0 17 true (0)
])
theorem kid01_part827_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part827) = true := by rfl

def kid01_part828 : Audit := .cycle 13 2 true (2)
theorem kid01_part828_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part828) = true := by rfl

def kid01_part829 : Audit := .split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 38 1 false (0),
.cycle 20 20 false (2),
.cycle 6 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (1),
.cycle 6 15 true (1),
.cycle 1 16 true (1),
.cycle 6 21 true (1),
.cycle 9 8 true (2),
.cycle 61 5 false (3),
.cycle 11 6 true (2),
.cycle 4 12 true (1),
.cycle 20 12 false (2),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 12 4 true (2),
.cycle 6 17 true (2)
])
theorem kid01_part829_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part829) = true := by rfl

def kid01_part830 : Audit := .cycle 11 4 true (2)
theorem kid01_part830_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part830) = true := by rfl

def kid01_part831 : Audit := .cycle 12 4 true (2)
theorem kid01_part831_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part831) = true := by rfl

def kid01_part832 : Audit := .cycle 6 15 true (1)
theorem kid01_part832_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part832) = true := by rfl

def kid01_part833 : Audit := .split 15 (0,true) (byMove [
.cycle 20 12 true (1),
.cycle 16 12 true (-2),
.last 16 (2,true),
.cycle 16 12 true (-2),
.cycle 17 12 true (-2),
.cycle 17 1 false (1),
.cycle 0 18 true (0),
.cycle 6 20 true (-1),
.last 16 (2,true),
.cycle 16 12 true (1),
.cycle 17 12 true (1),
.cycle 16 12 true (1),
.cycle 6 16 true (-1),
.cycle 6 32 true (-2),
.last 16 (2,true),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 6 28 true (-1),
.cycle 0 18 true (0),
.cycle 16 12 true (1),
.last 16 (2,true),
.cycle 7 10 true (1),
.cycle 6 10 true (1),
.cycle 10 6 true (1)
])
theorem kid01_part833_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part833) = true := by rfl

def kid01_part834 : Audit := .split 30 (2,true) (byMove [
.last 31 (0,true),
.cycle 27 4 false (1),
.cycle 33 1 false (-1),
.cycle 27 6 false (1),
.cycle 27 6 false (1),
.cycle 32 1 false (0),
.last 31 (0,true),
.cycle 25 6 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.cycle 6 43 true (-1),
.last 31 (0,true),
.cycle 27 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.cycle 6 28 true (-1),
.last 31 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 18, 64],[64, 16, 2, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 48, 64],[64, 24, 32, 16, 16, 8, 64],64⟩
])
theorem kid01_part834_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part834) = true := by rfl

def kid01_part835 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 16 10 true (-2),
.cycle 18 1 false (0),
.cycle 16 10 true (-2),
.cycle 17 10 true (-2),
.cycle 17 1 false (1),
.last 16 (0,true),
.cycle 6 18 true (-1),
.cycle 6 22 true (0),
.cycle 16 10 true (1),
.cycle 17 10 true (1),
.cycle 16 10 true (1),
.last 16 (0,true),
.cycle 6 30 true (-2),
.cycle 6 14 true (-1),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 6 26 true (-1),
.last 16 (0,true),
.cycle 18 10 true (1),
.cycle 2 16 true (1),
.cycle 7 10 true (1),
.cycle 6 10 true (1),
.cycle 10 6 true (1)
])
theorem kid01_part835_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part835) = true := by rfl

def kid01_part836 : Audit := .cycle 5 10 true (1)
theorem kid01_part836_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part836) = true := by rfl

def kid01_part837 : Audit := .cycle 6 10 true (1)
theorem kid01_part837_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part837) = true := by rfl

def kid01_part838 : Audit := .cycle 46 1 false (2)
theorem kid01_part838_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part838) = true := by rfl

def kid01_part839 : Audit := .split 15 (0,true) (byMove [
.cycle 0 19 false (4),
.cycle 27 3 false (1),
.last 16 (2,true),
.cycle 29 5 false (2),
.cycle 30 5 false (2),
.cycle 3 14 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 6 18 true (-1),
.cycle 53 3 false (3),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 0 17 true (0)
])
theorem kid01_part839_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part839) = true := by rfl

def kid01_part840 : Audit := .cycle 9 6 true (2)
theorem kid01_part840_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part840) = true := by rfl

def kid01_part841 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 27 3 false (1),
.cycle 20 1 false (0),
.cycle 29 5 false (2),
.cycle 30 5 false (2),
.cycle 3 14 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.last 16 (0,true),
.cycle 53 3 false (3),
.cycle 6 16 true (-1),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 2 15 true (1)
])
theorem kid01_part841_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part841) = true := by rfl

def kid01_part842 : Audit := .cycle 8 8 true (2)
theorem kid01_part842_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part842) = true := by rfl

def kid01_part843 : Audit := .cycle 7 8 true (2)
theorem kid01_part843_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part843) = true := by rfl

def kid01_part844 : Audit := .cycle 3 13 true (1)
theorem kid01_part844_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part844) = true := by rfl

def kid01_part820 : Audit := .split 14 (5,false) (byMove [(kid01_part821),(kid01_part822),(kid01_part823),(kid01_part824),(kid01_part825),(kid01_part826),(kid01_part827),(kid01_part828),(kid01_part829),(kid01_part830),(kid01_part831),(kid01_part832),(kid01_part833),(kid01_part834),(kid01_part835),(kid01_part836),(kid01_part837),(kid01_part838),(kid01_part839),(kid01_part840),(kid01_part841),(kid01_part842),(kid01_part843),(kid01_part844)])

theorem kid01_part820_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part820) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) 14 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (5,false) (some mv)) (byMove [(kid01_part821),(kid01_part822),(kid01_part823),(kid01_part824),(kid01_part825),(kid01_part826),(kid01_part827),(kid01_part828),(kid01_part829),(kid01_part830),(kid01_part831),(kid01_part832),(kid01_part833),(kid01_part834),(kid01_part835),(kid01_part836),(kid01_part837),(kid01_part838),(kid01_part839),(kid01_part840),(kid01_part841),(kid01_part842),(kid01_part843),(kid01_part844)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part821_checked

  · exact kid01_part827_checked

  · exact kid01_part833_checked

  · exact kid01_part839_checked

  · exact kid01_part822_checked

  · exact kid01_part828_checked

  · exact kid01_part834_checked

  · exact kid01_part840_checked

  · exact kid01_part823_checked

  · exact kid01_part829_checked

  · exact kid01_part835_checked

  · exact kid01_part841_checked

  · exact kid01_part824_checked

  · exact kid01_part830_checked

  · exact kid01_part836_checked

  · exact kid01_part842_checked

  · exact kid01_part825_checked

  · exact kid01_part831_checked

  · exact kid01_part837_checked

  · exact kid01_part843_checked

  · exact kid01_part826_checked

  · exact kid01_part832_checked

  · exact kid01_part838_checked

  · exact kid01_part844_checked

def kid01_part846 : Audit := .split 15 (0,true) (byMove [
.cycle 0 36 false (4),
.last 20 (2,true),
.last 16 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 6 18 true (0),
.last 25 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.cycle 6 14 true (0),
.cycle 12 8 true (1),
.last 19 (2,true),
.last 31 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.last 27 (2,true),
.last 27 (2,true),
.last 23 (2,true),
.cycle 9 8 true (1),
.last 17 (2,true),
.cycle 12 6 true (1),
.cycle 4 12 true (1),
.last 25 (2,true),
.cycle 14 2 true (1)
])
theorem kid01_part846_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part846) = true := by rfl

def kid01_part847 : Audit := .cycle 19 8 false (2)
theorem kid01_part847_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part847) = true := by rfl

def kid01_part848 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 6 18 true (0),
.cycle 6 22 true (0),
.cycle 1 17 true (1),
.cycle 6 20 true (0),
.cycle 6 14 true (0),
.cycle 12 8 true (1),
.cycle 6 16 true (0),
.last 16 (0,true),
.cycle 19 1 false (-1),
.cycle 28 1 false (0),
.cycle 26 1 false (0),
.cycle 26 1 false (0),
.cycle 22 1 false (0),
.cycle 9 8 true (1),
.cycle 1 17 true (1),
.cycle 12 6 true (1),
.cycle 4 12 true (1),
.cycle 24 1 false (0),
.cycle 14 2 true (1)
])
theorem kid01_part848_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part848) = true := by rfl

def kid01_part849 : Audit := .cycle 23 1 false (-1)
theorem kid01_part849_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part849) = true := by rfl

def kid01_part850 : Audit := .cycle 6 24 false (4)
theorem kid01_part850_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part850) = true := by rfl

def kid01_part851 : Audit := .cycle 12 8 true (1)
theorem kid01_part851_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part851) = true := by rfl

def kid01_part852 : Audit := .split 15 (0,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 38 1 false (0),
.cycle 20 20 false (2),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (1),
.cycle 6 15 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 9 8 true (2),
.last 17 (2,true),
.cycle 12 6 true (2),
.cycle 4 12 true (1),
.cycle 20 12 false (2),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 12 4 true (2),
.cycle 0 17 true (0)
])
theorem kid01_part852_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part852) = true := by rfl

def kid01_part853 : Audit := .cycle 13 2 true (2)
theorem kid01_part853_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part853) = true := by rfl

def kid01_part854 : Audit := .split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 38 1 false (0),
.cycle 20 20 false (2),
.cycle 6 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (1),
.cycle 6 15 true (1),
.cycle 1 16 true (1),
.cycle 6 21 true (1),
.cycle 9 8 true (2),
.cycle 61 5 false (3),
.cycle 12 6 true (2),
.cycle 4 12 true (1),
.cycle 20 12 false (2),
.cycle 14 2 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 12 4 true (2),
.cycle 6 17 true (2)
])
theorem kid01_part854_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part854) = true := by rfl

def kid01_part855 : Audit := .cycle 12 4 true (2)
theorem kid01_part855_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part855) = true := by rfl

def kid01_part856 : Audit := .cycle 11 4 true (2)
theorem kid01_part856_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part856) = true := by rfl

def kid01_part857 : Audit := .cycle 1 16 true (1)
theorem kid01_part857_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part857) = true := by rfl

def kid01_part858 : Audit := .split 15 (0,true) (byMove [
.cycle 21 12 true (1),
.cycle 16 12 true (-2),
.last 16 (2,true),
.cycle 17 12 true (-2),
.cycle 16 12 true (-2),
.cycle 21 12 true (1),
.cycle 0 18 true (0),
.cycle 6 20 true (-1),
.last 16 (2,true),
.cycle 17 12 true (1),
.cycle 16 12 true (1),
.cycle 16 12 true (1),
.cycle 6 16 true (-1),
.cycle 6 32 true (-2),
.last 16 (2,true),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 6 28 true (-1),
.cycle 0 18 true (0),
.cycle 16 12 true (1),
.last 16 (2,true),
.cycle 7 10 true (1),
.cycle 6 10 true (1),
.cycle 10 6 true (1)
])
theorem kid01_part858_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part858) = true := by rfl

def kid01_part859 : Audit := .split 30 (2,true) (byMove [
.last 31 (0,true),
.cycle 27 4 false (1),
.cycle 33 1 false (-1),
.cycle 27 6 false (1),
.cycle 27 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 24, 16, 16, 16, 64],64⟩,
.last 31 (0,true),
.cycle 25 6 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 48, 64],[64, 16, 32, 16, 16, 16, 64],64⟩,
.last 31 (0,true),
.cycle 27 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 6 28 true (-1),
.last 31 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 18, 64],[64, 16, 2, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 48, 64],[64, 16, 32, 16, 16, 16, 64],64⟩
])
theorem kid01_part859_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part859) = true := by rfl

def kid01_part860 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 16 10 true (-2),
.cycle 18 1 false (0),
.cycle 17 10 true (-2),
.cycle 16 10 true (-2),
.cycle 19 10 true (1),
.last 16 (0,true),
.cycle 6 18 true (-1),
.cycle 6 22 true (0),
.cycle 16 10 true (1),
.cycle 17 10 true (1),
.cycle 16 10 true (1),
.last 16 (0,true),
.cycle 6 30 true (-2),
.cycle 6 14 true (-1),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 6 26 true (-1),
.last 16 (0,true),
.cycle 19 10 true (1),
.cycle 2 16 true (1),
.cycle 7 10 true (1),
.cycle 6 10 true (1),
.cycle 10 6 true (1)
])
theorem kid01_part860_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part860) = true := by rfl

def kid01_part861 : Audit := .cycle 5 10 true (1)
theorem kid01_part861_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part861) = true := by rfl

def kid01_part862 : Audit := .cycle 6 10 true (1)
theorem kid01_part862_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part862) = true := by rfl

def kid01_part863 : Audit := .cycle 46 1 false (2)
theorem kid01_part863_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part863) = true := by rfl

def kid01_part864 : Audit := .split 15 (0,true) (byMove [
.cycle 0 19 false (4),
.cycle 27 3 false (1),
.last 16 (2,true),
.cycle 30 5 false (2),
.cycle 29 5 false (2),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 0 17 true (0),
.cycle 6 18 true (-1),
.cycle 53 3 false (3),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 0 17 true (0)
])
theorem kid01_part864_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part864) = true := by rfl

def kid01_part865 : Audit := .cycle 9 6 true (2)
theorem kid01_part865_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part865) = true := by rfl

def kid01_part866 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 27 3 false (1),
.cycle 20 1 false (0),
.cycle 30 5 false (2),
.cycle 29 5 false (2),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.last 16 (0,true),
.cycle 53 3 false (3),
.cycle 6 16 true (-1),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 10 6 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 2 15 true (1)
])
theorem kid01_part866_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part866) = true := by rfl

def kid01_part867 : Audit := .cycle 8 8 true (2)
theorem kid01_part867_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part867) = true := by rfl

def kid01_part868 : Audit := .cycle 7 8 true (2)
theorem kid01_part868_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part868) = true := by rfl

def kid01_part869 : Audit := .cycle 1 16 true (1)
theorem kid01_part869_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part869) = true := by rfl

def kid01_part845 : Audit := .split 14 (5,false) (byMove [(kid01_part846),(kid01_part847),(kid01_part848),(kid01_part849),(kid01_part850),(kid01_part851),(kid01_part852),(kid01_part853),(kid01_part854),(kid01_part855),(kid01_part856),(kid01_part857),(kid01_part858),(kid01_part859),(kid01_part860),(kid01_part861),(kid01_part862),(kid01_part863),(kid01_part864),(kid01_part865),(kid01_part866),(kid01_part867),(kid01_part868),(kid01_part869)])

theorem kid01_part845_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part845) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 14 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (5,false) (some mv)) (byMove [(kid01_part846),(kid01_part847),(kid01_part848),(kid01_part849),(kid01_part850),(kid01_part851),(kid01_part852),(kid01_part853),(kid01_part854),(kid01_part855),(kid01_part856),(kid01_part857),(kid01_part858),(kid01_part859),(kid01_part860),(kid01_part861),(kid01_part862),(kid01_part863),(kid01_part864),(kid01_part865),(kid01_part866),(kid01_part867),(kid01_part868),(kid01_part869)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part846_checked

  · exact kid01_part852_checked

  · exact kid01_part858_checked

  · exact kid01_part864_checked

  · exact kid01_part847_checked

  · exact kid01_part853_checked

  · exact kid01_part859_checked

  · exact kid01_part865_checked

  · exact kid01_part848_checked

  · exact kid01_part854_checked

  · exact kid01_part860_checked

  · exact kid01_part866_checked

  · exact kid01_part849_checked

  · exact kid01_part855_checked

  · exact kid01_part861_checked

  · exact kid01_part867_checked

  · exact kid01_part850_checked

  · exact kid01_part856_checked

  · exact kid01_part862_checked

  · exact kid01_part868_checked

  · exact kid01_part851_checked

  · exact kid01_part857_checked

  · exact kid01_part863_checked

  · exact kid01_part869_checked

def kid01_part870 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 19 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 17 true (1),
.cycle 6 14 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 22 4 false (4),
.cycle 2 14 true (1),
.cycle 24 6 false (4),
.cycle 24 6 false (4),
.cycle 11 4 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (3),
.last 15 (0,true),
.cycle 23 4 false (5),
.cycle 7 11 true (2),
.cycle 7 9 true (2),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (2),
.cycle 8 7 true (2),
.cycle 10 8 true (2)
]),
.cycle 7 13 true (2),
.cycle 6 11 true (1),
.cycle 6 15 true (2),
.cycle 30 1 false (6),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 9 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part870_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part870) = true := by rfl

def kid01_part872 : Audit := .split 38 (2,true) (byMove [
.cycle 0 43 false (4),
.cycle 9 30 false (4),
.cycle 44 1 false (-2),
.cycle 8 32 false (4),
.cycle 7 32 false (4),
.cycle 0 75 false (4),
.cycle 0 57 false (6),
.last 40 (5,false),
.cycle 0 59 false (6),
.last 42 (5,false),
.last 42 (5,false),
.cycle 0 47 false (4),
.cycle 0 43 false (4),
.cycle 0 70 false (4),
.cycle 0 57 false (4),
.cycle 0 49 false (4),
.cycle 0 49 false (4),
.cycle 0 62 false (4),
.cycle 0 45 false (4),
.cycle 0 45 false (4),
.cycle 0 55 false (6),
.cycle 0 47 false (4),
.cycle 0 47 false (4),
.cycle 0 45 false (4)
])
theorem kid01_part872_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part872) = true := by rfl

def kid01_part873 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 12 8 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.cycle 28 3 false (0),
.cycle 12 2 true (-1),
.last 14 (2,true),
.cycle 12 4 true (-1),
.cycle 12 4 true (-1),
.cycle 14 3 false (0),
.cycle 14 3 false (-1),
.last 15 (2,true),
.cycle 18 3 false (0),
.cycle 14 1 false (-2),
.cycle 9 34 false (3),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 16 3 false (0),
.cycle 16 3 false (0),
.cycle 10 12 false (2)
])
theorem kid01_part873_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part873) = true := by rfl

def kid01_part874 : Audit := .split 12 (2,true) (byMove [
.cycle 0 51 false (4),
.last 28 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 26 1 false (-2),
.last 13 (5,false),
.cycle 13 3 false (2),
.last 16 (5,false),
.cycle 17 3 false (3),
.cycle 13 1 false (1),
.cycle 26 1 false (0),
.last 13 (5,false),
.cycle 13 3 false (0),
.last 16 (5,false),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 18 1 false (0),
.cycle 9 6 true (0),
.cycle 24 1 false (0),
.cycle 6 10 true (0),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part874_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part874) = true := by rfl

def kid01_part875 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 14 2 true (-1),
.last 16 (2,true),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.cycle 16 3 false (0),
.cycle 16 3 false (-1),
.last 17 (2,true),
.cycle 20 3 false (0),
.cycle 16 1 false (-2),
.cycle 28 1 false (-4),
.cycle 15 1 false (-1),
.cycle 11 5 false (1),
.cycle 16 3 false (0),
.last 16 (2,true),
.cycle 18 3 false (0),
.cycle 18 3 false (0),
.cycle 18 1 false (-2)
])
theorem kid01_part875_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part875) = true := by rfl

def kid01_part876 : Audit := .split 15 (5,false) (byMove [
.last 18 (2,true),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.cycle 45 3 false (-3),
.cycle 14 2 true (-1),
.last 16 (2,true),
.cycle 13 4 true (-1),
.cycle 12 4 true (-1),
.cycle 16 3 false (0),
.cycle 16 3 false (-1),
.last 17 (2,true),
.cycle 20 3 false (0),
.cycle 16 1 false (-2),
.cycle 64 3 false (-6),
.cycle 15 1 false (-1),
.cycle 11 5 false (1),
.cycle 16 3 false (0),
.last 16 (2,true),
.cycle 18 3 false (0),
.cycle 18 3 false (0),
.cycle 6 19 false (4)
])
theorem kid01_part876_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part876) = true := by rfl

def kid01_part877 : Audit := .cycle 12 3 false (0)
theorem kid01_part877_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part877) = true := by rfl

def kid01_part878 : Audit := .cycle 0 14 true (0)
theorem kid01_part878_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part878) = true := by rfl

def kid01_part879 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 12 8 false (2),
.last 14 (2,true),
.cycle 18 1 false (-2),
.cycle 6 19 false (4),
.cycle 14 3 false (0),
.cycle 1 17 true (1),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 37 3 false (3),
.cycle 37 3 false (3),
.cycle 21 3 false (1),
.cycle 17 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 14 3 false (0),
.cycle 1 17 true (1),
.cycle 19 3 false (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1)
])
theorem kid01_part879_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part879) = true := by rfl

def kid01_part880 : Audit := .split 12 (2,true) (byMove [
.cycle 6 17 true (1),
.last 18 (5,false),
.cycle 6 12 true (0),
.cycle 17 3 false (1),
.last 15 (5,false),
.last 13 (5,false),
.cycle 6 18 true (0),
.last 14 (5,false),
.cycle 6 18 true (0),
.last 16 (5,false),
.last 16 (5,false),
.cycle 22 3 false (2),
.cycle 18 3 false (1),
.cycle 15 3 false (1),
.cycle 37 3 false (3),
.cycle 6 10 true (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 6 14 true (1),
.cycle 20 3 false (2),
.cycle 2 12 true (1),
.cycle 31 3 false (3),
.cycle 31 3 false (3),
.last 16 (5,false)
])
theorem kid01_part880_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part880) = true := by rfl

def kid01_part881 : Audit := .cycle 31 3 false (3)
theorem kid01_part881_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part881) = true := by rfl

def kid01_part882 : Audit := .cycle 31 3 false (3)
theorem kid01_part882_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part882) = true := by rfl

def kid01_part883 : Audit := .cycle 17 3 false (1)
theorem kid01_part883_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part883) = true := by rfl

def kid01_part884 : Audit := .cycle 13 3 false (0)
theorem kid01_part884_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part884) = true := by rfl

def kid01_part885 : Audit := .split 13 (5,false) (byMove [
.last 16 (2,true),
.cycle 24 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.proven (BB6.Agent11Raw121Pumps.M1840.table) (fun m hm => BB6.Agent11Raw121Pumps.M1840.never m hm),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 12 2 true (-1),
.last 14 (2,true),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 14 3 false (0),
.cycle 14 3 false (-1),
.last 15 (2,true),
.cycle 24 3 false (0),
.cycle 14 1 false (-2),
.last 33 (2,true),
.cycle 13 1 false (-1),
.cycle 11 3 false (1),
.cycle 14 3 false (0),
.last 14 (2,true),
.cycle 22 3 false (0),
.cycle 22 3 false (0),
.last 17 (2,true)
])
theorem kid01_part885_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part885) = true := by rfl

def kid01_part886 : Audit := .split 12 (2,true) (byMove [
.cycle 11 5 false (1),
.cycle 14 8 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 31 3 false (-1),
.last 13 (5,false),
.cycle 13 8 true (0),
.last 14 (5,false),
.cycle 17 1 false (5),
.cycle 13 8 true (0),
.cycle 14 8 true (0),
.cycle 13 3 false (1),
.cycle 13 3 false (0),
.last 16 (5,false),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.last 27 (5,false),
.last 13 (5,false),
.cycle 11 2 true (0),
.cycle 13 3 false (1),
.cycle 2 14 true (0),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.cycle 6 12 true (-1)
])
theorem kid01_part886_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part886) = true := by rfl

def kid01_part887 : Audit := .cycle 6 8 true (0)
theorem kid01_part887_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part887) = true := by rfl

def kid01_part888 : Audit := .cycle 6 8 true (0)
theorem kid01_part888_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part888) = true := by rfl

def kid01_part889 : Audit := .cycle 12 3 false (0)
theorem kid01_part889_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part889) = true := by rfl

def kid01_part890 : Audit := .cycle 0 14 true (0)
theorem kid01_part890_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part890) = true := by rfl

def kid01_part891 : Audit := .cycle 15 3 false (1)
theorem kid01_part891_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part891) = true := by rfl

def kid01_part892 : Audit := .split 12 (2,true) (byMove [
.last 18 (5,false),
.cycle 13 3 false (1),
.cycle 16 1 false (0),
.cycle 15 3 false (1),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 2 12 true (1),
.last 14 (5,false),
.cycle 6 16 true (1),
.last 16 (5,false),
.last 16 (5,false),
.cycle 9 6 true (1),
.cycle 11 2 true (1),
.cycle 13 3 false (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 16 3 false (0),
.cycle 2 12 true (1),
.cycle 9 4 true (1),
.cycle 2 12 true (1),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 16 (5,false)
])
theorem kid01_part892_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part892) = true := by rfl

def kid01_part893 : Audit := .cycle 7 6 true (1)
theorem kid01_part893_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part893) = true := by rfl

def kid01_part894 : Audit := .cycle 6 6 true (1)
theorem kid01_part894_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part894) = true := by rfl

def kid01_part895 : Audit := .cycle 10 2 true (1)
theorem kid01_part895_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part895) = true := by rfl

def kid01_part871 : Audit := .split 11 (0,true) (byMove [(kid01_part872),(kid01_part873),(kid01_part874),(kid01_part875),(kid01_part876),(kid01_part877),(kid01_part878),(kid01_part879),(kid01_part880),(kid01_part881),(kid01_part882),(kid01_part883),(kid01_part884),(kid01_part885),(kid01_part886),(kid01_part887),(kid01_part888),(kid01_part889),(kid01_part890),(kid01_part891),(kid01_part892),(kid01_part893),(kid01_part894),(kid01_part895)])

theorem kid01_part871_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part871) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part872),(kid01_part873),(kid01_part874),(kid01_part875),(kid01_part876),(kid01_part877),(kid01_part878),(kid01_part879),(kid01_part880),(kid01_part881),(kid01_part882),(kid01_part883),(kid01_part884),(kid01_part885),(kid01_part886),(kid01_part887),(kid01_part888),(kid01_part889),(kid01_part890),(kid01_part891),(kid01_part892),(kid01_part893),(kid01_part894),(kid01_part895)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part872_checked

  · exact kid01_part878_checked

  · exact kid01_part884_checked

  · exact kid01_part890_checked

  · exact kid01_part873_checked

  · exact kid01_part879_checked

  · exact kid01_part885_checked

  · exact kid01_part891_checked

  · exact kid01_part874_checked

  · exact kid01_part880_checked

  · exact kid01_part886_checked

  · exact kid01_part892_checked

  · exact kid01_part875_checked

  · exact kid01_part881_checked

  · exact kid01_part887_checked

  · exact kid01_part893_checked

  · exact kid01_part876_checked

  · exact kid01_part882_checked

  · exact kid01_part888_checked

  · exact kid01_part894_checked

  · exact kid01_part877_checked

  · exact kid01_part883_checked

  · exact kid01_part889_checked

  · exact kid01_part895_checked

def kid01_part897 : Audit := .split 15 (0,true) (byMove [
.last 26 (5,false),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 4, 5, 1, 4, 4, 0, 1],[128, 256, 8, 4195328, 32768, 68719476736, 524288, 1048576, 32768, 4194304, 68719476736, 68719476736, 33554432, 67108864, 134217728, 1024, 8589934592, 68719476736, 128, 256, 8589934592, 1024, 0, 68719476736, 33554432, 67108864, 134217728, 272630784, 68853694464, 68719476736, 128, 256, 8, 4194304, 32768, 68719476736, 68719476736],[32768, 68719476736, 1048576, 1024, 1024, 1024, 68719476736, 4194304, 1024, 4194304, 4194304, 68719476736, 8589934592, 68719476736, 256, 268435456, 268435456, 68719476736, 0, 68719476736, 68719476736, 1024, 1024, 1024, 68853694464, 69059216384, 69059216384, 268435456, 268435456, 69059216384, 32768, 68719476736, 1048576, 1024, 1024, 1024, 68719476736],127769705854⟩,
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 28 (5,false),
.last 16 (5,false),
.cycle 11 6 true (-1),
.last 36 (5,false),
.last 24 (5,false),
.cycle 16 1 false (0),
.last 26 (5,false),
.last 16 (5,false),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.last 20 (5,false),
.cycle 16 1 false (-2),
.last 22 (5,false),
.last 16 (5,false),
.last 20 (5,false),
.last 40 (5,false),
.last 24 (5,false),
.last 28 (5,false),
.last 18 (5,false),
.last 16 (5,false)
])
theorem kid01_part897_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part897) = true := by rfl

def kid01_part898 : Audit := .split 16 (5,false) (byMove [
.cycle 11 9 false (1),
.cycle 15 8 false (0),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 6 18 false (4),
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 15 2 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 15 4 true (-2),
.cycle 15 4 true (-2),
.cycle 12 5 false (0),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.cycle 11 10 false (1),
.cycle 17 1 false (-3),
.cycle 11 16 false (1),
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.cycle 11 8 false (1),
.cycle 11 8 false (1),
.cycle 15 3 false (-1)
])
theorem kid01_part898_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part898) = true := by rfl

def kid01_part899 : Audit := .cycle 17 1 false (-1)
theorem kid01_part899_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part899) = true := by rfl

def kid01_part900 : Audit := .split 18 (5,false) (byMove [
.cycle 11 13 false (1),
.cycle 17 8 false (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 6 20 false (4),
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 17 2 true (-2),
.cycle 20 1 false (-2),
.cycle 15 4 true (-2),
.cycle 16 4 true (-2),
.cycle 12 7 false (0),
.cycle 11 9 false (1),
.cycle 13 6 false (0),
.cycle 11 12 false (1),
.cycle 19 1 false (-3),
.cycle 11 20 false (1),
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 11 8 false (1),
.cycle 14 5 false (0),
.cycle 11 10 false (1),
.cycle 11 10 false (1),
.cycle 17 3 false (-1)
])
theorem kid01_part900_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part900) = true := by rfl

def kid01_part901 : Audit := .split 18 (5,false) (byMove [
.cycle 11 13 false (1),
.cycle 17 8 false (0),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 6 20 false (4),
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 17 2 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 16 4 true (-2),
.cycle 15 4 true (-2),
.cycle 12 7 false (0),
.cycle 11 9 false (1),
.cycle 13 6 false (0),
.cycle 11 12 false (1),
.cycle 19 1 false (-3),
.cycle 11 20 false (1),
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 11 8 false (1),
.cycle 14 5 false (0),
.cycle 11 10 false (1),
.cycle 11 10 false (1),
.cycle 17 3 false (-1)
])
theorem kid01_part901_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part901) = true := by rfl

def kid01_part902 : Audit := .cycle 12 3 false (0)
theorem kid01_part902_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part902) = true := by rfl

def kid01_part903 : Audit := .split 15 (0,true) (byMove [
.last 36 (5,false),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[524288, 2048, 2097152, 512, 2, 1073741824, 524288, 1074407424, 1073741824, 2097152, 8192, 1073741824, 1074407424, 1074407424, 1074440704, 32768, 8192, 1073741824, 128, 524288, 524288, 512, 33554432, 1073741824, 2048, 2048, 2097152, 512, 2, 1073741824, 1073741824],[2, 2048, 1074266112, 2048, 2048, 128, 8192, 8388608, 2048, 524288, 524288, 524288, 8192, 131072, 1074407424, 139264, 139264, 8192, 33554432, 2048, 1074407424, 2048, 2048, 128, 2, 2048, 1074407424, 2048, 2048, 128, 1073741824],1942453682⟩,
.last 30 (5,false),
.cycle 11 9 false (1),
.last 18 (5,false),
.last 16 (5,false),
.cycle 0 18 true (-1),
.last 17 (5,false),
.last 40 (5,false),
.cycle 6 23 true (-1),
.last 36 (5,false),
.last 20 (5,false),
.last 20 (5,false),
.cycle 0 24 true (-1),
.last 24 (5,false),
.last 28 (5,false),
.last 18 (5,false),
.last 16 (5,false),
.last 34 (5,false),
.cycle 1 25 true (-1),
.last 28 (5,false),
.last 22 (5,false),
.last 22 (5,false),
.last 18 (5,false)
])
theorem kid01_part903_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part903) = true := by rfl

def kid01_part904 : Audit := .split 16 (5,false) (byMove [
.last 17 (0,true),
.cycle 15 8 false (1),
.cycle 15 25 true (-1),
.cycle 21 1 false (-3),
.cycle 6 22 false (4),
.cycle 15 31 true (-2),
.last 17 (0,true),
.cycle 15 2 true (0),
.cycle 15 19 true (0),
.cycle 15 8 true (0),
.cycle 15 8 true (0),
.cycle 15 25 true (0),
.last 17 (0,true),
.cycle 13 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 29 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 12 5 false (1),
.last 17 (0,true),
.cycle 11 10 false (1),
.cycle 15 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 10 7 false (2)
])
theorem kid01_part904_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part904) = true := by rfl

def kid01_part905 : Audit := .split 40 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18907136, 17825792, 16777216],[16777216, 16384, 4, 1024, 1024, 16384, 16777216, 16384, 16384, 1024, 1024, 16384, 16777216, 17842176, 16384, 4194304, 4194304, 1064960, 16777216, 17842176, 1048576, 4194304, 4194304, 17842176, 16777216],33503232⟩,
.cycle 57 8 false (-1),
.cycle 42 1 false (-2),
.cycle 41 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 40 1 false (-2),
.last 41 (0,true),
.cycle 39 2 true (-2),
.cycle 49 1 false (7),
.cycle 25 16 true (-2),
.cycle 26 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 16384, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 17842176, 524288, 1048576, 2097152, 4194304, 18907136, 17842176, 16777216],[16777216, 16384, 4, 1024, 1024, 16384, 16777216, 16384, 16384, 1024, 1024, 16384, 16777216, 17842176, 16384, 4194304, 4194304, 1064960, 16777216, 17842176, 1048576, 4194304, 4194304, 17842176, 16777216],33503232⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 41 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 40 1 false (-2),
.last 41 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 38 3 false (0)
])
theorem kid01_part905_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part905) = true := by rfl

def kid01_part906 : Audit := .split 22 (5,false) (byMove [
.last 23 (0,true),
.cycle 21 8 false (1),
.cycle 24 1 false (0),
.cycle 27 1 false (-3),
.cycle 6 28 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.last 23 (0,true),
.cycle 21 2 true (0),
.cycle 6 35 true (-1),
.cycle 15 8 true (0),
.cycle 16 8 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 32, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.last 23 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 6 20 true (-1),
.cycle 35 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 47 1 false (-3),
.last 23 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 49 3 false (-1)
])
theorem kid01_part906_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part906) = true := by rfl

def kid01_part907 : Audit := .split 22 (5,false) (byMove [
.last 23 (0,true),
.cycle 21 8 false (1),
.cycle 16 12 true (-1),
.cycle 27 1 false (-3),
.cycle 6 28 false (4),
.cycle 39 1 false (-3),
.last 23 (0,true),
.cycle 21 2 true (0),
.cycle 16 26 true (0),
.cycle 16 8 true (0),
.cycle 15 8 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.last 23 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 6 20 true (-1),
.cycle 35 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 47 1 false (-3),
.last 23 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 49 3 false (-1)
])
theorem kid01_part907_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part907) = true := by rfl

def kid01_part908 : Audit := .split 24 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 256, 16777216, 524288, 1048576, 2097152, 1024, 32768, 256, 524288, 1048576, 2097152, 4195328, 19923200, 17825792, 16777216],[16777216, 131072, 32, 1024, 1024, 131072, 16777216, 131072, 131072, 1024, 1024, 131072, 16777216, 16777216, 8388608, 4194304, 4194304, 131072, 16777216, 25296896, 8388608, 4194304, 4194304, 25296896, 16777216],33323008⟩,
.cycle 57 8 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 35 1 false (-3),
.cycle 8 17 false (4),
.cycle 30 1 false (-2),
.cycle 0 25 true (-1),
.cycle 35 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 29 16 true (-2),
.cycle 31 8 true (3),
.cycle 24 1 true (4),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 2, 64, 128, 2176, 2240, 512, 8192, 64, 264320, 264320, 512, 512, 8192, 64, 262144],[262144, 2048, 128, 2048, 2048, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144, 2048, 128, 2048, 2048, 128, 262144],340992⟩,
.cycle 22 3 true (2),
.cycle 17 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 8 17 false (4),
.cycle 30 1 false (-2),
.last 40 (0,true),
.cycle 1 24 true (-1),
.cycle 17 19 true (1),
.cycle 18 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 24 1 true (4)
])
theorem kid01_part908_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part908) = true := by rfl

def kid01_part909 : Audit := .split 15 (0,true) (byMove [
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1207992320, 1073741824, 128, 256, 134217728, 1024, 0, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1048576, 1073741824, 4194304, 1024, 1024, 1024, 134217728, 4194304, 1024, 4194304, 4194304, 1073741824, 1212269824, 1078002688, 1078002688, 65536, 65536, 1078002688, 4194304, 1073741824, 1024, 1024, 1024, 1024, 1048576, 1073741824, 4194304, 1024, 1024, 1024, 1073741824],1990983038⟩,
.last 31 (5,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 36 (5,false),
.last 16 (5,false),
.cycle 0 20 true (-1),
.last 17 (5,false),
.cycle 11 7 false (1),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.cycle 12 4 true (-1),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.last 28 (5,false),
.cycle 16 1 false (-2),
.last 30 (5,false),
.last 16 (5,false),
.last 38 (5,false),
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.last 26 (5,false),
.last 26 (5,false),
.last 18 (5,false)
])
theorem kid01_part909_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part909) = true := by rfl

def kid01_part910 : Audit := .split 16 (5,false) (byMove [
.cycle 11 9 false (1),
.cycle 29 8 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 15 2 true (-2),
.cycle 13 5 false (0),
.cycle 15 12 true (-2),
.cycle 15 12 true (-2),
.cycle 12 5 false (0),
.cycle 11 7 false (1),
.cycle 13 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 17 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 16 1 false (-2),
.last 17 (0,true),
.cycle 11 6 false (1),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (-1)
])
theorem kid01_part910_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part910) = true := by rfl

def kid01_part911 : Audit := .split 28 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 4195328, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 41 8 false (-1),
.cycle 30 1 false (-2),
.cycle 29 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 28 1 false (-2),
.last 29 (0,true),
.cycle 27 2 true (-2),
.cycle 15 14 true (-2),
.cycle 17 12 true (-2),
.cycle 18 12 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[139264, 139264, 32768, 512, 2, 64, 417792, 417792, 36864, 32768, 128, 4096, 8192, 16384, 20480, 32768, 128, 4096, 262144],[262144, 2048, 256, 2048, 2048, 128, 262144, 131072, 16384, 139264, 139264, 8192, 262144, 131072, 16384, 139264, 139264, 8192, 262144],328928⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 29 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 28 1 false (-2),
.last 29 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 26 3 false (0)
])
theorem kid01_part911_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part911) = true := by rfl

def kid01_part912 : Audit := .split 26 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 0, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 1024, 4194304, 4194304, 4195328, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 39 8 false (-1),
.cycle 28 1 false (-2),
.cycle 27 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 26 1 false (-2),
.last 27 (0,true),
.cycle 25 2 true (-2),
.cycle 28 1 false (-2),
.cycle 15 12 true (-2),
.cycle 16 12 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[139264, 139264, 32768, 512, 2, 64, 401408, 401408, 36864, 32768, 128, 4096, 8192, 139264, 143360, 32768, 128, 4096, 262144],[262144, 2048, 512, 2048, 2048, 128, 262144, 131072, 32768, 139264, 139264, 8192, 262144, 131072, 32768, 139264, 139264, 8192, 262144],328928⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 27 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 26 1 false (-2),
.last 27 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 24 3 false (0)
])
theorem kid01_part912_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part912) = true := by rfl

def kid01_part913 : Audit := .split 26 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 4194304, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216, 20972544, 20971520, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 39 8 false (-1),
.cycle 28 1 false (-2),
.cycle 27 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 26 1 false (-2),
.last 27 (0,true),
.cycle 25 2 true (-2),
.cycle 41 12 false (-1),
.cycle 16 12 true (-2),
.cycle 15 12 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[139264, 139264, 32768, 512, 2, 64, 401408, 401408, 36864, 32768, 128, 4096, 8192, 139264, 143360, 32768, 128, 4096, 262144],[262144, 2048, 1024, 2048, 2048, 128, 262144, 131072, 65536, 139264, 139264, 8192, 262144, 131072, 65536, 139264, 139264, 8192, 262144],328928⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 27 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 26 1 false (-2),
.last 27 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 24 3 false (0)
])
theorem kid01_part913_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part913) = true := by rfl

def kid01_part914 : Audit := .cycle 12 3 false (0)
theorem kid01_part914_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part914) = true := by rfl

def kid01_part915 : Audit := .split 15 (0,true) (byMove [
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1212253184, 1073741824, 128, 256, 134217728, 1024, 0, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[1048576, 1073741824, 64, 1024, 1024, 262144, 134217728, 4194304, 262144, 4194304, 4194304, 1073741824, 1212269824, 1212269824, 4096, 65536, 65536, 1078268992, 4194304, 1073741824, 64, 1024, 1024, 1024, 1048576, 1073741824, 64, 1024, 1024, 262144, 1073741824],1990983038⟩,
.cycle 11 5 false (1),
.cycle 9 9 false (3),
.cycle 11 7 false (1),
.cycle 11 7 false (1),
.last 18 (5,false),
.cycle 0 18 true (-1),
.last 17 (5,false),
.cycle 6 18 true (-1),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32768, 1073741824, 524288, 1048576, 32768, 4194304, 1073741824, 1073741824, 8192, 16384, 32768, 4260864, 1212253184, 1073741824, 128, 256, 134217728, 1024, 4194304, 1073741824, 128, 256, 8, 4194304, 32768, 1073741824, 1073741824],[8, 1073741824, 64, 1024, 1024, 262144, 32768, 138412032, 262144, 4194304, 4194304, 1073741824, 32768, 1073840128, 4096, 65536, 65536, 1073811520, 134217728, 1073741824, 64, 1024, 1024, 1024, 8, 1073741824, 64, 1024, 1024, 262144, 1073741824],1990983038⟩,
.last 40 (5,false),
.last 20 (5,false),
.cycle 11 8 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.last 26 (5,false),
.last 26 (5,false),
.last 18 (5,false),
.last 36 (5,false),
.cycle 9 7 false (3),
.last 32 (5,false),
.last 24 (5,false),
.last 24 (5,false),
.last 20 (5,false)
])
theorem kid01_part915_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part915) = true := by rfl

def kid01_part916 : Audit := .split 18 (5,false) (byMove [
.cycle 9 13 false (3),
.cycle 31 8 false (-1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 17 2 true (-2),
.cycle 11 9 false (1),
.cycle 15 12 true (-2),
.cycle 15 12 true (-2),
.cycle 12 7 false (1),
.cycle 11 9 false (1),
.cycle 13 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 19 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 18 1 false (-2),
.last 19 (0,true),
.cycle 11 8 false (1),
.cycle 14 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 2, 16, 16, 18, 64],64⟩,
.cycle 16 3 false (0)
])
theorem kid01_part916_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part916) = true := by rfl

def kid01_part917 : Audit := .split 32 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18907136, 17825792, 16777216],[16777216, 256, 256, 1024, 1024, 256, 16777216, 256, 256, 1024, 1024, 256, 16777216, 17826048, 1048576, 4194304, 4194304, 1048832, 16777216, 17826048, 1048576, 4194304, 4194304, 17826048, 16777216],33503232⟩,
.cycle 49 8 false (-1),
.cycle 34 1 false (-2),
.cycle 33 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 32 1 false (-2),
.last 33 (0,true),
.cycle 31 2 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.cycle 22 16 true (-2),
.cycle 22 16 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 17826048, 524288, 1048576, 2097152, 4194304, 18907136, 17826048, 16777216],[16777216, 256, 256, 1024, 1024, 256, 16777216, 256, 256, 1024, 1024, 256, 16777216, 17826048, 1048576, 4194304, 4194304, 1048832, 16777216, 17826048, 1048576, 4194304, 4194304, 17826048, 16777216],33503232⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 20, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 33 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 32 1 false (-2),
.last 33 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 20, 4, 16, 16, 20, 64],64⟩,
.cycle 30 3 false (0)
])
theorem kid01_part917_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part917) = true := by rfl

def kid01_part918 : Audit := .split 24 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 512, 512, 1024, 1024, 512, 16777216, 1024, 512, 1024, 1024, 1024, 16777216, 18874880, 2097152, 4194304, 4194304, 2097664, 16777216, 23069696, 2097152, 4194304, 4194304, 23069696, 16777216],33503232⟩,
.cycle 37 8 false (-1),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 24 1 false (-2),
.last 25 (0,true),
.cycle 23 2 true (-2),
.cycle 16 12 true (-2),
.cycle 16 12 true (-2),
.cycle 16 12 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 32, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[139264, 139264, 32768, 512, 2, 64, 401408, 401408, 36864, 32768, 128, 4096, 8192, 139264, 143360, 32768, 128, 4096, 262144],[262144, 2048, 139264, 2048, 2048, 128, 262144, 131072, 139264, 139264, 139264, 8192, 262144, 131072, 139264, 139264, 139264, 8192, 262144],328928⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 25 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 24 1 false (-2),
.last 25 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 8, 16, 16, 24, 64],64⟩,
.cycle 22 3 false (0)
])
theorem kid01_part918_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part918) = true := by rfl

def kid01_part919 : Audit := .split 24 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 4195328, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 37 8 false (-1),
.cycle 26 1 false (-2),
.cycle 25 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 24 1 false (-2),
.last 25 (0,true),
.cycle 23 2 true (-2),
.cycle 15 12 true (-2),
.cycle 15 12 true (-2),
.cycle 15 12 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[139264, 139264, 32768, 512, 2, 64, 401408, 401408, 36864, 32768, 128, 4096, 8192, 139264, 143360, 32768, 128, 4096, 262144],[262144, 2048, 2048, 2048, 2048, 128, 262144, 131072, 139264, 139264, 139264, 8192, 262144, 131072, 139264, 139264, 139264, 8192, 262144],328928⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 25 1 false (-3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 24 1 false (-2),
.last 25 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 2, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 22 3 false (0)
])
theorem kid01_part919_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part919) = true := by rfl

def kid01_part920 : Audit := .cycle 10 5 false (2)
theorem kid01_part920_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part920) = true := by rfl

def kid01_part896 : Audit := .split 14 (2,true) (byMove [(kid01_part897),(kid01_part898),(kid01_part899),(kid01_part900),(kid01_part901),(kid01_part902),(kid01_part903),(kid01_part904),(kid01_part905),(kid01_part906),(kid01_part907),(kid01_part908),(kid01_part909),(kid01_part910),(kid01_part911),(kid01_part912),(kid01_part913),(kid01_part914),(kid01_part915),(kid01_part916),(kid01_part917),(kid01_part918),(kid01_part919),(kid01_part920)])

theorem kid01_part896_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part896) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid01_part897),(kid01_part898),(kid01_part899),(kid01_part900),(kid01_part901),(kid01_part902),(kid01_part903),(kid01_part904),(kid01_part905),(kid01_part906),(kid01_part907),(kid01_part908),(kid01_part909),(kid01_part910),(kid01_part911),(kid01_part912),(kid01_part913),(kid01_part914),(kid01_part915),(kid01_part916),(kid01_part917),(kid01_part918),(kid01_part919),(kid01_part920)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part897_checked

  · exact kid01_part903_checked

  · exact kid01_part909_checked

  · exact kid01_part915_checked

  · exact kid01_part898_checked

  · exact kid01_part904_checked

  · exact kid01_part910_checked

  · exact kid01_part916_checked

  · exact kid01_part899_checked

  · exact kid01_part905_checked

  · exact kid01_part911_checked

  · exact kid01_part917_checked

  · exact kid01_part900_checked

  · exact kid01_part906_checked

  · exact kid01_part912_checked

  · exact kid01_part918_checked

  · exact kid01_part901_checked

  · exact kid01_part907_checked

  · exact kid01_part913_checked

  · exact kid01_part919_checked

  · exact kid01_part902_checked

  · exact kid01_part908_checked

  · exact kid01_part914_checked

  · exact kid01_part920_checked

def kid01_part922 : Audit := .split 12 (0,true) (byMove [
.cycle 15 6 true (1),
.last 28 (5,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 32 (5,false),
.last 13 (5,false),
.cycle 29 6 true (1),
.cycle 13 18 true (1),
.cycle 13 6 true (1),
.cycle 13 1 false (1),
.cycle 15 6 true (1),
.last 13 (5,false),
.cycle 14 6 true (-2),
.cycle 11 3 false (1),
.last 17 (5,false),
.cycle 13 1 false (-1),
.last 19 (5,false),
.last 13 (5,false),
.cycle 9 13 false (3),
.cycle 1 18 true (0),
.cycle 13 6 true (1),
.cycle 6 10 true (0),
.last 15 (5,false),
.last 13 (5,false)
])
theorem kid01_part922_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part922) = true := by rfl

def kid01_part923 : Audit := .split 13 (5,false) (byMove [
.cycle 17 6 true (-3),
.cycle 12 8 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 6 15 false (4),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (-1),
.cycle 28 6 true (-2),
.cycle 12 4 true (-1),
.cycle 12 4 true (-1),
.cycle 12 6 true (-1),
.cycle 26 6 true (-2),
.cycle 11 4 false (1),
.cycle 14 6 true (-2),
.cycle 14 1 false (-2),
.cycle 16 6 true (-2),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 14 6 true (-2),
.cycle 11 3 false (1),
.cycle 15 6 true (-2),
.cycle 14 6 true (-2),
.cycle 10 12 false (2)
])
theorem kid01_part923_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part923) = true := by rfl

def kid01_part924 : Audit := .cycle 14 1 false (0)
theorem kid01_part924_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part924) = true := by rfl

def kid01_part925 : Audit := .split 15 (5,false) (byMove [
.cycle 20 6 true (-3),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 14 2 true (-1),
.cycle 17 1 false (-1),
.cycle 12 4 true (-1),
.cycle 13 4 true (-1),
.cycle 12 6 true (-1),
.cycle 27 1 false (-3),
.cycle 11 6 false (1),
.cycle 16 6 true (-2),
.cycle 16 1 false (-2),
.cycle 18 6 true (-2),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 16 6 true (-2),
.cycle 11 5 false (1),
.cycle 17 6 true (-2),
.cycle 16 6 true (-2),
.cycle 18 1 false (-2)
])
theorem kid01_part925_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part925) = true := by rfl

def kid01_part926 : Audit := .split 15 (5,false) (byMove [
.cycle 19 6 true (-3),
.cycle 14 8 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 6 17 false (4),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 14 2 true (-1),
.cycle 43 6 true (-5),
.cycle 13 4 true (-1),
.cycle 12 4 true (-1),
.cycle 13 6 true (-1),
.cycle 41 6 true (-5),
.cycle 11 6 false (1),
.cycle 16 6 true (-2),
.cycle 16 1 false (-2),
.cycle 18 6 true (-2),
.cycle 15 1 false (-1),
.last 16 (0,true),
.cycle 16 6 true (-2),
.cycle 11 5 false (1),
.cycle 17 6 true (-2),
.cycle 16 6 true (-2),
.cycle 6 19 false (4)
])
theorem kid01_part926_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part926) = true := by rfl

def kid01_part927 : Audit := .split 17 (5,false) (byMove [
.last 31 (0,true),
.cycle 16 8 false (1),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 6 19 false (4),
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 16 2 true (-1),
.cycle 21 1 false (1),
.cycle 14 4 true (-1),
.cycle 15 4 true (-1),
.cycle 12 6 true (-1),
.cycle 31 6 true (-5),
.cycle 11 8 false (1),
.cycle 18 6 true (-2),
.cycle 18 1 false (-2),
.cycle 20 6 true (-2),
.cycle 17 1 false (-1),
.last 18 (0,true),
.cycle 18 6 true (-2),
.cycle 11 7 false (1),
.cycle 19 6 true (-2),
.cycle 18 6 true (-2),
.cycle 10 12 false (2)
])
theorem kid01_part927_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part927) = true := by rfl

def kid01_part928 : Audit := .split 12 (0,true) (byMove [
.cycle 0 16 true (0),
.last 18 (5,false),
.cycle 6 12 true (0),
.cycle 14 6 true (-1),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 16 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.cycle 6 18 true (-1),
.cycle 0 18 true (0),
.cycle 13 6 true (1),
.cycle 6 10 true (0),
.last 15 (5,false),
.last 13 (5,false),
.cycle 0 14 true (0),
.cycle 13 6 true (1),
.cycle 0 14 true (0),
.cycle 14 6 true (1),
.cycle 13 6 true (1),
.last 16 (5,false)
])
theorem kid01_part928_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part928) = true := by rfl

def kid01_part929 : Audit := .split 13 (5,false) (byMove [
.last 14 (0,true),
.cycle 12 8 false (2),
.cycle 6 35 true (0),
.cycle 18 1 false (-2),
.cycle 6 19 false (4),
.cycle 19 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (1),
.cycle 1 17 true (1),
.cycle 14 6 true (1),
.cycle 15 6 true (1),
.cycle 14 6 true (1),
.last 14 (0,true),
.cycle 11 6 false (2),
.cycle 6 14 true (-1),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 6 12 true (-1),
.last 14 (0,true),
.cycle 6 18 true (-1),
.cycle 1 17 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 10 4 true (1)
])
theorem kid01_part929_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part929) = true := by rfl

def kid01_part930 : Audit := .cycle 6 18 true (0)
theorem kid01_part930_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part930) = true := by rfl

def kid01_part931 : Audit := .cycle 12 6 true (1)
theorem kid01_part931_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part931) = true := by rfl

def kid01_part932 : Audit := .cycle 13 6 true (1)
theorem kid01_part932_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part932) = true := by rfl

def kid01_part933 : Audit := .cycle 12 6 true (1)
theorem kid01_part933_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part933) = true := by rfl

def kid01_part934 : Audit := .split 12 (0,true) (byMove [
.cycle 0 92 false (4),
.cycle 41 6 true (-3),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 29 6 true (-3),
.last 13 (5,false),
.cycle 0 16 true (0),
.last 14 (5,false),
.cycle 6 14 true (-1),
.cycle 6 20 true (-1),
.cycle 6 20 true (-1),
.cycle 6 22 true (-1),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[65536, 262144, 65536, 1024, 1024, 1024, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 262144],396320⟩,
.cycle 11 3 false (1),
.cycle 6 10 true (-1),
.cycle 13 1 false (-1),
.last 27 (5,false),
.last 13 (5,false),
.cycle 0 16 true (0),
.cycle 6 12 true (-1),
.cycle 11 2 true (0),
.cycle 5 8 true (0),
.cycle 6 8 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[2048, 262144, 65536, 1024, 1024, 1024, 131072, 65536, 65536, 65536, 65536, 65536, 131072, 65536, 65536, 65536, 65536, 65536, 262144],396320⟩
])
theorem kid01_part934_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part934) = true := by rfl

def kid01_part935 : Audit := .split 13 (5,false) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 20972544, 4194304, 4194304, 4194304, 16777216, 20972544, 20972544, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 24 8 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (-1),
.cycle 11 5 false (1),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 6 12 true (-1),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 2],[155648, 155648, 32768, 512, 2, 64, 417792, 417792, 36864, 32768, 128, 4096, 16384, 131072, 135168, 32768, 128, 4096, 262144],[262144, 2048, 128, 2048, 2048, 256, 262144, 131072, 8192, 147456, 147456, 16384, 262144, 131072, 8192, 155648, 155648, 16384, 262144],328928⟩,
.cycle 11 4 false (1),
.cycle 14 12 true (-2),
.cycle 14 1 false (-2),
.cycle 16 12 true (-2),
.cycle 13 1 false (-1),
.last 14 (0,true),
.cycle 14 12 true (-2),
.cycle 11 3 false (1),
.cycle 15 12 true (-2),
.cycle 14 12 true (-2),
.cycle 11 6 false (1)
])
theorem kid01_part935_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part935) = true := by rfl

def kid01_part936 : Audit := .cycle 6 10 true (-1)
theorem kid01_part936_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part936) = true := by rfl

def kid01_part937 : Audit := .cycle 6 8 true (0)
theorem kid01_part937_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part937) = true := by rfl

def kid01_part938 : Audit := .cycle 6 8 true (0)
theorem kid01_part938_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part938) = true := by rfl

def kid01_part939 : Audit := .cycle 6 10 true (-1)
theorem kid01_part939_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part939) = true := by rfl

def kid01_part940 : Audit := .split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 13 6 true (-1),
.cycle 9 6 true (1),
.cycle 14 6 true (-1),
.cycle 13 6 true (-1),
.last 21 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 0 14 true (0),
.last 16 (5,false),
.last 16 (5,false),
.last 18 (5,false),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 262144, 8192, 16384, 8, 65536, 262144, 262144, 8192, 16384, 8, 65536, 0, 262144, 262144],[65536, 262144, 64, 1024, 1024, 1024, 65536, 65536, 4096, 65536, 65536, 65536, 65536, 65536, 4096, 65536, 65536, 65536, 262144],396320⟩,
.cycle 6 12 true (-1),
.cycle 11 2 true (1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 6 14 true (-1),
.cycle 0 14 true (0),
.cycle 9 4 true (1),
.cycle 0 14 true (0),
.cycle 8 6 true (1),
.cycle 7 6 true (1),
.last 16 (5,false)
])
theorem kid01_part940_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part940) = true := by rfl

def kid01_part941 : Audit := .cycle 6 14 true (-1)
theorem kid01_part941_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part941) = true := by rfl

def kid01_part942 : Audit := .cycle 2 12 true (1)
theorem kid01_part942_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part942) = true := by rfl

def kid01_part943 : Audit := .cycle 7 6 true (1)
theorem kid01_part943_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part943) = true := by rfl

def kid01_part944 : Audit := .cycle 6 6 true (1)
theorem kid01_part944_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part944) = true := by rfl

def kid01_part945 : Audit := .cycle 10 2 true (1)
theorem kid01_part945_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part945) = true := by rfl

def kid01_part921 : Audit := .split 11 (2,true) (byMove [(kid01_part922),(kid01_part923),(kid01_part924),(kid01_part925),(kid01_part926),(kid01_part927),(kid01_part928),(kid01_part929),(kid01_part930),(kid01_part931),(kid01_part932),(kid01_part933),(kid01_part934),(kid01_part935),(kid01_part936),(kid01_part937),(kid01_part938),(kid01_part939),(kid01_part940),(kid01_part941),(kid01_part942),(kid01_part943),(kid01_part944),(kid01_part945)])

theorem kid01_part921_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part921) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part922),(kid01_part923),(kid01_part924),(kid01_part925),(kid01_part926),(kid01_part927),(kid01_part928),(kid01_part929),(kid01_part930),(kid01_part931),(kid01_part932),(kid01_part933),(kid01_part934),(kid01_part935),(kid01_part936),(kid01_part937),(kid01_part938),(kid01_part939),(kid01_part940),(kid01_part941),(kid01_part942),(kid01_part943),(kid01_part944),(kid01_part945)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part922_checked

  · exact kid01_part928_checked

  · exact kid01_part934_checked

  · exact kid01_part940_checked

  · exact kid01_part923_checked

  · exact kid01_part929_checked

  · exact kid01_part935_checked

  · exact kid01_part941_checked

  · exact kid01_part924_checked

  · exact kid01_part930_checked

  · exact kid01_part936_checked

  · exact kid01_part942_checked

  · exact kid01_part925_checked

  · exact kid01_part931_checked

  · exact kid01_part937_checked

  · exact kid01_part943_checked

  · exact kid01_part926_checked

  · exact kid01_part932_checked

  · exact kid01_part938_checked

  · exact kid01_part944_checked

  · exact kid01_part927_checked

  · exact kid01_part933_checked

  · exact kid01_part939_checked

  · exact kid01_part945_checked

def kid01_part946 : Audit := .cycle 5 6 true (1)
theorem kid01_part946_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part946) = true := by rfl

def kid01_part947 : Audit := .cycle 6 6 true (1)
theorem kid01_part947_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part947) = true := by rfl

def kid01_part948 : Audit := .split 13 (5,false) (byMove [
.split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 12 6 false (0),
.cycle 20 1 false (-2),
.cycle 12 8 false (0),
.cycle 12 8 false (0),
.cycle 11 6 false (1),
.last 17 (0,true),
.last 19 (0,true),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18907136, 17825792, 16777216],[16777216, 16384, 4, 1024, 1024, 16384, 16777216, 16384, 16384, 1024, 1024, 16384, 16777216, 17842176, 16384, 4194304, 4194304, 17842176, 16777216, 17842176, 1048576, 4194304, 4194304, 17842176, 16777216],33503232⟩,
.last 25 (0,true),
.last 25 (0,true),
.last 19 (0,true),
.last 17 (0,true),
.cycle 12 6 false (0),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 0, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 1024, 4194304, 4194304, 20972544, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 4194304, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216, 20972544, 20971520, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 11 6 false (1),
.last 17 (0,true),
.cycle 9 8 false (3),
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 32768, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18907136, 17825792, 16777216],[16777216, 256, 256, 1024, 1024, 256, 16777216, 256, 256, 1024, 1024, 256, 16777216, 17826048, 1048576, 4194304, 4194304, 17826048, 16777216, 17826048, 1048576, 4194304, 4194304, 17826048, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 1024, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 23069696, 17825792, 16777216],[16777216, 512, 512, 1024, 1024, 512, 16777216, 1024, 512, 1024, 1024, 1024, 16777216, 18874880, 2097152, 4194304, 4194304, 18874880, 16777216, 23069696, 2097152, 4194304, 4194304, 23069696, 16777216],33503232⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],[128, 256, 8, 0, 32768, 256, 128, 256, 32768, 1024, 0, 16777216, 524288, 1048576, 32768, 1024, 2129920, 1048832, 524288, 1048576, 2097152, 4194304, 18874368, 17825792, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216, 20972544, 4194304, 4194304, 4194304, 20972544, 16777216],33503232⟩,
.cycle 10 8 false (2)
]),
.cycle 25 8 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.split 14 (0,true) (byMove [
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 1, 64],[24, 24, 64, 16, 16, 24, 64],64⟩,
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 1, 64],[24, 24, 64, 16, 16, 24, 64],64⟩,
.cycle 12 6 true (-1),
.cycle 0 18 true (-1),
.cycle 16 19 true (0),
.last 15 (2,true),
.cycle 36 1 false (4),
.cycle 16 26 true (0),
.cycle 0 25 true (-1),
.cycle 12 5 false (0),
.last 16 (2,true),
.cycle 6 12 true (-1),
.cycle 15 1 false (-1),
.cycle 27 12 false (0),
.cycle 13 2 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 1, 64],[1, 1, 64, 16, 16, 1, 64],64⟩,
.cycle 12 4 true (-1),
.last 15 (2,true),
.cycle 5 10 true (-1),
.cycle 6 10 true (-1),
.cycle 11 4 true (-1)
]),
.cycle 13 2 true (-1),
.split 14 (2,true) (byMove [
.last 18 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 24, 16, 16, 24, 64],64⟩,
.cycle 44 1 false (4),
.last 15 (0,true),
.cycle 16 19 true (0),
.cycle 19 1 false (5),
.cycle 36 1 false (4),
.cycle 16 26 true (0),
.cycle 26 1 false (6),
.cycle 12 5 false (0),
.cycle 13 5 false (0),
.cycle 6 12 true (-1),
.cycle 15 1 false (-1),
.cycle 27 12 false (0),
.cycle 13 2 true (-1),
.last 15 (0,true),
.cycle 12 4 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.cycle 5 10 true (-1),
.cycle 6 10 true (-1),
.cycle 11 4 true (-1)
]),
.cycle 6 10 true (-1),
.cycle 6 10 true (-1),
.cycle 12 2 true (-1),
.cycle 12 4 false (0),
.split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 13 4 false (-1),
.cycle 18 1 false (-2),
.cycle 13 6 false (-1),
.cycle 13 6 false (-1),
.cycle 12 4 false (0),
.last 16 (0,true),
.cycle 13 6 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 6 false (0),
.last 16 (0,true),
.cycle 13 4 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 12 4 false (0),
.last 16 (0,true),
.cycle 11 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 10 6 false (2)
]),
.far true 3 ⟨0,[0, 1, 1, 2, 1, 1],[131072, 2048, 32768, 512, 2, 256, 395264, 395264, 49664, 32768, 128, 16384, 2048, 262144, 256, 512, 128, 256, 262144],[262144, 2048, 262144, 2048, 2048, 2048, 262144, 131072, 262144, 131072, 131072, 131072, 262144, 2048, 262144, 2048, 2048, 2048, 262144],337088⟩,
.cycle 14 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 1 false (-1),
.split 14 (0,true) (byMove [
.cycle 0 31 false (4),
.cycle 13 3 false (0),
.last 15 (2,true),
.cycle 13 5 false (0),
.cycle 13 5 false (0),
.cycle 12 3 false (0),
.cycle 0 18 true (-1),
.cycle 16 19 true (0),
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 1, 64],[8, 24, 64, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 12 29 true (-1),
.cycle 12 6 false (0),
.cycle 13 3 false (0),
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 12 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 10, 1, 64],[1, 1, 64, 16, 16, 1, 64],64⟩,
.cycle 11 5 false (1),
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 1, 64],[8, 24, 64, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 1, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 10 5 false (2)
]),
.cycle 12 3 false (0),
.split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 13 3 false (0),
.cycle 17 1 false (-1),
.cycle 13 5 false (0),
.cycle 13 5 false (0),
.cycle 12 3 false (0),
.last 15 (0,true),
.cycle 16 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 19 true (0),
.last 15 (0,true),
.cycle 13 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 12 3 false (0),
.last 15 (0,true),
.cycle 11 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 4, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 4, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 10 5 false (2)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 11 3 false (1)
])
theorem kid01_part948_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part948) = true := by rfl

def kid01_part950 : Audit := .cycle 0 15 false (4)
theorem kid01_part950_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part950) = true := by rfl

def kid01_part951 : Audit := .split 19 (5,false) (byMove [
.last 22 (2,true),
.cycle 18 8 false (1),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 6 21 false (4),
.cycle 19 1 false (-1),
.cycle 12 17 false (2),
.cycle 18 2 true (-1),
.last 20 (2,true),
.cycle 18 4 true (-1),
.cycle 18 4 true (-1),
.cycle 9 24 true (-1),
.cycle 15 6 false (1),
.last 21 (2,true),
.cycle 15 9 false (1),
.cycle 20 1 false (-2),
.cycle 12 23 false (2),
.cycle 19 1 false (-1),
.cycle 17 3 false (1),
.cycle 15 5 false (1),
.last 20 (2,true),
.cycle 15 7 false (1),
.cycle 15 7 false (1),
.cycle 9 27 false (5)
])
theorem kid01_part951_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part951) = true := by rfl

def kid01_part952 : Audit := .split 12 (2,true) (byMove [
.cycle 0 15 false (4),
.last 30 (5,false),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.last 35 (5,false),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 13 5 false (1),
.last 20 (5,false),
.last 37 (5,false),
.cycle 27 1 false (-1),
.last 33 (5,false),
.last 19 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.last 25 (5,false),
.last 13 (5,false)
])
theorem kid01_part952_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part952) = true := by rfl

def kid01_part953 : Audit := .split 25 (5,false) (byMove [
.last 28 (2,true),
.cycle 24 8 false (1),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 25 1 false (-1),
.cycle 27 1 false (-1),
.cycle 24 2 true (-1),
.last 26 (2,true),
.cycle 22 4 true (-1),
.cycle 23 4 true (-1),
.cycle 8 32 true (-1),
.cycle 19 8 false (1),
.last 27 (2,true),
.cycle 18 11 false (2),
.cycle 26 1 false (-2),
.cycle 13 29 false (3),
.cycle 25 1 false (-1),
.cycle 21 5 false (1),
.cycle 19 7 false (1),
.last 26 (2,true),
.cycle 17 9 false (2),
.cycle 18 9 false (2),
.cycle 8 37 false (5)
])
theorem kid01_part953_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part953) = true := by rfl

def kid01_part954 : Audit := .split 25 (5,false) (byMove [
.last 28 (2,true),
.cycle 24 8 false (1),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 25 1 false (-1),
.cycle 12 22 false (3),
.cycle 24 2 true (-1),
.last 26 (2,true),
.cycle 23 4 true (-1),
.cycle 22 4 true (-1),
.cycle 7 32 true (-1),
.cycle 19 8 false (1),
.last 27 (2,true),
.cycle 17 11 false (2),
.cycle 26 1 false (-2),
.cycle 12 29 false (3),
.cycle 25 1 false (-1),
.cycle 21 5 false (1),
.cycle 19 7 false (1),
.last 26 (2,true),
.cycle 18 9 false (2),
.cycle 17 9 false (2),
.cycle 7 37 false (5)
])
theorem kid01_part954_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part954) = true := by rfl

def kid01_part955 : Audit := .cycle 0 13 true (0)
theorem kid01_part955_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part955) = true := by rfl

def kid01_part956 : Audit := .cycle 0 12 true (0)
theorem kid01_part956_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part956) = true := by rfl

def kid01_part957 : Audit := .cycle 1 11 true (1)
theorem kid01_part957_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part957) = true := by rfl

def kid01_part958 : Audit := .cycle 6 12 true (2)
theorem kid01_part958_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part958) = true := by rfl

def kid01_part959 : Audit := .cycle 3 9 true (1)
theorem kid01_part959_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part959) = true := by rfl

def kid01_part960 : Audit := .cycle 1 12 true (1)
theorem kid01_part960_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part960) = true := by rfl

def kid01_part961 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 6 27 false (4),
.cycle 0 15 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.last 14 (2,true),
.last 18 (2,true),
.cycle 4 9 true (1),
.cycle 13 29 false (3),
.cycle 0 17 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 9 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part961_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part961) = true := by rfl

def kid01_part962 : Audit := .cycle 13 5 false (1)
theorem kid01_part962_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part962) = true := by rfl

def kid01_part963 : Audit := .split 19 (5,false) (byMove [
.last 22 (2,true),
.cycle 36 8 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 0, 0, 4096],[4096, 1024, 4096, 1024, 1024, 64, 1024, 1024, 4096, 1024, 1024, 64, 4096],4096⟩,
.cycle 19 1 false (-1),
.last 22 (2,true),
.cycle 18 2 true (-1),
.last 20 (2,true),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.cycle 16 4 true (-1),
.cycle 15 6 false (1),
.last 21 (2,true),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2048, 2048, 512, 512, 2, 256, 2048, 262144, 256, 512, 8192, 256, 264192, 264192, 512, 512, 8192, 256, 262144],[128, 2048, 262144, 2048, 2048, 2048, 128, 2048, 262144, 2048, 2048, 2048, 128, 2048, 262144, 2048, 2048, 264192, 262144],341120⟩,
.cycle 20 1 false (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 0, 1024, 4096],[4096, 1024, 4096, 1024, 1024, 64, 1024, 1024, 4096, 1024, 1024, 64, 4096],4096⟩,
.cycle 19 1 false (-1),
.cycle 17 3 false (1),
.cycle 15 5 false (1),
.last 20 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 512, 128, 256, 8, 1024, 0, 512, 4096],[4096, 1024, 4096, 1024, 1024, 64, 1024, 1024, 4096, 1024, 1024, 64, 4096],4096⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 0, 1024, 4096],[4096, 1024, 4096, 1024, 1024, 64, 1024, 1024, 4096, 1024, 1024, 64, 4096],4096⟩,
.cycle 13 7 false (2)
])
theorem kid01_part963_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part963) = true := by rfl

def kid01_part964 : Audit := .split 12 (2,true) (byMove [
.cycle 12 5 false (2),
.last 22 (5,false),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 9 6 true (1),
.last 18 (5,false),
.last 14 (5,false),
.cycle 6 16 true (1),
.last 16 (5,false),
.last 16 (5,false),
.cycle 0 14 true (0),
.cycle 13 5 false (1),
.last 20 (5,false),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 19 (5,false),
.cycle 11 2 true (2),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0)
])
theorem kid01_part964_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part964) = true := by rfl

def kid01_part965 : Audit := .cycle 7 6 true (2)
theorem kid01_part965_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part965) = true := by rfl

def kid01_part966 : Audit := .cycle 6 6 true (2)
theorem kid01_part966_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part966) = true := by rfl

def kid01_part967 : Audit := .cycle 10 2 true (2)
theorem kid01_part967_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part967) = true := by rfl

def kid01_part968 : Audit := .cycle 0 12 true (0)
theorem kid01_part968_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part968) = true := by rfl

def kid01_part969 : Audit := .cycle 1 11 true (1)
theorem kid01_part969_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part969) = true := by rfl

def kid01_part970 : Audit := .cycle 2 10 true (1)
theorem kid01_part970_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part970) = true := by rfl

def kid01_part971 : Audit := .cycle 7 7 true (2)
theorem kid01_part971_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part971) = true := by rfl

def kid01_part972 : Audit := .cycle 8 4 true (2)
theorem kid01_part972_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part972) = true := by rfl

def kid01_part973 : Audit := .split 12 (5,false) (byMove [
.cycle 11 2 true (3),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part973_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part973) = true := by rfl

def kid01_part949 : Audit := .split 11 (0,true) (byMove [(kid01_part950),(kid01_part951),(kid01_part952),(kid01_part953),(kid01_part954),(kid01_part955),(kid01_part956),(kid01_part957),(kid01_part958),(kid01_part959),(kid01_part960),(kid01_part961),(kid01_part962),(kid01_part963),(kid01_part964),(kid01_part965),(kid01_part966),(kid01_part967),(kid01_part968),(kid01_part969),(kid01_part970),(kid01_part971),(kid01_part972),(kid01_part973)])

theorem kid01_part949_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part949) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some mv)) (byMove [(kid01_part950),(kid01_part951),(kid01_part952),(kid01_part953),(kid01_part954),(kid01_part955),(kid01_part956),(kid01_part957),(kid01_part958),(kid01_part959),(kid01_part960),(kid01_part961),(kid01_part962),(kid01_part963),(kid01_part964),(kid01_part965),(kid01_part966),(kid01_part967),(kid01_part968),(kid01_part969),(kid01_part970),(kid01_part971),(kid01_part972),(kid01_part973)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part950_checked

  · exact kid01_part956_checked

  · exact kid01_part962_checked

  · exact kid01_part968_checked

  · exact kid01_part951_checked

  · exact kid01_part957_checked

  · exact kid01_part963_checked

  · exact kid01_part969_checked

  · exact kid01_part952_checked

  · exact kid01_part958_checked

  · exact kid01_part964_checked

  · exact kid01_part970_checked

  · exact kid01_part953_checked

  · exact kid01_part959_checked

  · exact kid01_part965_checked

  · exact kid01_part971_checked

  · exact kid01_part954_checked

  · exact kid01_part960_checked

  · exact kid01_part966_checked

  · exact kid01_part972_checked

  · exact kid01_part955_checked

  · exact kid01_part961_checked

  · exact kid01_part967_checked

  · exact kid01_part973_checked

def kid01_part974 : Audit := .cycle 9 2 true (2)
theorem kid01_part974_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part974) = true := by rfl

def kid01_part976 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.last 30 (5,false),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.last 35 (5,false),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.last 13 (5,false),
.cycle 14 5 false (0),
.cycle 15 3 false (1),
.last 19 (5,false),
.cycle 27 1 false (-1),
.last 33 (5,false),
.last 19 (5,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.last 25 (5,false),
.last 13 (5,false)
])
theorem kid01_part976_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part976) = true := by rfl

def kid01_part977 : Audit := .split 19 (5,false) (byMove [
.cycle 14 8 false (2),
.cycle 18 8 false (1),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 6 21 false (4),
.cycle 19 1 false (-1),
.last 20 (0,true),
.cycle 18 2 true (-1),
.cycle 12 17 false (2),
.cycle 18 4 true (-1),
.cycle 18 4 true (-1),
.cycle 12 16 true (-1),
.cycle 15 6 false (1),
.cycle 17 4 false (1),
.cycle 15 9 false (1),
.cycle 20 1 false (-2),
.cycle 12 23 false (2),
.cycle 19 1 false (-1),
.last 20 (0,true),
.cycle 15 5 false (1),
.cycle 17 3 false (1),
.cycle 15 7 false (1),
.cycle 15 7 false (1),
.cycle 2 19 false (4)
])
theorem kid01_part977_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part977) = true := by rfl

def kid01_part978 : Audit := .cycle 16 1 false (0)
theorem kid01_part978_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part978) = true := by rfl

def kid01_part979 : Audit := .split 25 (5,false) (byMove [
.cycle 16 12 false (2),
.cycle 24 8 false (1),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 24 2 true (-1),
.cycle 27 1 false (-1),
.cycle 22 4 true (-1),
.cycle 23 4 true (-1),
.cycle 13 20 true (-1),
.cycle 19 8 false (1),
.cycle 21 6 false (1),
.cycle 18 11 false (2),
.cycle 26 1 false (-2),
.cycle 13 29 false (3),
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 19 7 false (1),
.cycle 21 5 false (1),
.cycle 17 9 false (2),
.cycle 18 9 false (2),
.cycle 2 25 false (4)
])
theorem kid01_part979_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part979) = true := by rfl

def kid01_part980 : Audit := .split 25 (5,false) (byMove [
.cycle 16 12 false (2),
.cycle 24 8 false (1),
.cycle 27 1 false (-1),
.cycle 26 1 false (-2),
.cycle 6 27 false (4),
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 24 2 true (-1),
.cycle 12 22 false (3),
.cycle 23 4 true (-1),
.cycle 22 4 true (-1),
.cycle 12 20 true (-1),
.cycle 19 8 false (1),
.cycle 21 6 false (1),
.cycle 17 11 false (2),
.cycle 26 1 false (-2),
.cycle 12 29 false (3),
.cycle 25 1 false (-1),
.last 26 (0,true),
.cycle 19 7 false (1),
.cycle 21 5 false (1),
.cycle 18 9 false (2),
.cycle 17 9 false (2),
.cycle 2 25 false (4)
])
theorem kid01_part980_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part980) = true := by rfl

def kid01_part981 : Audit := .cycle 2 11 true (1)
theorem kid01_part981_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part981) = true := by rfl

def kid01_part982 : Audit := .cycle 0 12 true (0)
theorem kid01_part982_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part982) = true := by rfl

def kid01_part983 : Audit := .cycle 1 11 true (1)
theorem kid01_part983_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part983) = true := by rfl

def kid01_part984 : Audit := .cycle 6 12 true (2)
theorem kid01_part984_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part984) = true := by rfl

def kid01_part985 : Audit := .cycle 3 9 true (1)
theorem kid01_part985_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part985) = true := by rfl

def kid01_part986 : Audit := .cycle 1 12 true (1)
theorem kid01_part986_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part986) = true := by rfl

def kid01_part987 : Audit := .split 12 (5,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 6 27 false (4),
.cycle 2 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.cycle 9 5 true (2),
.cycle 11 3 true (3),
.cycle 10 9 true (2),
.cycle 4 9 true (1),
.cycle 13 29 false (3),
.cycle 2 15 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 7 9 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part987_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part987) = true := by rfl

def kid01_part988 : Audit := .split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.last 22 (5,false),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 18 (5,false),
.cycle 0 14 true (0),
.last 14 (5,false),
.cycle 9 6 true (2),
.last 16 (5,false),
.last 16 (5,false),
.cycle 2 12 true (1),
.cycle 14 5 false (0),
.cycle 15 3 false (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 19 (5,false),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 2 12 true (1)
])
theorem kid01_part988_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part988) = true := by rfl

def kid01_part989 : Audit := .split 19 (5,false) (byMove [
.cycle 14 8 false (2),
.cycle 36 8 false (0),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 24, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 19 1 false (-1),
.last 20 (0,true),
.cycle 18 2 true (-1),
.cycle 17 5 false (1),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.cycle 16 4 true (-1),
.cycle 15 6 false (1),
.cycle 17 4 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 20 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 19 1 false (-1),
.last 20 (0,true),
.cycle 15 5 false (1),
.cycle 17 3 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 8, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 8, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 13 7 false (2)
])
theorem kid01_part989_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part989) = true := by rfl

def kid01_part990 : Audit := .cycle 6 12 true (-1)
theorem kid01_part990_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part990) = true := by rfl

def kid01_part991 : Audit := .cycle 7 6 true (2)
theorem kid01_part991_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part991) = true := by rfl

def kid01_part992 : Audit := .cycle 6 6 true (2)
theorem kid01_part992_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part992) = true := by rfl

def kid01_part993 : Audit := .cycle 10 2 true (2)
theorem kid01_part993_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part993) = true := by rfl

def kid01_part994 : Audit := .cycle 0 12 true (0)
theorem kid01_part994_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part994) = true := by rfl

def kid01_part995 : Audit := .cycle 1 11 true (1)
theorem kid01_part995_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part995) = true := by rfl

def kid01_part996 : Audit := .cycle 2 10 true (1)
theorem kid01_part996_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part996) = true := by rfl

def kid01_part997 : Audit := .cycle 7 7 true (2)
theorem kid01_part997_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part997) = true := by rfl

def kid01_part998 : Audit := .cycle 8 4 true (2)
theorem kid01_part998_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part998) = true := by rfl

def kid01_part999 : Audit := .split 12 (5,false) (byMove [
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 11 2 true (3),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.last 13 (0,true),
.cycle 2 15 true (1),
.cycle 2 13 true (1),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part999_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part999) = true := by rfl

def kid01_part975 : Audit := .split 11 (2,true) (byMove [(kid01_part976),(kid01_part977),(kid01_part978),(kid01_part979),(kid01_part980),(kid01_part981),(kid01_part982),(kid01_part983),(kid01_part984),(kid01_part985),(kid01_part986),(kid01_part987),(kid01_part988),(kid01_part989),(kid01_part990),(kid01_part991),(kid01_part992),(kid01_part993),(kid01_part994),(kid01_part995),(kid01_part996),(kid01_part997),(kid01_part998),(kid01_part999)])

theorem kid01_part975_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part975) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid01_part976),(kid01_part977),(kid01_part978),(kid01_part979),(kid01_part980),(kid01_part981),(kid01_part982),(kid01_part983),(kid01_part984),(kid01_part985),(kid01_part986),(kid01_part987),(kid01_part988),(kid01_part989),(kid01_part990),(kid01_part991),(kid01_part992),(kid01_part993),(kid01_part994),(kid01_part995),(kid01_part996),(kid01_part997),(kid01_part998),(kid01_part999)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part976_checked

  · exact kid01_part982_checked

  · exact kid01_part988_checked

  · exact kid01_part994_checked

  · exact kid01_part977_checked

  · exact kid01_part983_checked

  · exact kid01_part989_checked

  · exact kid01_part995_checked

  · exact kid01_part978_checked

  · exact kid01_part984_checked

  · exact kid01_part990_checked

  · exact kid01_part996_checked

  · exact kid01_part979_checked

  · exact kid01_part985_checked

  · exact kid01_part991_checked

  · exact kid01_part997_checked

  · exact kid01_part980_checked

  · exact kid01_part986_checked

  · exact kid01_part992_checked

  · exact kid01_part998_checked

  · exact kid01_part981_checked

  · exact kid01_part987_checked

  · exact kid01_part993_checked

  · exact kid01_part999_checked

def kid01_part1000 : Audit := .cycle 8 4 true (2)
theorem kid01_part1000_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part1000) = true := by rfl

def kid01_part1001 : Audit := .cycle 7 4 true (2)
theorem kid01_part1001_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part1001) = true := by rfl

def kid01_part1002 : Audit := .split 12 (5,false) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.last 28 (2,true),
.last 14 (2,true),
.last 34 (2,true),
.last 34 (2,true),
.cycle 0 24 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 0, 2],[128, 256, 8, 65536, 8, 16384, 8192, 16384, 8, 65536, 262144, 0, 8192, 16384, 8, 65536, 0, 0, 262144],[131072, 262144, 262144, 1024, 1024, 2048, 131072, 131072, 262144, 65536, 65536, 131072, 131072, 131072, 262144, 65536, 65536, 131072, 262144],263168⟩,
.cycle 10 6 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 12 2 true (3)
]),
.cycle 9 4 true (2),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 27 1 false (-1),
.cycle 18 1 false (0),
.cycle 33 1 false (-1),
.cycle 33 1 false (-1),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 14 (0,true),
.cycle 10 6 true (1),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 12 2 true (3)
]),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 12 1 true (4),
.split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 15 14 false (3),
.last 14 (2,true),
.cycle 17 18 false (3),
.cycle 17 18 false (3),
.cycle 17 10 false (2),
.cycle 0 15 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[2, 32, 64, 16, 16, 32, 64],64⟩,
.last 14 (2,true),
.cycle 7 13 true (2),
.cycle 6 13 true (2),
.cycle 11 3 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 10 7 true (1),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 0 15 true (0),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 11 3 true (3)
]),
.cycle 10 5 true (2),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 19 11 false (2),
.cycle 18 1 false (0),
.cycle 22 13 false (2),
.cycle 21 13 false (2),
.cycle 17 18 false (2),
.last 14 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[64, 48, 2, 16, 16, 32, 64],64⟩,
.cycle 6 17 true (2),
.cycle 7 13 true (2),
.cycle 6 13 true (2),
.cycle 11 3 true (3),
.last 14 (0,true),
.cycle 10 7 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 48, 16, 16, 16, 32, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.last 14 (0,true),
.cycle 9 5 true (2),
.cycle 2 13 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 11 3 true (3)
]),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 3 true (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 8 5 true (2),
.cycle 12 1 true (4)
])
theorem kid01_part1002_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part1002) = true := by rfl

def kid01_part666 : Audit := .split 10 (5,true) (byMove [(kid01_part667),(kid01_part692),(kid01_part717),(kid01_part742),(kid01_part743),(kid01_part744),(kid01_part745),(kid01_part770),(kid01_part795),(kid01_part820),(kid01_part845),(kid01_part870),(kid01_part871),(kid01_part896),(kid01_part921),(kid01_part946),(kid01_part947),(kid01_part948),(kid01_part949),(kid01_part974),(kid01_part975),(kid01_part1000),(kid01_part1001),(kid01_part1002)])

theorem kid01_part666_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (kid01_part666) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part667),(kid01_part692),(kid01_part717),(kid01_part742),(kid01_part743),(kid01_part744),(kid01_part745),(kid01_part770),(kid01_part795),(kid01_part820),(kid01_part845),(kid01_part870),(kid01_part871),(kid01_part896),(kid01_part921),(kid01_part946),(kid01_part947),(kid01_part948),(kid01_part949),(kid01_part974),(kid01_part975),(kid01_part1000),(kid01_part1001),(kid01_part1002)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part667_checked

  · exact kid01_part745_checked

  · exact kid01_part871_checked

  · exact kid01_part949_checked

  · exact kid01_part692_checked

  · exact kid01_part770_checked

  · exact kid01_part896_checked

  · exact kid01_part974_checked

  · exact kid01_part717_checked

  · exact kid01_part795_checked

  · exact kid01_part921_checked

  · exact kid01_part975_checked

  · exact kid01_part742_checked

  · exact kid01_part820_checked

  · exact kid01_part946_checked

  · exact kid01_part1000_checked

  · exact kid01_part743_checked

  · exact kid01_part845_checked

  · exact kid01_part947_checked

  · exact kid01_part1001_checked

  · exact kid01_part744_checked

  · exact kid01_part870_checked

  · exact kid01_part948_checked

  · exact kid01_part1002_checked

def kid01_part1003 : Audit := .cycle 0 10 true (0)
theorem kid01_part1003_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,0⟩)) (kid01_part1003) = true := by rfl

def kid01_part1004 : Audit := .cycle 1 9 true (1)
theorem kid01_part1004_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,1⟩)) (kid01_part1004) = true := by rfl

def kid01_part1005 : Audit := .cycle 2 8 true (1)
theorem kid01_part1005_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,2⟩)) (kid01_part1005) = true := by rfl

def kid01_part1006 : Audit := .cycle 7 5 true (3)
theorem kid01_part1006_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,3⟩)) (kid01_part1006) = true := by rfl

def kid01_part1007 : Audit := .cycle 8 2 true (3)
theorem kid01_part1007_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,4⟩)) (kid01_part1007) = true := by rfl

def kid01_part1009 : Audit := .split 11 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 12 17 false (3),
.split 12 (2,true) (byMove [
.cycle 0 15 false (4),
.cycle 33 1 false (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 38 1 false (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 13 5 false (1),
.last 14 (5,true),
.cycle 40 1 false (0),
.cycle 27 1 false (-1),
.cycle 13 26 false (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 28 1 false (0),
.cycle 22 1 false (0)
]),
.cycle 27 1 false (-1),
.cycle 12 22 false (3),
.split 12 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 0 33 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 0 38 false (4),
.cycle 0 16 false (4),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 13 5 false (1),
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 0 38 false (4),
.last 18 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 28 false (4),
.cycle 0 22 false (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.split 17 (5,true) (byMove [
.cycle 13 5 false (1),
.cycle 13 7 false (1),
.last 18 (2,true),
.cycle 13 9 false (1),
.cycle 13 9 false (1),
.cycle 0 21 false (4),
.cycle 0 22 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[34, 32, 64, 16, 16, 2, 64],64⟩,
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 28, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 12, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 0 21 true (-1),
.cycle 13 5 false (1),
.cycle 16 2 true (0),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 12, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 256, 128, 256, 8, 1024, 0, 0, 4096],[2048, 2048, 4096, 1024, 1024, 1024, 1024, 2048, 4096, 1024, 1024, 1024, 4096],4096⟩,
.last 23 (2,true),
.cycle 11 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[34, 32, 64, 16, 16, 2, 64],64⟩,
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 28, 28, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 12, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[32, 32, 64, 16, 16, 32, 64],64⟩
]),
.split 13 (5,true) (byMove [
.last 22 (2,true),
.last 28 (2,true),
.last 14 (2,true),
.last 34 (2,true),
.last 34 (2,true),
.cycle 0 18 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.last 22 (2,true),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 20 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
]),
.split 12 (2,true) (byMove [
.cycle 12 5 false (2),
.cycle 18 6 true (0),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 13 6 true (2),
.cycle 13 6 true (2),
.cycle 6 16 true (1),
.cycle 13 6 true (2),
.cycle 14 6 true (2),
.last 13 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 11 2 true (2),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.last 17 (2,true),
.last 29 (2,true),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 0 16 false (4),
.last 21 (2,true),
.last 25 (2,true),
.last 13 (2,true),
.last 29 (2,true),
.last 29 (2,true),
.cycle 0 15 true (0),
.cycle 12 5 false (2),
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 18 (2,true),
.cycle 11 2 true (2),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 10 4 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (3),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid01_part1009_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,0⟩)) (kid01_part1009) = true := by rfl

def kid01_part1010 : Audit := .cycle 9 2 true (3)
theorem kid01_part1010_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) (kid01_part1010) = true := by rfl

def kid01_part1011 : Audit := .split 11 (2,true) (byMove [
.split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 0 32 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 37 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (5,true),
.last 14 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[28, 32, 28, 16, 16, 64, 64],64⟩,
.cycle 27 1 false (-1),
.cycle 6 42 false (4),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 27 false (4),
.cycle 0 21 false (4)
]),
.cycle 12 17 false (3),
.cycle 16 1 false (0),
.cycle 27 1 false (-1),
.cycle 12 22 false (3),
.split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 34 1 false (-2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 39 1 false (-3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 13 (0,true),
.cycle 12 2 true (1),
.cycle 23 1 false (-1),
.cycle 27 1 false (-1),
.cycle 39 1 false (-3),
.cycle 17 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 29 1 false (-1),
.cycle 23 1 false (-1)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 13 20 false (2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.last 13 (5,true),
.cycle 0 14 true (0),
.cycle 9 8 true (2),
.cycle 9 6 true (2),
.cycle 9 10 true (2),
.cycle 9 10 true (2),
.last 13 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.last 13 (5,true),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.last 13 (5,true)
]),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 21 7 false (1),
.cycle 17 5 false (1),
.cycle 25 9 false (1),
.cycle 25 9 false (1),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 14 (0,true),
.cycle 12 2 true (2),
.cycle 17 5 false (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 19 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
]),
.cycle 6 12 true (-1),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 28 1 false (-2),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 17 1 false (-1),
.last 13 (0,true),
.cycle 24 1 false (0),
.cycle 20 1 false (0),
.cycle 28 1 false (0),
.cycle 28 1 false (0),
.cycle 6 15 true (1),
.last 13 (0,true),
.cycle 12 2 true (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 17 1 false (-1),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 11 2 true (2),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 10 4 true (2)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (3),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid01_part1011_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,2⟩)) (kid01_part1011) = true := by rfl

def kid01_part1012 : Audit := .cycle 8 4 true (3)
theorem kid01_part1012_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,3⟩)) (kid01_part1012) = true := by rfl

def kid01_part1013 : Audit := .cycle 7 4 true (3)
theorem kid01_part1013_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,4⟩)) (kid01_part1013) = true := by rfl

def kid01_part1014 : Audit := .split 11 (5,true) (byMove [
.split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 0 32 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 0 37 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 17 1 false (1),
.cycle 13 5 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 6 42 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 27 false (4),
.cycle 0 21 false (4)
]),
.cycle 12 17 false (3),
.split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 33 1 false (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 38 1 false (-2),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 17 1 false (1),
.last 13 (0,true),
.cycle 15 5 false (1),
.cycle 40 1 false (0),
.cycle 27 1 false (-1),
.cycle 13 26 false (3),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 28 1 false (0),
.cycle 22 1 false (0)
]),
.cycle 27 1 false (-1),
.cycle 12 22 false (3),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 6 12 true (2),
.cycle 3 9 true (1),
.cycle 1 12 true (1),
.cycle 21 1 false (1),
.split 12 (0,true) (byMove [
.cycle 0 32 false (4),
.cycle 13 20 false (2),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 9 8 true (2),
.last 13 (2,true),
.cycle 9 10 true (2),
.cycle 9 10 true (2),
.cycle 9 6 true (2),
.cycle 13 5 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.cycle 0 14 true (0),
.cycle 9 4 true (2),
.last 13 (2,true),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (2)
]),
.cycle 11 2 true (2),
.split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 18 6 true (0),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 6 20 false (4),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 13 6 true (2),
.cycle 6 16 true (1),
.cycle 13 6 true (2),
.cycle 14 6 true (2),
.cycle 13 6 true (2),
.last 13 (0,true),
.cycle 15 5 false (1),
.cycle 6 12 true (-1),
.cycle 5 8 true (1),
.cycle 6 8 true (1),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 9 4 true (2),
.cycle 2 12 true (1),
.cycle 8 6 true (2),
.cycle 7 6 true (2),
.cycle 11 2 true (2)
]),
.cycle 7 6 true (2),
.cycle 6 6 true (2),
.cycle 15 1 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 7 7 true (3),
.cycle 8 4 true (3),
.cycle 10 2 true (3)
])
theorem kid01_part1014_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,false,5⟩)) (kid01_part1014) = true := by rfl

def kid01_part1015 : Audit := .cycle 0 11 true (0)
theorem kid01_part1015_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,0⟩)) (kid01_part1015) = true := by rfl

def kid01_part1016 : Audit := .cycle 1 10 true (1)
theorem kid01_part1016_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,1⟩)) (kid01_part1016) = true := by rfl

def kid01_part1017 : Audit := .cycle 6 11 true (2)
theorem kid01_part1017_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,2⟩)) (kid01_part1017) = true := by rfl

def kid01_part1018 : Audit := .cycle 3 8 true (1)
theorem kid01_part1018_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,3⟩)) (kid01_part1018) = true := by rfl

def kid01_part1019 : Audit := .cycle 1 11 true (1)
theorem kid01_part1019_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,4⟩)) (kid01_part1019) = true := by rfl

def kid01_part1020 : Audit := .cycle 10 1 true (4)
theorem kid01_part1020_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨false,true,5⟩)) (kid01_part1020) = true := by rfl

def kid01_part1022 : Audit := .cycle 0 15 false (4)
theorem kid01_part1022_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid01_part1022) = true := by rfl

def kid01_part1023 : Audit := .cycle 6 19 true (-1)
theorem kid01_part1023_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid01_part1023) = true := by rfl

def kid01_part1024 : Audit := .split 12 (2,true) (byMove [
.cycle 0 15 false (4),
.cycle 6 17 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 38 1 false (-2),
.last 13 (5,true),
.cycle 9 5 true (2),
.cycle 1 14 true (1),
.cycle 6 20 true (1),
.cycle 6 11 true (1),
.cycle 6 20 true (2),
.last 16 (5,true),
.cycle 13 5 false (1),
.last 14 (5,true),
.cycle 40 1 false (0),
.cycle 27 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 2048, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 1024, 1024, 1024, 4096, 1024, 2048, 1024, 1024, 1024, 4096, 4096],4096⟩,
.last 13 (5,true),
.cycle 9 5 true (2),
.cycle 1 14 true (1),
.cycle 6 18 true (2),
.cycle 4 9 true (1),
.cycle 28 1 false (0),
.cycle 22 1 false (0)
])
theorem kid01_part1024_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid01_part1024) = true := by rfl

def kid01_part1025 : Audit := .cycle 27 1 false (-1)
theorem kid01_part1025_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid01_part1025) = true := by rfl

def kid01_part1026 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 2048, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 4096, 1024, 1024, 4096, 1024, 2048, 4096, 1024, 1024, 4096, 4096],4096⟩
theorem kid01_part1026_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid01_part1026) = true := by rfl

def kid01_part1027 : Audit := .split 12 (5,true) (byMove [
.cycle 0 15 false (4),
.cycle 6 17 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 15 24 false (2),
.cycle 14 6 false (0),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 7 20 true (2),
.cycle 6 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[56, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 9 10 true (2),
.cycle 13 5 false (1),
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 27 1 false (-1),
.cycle 23 16 false (2),
.cycle 12 6 false (2),
.cycle 9 5 true (2),
.last 14 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 2048, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 4096, 1024, 1024, 256, 8, 2048, 4096, 1024, 1024, 256, 4096],4096⟩,
.cycle 4 9 true (1),
.cycle 19 10 false (2),
.cycle 16 8 false (2)
])
theorem kid01_part1027_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid01_part1027) = true := by rfl

def kid01_part1028 : Audit := .cycle 0 13 true (0)
theorem kid01_part1028_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid01_part1028) = true := by rfl

def kid01_part1029 : Audit := .cycle 9 3 true (3)
theorem kid01_part1029_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid01_part1029) = true := by rfl

def kid01_part1030 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 16 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 9 6 true (3),
.cycle 9 5 true (3),
.last 16 (5,true),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.last 25 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1030_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid01_part1030) = true := by rfl

def kid01_part1031 : Audit := .cycle 8 5 true (3)
theorem kid01_part1031_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid01_part1031) = true := by rfl

def kid01_part1032 : Audit := .cycle 7 5 true (3)
theorem kid01_part1032_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid01_part1032) = true := by rfl

def kid01_part1033 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 16 9 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 9 6 true (3),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.cycle 21 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1033_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid01_part1033) = true := by rfl

def kid01_part1034 : Audit := .split 17 (5,true) (byMove [
.cycle 13 5 false (1),
.cycle 13 7 false (1),
.last 18 (2,true),
.cycle 13 9 false (1),
.cycle 13 9 false (1),
.cycle 13 11 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 41, 33, 64],[33, 32, 64, 16, 16, 1, 64],64⟩,
.cycle 24 18 true (4),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 56, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 19 10 true (3),
.cycle 13 5 false (1),
.cycle 16 2 true (0),
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 15 6 false (1),
.cycle 11 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 42, 34, 64],[34, 32, 64, 16, 16, 2, 64],64⟩,
.last 18 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 56, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 40, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩
])
theorem kid01_part1034_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid01_part1034) = true := by rfl

def kid01_part1035 : Audit := .split 13 (5,true) (byMove [
.last 22 (2,true),
.last 28 (2,true),
.last 14 (2,true),
.last 34 (2,true),
.last 34 (2,true),
.cycle 15 8 false (1),
.last 16 (2,true),
.last 18 (2,true),
.last 14 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.cycle 9 8 true (2),
.last 22 (2,true),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 14 6 false (2),
.cycle 0 17 true (0),
.cycle 9 5 true (2),
.last 14 (2,true),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 10 5 true (2)
])
theorem kid01_part1035_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid01_part1035) = true := by rfl

def kid01_part1036 : Audit := .split 12 (2,true) (byMove [
.cycle 12 5 false (2),
.cycle 6 15 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 2048, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 1024, 1024, 1024, 4096, 1024, 2048, 1024, 1024, 1024, 4096, 4096],4096⟩,
.last 13 (5,true),
.cycle 7 9 true (2),
.last 14 (5,true),
.cycle 6 19 true (1),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[16, 32, 16, 16, 16, 64, 64],64⟩,
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.last 13 (5,true),
.cycle 11 2 true (2),
.last 14 (5,true),
.cycle 2 13 true (1),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true)
])
theorem kid01_part1036_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid01_part1036) = true := by rfl

def kid01_part1037 : Audit := .cycle 5 7 true (1)
theorem kid01_part1037_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid01_part1037) = true := by rfl

def kid01_part1038 : Audit := .cycle 6 7 true (2)
theorem kid01_part1038_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid01_part1038) = true := by rfl

def kid01_part1039 : Audit := .split 12 (5,true) (byMove [
.last 17 (2,true),
.cycle 6 15 true (-1),
.last 13 (2,true),
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 56, 64],[56, 32, 64, 16, 16, 56, 64],64⟩,
.cycle 14 6 false (0),
.cycle 12 9 false (3),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 9 8 true (2),
.cycle 12 5 false (2),
.cycle 12 2 true (1),
.last 13 (2,true),
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.cycle 12 6 false (2),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 5 true (2)
])
theorem kid01_part1039_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid01_part1039) = true := by rfl

def kid01_part1040 : Audit := .cycle 0 13 true (0)
theorem kid01_part1040_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid01_part1040) = true := by rfl

def kid01_part1041 : Audit := .cycle 9 3 true (3)
theorem kid01_part1041_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid01_part1041) = true := by rfl

def kid01_part1042 : Audit := .split 12 (2,true) (byMove [
.cycle 2 12 true (1),
.cycle 9 4 true (3),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 9 6 true (3),
.cycle 11 2 true (3),
.last 14 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[4, 32, 16, 16, 16, 64, 64],64⟩,
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1042_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid01_part1042) = true := by rfl

def kid01_part1043 : Audit := .cycle 8 5 true (3)
theorem kid01_part1043_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid01_part1043) = true := by rfl

def kid01_part1044 : Audit := .cycle 7 5 true (3)
theorem kid01_part1044_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid01_part1044) = true := by rfl

def kid01_part1045 : Audit := .split 12 (5,true) (byMove [
.cycle 10 4 true (3),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 14 8 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 9 6 true (3),
.cycle 11 2 true (3),
.cycle 12 2 true (3),
.last 13 (2,true),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.cycle 14 6 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1045_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid01_part1045) = true := by rfl

def kid01_part1021 : Audit := .split 11 (0,true) (byMove [(kid01_part1022),(kid01_part1023),(kid01_part1024),(kid01_part1025),(kid01_part1026),(kid01_part1027),(kid01_part1028),(kid01_part1029),(kid01_part1030),(kid01_part1031),(kid01_part1032),(kid01_part1033),(kid01_part1034),(kid01_part1035),(kid01_part1036),(kid01_part1037),(kid01_part1038),(kid01_part1039),(kid01_part1040),(kid01_part1041),(kid01_part1042),(kid01_part1043),(kid01_part1044),(kid01_part1045)])

theorem kid01_part1021_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (kid01_part1021) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) 11 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid01_part1022),(kid01_part1023),(kid01_part1024),(kid01_part1025),(kid01_part1026),(kid01_part1027),(kid01_part1028),(kid01_part1029),(kid01_part1030),(kid01_part1031),(kid01_part1032),(kid01_part1033),(kid01_part1034),(kid01_part1035),(kid01_part1036),(kid01_part1037),(kid01_part1038),(kid01_part1039),(kid01_part1040),(kid01_part1041),(kid01_part1042),(kid01_part1043),(kid01_part1044),(kid01_part1045)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1022_checked

  · exact kid01_part1028_checked

  · exact kid01_part1034_checked

  · exact kid01_part1040_checked

  · exact kid01_part1023_checked

  · exact kid01_part1029_checked

  · exact kid01_part1035_checked

  · exact kid01_part1041_checked

  · exact kid01_part1024_checked

  · exact kid01_part1030_checked

  · exact kid01_part1036_checked

  · exact kid01_part1042_checked

  · exact kid01_part1025_checked

  · exact kid01_part1031_checked

  · exact kid01_part1037_checked

  · exact kid01_part1043_checked

  · exact kid01_part1026_checked

  · exact kid01_part1032_checked

  · exact kid01_part1038_checked

  · exact kid01_part1044_checked

  · exact kid01_part1027_checked

  · exact kid01_part1033_checked

  · exact kid01_part1039_checked

  · exact kid01_part1045_checked

def kid01_part1047 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 14 23 false (3),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 14 28 false (3),
.cycle 0 17 false (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.last 16 (2,true),
.cycle 15 5 false (1),
.last 24 (2,true),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 19 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 10 4 true (3)
])
theorem kid01_part1047_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part1047) = true := by rfl

def kid01_part1048 : Audit := .cycle 9 4 true (3)
theorem kid01_part1048_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part1048) = true := by rfl

def kid01_part1049 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 14 23 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 14 28 false (3),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 14 true (1),
.cycle 13 3 true (3),
.last 14 (0,true),
.cycle 19 5 false (1),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 10 4 true (3)
])
theorem kid01_part1049_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part1049) = true := by rfl

def kid01_part1050 : Audit := .cycle 8 6 true (3)
theorem kid01_part1050_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part1050) = true := by rfl

def kid01_part1051 : Audit := .cycle 7 6 true (3)
theorem kid01_part1051_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part1051) = true := by rfl

def kid01_part1052 : Audit := .split 19 (2,true) (byMove [
.last 20 (0,true),
.cycle 15 8 false (1),
.cycle 22 1 false (-2),
.cycle 15 10 false (1),
.cycle 15 10 false (1),
.cycle 16 4 false (0),
.cycle 15 24 false (4),
.cycle 15 22 false (3),
.cycle 6 20 false (4),
.cycle 13 16 false (3),
.cycle 1 20 false (4),
.cycle 17 3 true (-2),
.last 20 (0,true),
.cycle 15 6 false (1),
.cycle 14 14 false (2),
.cycle 14 12 false (2),
.cycle 14 12 false (2),
.cycle 16 4 false (0),
.cycle 12 22 false (4),
.cycle 12 20 false (4),
.cycle 2 18 false (4),
.cycle 13 14 false (3),
.cycle 14 10 false (2),
.cycle 14 8 false (2)
])
theorem kid01_part1052_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part1052) = true := by rfl

def kid01_part1053 : Audit := .cycle 0 13 true (0)
theorem kid01_part1053_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part1053) = true := by rfl

def kid01_part1054 : Audit := .cycle 1 12 true (1)
theorem kid01_part1054_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part1054) = true := by rfl

def kid01_part1055 : Audit := .cycle 6 13 true (2)
theorem kid01_part1055_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part1055) = true := by rfl

def kid01_part1056 : Audit := .cycle 3 10 true (1)
theorem kid01_part1056_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part1056) = true := by rfl

def kid01_part1057 : Audit := .cycle 1 13 true (1)
theorem kid01_part1057_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part1057) = true := by rfl

def kid01_part1058 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 9 7 true (3),
.cycle 22 1 false (0),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 12 4 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 1 16 true (1),
.cycle 13 3 true (4),
.last 16 (0,true),
.cycle 11 5 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 56, 48, 64],[64, 32, 16, 16, 16, 32, 64],64⟩,
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 12 5 true (4),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 10 6 true (3)
])
theorem kid01_part1058_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part1058) = true := by rfl

def kid01_part1059 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 6 27 true (-1),
.last 14 (2,true),
.cycle 35 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 4096, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 4096, 1024, 1024, 2048, 1024, 2048, 4096, 1024, 1024, 1024, 4096],4128⟩,
.cycle 14 7 false (2),
.cycle 0 15 true (0),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 9 7 true (3),
.cycle 15 5 false (1),
.last 24 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 14 5 false (2),
.cycle 0 15 true (0),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
])
theorem kid01_part1059_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part1059) = true := by rfl

def kid01_part1060 : Audit := .cycle 11 2 true (3)
theorem kid01_part1060_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part1060) = true := by rfl

def kid01_part1061 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 6 27 true (-1),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 32, 24, 16, 16, 16, 64],64⟩,
.cycle 15 12 false (1),
.last 14 (0,true),
.cycle 9 5 true (3),
.cycle 6 17 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 8 9 true (3),
.last 14 (0,true),
.cycle 19 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.last 14 (0,true),
.cycle 9 5 true (3),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
])
theorem kid01_part1061_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part1061) = true := by rfl

def kid01_part1062 : Audit := .cycle 7 7 true (3)
theorem kid01_part1062_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part1062) = true := by rfl

def kid01_part1063 : Audit := .cycle 6 7 true (2)
theorem kid01_part1063_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part1063) = true := by rfl

def kid01_part1064 : Audit := .split 19 (2,true) (byMove [
.last 20 (0,true),
.cycle 15 8 false (1),
.cycle 22 1 false (-2),
.cycle 15 10 false (1),
.cycle 15 10 false (1),
.cycle 16 4 false (0),
.last 20 (0,true),
.cycle 15 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 32, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 15 8 false (1),
.last 20 (0,true),
.cycle 15 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 16 4 false (0),
.last 20 (0,true),
.cycle 13 8 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 12, 4, 64],[64, 32, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 24, 64],[64, 32, 8, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 14 6 false (2)
])
theorem kid01_part1064_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part1064) = true := by rfl

def kid01_part1065 : Audit := .cycle 0 13 true (0)
theorem kid01_part1065_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part1065) = true := by rfl

def kid01_part1066 : Audit := .cycle 1 12 true (1)
theorem kid01_part1066_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part1066) = true := by rfl

def kid01_part1067 : Audit := .cycle 2 11 true (1)
theorem kid01_part1067_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part1067) = true := by rfl

def kid01_part1068 : Audit := .cycle 7 8 true (3)
theorem kid01_part1068_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part1068) = true := by rfl

def kid01_part1069 : Audit := .cycle 8 5 true (3)
theorem kid01_part1069_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part1069) = true := by rfl

def kid01_part1070 : Audit := .cycle 10 3 true (3)
theorem kid01_part1070_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part1070) = true := by rfl

def kid01_part1046 : Audit := .split 12 (5,true) (byMove [(kid01_part1047),(kid01_part1048),(kid01_part1049),(kid01_part1050),(kid01_part1051),(kid01_part1052),(kid01_part1053),(kid01_part1054),(kid01_part1055),(kid01_part1056),(kid01_part1057),(kid01_part1058),(kid01_part1059),(kid01_part1060),(kid01_part1061),(kid01_part1062),(kid01_part1063),(kid01_part1064),(kid01_part1065),(kid01_part1066),(kid01_part1067),(kid01_part1068),(kid01_part1069),(kid01_part1070)])

theorem kid01_part1046_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (kid01_part1046) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,1⟩)) (5,true) (some mv)) (byMove [(kid01_part1047),(kid01_part1048),(kid01_part1049),(kid01_part1050),(kid01_part1051),(kid01_part1052),(kid01_part1053),(kid01_part1054),(kid01_part1055),(kid01_part1056),(kid01_part1057),(kid01_part1058),(kid01_part1059),(kid01_part1060),(kid01_part1061),(kid01_part1062),(kid01_part1063),(kid01_part1064),(kid01_part1065),(kid01_part1066),(kid01_part1067),(kid01_part1068),(kid01_part1069),(kid01_part1070)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1047_checked

  · exact kid01_part1053_checked

  · exact kid01_part1059_checked

  · exact kid01_part1065_checked

  · exact kid01_part1048_checked

  · exact kid01_part1054_checked

  · exact kid01_part1060_checked

  · exact kid01_part1066_checked

  · exact kid01_part1049_checked

  · exact kid01_part1055_checked

  · exact kid01_part1061_checked

  · exact kid01_part1067_checked

  · exact kid01_part1050_checked

  · exact kid01_part1056_checked

  · exact kid01_part1062_checked

  · exact kid01_part1068_checked

  · exact kid01_part1051_checked

  · exact kid01_part1057_checked

  · exact kid01_part1063_checked

  · exact kid01_part1069_checked

  · exact kid01_part1052_checked

  · exact kid01_part1058_checked

  · exact kid01_part1064_checked

  · exact kid01_part1070_checked

def kid01_part1072 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 6 17 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 30 9 false (0),
.last 13 (5,true),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.cycle 6 23 true (2),
.cycle 6 11 true (1),
.cycle 1 25 true (1),
.cycle 7 9 true (2),
.last 17 (5,true),
.last 14 (5,true),
.cycle 20 5 false (1),
.cycle 27 1 false (-1),
.cycle 11 26 false (3),
.last 13 (5,true),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.cycle 2 21 true (1),
.cycle 4 9 true (1),
.cycle 16 13 false (2),
.cycle 14 9 false (2)
])
theorem kid01_part1072_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid01_part1072) = true := by rfl

def kid01_part1073 : Audit := .cycle 6 19 true (-1)
theorem kid01_part1073_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid01_part1073) = true := by rfl

def kid01_part1074 : Audit := .cycle 16 1 false (0)
theorem kid01_part1074_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid01_part1074) = true := by rfl

def kid01_part1075 : Audit := .cycle 27 1 false (-1)
theorem kid01_part1075_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid01_part1075) = true := by rfl

def kid01_part1076 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 24, 16, 16, 64, 64],64⟩
theorem kid01_part1076_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid01_part1076) = true := by rfl

def kid01_part1077 : Audit := .split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 6 17 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 33 7 false (-1),
.cycle 15 7 false (0),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.cycle 29 7 false (3),
.cycle 6 11 true (1),
.cycle 43 7 false (1),
.cycle 7 9 true (2),
.last 13 (0,true),
.cycle 12 2 true (1),
.cycle 15 7 false (1),
.cycle 27 1 false (-1),
.cycle 35 7 false (-1),
.cycle 6 13 false (4),
.cycle 9 5 true (2),
.cycle 1 15 true (1),
.cycle 37 7 false (1),
.cycle 4 9 true (1),
.cycle 23 7 false (1),
.cycle 19 7 false (1)
])
theorem kid01_part1077_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid01_part1077) = true := by rfl

def kid01_part1078 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 19 8 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 8 8 true (3),
.cycle 9 5 true (3),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 8, 1024, 128, 256, 8, 1024, 1024, 1024, 4096],[1024, 2048, 1, 1024, 1024, 4096, 4096, 2048, 1, 1024, 1024, 4096, 4096],4096⟩,
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1078_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid01_part1078) = true := by rfl

def kid01_part1079 : Audit := .cycle 9 3 true (3)
theorem kid01_part1079_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid01_part1079) = true := by rfl

def kid01_part1080 : Audit := .cycle 6 15 true (2)
theorem kid01_part1080_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid01_part1080) = true := by rfl

def kid01_part1081 : Audit := .cycle 8 5 true (3)
theorem kid01_part1081_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid01_part1081) = true := by rfl

def kid01_part1082 : Audit := .cycle 7 5 true (3)
theorem kid01_part1082_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid01_part1082) = true := by rfl

def kid01_part1083 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 19 8 true (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 8 8 true (3),
.cycle 9 5 true (3),
.cycle 8 10 true (3),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 16, 64],64⟩,
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1083_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid01_part1083) = true := by rfl

def kid01_part1084 : Audit := .split 12 (0,true) (byMove [
.cycle 0 34 false (5),
.cycle 6 15 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.last 55 (5,true),
.last 13 (5,true),
.cycle 0 15 true (0),
.last 14 (5,true),
.last 16 (5,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.last 31 (5,true),
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.last 13 (5,true),
.cycle 0 15 true (0),
.last 14 (5,true),
.cycle 11 2 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.last 13 (5,true)
])
theorem kid01_part1084_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid01_part1084) = true := by rfl

def kid01_part1085 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 21 7 false (1),
.cycle 17 5 false (1),
.cycle 25 9 false (1),
.cycle 25 9 false (1),
.cycle 15 12 false (1),
.last 14 (0,true),
.cycle 11 7 true (2),
.cycle 6 19 true (2),
.cycle 11 9 true (2),
.cycle 11 9 true (2),
.cycle 11 12 true (2),
.last 14 (0,true),
.cycle 12 2 true (2),
.cycle 17 5 false (1),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.last 14 (0,true),
.cycle 9 5 true (2),
.cycle 2 15 true (1),
.cycle 8 7 true (2),
.cycle 7 7 true (2),
.cycle 10 5 true (2)
])
theorem kid01_part1085_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid01_part1085) = true := by rfl

def kid01_part1086 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 64, 64],64⟩
theorem kid01_part1086_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid01_part1086) = true := by rfl

def kid01_part1087 : Audit := .cycle 5 7 true (1)
theorem kid01_part1087_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid01_part1087) = true := by rfl

def kid01_part1088 : Audit := .cycle 6 7 true (2)
theorem kid01_part1088_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid01_part1088) = true := by rfl

def kid01_part1089 : Audit := .split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 6 15 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 24, 64],64⟩,
.cycle 13 18 false (1),
.last 13 (0,true),
.cycle 1 14 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 4, 64],64⟩,
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 5 19 true (1),
.last 13 (0,true),
.cycle 12 2 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.last 13 (0,true),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 10 5 true (2)
])
theorem kid01_part1089_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid01_part1089) = true := by rfl

def kid01_part1090 : Audit := .split 12 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 9 4 true (3),
.cycle 0 14 true (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 8 8 true (3),
.last 19 (5,true),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1090_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid01_part1090) = true := by rfl

def kid01_part1091 : Audit := .cycle 9 3 true (3)
theorem kid01_part1091_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid01_part1091) = true := by rfl

def kid01_part1092 : Audit := .cycle 2 11 true (1)
theorem kid01_part1092_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid01_part1092) = true := by rfl

def kid01_part1093 : Audit := .cycle 8 5 true (3)
theorem kid01_part1093_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid01_part1093) = true := by rfl

def kid01_part1094 : Audit := .cycle 7 5 true (3)
theorem kid01_part1094_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid01_part1094) = true := by rfl

def kid01_part1095 : Audit := .split 12 (5,true) (byMove [
.last 13 (0,true),
.cycle 9 4 true (3),
.cycle 10 4 true (3),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 15 9 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 8 8 true (3),
.last 13 (0,true),
.cycle 12 2 true (3),
.cycle 11 2 true (3),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 32, 16, 16, 16, 64],64⟩,
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1095_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid01_part1095) = true := by rfl

def kid01_part1071 : Audit := .split 11 (2,true) (byMove [(kid01_part1072),(kid01_part1073),(kid01_part1074),(kid01_part1075),(kid01_part1076),(kid01_part1077),(kid01_part1078),(kid01_part1079),(kid01_part1080),(kid01_part1081),(kid01_part1082),(kid01_part1083),(kid01_part1084),(kid01_part1085),(kid01_part1086),(kid01_part1087),(kid01_part1088),(kid01_part1089),(kid01_part1090),(kid01_part1091),(kid01_part1092),(kid01_part1093),(kid01_part1094),(kid01_part1095)])

theorem kid01_part1071_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (kid01_part1071) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid01_part1072),(kid01_part1073),(kid01_part1074),(kid01_part1075),(kid01_part1076),(kid01_part1077),(kid01_part1078),(kid01_part1079),(kid01_part1080),(kid01_part1081),(kid01_part1082),(kid01_part1083),(kid01_part1084),(kid01_part1085),(kid01_part1086),(kid01_part1087),(kid01_part1088),(kid01_part1089),(kid01_part1090),(kid01_part1091),(kid01_part1092),(kid01_part1093),(kid01_part1094),(kid01_part1095)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1072_checked

  · exact kid01_part1078_checked

  · exact kid01_part1084_checked

  · exact kid01_part1090_checked

  · exact kid01_part1073_checked

  · exact kid01_part1079_checked

  · exact kid01_part1085_checked

  · exact kid01_part1091_checked

  · exact kid01_part1074_checked

  · exact kid01_part1080_checked

  · exact kid01_part1086_checked

  · exact kid01_part1092_checked

  · exact kid01_part1075_checked

  · exact kid01_part1081_checked

  · exact kid01_part1087_checked

  · exact kid01_part1093_checked

  · exact kid01_part1076_checked

  · exact kid01_part1082_checked

  · exact kid01_part1088_checked

  · exact kid01_part1094_checked

  · exact kid01_part1077_checked

  · exact kid01_part1083_checked

  · exact kid01_part1089_checked

  · exact kid01_part1095_checked

def kid01_part1096 : Audit := .cycle 7 5 true (3)
theorem kid01_part1096_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,3⟩)) (kid01_part1096) = true := by rfl

def kid01_part1097 : Audit := .cycle 6 5 true (2)
theorem kid01_part1097_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,4⟩)) (kid01_part1097) = true := by rfl

def kid01_part1099 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (4),
.cycle 6 17 false (4),
.last 13 (2,true),
.cycle 19 1 false (-1),
.last 39 (2,true),
.cycle 15 1 false (-1),
.cycle 9 5 true (2),
.last 14 (2,true),
.last 21 (2,true),
.cycle 6 11 true (1),
.last 23 (2,true),
.cycle 17 1 false (1),
.cycle 13 5 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 27 1 false (-1),
.last 37 (2,true),
.cycle 15 1 false (-1),
.cycle 9 5 true (2),
.last 14 (2,true),
.last 21 (2,true),
.cycle 4 9 true (1),
.last 29 (2,true),
.last 23 (2,true)
])
theorem kid01_part1099_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid01_part1099) = true := by rfl

def kid01_part1100 : Audit := .cycle 6 19 true (-1)
theorem kid01_part1100_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid01_part1100) = true := by rfl

def kid01_part1101 : Audit := .split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 6 17 false (4),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 38 1 false (-2),
.cycle 15 1 false (-1),
.cycle 9 5 true (2),
.cycle 1 14 true (1),
.cycle 6 20 true (1),
.cycle 6 11 true (1),
.cycle 6 20 true (2),
.cycle 17 1 false (1),
.last 13 (0,true),
.cycle 15 5 false (1),
.cycle 40 1 false (0),
.cycle 27 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 24, 64],64⟩,
.cycle 15 1 false (-1),
.cycle 9 5 true (2),
.cycle 1 14 true (1),
.cycle 6 18 true (2),
.cycle 4 9 true (1),
.cycle 28 1 false (0),
.cycle 22 1 false (0)
])
theorem kid01_part1101_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid01_part1101) = true := by rfl

def kid01_part1102 : Audit := .cycle 27 1 false (-1)
theorem kid01_part1102_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid01_part1102) = true := by rfl

def kid01_part1103 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 64, 16, 16, 24, 64],64⟩
theorem kid01_part1103_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid01_part1103) = true := by rfl

def kid01_part1104 : Audit := .cycle 15 1 false (-1)
theorem kid01_part1104_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid01_part1104) = true := by rfl

def kid01_part1105 : Audit := .split 12 (0,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 46 1 false (8),
.cycle 9 5 true (3),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1105_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid01_part1105) = true := by rfl

def kid01_part1106 : Audit := .cycle 9 3 true (3)
theorem kid01_part1106_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid01_part1106) = true := by rfl

def kid01_part1107 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 23 false (3),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 15 true (2),
.cycle 6 12 true (2),
.cycle 1 13 true (1),
.cycle 46 1 false (8),
.cycle 9 5 true (3),
.cycle 6 17 true (2),
.cycle 8 7 true (3),
.cycle 4 9 true (1),
.cycle 6 27 true (-1),
.cycle 22 1 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1107_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid01_part1107) = true := by rfl

def kid01_part1108 : Audit := .cycle 8 5 true (3)
theorem kid01_part1108_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid01_part1108) = true := by rfl

def kid01_part1109 : Audit := .cycle 7 5 true (3)
theorem kid01_part1109_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid01_part1109) = true := by rfl

def kid01_part1110 : Audit := .cycle 46 1 false (8)
theorem kid01_part1110_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid01_part1110) = true := by rfl

def kid01_part1111 : Audit := .split 12 (0,true) (byMove [
.cycle 0 34 false (5),
.cycle 6 15 true (-1),
.last 13 (2,true),
.cycle 19 1 false (-1),
.cycle 46 9 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 13 7 true (3),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 9 11 true (2),
.cycle 13 5 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 9 7 true (2),
.last 13 (2,true),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 2 true (2)
])
theorem kid01_part1111_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid01_part1111) = true := by rfl

def kid01_part1112 : Audit := .cycle 11 2 true (2)
theorem kid01_part1112_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid01_part1112) = true := by rfl

def kid01_part1113 : Audit := .split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 6 15 true (-1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 24, 16, 16, 16, 64],64⟩,
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 7 14 true (2),
.cycle 6 19 true (1),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 7 9 true (2),
.last 13 (0,true),
.cycle 15 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 9 true (1),
.cycle 6 9 true (1),
.cycle 15 1 false (-1),
.last 13 (0,true),
.cycle 9 7 true (2),
.cycle 2 13 true (1),
.cycle 7 7 true (2),
.cycle 6 7 true (2),
.cycle 11 2 true (2)
])
theorem kid01_part1113_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid01_part1113) = true := by rfl

def kid01_part1114 : Audit := .cycle 5 7 true (1)
theorem kid01_part1114_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid01_part1114) = true := by rfl

def kid01_part1115 : Audit := .cycle 6 7 true (2)
theorem kid01_part1115_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid01_part1115) = true := by rfl

def kid01_part1116 : Audit := .cycle 15 1 false (-1)
theorem kid01_part1116_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid01_part1116) = true := by rfl

def kid01_part1117 : Audit := .split 12 (0,true) (byMove [
.cycle 0 17 false (4),
.cycle 9 4 true (3),
.last 13 (2,true),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 0 18 true (0),
.cycle 13 7 false (3),
.cycle 0 15 true (0),
.last 13 (2,true),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1117_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid01_part1117) = true := by rfl

def kid01_part1118 : Audit := .cycle 9 3 true (3)
theorem kid01_part1118_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid01_part1118) = true := by rfl

def kid01_part1119 : Audit := .split 12 (2,true) (byMove [
.last 13 (0,true),
.cycle 9 4 true (3),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 2 16 true (1),
.last 13 (0,true),
.cycle 2 13 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 24, 16, 64],[64, 32, 16, 16, 16, 4, 64],64⟩,
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (3),
.cycle 10 3 true (3)
])
theorem kid01_part1119_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid01_part1119) = true := by rfl

def kid01_part1120 : Audit := .cycle 8 5 true (3)
theorem kid01_part1120_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid01_part1120) = true := by rfl

def kid01_part1121 : Audit := .cycle 7 5 true (3)
theorem kid01_part1121_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid01_part1121) = true := by rfl

def kid01_part1122 : Audit := .cycle 10 3 true (3)
theorem kid01_part1122_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid01_part1122) = true := by rfl

def kid01_part1098 : Audit := .split 11 (5,true) (byMove [(kid01_part1099),(kid01_part1100),(kid01_part1101),(kid01_part1102),(kid01_part1103),(kid01_part1104),(kid01_part1105),(kid01_part1106),(kid01_part1107),(kid01_part1108),(kid01_part1109),(kid01_part1110),(kid01_part1111),(kid01_part1112),(kid01_part1113),(kid01_part1114),(kid01_part1115),(kid01_part1116),(kid01_part1117),(kid01_part1118),(kid01_part1119),(kid01_part1120),(kid01_part1121),(kid01_part1122)])

theorem kid01_part1098_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (kid01_part1098) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid01_part1099),(kid01_part1100),(kid01_part1101),(kid01_part1102),(kid01_part1103),(kid01_part1104),(kid01_part1105),(kid01_part1106),(kid01_part1107),(kid01_part1108),(kid01_part1109),(kid01_part1110),(kid01_part1111),(kid01_part1112),(kid01_part1113),(kid01_part1114),(kid01_part1115),(kid01_part1116),(kid01_part1117),(kid01_part1118),(kid01_part1119),(kid01_part1120),(kid01_part1121),(kid01_part1122)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1099_checked

  · exact kid01_part1105_checked

  · exact kid01_part1111_checked

  · exact kid01_part1117_checked

  · exact kid01_part1100_checked

  · exact kid01_part1106_checked

  · exact kid01_part1112_checked

  · exact kid01_part1118_checked

  · exact kid01_part1101_checked

  · exact kid01_part1107_checked

  · exact kid01_part1113_checked

  · exact kid01_part1119_checked

  · exact kid01_part1102_checked

  · exact kid01_part1108_checked

  · exact kid01_part1114_checked

  · exact kid01_part1120_checked

  · exact kid01_part1103_checked

  · exact kid01_part1109_checked

  · exact kid01_part1115_checked

  · exact kid01_part1121_checked

  · exact kid01_part1104_checked

  · exact kid01_part1110_checked

  · exact kid01_part1116_checked

  · exact kid01_part1122_checked

def kid01_part1123 : Audit := .cycle 0 11 true (0)
theorem kid01_part1123_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,0⟩)) (kid01_part1123) = true := by rfl

def kid01_part1124 : Audit := .cycle 1 10 true (1)
theorem kid01_part1124_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,1⟩)) (kid01_part1124) = true := by rfl

def kid01_part1125 : Audit := .cycle 2 9 true (1)
theorem kid01_part1125_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,2⟩)) (kid01_part1125) = true := by rfl

def kid01_part1126 : Audit := .cycle 7 6 true (3)
theorem kid01_part1126_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) (kid01_part1126) = true := by rfl

def kid01_part1127 : Audit := .cycle 8 3 true (3)
theorem kid01_part1127_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,4⟩)) (kid01_part1127) = true := by rfl

def kid01_part1128 : Audit := .cycle 10 1 true (4)
theorem kid01_part1128_checked : zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some ⟨true,true,5⟩)) (kid01_part1128) = true := by rfl

def kid01_part1008 : Audit := .split 10 (5,false) (byMove [(kid01_part1009),(kid01_part1010),(kid01_part1011),(kid01_part1012),(kid01_part1013),(kid01_part1014),(kid01_part1015),(kid01_part1016),(kid01_part1017),(kid01_part1018),(kid01_part1019),(kid01_part1020),(kid01_part1021),(kid01_part1046),(kid01_part1071),(kid01_part1096),(kid01_part1097),(kid01_part1098),(kid01_part1123),(kid01_part1124),(kid01_part1125),(kid01_part1126),(kid01_part1127),(kid01_part1128)])

theorem kid01_part1008_checked : zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (kid01_part1008) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) 10 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,false,1⟩) (1,true) (some ⟨true,true,5⟩)) (5,false) (some mv)) (byMove [(kid01_part1009),(kid01_part1010),(kid01_part1011),(kid01_part1012),(kid01_part1013),(kid01_part1014),(kid01_part1015),(kid01_part1016),(kid01_part1017),(kid01_part1018),(kid01_part1019),(kid01_part1020),(kid01_part1021),(kid01_part1046),(kid01_part1071),(kid01_part1096),(kid01_part1097),(kid01_part1098),(kid01_part1123),(kid01_part1124),(kid01_part1125),(kid01_part1126),(kid01_part1127),(kid01_part1128)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1009_checked

  · exact kid01_part1015_checked

  · exact kid01_part1021_checked

  · exact kid01_part1123_checked

  · exact kid01_part1010_checked

  · exact kid01_part1016_checked

  · exact kid01_part1046_checked

  · exact kid01_part1124_checked

  · exact kid01_part1011_checked

  · exact kid01_part1017_checked

  · exact kid01_part1071_checked

  · exact kid01_part1125_checked

  · exact kid01_part1012_checked

  · exact kid01_part1018_checked

  · exact kid01_part1096_checked

  · exact kid01_part1126_checked

  · exact kid01_part1013_checked

  · exact kid01_part1019_checked

  · exact kid01_part1097_checked

  · exact kid01_part1127_checked

  · exact kid01_part1014_checked

  · exact kid01_part1020_checked

  · exact kid01_part1098_checked

  · exact kid01_part1128_checked

def kid01 : Audit := .split 9 (1,true) (byMove [(kid01_part1),(kid01_part74),(kid01_part75),(kid01_part148),(kid01_part149),(kid01_part150),(kid01_part319),(kid01_part320),(kid01_part321),(kid01_part322),(kid01_part323),(kid01_part324),(kid01_part373),(kid01_part470),(kid01_part567),(kid01_part664),(kid01_part665),(kid01_part666),(kid01_part1003),(kid01_part1004),(kid01_part1005),(kid01_part1006),(kid01_part1007),(kid01_part1008)])

theorem check01 : zipCheck 4063 (child121 ⟨false,false,1⟩) (kid01) = true := by

  change (zipQueryOK 4063 (child121 ⟨false,false,1⟩) 9 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (child121 ⟨false,false,1⟩) (1,true) (some mv)) (byMove [(kid01_part1),(kid01_part74),(kid01_part75),(kid01_part148),(kid01_part149),(kid01_part150),(kid01_part319),(kid01_part320),(kid01_part321),(kid01_part322),(kid01_part323),(kid01_part324),(kid01_part373),(kid01_part470),(kid01_part567),(kid01_part664),(kid01_part665),(kid01_part666),(kid01_part1003),(kid01_part1004),(kid01_part1005),(kid01_part1006),(kid01_part1007),(kid01_part1008)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid01_part1_checked

  · exact kid01_part319_checked

  · exact kid01_part373_checked

  · exact kid01_part1003_checked

  · exact kid01_part74_checked

  · exact kid01_part320_checked

  · exact kid01_part470_checked

  · exact kid01_part1004_checked

  · exact kid01_part75_checked

  · exact kid01_part321_checked

  · exact kid01_part567_checked

  · exact kid01_part1005_checked

  · exact kid01_part148_checked

  · exact kid01_part322_checked

  · exact kid01_part664_checked

  · exact kid01_part1006_checked

  · exact kid01_part149_checked

  · exact kid01_part323_checked

  · exact kid01_part665_checked

  · exact kid01_part1007_checked

  · exact kid01_part150_checked

  · exact kid01_part324_checked

  · exact kid01_part666_checked

  · exact kid01_part1008_checked

end BB6.Agent11Raw121
