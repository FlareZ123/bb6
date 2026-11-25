import Raw121Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid11_part1 : Audit := .cycle 0 10 true (0)
theorem kid11_part1_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,0⟩)) (kid11_part1) = true := by rfl

def kid11_part2 : Audit := .cycle 1 9 true (1)
theorem kid11_part2_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,1⟩)) (kid11_part2) = true := by rfl

def kid11_part3 : Audit := .cycle 2 8 true (1)
theorem kid11_part3_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (kid11_part3) = true := by rfl

def kid11_part4 : Audit := .cycle 7 5 true (3)
theorem kid11_part4_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (kid11_part4) = true := by rfl

def kid11_part5 : Audit := .cycle 8 2 true (4)
theorem kid11_part5_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (kid11_part5) = true := by rfl

def kid11_part7 : Audit := .split 12 (0,true) (byMove [
.cycle 0 15 false (5),
.split 13 (1,true) (byMove [
.cycle 0 28 false (5),
.cycle 14 13 false (3),
.last 14 (2,true),
.cycle 0 19 false (5),
.cycle 0 19 false (5),
.cycle 0 15 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 0 19 false (5),
.cycle 0 17 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 60, 64, 16, 16, 60, 64],64⟩,
.last 16 (2,true),
.last 14 (2,true),
.cycle 34 1 false (-2),
.cycle 0 36 false (5),
.last 17 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 16 21 false (4),
.cycle 0 36 false (5),
.cycle 0 32 false (5)
]),
.split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 19 false (5),
.cycle 0 19 false (5),
.cycle 0 15 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 0 19 false (5),
.cycle 0 17 false (5),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0)
]),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.split 16 (1,true) (byMove [
.cycle 14 3 false (0),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 4, 2, 3, 4, 4],[128, 256, 8, 0, 32, 0, 524288, 1048576, 32768, 4194304, 131072, 32768, 33554432, 67108864, 32768, 4194304, 131072, 4325376, 524288, 1048576, 32768, 4194304, 131072, 4325376, 33554432, 67108864, 134217728, 268435456, 536870912, 2017624064, 1073741824],[4194304, 32768, 1073741824, 1024, 1024, 1048576, 4194304, 4194304, 1073741824, 4194304, 4194304, 131072, 2017624064, 134250496, 1073741824, 268435456, 268435456, 68157440, 4194304, 4325376, 1073741824, 4194304, 4194304, 131072, 2085781504, 2017624064, 1073741824, 268435456, 268435456, 2084732928, 1073741824],2130718720⟩,
.last 17 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.proven (BB6.Agent11Raw121Pumps.M4022.table) (fun m hm => BB6.Agent11Raw121Pumps.M4022.never m hm),
.cycle 0 23 true (-1),
.cycle 17 16 true (1),
.last 17 (2,true),
.cycle 3 23 false (5),
.cycle 0 39 false (5),
.last 20 (2,true),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.cycle 6 13 false (5),
.cycle 6 13 false (5),
.last 20 (2,true),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[2, 2, 64, 16, 16, 4, 64],64⟩,
.last 17 (2,true),
.cycle 7 11 false (5),
.cycle 6 11 false (5),
.cycle 13 5 false (1)
]),
.split 13 (1,true) (byMove [
.last 16 (2,true),
.cycle 6 15 false (5),
.last 14 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 40 1 false (-2),
.last 16 (2,true),
.cycle 1 14 true (1),
.last 14 (2,true),
.cycle 0 19 true (0),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.last 16 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.last 27 (2,true),
.last 17 (2,true),
.cycle 12 2 true (1),
.cycle 1 14 true (1),
.last 14 (2,true),
.last 28 (2,true),
.last 28 (2,true),
.last 20 (2,true)
]),
.split 13 (2,true) (byMove [
.cycle 32 5 false (2),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 40 1 false (-2),
.cycle 0 21 true (0),
.last 14 (1,true),
.cycle 6 17 true (0),
.cycle 0 19 true (0),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.last 26 (1,true),
.last 14 (1,true),
.cycle 0 39 false (5),
.cycle 23 1 false (-1),
.cycle 15 13 false (4),
.cycle 30 1 false (-2),
.cycle 12 2 true (1),
.last 14 (1,true),
.cycle 2 13 true (1),
.cycle 0 33 false (5),
.cycle 0 33 false (5),
.cycle 0 25 false (5)
]),
.cycle 27 1 false (-1),
.cycle 0 29 false (5),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 0 27 false (5),
.cycle 0 21 false (5)
])
theorem kid11_part7_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part7) = true := by rfl

def kid11_part8 : Audit := .split 12 (1,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 15 false (5),
.cycle 0 15 false (5),
.last 14 (2,true),
.cycle 32 1 false (-2),
.cycle 33 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 33 1 false (1),
.cycle 30 1 false (0),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 0 21 false (5),
.cycle 0 21 false (5),
.cycle 1 21 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 31 false (5),
.cycle 0 19 false (5),
.cycle 0 17 false (5)
]),
.cycle 13 13 false (3),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 32 1 false (-2),
.cycle 33 1 false (-1),
.cycle 28 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 33 1 false (1),
.cycle 30 1 false (0),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 1 21 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0)
]),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.split 13 (0,true) (byMove [
.cycle 28 17 false (5),
.cycle 42 45 false (4),
.last 14 (2,true),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 6 15 false (5),
.cycle 0 15 true (0),
.cycle 12 4 true (1),
.last 14 (2,true),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 23 1 false (-1),
.cycle 1 31 false (5),
.cycle 12 13 false (4),
.cycle 0 15 true (0),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 19 9 false (3),
.cycle 19 9 false (3),
.cycle 15 5 false (1)
]),
.split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 14 3 false (0),
.cycle 19 1 false (-1),
.cycle 1 69 false (5),
.cycle 1 69 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 56, 48, 16, 16, 56, 64],64⟩,
.last 17 (0,true),
.cycle 17 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 4, 4, 16, 16, 8, 64],64⟩,
.cycle 3 23 false (5),
.cycle 1 58 false (5),
.cycle 1 61 false (5),
.last 17 (0,true),
.cycle 14 3 false (0),
.cycle 6 15 false (5),
.cycle 6 13 false (5),
.cycle 6 13 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.last 17 (0,true),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 4, 4, 16, 16, 8, 64],64⟩,
.cycle 7 11 false (5),
.cycle 6 11 false (5),
.cycle 13 5 false (1)
]),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 1 18 true (-1),
.cycle 16 1 false (0),
.cycle 1 16 true (0),
.cycle 1 16 true (0),
.cycle 6 15 false (5),
.last 14 (0,true),
.cycle 1 20 true (1),
.cycle 6 17 true (0),
.cycle 1 18 true (1),
.cycle 1 18 true (1),
.cycle 1 14 true (1),
.last 14 (0,true),
.cycle 13 13 false (4),
.cycle 16 27 false (4),
.cycle 23 1 false (-1),
.cycle 1 31 false (5),
.cycle 1 29 false (5),
.last 14 (0,true),
.cycle 12 2 true (1),
.cycle 2 13 true (1),
.cycle 15 25 false (4),
.cycle 14 25 false (4),
.cycle 14 21 false (3)
]),
.cycle 27 1 false (-1),
.cycle 13 21 false (4),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 13 21 false (4),
.cycle 13 17 false (3)
])
theorem kid11_part8_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part8) = true := by rfl

def kid11_part9 : Audit := .split 12 (2,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 15 false (5),
.last 14 (1,true),
.cycle 0 15 false (5),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 5 false (2),
.cycle 0 21 false (5),
.cycle 0 21 false (5),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 31 false (5),
.cycle 0 19 false (5),
.cycle 0 17 false (5)
]),
.split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 13 false (3),
.cycle 29 1 false (-1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 41 1 false (-1),
.cycle 34 1 false (-2),
.cycle 37 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 16 21 false (4),
.cycle 37 1 false (-1),
.cycle 33 1 false (-1)
]),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (1),
.cycle 3 10 true (1),
.cycle 20 1 false (2),
.cycle 17 1 false (1),
.split 13 (0,true) (byMove [
.cycle 2 21 false (5),
.last 14 (1,true),
.last 16 (1,true),
.cycle 29 1 false (-1),
.cycle 30 1 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 14 (1,true),
.last 16 (1,true),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.cycle 29 1 false (1),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 14 (1,true),
.cycle 12 2 true (1),
.last 28 (1,true),
.last 28 (1,true),
.last 20 (1,true)
]),
.split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 6 15 false (5),
.cycle 19 1 false (-1),
.cycle 29 1 false (-1),
.cycle 30 1 false (0),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 1 14 true (1),
.cycle 12 4 true (1),
.cycle 37 1 false (1),
.cycle 37 1 false (1),
.cycle 29 1 false (1),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 6 15 false (5),
.cycle 23 1 false (-1),
.cycle 26 1 false (0),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 1 14 true (1),
.cycle 12 2 true (1),
.cycle 19 9 false (3),
.cycle 19 9 false (3),
.cycle 15 5 false (1)
]),
.cycle 40 1 false (0),
.cycle 27 1 false (-1),
.cycle 30 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (2),
.cycle 28 1 false (0),
.cycle 22 1 false (0)
])
theorem kid11_part9_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part9) = true := by rfl

def kid11_part10 : Audit := .cycle 27 1 false (-1)
theorem kid11_part10_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part10) = true := by rfl

def kid11_part11 : Audit := .cycle 28 1 false (0)
theorem kid11_part11_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part11) = true := by rfl

def kid11_part12 : Audit := .cycle 15 1 false (-1)
theorem kid11_part12_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part12) = true := by rfl

def kid11_part13 : Audit := .cycle 0 12 true (0)
theorem kid11_part13_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part13) = true := by rfl

def kid11_part14 : Audit := .cycle 1 11 true (1)
theorem kid11_part14_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part14) = true := by rfl

def kid11_part15 : Audit := .cycle 6 12 true (2)
theorem kid11_part15_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part15) = true := by rfl

def kid11_part16 : Audit := .cycle 3 9 true (1)
theorem kid11_part16_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part16) = true := by rfl

def kid11_part17 : Audit := .cycle 28 1 false (2)
theorem kid11_part17_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part17) = true := by rfl

def kid11_part18 : Audit := .cycle 21 1 false (1)
theorem kid11_part18_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part18) = true := by rfl

def kid11_part20 : Audit := .split 43 (1,true) (byMove [
.cycle 0 49 false (5),
.cycle 45 26 false (1),
.last 44 (2,true),
.cycle 24 21 false (5),
.cycle 23 21 false (5),
.cycle 27 17 false (3),
.cycle 0 81 false (9),
.cycle 41 23 true (2),
.cycle 0 63 false (7),
.cycle 0 59 false (6),
.cycle 25 21 false (5),
.cycle 25 19 false (5),
.cycle 0 49 false (5),
.last 50 (2,true),
.last 44 (2,true),
.cycle 0 55 false (5),
.cycle 0 55 false (5),
.cycle 27 17 false (3),
.cycle 0 65 false (9),
.cycle 0 63 false (8),
.cycle 0 61 false (7),
.cycle 0 57 false (6),
.cycle 0 53 false (5),
.cycle 0 51 false (5)
])
theorem kid11_part20_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part20) = true := by rfl

def kid11_part21 : Audit := .split 13 (1,true) (byMove [
.cycle 0 30 false (5),
.cycle 6 43 false (5),
.last 14 (2,true),
.cycle 13 7 false (2),
.cycle 13 7 false (2),
.cycle 13 3 false (1),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 6 22 true (1),
.cycle 6 12 true (0),
.cycle 20 15 false (4),
.cycle 13 5 false (2),
.cycle 13 16 false (3),
.last 16 (2,true),
.last 14 (2,true),
.cycle 7 14 true (0),
.cycle 6 14 true (0),
.cycle 13 3 false (1),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 2 20 true (1),
.cycle 4 10 true (1),
.cycle 8 10 true (1),
.cycle 13 26 false (4)
])
theorem kid11_part21_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part21) = true := by rfl

def kid11_part22 : Audit := .split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 20 (1,true),
.last 20 (1,true),
.last 16 (1,true),
.last 15 (1,true),
.cycle 1 15 true (1),
.last 21 (1,true),
.cycle 6 12 true (0),
.last 17 (1,true),
.last 18 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.last 21 (1,true),
.last 19 (1,true),
.last 19 (1,true),
.last 16 (1,true),
.last 15 (1,true),
.cycle 1 15 true (1),
.last 21 (1,true),
.cycle 4 10 true (1),
.last 17 (1,true),
.cycle 18 1 false (0)
])
theorem kid11_part22_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part22) = true := by rfl

def kid11_part23 : Audit := .split 17 (1,true) (byMove [
.cycle 25 1 false (-1),
.cycle 18 19 false (3),
.last 18 (2,true),
.cycle 35 1 false (-1),
.cycle 35 1 false (-1),
.cycle 27 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (1),
.cycle 3 15 true (1),
.cycle 35 1 false (-1),
.cycle 31 1 false (-1),
.cycle 12 6 true (1),
.last 22 (2,true),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 27 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (1),
.cycle 8 10 true (1),
.cycle 10 8 true (1)
])
theorem kid11_part23_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part23) = true := by rfl

def kid11_part24 : Audit := .split 17 (1,true) (byMove [
.cycle 26 1 false (0),
.cycle 18 19 false (3),
.last 18 (2,true),
.cycle 36 1 false (0),
.cycle 36 1 false (0),
.cycle 28 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (1),
.cycle 3 15 true (1),
.cycle 36 1 false (0),
.cycle 32 1 false (0),
.cycle 12 6 true (1),
.last 22 (2,true),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 28 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (1),
.cycle 8 10 true (1),
.cycle 10 8 true (1)
])
theorem kid11_part24_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part24) = true := by rfl

def kid11_part25 : Audit := .cycle 15 1 false (-1)
theorem kid11_part25_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part25) = true := by rfl

def kid11_part26 : Audit := .cycle 0 14 true (0)
theorem kid11_part26_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part26) = true := by rfl

def kid11_part27 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 12 4 true (2),
.last 15 (2,true),
.last 22 (2,true),
.cycle 4 10 true (1),
.cycle 6 12 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 12 true (2),
.cycle 10 8 true (2)
])
theorem kid11_part27_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part27) = true := by rfl

def kid11_part28 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.last 15 (1,true),
.last 16 (1,true),
.last 21 (1,true),
.cycle 4 10 true (1),
.last 17 (1,true),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.last 19 (1,true),
.last 17 (1,true)
])
theorem kid11_part28_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part28) = true := by rfl

def kid11_part29 : Audit := .split 19 (1,true) (byMove [
.cycle 3 18 true (1),
.cycle 20 21 false (3),
.last 20 (2,true),
.cycle 39 7 false (3),
.cycle 40 7 false (3),
.cycle 35 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (2),
.cycle 3 17 true (1),
.cycle 41 7 false (3),
.cycle 37 5 false (3),
.cycle 12 8 true (2),
.last 24 (2,true),
.last 20 (2,true),
.cycle 7 14 true (2),
.cycle 6 14 true (2),
.cycle 69 3 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (2),
.cycle 8 12 true (2),
.cycle 10 10 true (2)
])
theorem kid11_part29_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part29) = true := by rfl

def kid11_part30 : Audit := .split 19 (1,true) (byMove [
.cycle 36 1 false (2),
.cycle 20 21 false (3),
.last 20 (2,true),
.cycle 40 7 false (3),
.cycle 39 7 false (3),
.cycle 35 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (2),
.cycle 3 17 true (1),
.cycle 41 7 false (3),
.cycle 37 5 false (3),
.cycle 12 8 true (2),
.last 24 (2,true),
.last 20 (2,true),
.cycle 7 14 true (2),
.cycle 6 14 true (2),
.cycle 69 3 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (2),
.cycle 8 12 true (2),
.cycle 10 10 true (2)
])
theorem kid11_part30_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part30) = true := by rfl

def kid11_part31 : Audit := .split 15 (1,true) (byMove [
.cycle 25 1 false (1),
.cycle 16 17 false (3),
.last 16 (2,true),
.cycle 31 7 false (2),
.cycle 31 7 false (2),
.cycle 23 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 31 7 false (3),
.cycle 27 5 false (2),
.cycle 12 4 true (2),
.last 20 (2,true),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 23 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 10 6 true (2)
])
theorem kid11_part31_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part31) = true := by rfl

def kid11_part32 : Audit := .split 16 (1,true) (byMove [
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.last 17 (2,true),
.cycle 8 25 false (5),
.cycle 7 25 false (5),
.cycle 15 3 false (0),
.cycle 0 26 true (-1),
.cycle 17 17 true (1),
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[24, 8, 64, 16, 16, 24, 64],64⟩,
.cycle 9 37 false (5),
.cycle 9 17 false (5),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (0),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 60, 64],[2, 2, 64, 16, 16, 2, 64],64⟩,
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[24, 8, 64, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 5 false (1)
])
theorem kid11_part32_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part32) = true := by rfl

def kid11_part33 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.last 70 (2,true),
.last 14 (2,true),
.cycle 31 1 false (-1),
.cycle 32 1 false (0),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 1 15 true (1),
.last 14 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.last 36 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 13 3 false (1),
.cycle 12 2 true (1),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.last 20 (2,true)
])
theorem kid11_part33_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part33) = true := by rfl

def kid11_part34 : Audit := .split 13 (2,true) (byMove [
.last 20 (1,true),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 18 (1,true),
.last 18 (1,true),
.last 16 (1,true),
.cycle 14 8 true (1),
.last 14 (1,true),
.cycle 6 20 true (0),
.cycle 14 8 true (1),
.cycle 15 8 true (1),
.last 16 (1,true),
.cycle 6 12 true (-1),
.last 14 (1,true),
.cycle 6 12 true (-1),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.last 16 (1,true),
.cycle 12 2 true (1),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 6 16 true (-1)
])
theorem kid11_part34_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part34) = true := by rfl

def kid11_part35 : Audit := .cycle 5 8 true (1)
theorem kid11_part35_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part35) = true := by rfl

def kid11_part36 : Audit := .cycle 6 8 true (1)
theorem kid11_part36_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part36) = true := by rfl

def kid11_part37 : Audit := .cycle 15 1 false (-1)
theorem kid11_part37_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part37) = true := by rfl

def kid11_part38 : Audit := .cycle 0 14 true (0)
theorem kid11_part38_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part38) = true := by rfl

def kid11_part39 : Audit := .split 13 (1,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 15 false (3),
.last 14 (2,true),
.cycle 27 7 false (2),
.cycle 27 7 false (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 27 7 false (3),
.cycle 23 5 false (2),
.cycle 12 2 true (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part39_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part39) = true := by rfl

def kid11_part40 : Audit := .split 13 (2,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 18 1 false (0),
.last 34 (1,true),
.last 34 (1,true),
.last 22 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.last 34 (1,true),
.last 28 (1,true),
.cycle 12 2 true (2),
.last 14 (1,true),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 22 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part40_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part40) = true := by rfl

def kid11_part41 : Audit := .cycle 8 6 true (2)
theorem kid11_part41_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part41) = true := by rfl

def kid11_part42 : Audit := .cycle 7 6 true (2)
theorem kid11_part42_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part42) = true := by rfl

def kid11_part43 : Audit := .cycle 11 2 true (2)
theorem kid11_part43_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part43) = true := by rfl

def kid11_part19 : Audit := .split 12 (0,true) (byMove [(kid11_part20),(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43)])

theorem kid11_part19_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part19) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part20),(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part20_checked

  · exact kid11_part26_checked

  · exact kid11_part32_checked

  · exact kid11_part38_checked

  · exact kid11_part21_checked

  · exact kid11_part27_checked

  · exact kid11_part33_checked

  · exact kid11_part39_checked

  · exact kid11_part22_checked

  · exact kid11_part28_checked

  · exact kid11_part34_checked

  · exact kid11_part40_checked

  · exact kid11_part23_checked

  · exact kid11_part29_checked

  · exact kid11_part35_checked

  · exact kid11_part41_checked

  · exact kid11_part24_checked

  · exact kid11_part30_checked

  · exact kid11_part36_checked

  · exact kid11_part42_checked

  · exact kid11_part25_checked

  · exact kid11_part31_checked

  · exact kid11_part37_checked

  · exact kid11_part43_checked

def kid11_part45 : Audit := .split 13 (0,true) (byMove [
.last 43 (2,true),
.cycle 6 45 false (5),
.last 14 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.last 15 (2,true),
.last 21 (2,true),
.cycle 6 12 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.last 15 (2,true),
.last 21 (2,true),
.cycle 4 10 true (1),
.last 17 (2,true),
.last 19 (2,true)
])
theorem kid11_part45_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part45) = true := by rfl

def kid11_part46 : Audit := .split 25 (2,true) (byMove [
.last 26 (0,true),
.cycle 6 43 false (5),
.cycle 31 1 false (-1),
.cycle 8 19 false (5),
.cycle 7 19 false (5),
.cycle 11 15 false (3),
.cycle 0 26 true (-1),
.cycle 6 71 false (8),
.cycle 6 57 false (7),
.cycle 6 53 false (6),
.cycle 9 19 false (5),
.cycle 9 17 false (5),
.last 26 (0,true),
.cycle 6 43 false (5),
.cycle 6 57 false (5),
.cycle 6 49 false (5),
.cycle 6 49 false (5),
.cycle 11 15 false (3),
.cycle 6 59 false (9),
.cycle 6 57 false (8),
.cycle 6 55 false (7),
.cycle 6 51 false (6),
.cycle 6 47 false (5),
.cycle 6 45 false (5)
])
theorem kid11_part46_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part46) = true := by rfl

def kid11_part47 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 13 7 false (2),
.cycle 13 7 false (2),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 6 22 true (1),
.cycle 6 12 true (0),
.cycle 32 1 false (0),
.cycle 13 5 false (2),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 6 22 true (-1),
.cycle 7 14 true (0),
.cycle 6 14 true (0),
.cycle 13 3 false (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 2 20 true (1),
.cycle 4 10 true (1),
.cycle 8 10 true (1),
.cycle 18 1 false (0)
])
theorem kid11_part47_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part47) = true := by rfl

def kid11_part48 : Audit := .split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 25 1 false (-1),
.cycle 22 1 false (0),
.cycle 35 1 false (-1),
.cycle 35 1 false (-1),
.cycle 27 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (1),
.cycle 3 15 true (1),
.cycle 35 1 false (-1),
.cycle 31 1 false (-1),
.last 18 (0,true),
.cycle 12 6 true (1),
.cycle 6 18 true (-1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 27 1 false (-1),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (1),
.cycle 8 10 true (1),
.cycle 10 8 true (1)
])
theorem kid11_part48_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part48) = true := by rfl

def kid11_part49 : Audit := .split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 26 1 false (0),
.cycle 22 1 false (0),
.cycle 36 1 false (0),
.cycle 36 1 false (0),
.cycle 28 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (1),
.cycle 3 15 true (1),
.cycle 36 1 false (0),
.cycle 32 1 false (0),
.last 18 (0,true),
.cycle 12 6 true (1),
.cycle 6 18 true (-1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 28 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (1),
.cycle 8 10 true (1),
.cycle 10 8 true (1)
])
theorem kid11_part49_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part49) = true := by rfl

def kid11_part50 : Audit := .cycle 15 1 false (-1)
theorem kid11_part50_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part50) = true := by rfl

def kid11_part51 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 0 16 true (0),
.last 15 (2,true),
.last 21 (2,true),
.cycle 4 10 true (1),
.last 17 (2,true),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.last 19 (2,true),
.last 17 (2,true)
])
theorem kid11_part51_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part51) = true := by rfl

def kid11_part52 : Audit := .cycle 1 13 true (1)
theorem kid11_part52_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part52) = true := by rfl

def kid11_part53 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 6 16 true (2),
.cycle 12 4 true (2),
.cycle 6 22 true (-1),
.cycle 4 10 true (1),
.cycle 6 12 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 12 true (2),
.cycle 10 8 true (2)
])
theorem kid11_part53_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part53) = true := by rfl

def kid11_part54 : Audit := .split 19 (2,true) (byMove [
.last 20 (0,true),
.cycle 3 18 true (1),
.cycle 24 1 false (0),
.cycle 39 7 false (3),
.cycle 40 7 false (3),
.cycle 35 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (2),
.cycle 3 17 true (1),
.cycle 41 7 false (3),
.cycle 37 5 false (3),
.last 20 (0,true),
.cycle 12 8 true (2),
.cycle 6 20 true (-1),
.cycle 7 14 true (2),
.cycle 6 14 true (2),
.cycle 69 3 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (2),
.cycle 8 12 true (2),
.cycle 10 10 true (2)
])
theorem kid11_part54_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part54) = true := by rfl

def kid11_part55 : Audit := .split 19 (2,true) (byMove [
.last 20 (0,true),
.cycle 36 1 false (2),
.cycle 24 1 false (0),
.cycle 40 7 false (3),
.cycle 39 7 false (3),
.cycle 35 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (2),
.cycle 3 17 true (1),
.cycle 41 7 false (3),
.cycle 37 5 false (3),
.last 20 (0,true),
.cycle 12 8 true (2),
.cycle 6 20 true (-1),
.cycle 7 14 true (2),
.cycle 6 14 true (2),
.cycle 69 3 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (2),
.cycle 8 12 true (2),
.cycle 10 10 true (2)
])
theorem kid11_part55_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part55) = true := by rfl

def kid11_part56 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 31 7 false (2),
.cycle 31 7 false (2),
.cycle 23 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 31 7 false (3),
.cycle 27 5 false (2),
.last 16 (0,true),
.cycle 12 4 true (2),
.cycle 6 16 true (-1),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 23 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 10 6 true (2)
])
theorem kid11_part56_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part56) = true := by rfl

def kid11_part57 : Audit := .split 13 (0,true) (byMove [
.last 60 (2,true),
.last 24 (2,true),
.last 14 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 16 true (0),
.cycle 12 4 true (1),
.last 14 (2,true),
.cycle 12 10 true (1),
.cycle 12 10 true (1),
.last 16 (2,true),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.last 16 (2,true),
.cycle 0 16 true (0),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part57_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part57) = true := by rfl

def kid11_part58 : Audit := .split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 14 3 false (0),
.cycle 19 1 false (-1),
.cycle 8 25 false (5),
.cycle 7 25 false (5),
.cycle 15 3 false (0),
.last 17 (0,true),
.cycle 17 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.cycle 9 37 false (5),
.cycle 9 17 false (5),
.last 17 (0,true),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (0),
.last 17 (0,true),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 5 false (1)
])
theorem kid11_part58_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part58) = true := by rfl

def kid11_part59 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 47 11 false (2),
.cycle 16 1 false (0),
.cycle 31 1 false (-1),
.cycle 32 1 false (0),
.cycle 13 3 false (1),
.last 14 (0,true),
.cycle 14 8 true (1),
.cycle 6 20 true (0),
.cycle 14 8 true (1),
.cycle 15 8 true (1),
.cycle 31 8 true (-1),
.last 14 (0,true),
.cycle 6 12 true (-1),
.cycle 6 12 true (-1),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 13 3 false (1),
.last 14 (0,true),
.cycle 12 2 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 6 16 true (-1)
])
theorem kid11_part59_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part59) = true := by rfl

def kid11_part60 : Audit := .cycle 5 8 true (1)
theorem kid11_part60_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part60) = true := by rfl

def kid11_part61 : Audit := .cycle 6 8 true (1)
theorem kid11_part61_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part61) = true := by rfl

def kid11_part62 : Audit := .cycle 15 1 false (-1)
theorem kid11_part62_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part62) = true := by rfl

def kid11_part63 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 15 true (0),
.last 14 (2,true),
.last 34 (2,true),
.last 34 (2,true),
.last 22 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.last 34 (2,true),
.last 28 (2,true),
.cycle 14 5 false (2),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 22 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part63_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part63) = true := by rfl

def kid11_part64 : Audit := .cycle 1 13 true (1)
theorem kid11_part64_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part64) = true := by rfl

def kid11_part65 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 2 13 true (1),
.cycle 18 1 false (0),
.cycle 27 7 false (2),
.cycle 27 7 false (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 27 7 false (3),
.cycle 23 5 false (2),
.last 14 (0,true),
.cycle 12 2 true (2),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part65_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part65) = true := by rfl

def kid11_part66 : Audit := .cycle 8 6 true (2)
theorem kid11_part66_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part66) = true := by rfl

def kid11_part67 : Audit := .cycle 7 6 true (2)
theorem kid11_part67_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part67) = true := by rfl

def kid11_part68 : Audit := .cycle 11 2 true (2)
theorem kid11_part68_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part68) = true := by rfl

def kid11_part44 : Audit := .split 12 (1,true) (byMove [(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part68)])

theorem kid11_part44_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part44) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part68)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part45_checked

  · exact kid11_part51_checked

  · exact kid11_part57_checked

  · exact kid11_part63_checked

  · exact kid11_part46_checked

  · exact kid11_part52_checked

  · exact kid11_part58_checked

  · exact kid11_part64_checked

  · exact kid11_part47_checked

  · exact kid11_part53_checked

  · exact kid11_part59_checked

  · exact kid11_part65_checked

  · exact kid11_part48_checked

  · exact kid11_part54_checked

  · exact kid11_part60_checked

  · exact kid11_part66_checked

  · exact kid11_part49_checked

  · exact kid11_part55_checked

  · exact kid11_part61_checked

  · exact kid11_part67_checked

  · exact kid11_part50_checked

  · exact kid11_part56_checked

  · exact kid11_part62_checked

  · exact kid11_part68_checked

def kid11_part70 : Audit := .split 13 (0,true) (byMove [
.cycle 41 6 true (2),
.last 14 (1,true),
.cycle 33 1 false (-1),
.cycle 14 6 true (-1),
.cycle 15 6 true (-1),
.cycle 14 6 true (-1),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 14 6 true (2),
.cycle 6 12 true (0),
.cycle 15 6 true (2),
.cycle 14 6 true (-1),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 5 false (2),
.cycle 17 6 true (2),
.cycle 17 6 true (2),
.cycle 19 6 true (2),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 14 6 true (2),
.cycle 4 10 true (1),
.cycle 15 6 true (2),
.cycle 12 7 false (2)
])
theorem kid11_part70_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part70) = true := by rfl

def kid11_part71 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 23 6 true (2),
.cycle 23 6 true (2),
.cycle 14 6 true (-1),
.cycle 15 6 true (-1),
.cycle 14 6 true (-1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 14 6 true (2),
.cycle 6 12 true (0),
.cycle 15 6 true (2),
.cycle 14 6 true (-1),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 19 6 true (2),
.cycle 17 6 true (2),
.cycle 17 6 true (2),
.cycle 19 6 true (2),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 14 6 true (2),
.cycle 4 10 true (1),
.cycle 15 6 true (2),
.cycle 21 6 true (2)
])
theorem kid11_part71_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part71) = true := by rfl

def kid11_part72 : Audit := .cycle 16 1 false (0)
theorem kid11_part72_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part72) = true := by rfl

def kid11_part73 : Audit := .cycle 15 6 true (2)
theorem kid11_part73_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part73) = true := by rfl

def kid11_part74 : Audit := .cycle 15 6 true (2)
theorem kid11_part74_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part74) = true := by rfl

def kid11_part75 : Audit := .cycle 15 1 false (-1)
theorem kid11_part75_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part75) = true := by rfl

def kid11_part76 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 14 6 true (2),
.cycle 4 10 true (1),
.cycle 15 6 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 14 6 true (2),
.cycle 14 6 true (2)
])
theorem kid11_part76_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part76) = true := by rfl

def kid11_part77 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 32 1 false (0),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (1),
.cycle 6 13 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.last 16 (0,true),
.cycle 1 15 true (1),
.cycle 14 6 true (2),
.cycle 4 10 true (1),
.cycle 15 6 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 14 6 true (2),
.cycle 14 6 true (2)
])
theorem kid11_part77_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part77) = true := by rfl

def kid11_part78 : Audit := .cycle 6 16 true (1)
theorem kid11_part78_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part78) = true := by rfl

def kid11_part79 : Audit := .cycle 13 6 true (2)
theorem kid11_part79_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part79) = true := by rfl

def kid11_part80 : Audit := .cycle 14 6 true (2)
theorem kid11_part80_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part80) = true := by rfl

def kid11_part81 : Audit := .cycle 13 6 true (2)
theorem kid11_part81_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part81) = true := by rfl

def kid11_part82 : Audit := .split 13 (0,true) (byMove [
.last 26 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.last 26 (1,true),
.last 26 (1,true),
.last 28 (1,true),
.cycle 0 16 true (0),
.last 14 (1,true),
.last 16 (1,true),
.last 22 (1,true),
.last 22 (1,true),
.last 24 (1,true),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 6 12 true (-1),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 12 2 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.last 20 (1,true)
])
theorem kid11_part82_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part82) = true := by rfl

def kid11_part83 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 12 66 false (5),
.cycle 19 1 false (-1),
.cycle 12 14 true (0),
.cycle 12 14 true (0),
.cycle 12 16 true (-1),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 12 4 true (1),
.cycle 12 10 true (1),
.cycle 12 10 true (1),
.cycle 12 12 true (1),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 16 14 true (-2),
.cycle 6 10 true (0),
.cycle 6 10 true (0),
.cycle 6 12 true (-1),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 12 2 true (1),
.cycle 7 8 true (1),
.cycle 6 8 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part83_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part83) = true := by rfl

def kid11_part84 : Audit := .cycle 6 12 true (-1)
theorem kid11_part84_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part84) = true := by rfl

def kid11_part85 : Audit := .cycle 5 8 true (1)
theorem kid11_part85_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part85) = true := by rfl

def kid11_part86 : Audit := .cycle 6 8 true (1)
theorem kid11_part86_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part86) = true := by rfl

def kid11_part87 : Audit := .cycle 15 1 false (-1)
theorem kid11_part87_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part87) = true := by rfl

def kid11_part88 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.last 14 (1,true),
.cycle 0 15 true (0),
.cycle 28 6 true (-1),
.cycle 29 6 true (-1),
.cycle 20 6 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 30 6 true (-1),
.cycle 24 6 true (-1),
.last 18 (1,true),
.last 14 (1,true),
.cycle 12 2 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 6 18 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part88_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part88) = true := by rfl

def kid11_part89 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 15 false (3),
.cycle 1 14 true (1),
.cycle 28 6 true (-1),
.cycle 29 6 true (-1),
.cycle 20 6 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 30 6 true (-1),
.cycle 24 6 true (-1),
.last 14 (0,true),
.cycle 14 5 false (2),
.cycle 12 2 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 6 18 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (2),
.cycle 8 6 true (2),
.cycle 10 4 true (2)
])
theorem kid11_part89_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part89) = true := by rfl

def kid11_part90 : Audit := .cycle 2 12 true (1)
theorem kid11_part90_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part90) = true := by rfl

def kid11_part91 : Audit := .cycle 8 6 true (2)
theorem kid11_part91_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part91) = true := by rfl

def kid11_part92 : Audit := .cycle 7 6 true (2)
theorem kid11_part92_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part92) = true := by rfl

def kid11_part93 : Audit := .cycle 11 2 true (2)
theorem kid11_part93_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part93) = true := by rfl

def kid11_part69 : Audit := .split 12 (2,true) (byMove [(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74),(kid11_part75),(kid11_part76),(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91),(kid11_part92),(kid11_part93)])

theorem kid11_part69_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part69) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74),(kid11_part75),(kid11_part76),(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91),(kid11_part92),(kid11_part93)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part70_checked

  · exact kid11_part76_checked

  · exact kid11_part82_checked

  · exact kid11_part88_checked

  · exact kid11_part71_checked

  · exact kid11_part77_checked

  · exact kid11_part83_checked

  · exact kid11_part89_checked

  · exact kid11_part72_checked

  · exact kid11_part78_checked

  · exact kid11_part84_checked

  · exact kid11_part90_checked

  · exact kid11_part73_checked

  · exact kid11_part79_checked

  · exact kid11_part85_checked

  · exact kid11_part91_checked

  · exact kid11_part74_checked

  · exact kid11_part80_checked

  · exact kid11_part86_checked

  · exact kid11_part92_checked

  · exact kid11_part75_checked

  · exact kid11_part81_checked

  · exact kid11_part87_checked

  · exact kid11_part93_checked

def kid11_part94 : Audit := .cycle 7 6 true (2)
theorem kid11_part94_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part94) = true := by rfl

def kid11_part95 : Audit := .cycle 6 6 true (2)
theorem kid11_part95_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part95) = true := by rfl

def kid11_part96 : Audit := .cycle 15 1 false (-1)
theorem kid11_part96_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part96) = true := by rfl

def kid11_part97 : Audit := .cycle 0 12 true (0)
theorem kid11_part97_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part97) = true := by rfl

def kid11_part98 : Audit := .cycle 1 11 true (1)
theorem kid11_part98_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part98) = true := by rfl

def kid11_part99 : Audit := .cycle 2 10 true (1)
theorem kid11_part99_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part99) = true := by rfl

def kid11_part100 : Audit := .cycle 7 7 true (3)
theorem kid11_part100_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part100) = true := by rfl

def kid11_part101 : Audit := .cycle 8 4 true (3)
theorem kid11_part101_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part101) = true := by rfl

def kid11_part102 : Audit := .cycle 10 2 true (3)
theorem kid11_part102_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part102) = true := by rfl

def kid11_part6 : Audit := .split 11 (5,true) (byMove [(kid11_part7),(kid11_part8),(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part44),(kid11_part69),(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102)])

theorem kid11_part6_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (kid11_part6) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part7),(kid11_part8),(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part44),(kid11_part69),(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part7_checked

  · exact kid11_part13_checked

  · exact kid11_part19_checked

  · exact kid11_part97_checked

  · exact kid11_part8_checked

  · exact kid11_part14_checked

  · exact kid11_part44_checked

  · exact kid11_part98_checked

  · exact kid11_part9_checked

  · exact kid11_part15_checked

  · exact kid11_part69_checked

  · exact kid11_part99_checked

  · exact kid11_part10_checked

  · exact kid11_part16_checked

  · exact kid11_part94_checked

  · exact kid11_part100_checked

  · exact kid11_part11_checked

  · exact kid11_part17_checked

  · exact kid11_part95_checked

  · exact kid11_part101_checked

  · exact kid11_part12_checked

  · exact kid11_part18_checked

  · exact kid11_part96_checked

  · exact kid11_part102_checked

def kid11_part103 : Audit := .cycle 0 10 true (0)
theorem kid11_part103_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,0⟩)) (kid11_part103) = true := by rfl

def kid11_part104 : Audit := .cycle 1 9 true (1)
theorem kid11_part104_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,1⟩)) (kid11_part104) = true := by rfl

def kid11_part105 : Audit := .cycle 6 12 true (2)
theorem kid11_part105_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (kid11_part105) = true := by rfl

def kid11_part106 : Audit := .cycle 6 9 true (2)
theorem kid11_part106_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (kid11_part106) = true := by rfl

def kid11_part107 : Audit := .cycle 8 2 true (4)
theorem kid11_part107_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (kid11_part107) = true := by rfl

def kid11_part108 : Audit := .cycle 9 1 true (5)
theorem kid11_part108_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨false,true,5⟩)) (kid11_part108) = true := by rfl

def kid11_part110 : Audit := .split 12 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 32 false (5),
.split 13 (2,true) (byMove [
.cycle 18 1 false (0),
.cycle 33 1 false (-1),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 41 1 false (-1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 2 17 true (1),
.cycle 34 1 false (0),
.cycle 18 1 false (0),
.cycle 26 1 false (-2),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 26 1 false (0)
]),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.cycle 30 4 false (0),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 34 4 false (0),
.cycle 29 4 false (1),
.cycle 16 4 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 24 4 false (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.cycle 16 3 false (0),
.split 18 (2,true) (byMove [
.cycle 16 3 false (0),
.last 30 (5,true),
.cycle 21 1 false (-1),
.cycle 13 20 false (3),
.cycle 13 20 false (3),
.last 19 (5,true),
.cycle 0 27 true (-1),
.cycle 19 20 true (1),
.last 22 (5,true),
.last 26 (5,true),
.last 20 (5,true),
.cycle 13 16 false (3),
.cycle 16 3 false (0),
.cycle 15 8 false (1),
.last 24 (5,true),
.last 22 (5,true),
.last 22 (5,true),
.last 19 (5,true),
.cycle 13 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[2, 4, 2, 16, 16, 64, 64],64⟩,
.last 22 (5,true),
.last 24 (5,true),
.last 20 (5,true),
.last 25 (5,true)
]),
.split 13 (2,true) (byMove [
.last 20 (5,true),
.last 30 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 8 9 true (3),
.cycle 0 15 true (0),
.cycle 6 17 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true),
.last 39 (5,true),
.last 28 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 36, 16, 16, 16, 64, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 20 10 true (-1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.cycle 1 30 true (-1),
.last 14 (2,true),
.cycle 7 12 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.cycle 20 4 false (0),
.cycle 0 15 true (0),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 34 4 false (0),
.cycle 16 4 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 17 4 false (-1),
.cycle 12 2 true (3),
.cycle 23 4 false (1),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 13 5 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (4),
.split 15 (5,true) (byMove [
.cycle 12 4 true (4),
.cycle 0 37 false (5),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 19 8 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (4),
.cycle 9 7 true (4),
.cycle 14 2 true (4),
.last 39 (2,true),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 19 8 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (4),
.cycle 13 3 true (4)
])
])
theorem kid11_part110_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part110) = true := by rfl

def kid11_part111 : Audit := .cycle 12 15 false (4)
theorem kid11_part111_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part111) = true := by rfl

def kid11_part112 : Audit := .split 12 (2,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 32 false (5),
.cycle 0 17 false (5),
.cycle 35 1 false (-1),
.cycle 0 40 false (5),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 0 19 true (0),
.cycle 0 33 false (5),
.cycle 33 18 false (1),
.cycle 15 3 false (1),
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
.cycle 33 1 false (-1),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 30 4 false (0),
.cycle 16 4 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.last 20 (0,true),
.cycle 29 4 false (1),
.last 14 (0,true),
.cycle 15 3 false (1),
.cycle 16 4 false (0),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 15 (0,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.split 13 (0,true) (byMove [
.last 26 (5,true),
.last 30 (5,true),
.cycle 16 3 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 2 13 true (1),
.cycle 29 3 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 17 3 false (0),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 23 3 false (1),
.cycle 12 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 21 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 32, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 32, 1024, 1024, 1024, 4096, 4096],6144⟩,
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 1 30 true (-1),
.cycle 16 4 false (0),
.cycle 7 12 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 2 13 true (1),
.last 16 (0,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 20 (0,true),
.last 14 (0,true),
.cycle 15 3 false (1),
.cycle 16 4 false (0),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 23 4 false (1),
.cycle 12 2 true (3),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 16 (0,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (4),
.split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.last 27 (5,true),
.cycle 28 1 false (0),
.last 17 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 16 true (0),
.cycle 2 14 true (1),
.cycle 12 3 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 18 5 false (0),
.last 25 (5,true),
.last 16 (5,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.last 15 (5,true),
.cycle 0 16 true (0),
.cycle 11 4 true (4),
.cycle 12 3 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true)
])
])
theorem kid11_part112_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part112) = true := by rfl

def kid11_part113 : Audit := .cycle 8 5 true (4)
theorem kid11_part113_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part113) = true := by rfl

def kid11_part114 : Audit := .cycle 7 5 true (3)
theorem kid11_part114_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part114) = true := by rfl

def kid11_part115 : Audit := .split 12 (5,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 32 false (5),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 0 40 false (5),
.cycle 0 17 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 0 19 true (0),
.cycle 0 33 false (5),
.cycle 33 18 false (1),
.last 18 (2,true),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 19 (2,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 12 4 true (3)
]),
.cycle 15 19 false (3),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 33 1 false (-1),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 41 1 false (-1),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 2 17 true (1),
.cycle 34 1 false (0),
.last 14 (0,true),
.cycle 25 1 false (-3),
.cycle 6 14 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 18 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 15 (0,true)
]),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.split 13 (0,true) (byMove [
.cycle 10 17 false (5),
.cycle 31 9 true (1),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 37 3 false (0),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 25 3 false (0),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 29 3 false (1),
.cycle 17 3 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 23 3 false (1),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
]),
.split 18 (2,true) (byMove [
.last 19 (0,true),
.cycle 15 7 false (1),
.cycle 21 1 false (-1),
.cycle 15 13 false (1),
.cycle 15 13 false (1),
.cycle 16 3 false (0),
.cycle 0 27 true (-1),
.last 39 (0,true),
.last 144 (0,true),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[128, 256, 8, 0, 32, 132096, 128, 256, 32768, 1024, 131072, 16777216, 524288, 1048576, 2097152, 1024, 8388608, 132096, 524288, 1048576, 2097152, 4195328, 8388608, 29492224, 16777216],[16777216, 132096, 8, 1024, 1024, 32768, 16777216, 132096, 32768, 1024, 1024, 33792, 16777216, 16777216, 2097152, 4194304, 4194304, 32768, 16777216, 29492224, 2097152, 4194304, 4194304, 23102464, 16777216],33388544⟩,
.cycle 24 7 true (3),
.cycle 15 11 false (1),
.last 19 (0,true),
.cycle 15 7 false (1),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[131456, 131456, 512, 512, 128, 64, 128, 256, 320, 512, 256, 64, 393600, 393600, 512, 512, 128, 64, 262144],[262144, 32, 256, 131072, 131072, 128, 262144, 131072, 256, 131456, 131456, 128, 262144, 131072, 256, 131328, 131328, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[131200, 131200, 512, 512, 128, 64, 128, 131200, 131264, 512, 131200, 64, 393344, 393344, 512, 512, 128, 64, 262144],[262144, 32, 512, 131072, 131072, 128, 262144, 131072, 512, 131200, 131200, 128, 262144, 131072, 512, 131200, 131200, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[131200, 131200, 512, 512, 128, 64, 128, 131200, 131264, 512, 131200, 64, 393344, 393344, 512, 512, 128, 64, 262144],[262144, 32, 1024, 131072, 131072, 128, 262144, 131072, 1024, 131200, 131200, 128, 262144, 131072, 1024, 131200, 131200, 128, 262144],274432⟩,
.cycle 16 3 false (0),
.cycle 13 7 false (3),
.proven (BB6.Agent11Raw121Pumps.M4050.table) (fun m hm => BB6.Agent11Raw121Pumps.M4050.never m hm),
.last 42 (0,true),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[131200, 131200, 512, 512, 128, 64, 128, 131200, 131264, 512, 131200, 64, 393344, 393344, 512, 512, 128, 64, 262144],[262144, 32, 131200, 131072, 131072, 128, 262144, 131072, 131200, 131200, 131200, 128, 262144, 131072, 131200, 131200, 131200, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[131200, 131200, 512, 512, 128, 64, 128, 131200, 131264, 512, 131200, 64, 393344, 393344, 512, 512, 128, 64, 262144],[262144, 32, 131072, 131072, 131072, 128, 262144, 131072, 131200, 131200, 131200, 128, 262144, 131072, 131200, 131200, 131200, 128, 262144],274432⟩,
.last 20 (0,true)
]),
.split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 31 9 true (3),
.cycle 18 1 false (0),
.cycle 15 13 true (2),
.far true 1 ⟨0,[0, 0],[20, 16, 28, 8, 28, 1, 64],[64, 32, 16, 16, 16, 4, 64],64⟩,
.last 34 (0,true),
.last 14 (0,true),
.last 16 (0,true),
.cycle 6 17 true (2),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 8 9 true (3),
.last 14 (0,true),
.cycle 14 15 false (2),
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 12, 1, 64],[64, 32, 4, 4, 4, 4, 64],64⟩,
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 80 (0,true),
.last 14 (0,true),
.cycle 20 10 true (-1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
]),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (4),
.split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 120 13 false (0),
.last 15 (2,true),
.cycle 16 7 true (3),
.cycle 12 18 true (3),
.cycle 24 6 false (1),
.cycle 0 16 true (0),
.cycle 25 7 false (1),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 12 3 true (4),
.cycle 18 5 false (0),
.last 24 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 12 5 true (3),
.cycle 0 16 true (0),
.cycle 11 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 12 3 true (4)
])
])
theorem kid11_part115_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part115) = true := by rfl

def kid11_part116 : Audit := .cycle 0 12 true (0)
theorem kid11_part116_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part116) = true := by rfl

def kid11_part117 : Audit := .cycle 1 11 true (1)
theorem kid11_part117_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part117) = true := by rfl

def kid11_part118 : Audit := .cycle 6 12 true (2)
theorem kid11_part118_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part118) = true := by rfl

def kid11_part119 : Audit := .cycle 3 9 true (1)
theorem kid11_part119_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part119) = true := by rfl

def kid11_part120 : Audit := .cycle 8 4 true (4)
theorem kid11_part120_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part120) = true := by rfl

def kid11_part121 : Audit := .cycle 9 3 true (4)
theorem kid11_part121_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part121) = true := by rfl

def kid11_part123 : Audit := .cycle 0 17 false (5)
theorem kid11_part123_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part123) = true := by rfl

def kid11_part124 : Audit := .split 21 (5,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[40, 20, 64, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 1024, 4096],[8, 1024, 4096, 1024, 1024, 1024, 32, 1024, 4096, 1024, 1024, 4096, 4096],4096⟩,
.cycle 13 41 false (6),
.cycle 15 18 false (3),
.cycle 13 21 false (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[42, 17, 64, 16, 16, 1, 64],64⟩,
.last 23 (2,true),
.cycle 138 32 true (10),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[56, 24, 64, 16, 16, 8, 64],64⟩,
.cycle 15 28 true (-1),
.cycle 13 43 true (-1),
.cycle 15 16 false (3),
.last 23 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 1024, 4096],[8, 1024, 4096, 1024, 1024, 1024, 32, 1024, 4096, 1024, 1024, 4096, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[40, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 20 2 true (2),
.cycle 13 21 false (5),
.cycle 15 20 false (5),
.last 23 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[40, 20, 64, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[56, 24, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[40, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 39 true (-1)
])
theorem kid11_part124_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part124) = true := by rfl

def kid11_part125 : Audit := .split 13 (2,true) (byMove [
.cycle 18 1 false (0),
.cycle 6 17 false (5),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 41 1 false (-1),
.last 14 (5,true),
.cycle 6 16 true (2),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 15 (5,true),
.cycle 34 1 false (0),
.cycle 18 1 false (0),
.cycle 24 1 false (-2),
.last 23 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 26 1 false (0)
])
theorem kid11_part125_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part125) = true := by rfl

def kid11_part126 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 33 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 14 12 true (3),
.cycle 14 9 true (3),
.cycle 10 6 true (3),
.last 17 (2,true),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.cycle 33 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 14 7 true (3)
])
theorem kid11_part126_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part126) = true := by rfl

def kid11_part127 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 32 5 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 28 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 10 6 true (3),
.last 17 (2,true),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.cycle 32 5 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 12 16 true (3)
])
theorem kid11_part127_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part127) = true := by rfl

def kid11_part128 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.cycle 6 17 false (5),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 24 4 false (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 52 4 false (0),
.cycle 29 4 false (1),
.cycle 16 4 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 17 4 false (-1),
.cycle 10 4 true (3),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 8 8 true (3),
.cycle 24 4 false (0)
])
theorem kid11_part128_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part128) = true := by rfl

def kid11_part129 : Audit := .cycle 0 14 true (0)
theorem kid11_part129_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part129) = true := by rfl

def kid11_part130 : Audit := .cycle 10 4 true (4)
theorem kid11_part130_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part130) = true := by rfl

def kid11_part131 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.cycle 31 7 false (1),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part131_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part131) = true := by rfl

def kid11_part132 : Audit := .cycle 8 6 true (4)
theorem kid11_part132_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part132) = true := by rfl

def kid11_part133 : Audit := .cycle 7 6 true (3)
theorem kid11_part133_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part133) = true := by rfl

def kid11_part134 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 13 2 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part134_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part134) = true := by rfl

def kid11_part135 : Audit := .cycle 16 3 false (0)
theorem kid11_part135_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part135) = true := by rfl

def kid11_part136 : Audit := .split 18 (2,true) (byMove [
.cycle 16 3 false (0),
.cycle 15 6 false (1),
.cycle 21 1 false (-1),
.last 21 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 34 true (-1),
.cycle 15 10 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[4, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[24, 16, 8, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 19 (5,true),
.cycle 16 3 false (0),
.cycle 15 6 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 1024, 4096],[1024, 1024, 4096, 1024, 1024, 4096, 1024, 1024, 1024, 1024, 1024, 4096, 4096],4096⟩,
.last 19 (5,true),
.cycle 14 5 false (2),
.cycle 15 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[4, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[24, 16, 8, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 19 (5,true)
])
theorem kid11_part136_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part136) = true := by rfl

def kid11_part137 : Audit := .split 13 (2,true) (byMove [
.last 20 (5,true),
.last 22 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 7 10 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 2, 16, 16, 64, 64],64⟩,
.cycle 6 20 true (2),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 2, 16, 16, 64, 64],64⟩,
.cycle 2 14 true (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true)
])
theorem kid11_part137_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part137) = true := by rfl

def kid11_part138 : Audit := .cycle 5 8 true (1)
theorem kid11_part138_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part138) = true := by rfl

def kid11_part139 : Audit := .cycle 6 8 true (2)
theorem kid11_part139_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part139) = true := by rfl

def kid11_part140 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.cycle 96 4 false (-1),
.last 14 (2,true),
.cycle 7 17 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.cycle 20 4 false (0),
.cycle 30 4 false (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 73 4 false (9),
.cycle 16 4 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 17 4 false (-1),
.cycle 12 2 true (3),
.cycle 23 4 false (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 5 true (3)
])
theorem kid11_part140_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part140) = true := by rfl

def kid11_part141 : Audit := .cycle 0 14 true (0)
theorem kid11_part141_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part141) = true := by rfl

def kid11_part142 : Audit := .cycle 11 2 true (4)
theorem kid11_part142_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part142) = true := by rfl

def kid11_part143 : Audit := .split 13 (2,true) (byMove [
.cycle 2 13 true (1),
.cycle 23 5 false (1),
.cycle 20 1 false (0),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 12 2 true (4),
.cycle 23 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[4, 16, 16, 16, 16, 64, 64],64⟩,
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part143_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part143) = true := by rfl

def kid11_part144 : Audit := .cycle 8 6 true (4)
theorem kid11_part144_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part144) = true := by rfl

def kid11_part145 : Audit := .cycle 7 6 true (3)
theorem kid11_part145_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part145) = true := by rfl

def kid11_part146 : Audit := .split 13 (5,true) (byMove [
.cycle 12 4 true (4),
.cycle 23 5 false (1),
.last 14 (2,true),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 12 2 true (4),
.cycle 23 5 false (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part146_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part146) = true := by rfl

def kid11_part122 : Audit := .split 12 (0,true) (byMove [(kid11_part123),(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142),(kid11_part143),(kid11_part144),(kid11_part145),(kid11_part146)])

theorem kid11_part122_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part122) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part123),(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142),(kid11_part143),(kid11_part144),(kid11_part145),(kid11_part146)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part123_checked

  · exact kid11_part129_checked

  · exact kid11_part135_checked

  · exact kid11_part141_checked

  · exact kid11_part124_checked

  · exact kid11_part130_checked

  · exact kid11_part136_checked

  · exact kid11_part142_checked

  · exact kid11_part125_checked

  · exact kid11_part131_checked

  · exact kid11_part137_checked

  · exact kid11_part143_checked

  · exact kid11_part126_checked

  · exact kid11_part132_checked

  · exact kid11_part138_checked

  · exact kid11_part144_checked

  · exact kid11_part127_checked

  · exact kid11_part133_checked

  · exact kid11_part139_checked

  · exact kid11_part145_checked

  · exact kid11_part128_checked

  · exact kid11_part134_checked

  · exact kid11_part140_checked

  · exact kid11_part146_checked

def kid11_part148 : Audit := .split 19 (0,true) (byMove [
.last 52 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 5120, 4096],[8, 1024, 256, 1024, 1024, 4096, 32, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩,
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 8 false (1),
.cycle 15 7 false (1),
.cycle 15 6 true (-1),
.cycle 20 30 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 28, 64],[4, 28, 12, 16, 16, 64, 64],64⟩,
.cycle 20 1 false (0),
.last 21 (5,true),
.cycle 15 7 false (1),
.cycle 15 6 false (1),
.cycle 17 3 false (0),
.last 23 (5,true),
.cycle 20 1 false (-2),
.last 21 (5,true),
.cycle 15 7 false (1),
.cycle 14 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[2, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 28, 64],[4, 28, 12, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[8, 20, 20, 16, 16, 64, 64],64⟩,
.last 21 (5,true),
.last 22 (5,true)
])
theorem kid11_part148_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part148) = true := by rfl

def kid11_part149 : Audit := .cycle 16 3 false (0)
theorem kid11_part149_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part149) = true := by rfl

def kid11_part150 : Audit := .cycle 21 1 false (-1)
theorem kid11_part150_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part150) = true := by rfl

def kid11_part151 : Audit := .split 21 (5,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 8, 2, 2, 1, 64],64⟩,
.cycle 6 20 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 8, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 8, 2, 2, 8, 64],64⟩,
.cycle 14 11 false (2),
.last 23 (0,true),
.last 22 (0,true),
.cycle 54 15 true (7),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 8, 2, 2, 10, 64],64⟩,
.cycle 6 18 true (-1),
.cycle 6 18 true (-1),
.cycle 25 9 true (4),
.cycle 14 9 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 8, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 8, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 8, 2, 2, 8, 64],64⟩,
.cycle 20 2 true (0),
.last 23 (0,true),
.last 22 (0,true),
.cycle 1 49 true (-1),
.cycle 49 13 true (6),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 8, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 8, 2, 2, 2, 64],64⟩,
.last 27 (0,true)
])
theorem kid11_part151_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part151) = true := by rfl

def kid11_part152 : Audit := .split 21 (5,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 16, 2, 2, 1, 64],64⟩,
.cycle 6 20 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 16, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 16, 2, 2, 8, 64],64⟩,
.cycle 14 11 false (2),
.last 23 (0,true),
.last 22 (0,true),
.cycle 54 15 true (7),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 16, 2, 2, 10, 64],64⟩,
.cycle 6 18 true (-1),
.cycle 6 18 true (-1),
.cycle 25 9 true (4),
.cycle 14 9 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 16, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 16, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 16, 2, 2, 8, 64],64⟩,
.cycle 20 2 true (0),
.last 23 (0,true),
.last 22 (0,true),
.cycle 1 49 true (-1),
.cycle 49 13 true (6),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 16, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 16, 2, 2, 2, 64],64⟩,
.last 27 (0,true)
])
theorem kid11_part152_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part152) = true := by rfl

def kid11_part153 : Audit := .split 19 (5,true) (byMove [
.last 41 (0,true),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 8 false (1),
.cycle 15 7 false (1),
.cycle 15 6 true (-1),
.cycle 20 30 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 8, 4128, 1024, 1024, 4, 4096, 1024, 8, 1024, 1024, 4, 4096],6144⟩,
.cycle 20 1 false (0),
.cycle 6 18 true (-1),
.cycle 15 7 false (1),
.cycle 15 6 false (1),
.cycle 17 3 false (0),
.last 86 (0,true),
.cycle 20 1 false (-2),
.cycle 19 2 true (-2),
.cycle 15 7 false (1),
.cycle 14 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.last 21 (0,true)
])
theorem kid11_part153_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part153) = true := by rfl

def kid11_part154 : Audit := .split 19 (0,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 257, 128, 256, 8, 1024, 32, 5377, 4096],[256, 1, 1, 1024, 1024, 4096, 1449, 257, 1, 1024, 1024, 4096, 4096],6144⟩,
.cycle 6 18 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 19, 64],[18, 19, 1, 16, 16, 64, 64],64⟩,
.last 24 (5,true),
.cycle 14 9 false (2),
.cycle 15 9 false (1),
.cycle 0 24 true (-1),
.cycle 0 53 true (-1),
.cycle 0 68 true (-2),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.last 20 (5,true),
.cycle 14 7 false (2),
.cycle 0 34 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 17, 1, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 17, 1, 16, 16, 64, 64],64⟩,
.last 21 (5,true),
.cycle 15 9 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 1, 64],[1, 1, 1, 16, 16, 64, 64],64⟩,
.cycle 1 39 true (-1),
.cycle 0 44 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[8, 25, 1, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 17, 1, 16, 16, 64, 64],64⟩,
.last 20 (5,true)
])
theorem kid11_part154_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part154) = true := by rfl

def kid11_part155 : Audit := .cycle 19 29 true (0)
theorem kid11_part155_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part155) = true := by rfl

def kid11_part156 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 4, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 4, 4, 1024, 1024, 4096, 4096, 4, 4, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part156_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part156) = true := by rfl

def kid11_part157 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 8, 8, 1024, 1024, 4096, 4096, 1024, 8, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part157_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part157) = true := by rfl

def kid11_part158 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 16, 16, 1024, 1024, 4096, 4096, 1024, 16, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part158_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part158) = true := by rfl

def kid11_part159 : Audit := .split 19 (5,true) (byMove [
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.cycle 6 18 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 10, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 10, 2, 2, 8, 64],64⟩,
.cycle 14 9 false (2),
.last 21 (0,true),
.last 20 (0,true),
.cycle 46 11 true (7),
.cycle 61 35 true (3),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.cycle 23 7 true (4),
.cycle 14 7 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 10, 2, 2, 4, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 10, 1, 64],[64, 2, 10, 2, 2, 8, 64],64⟩,
.cycle 19 2 true (0),
.last 21 (0,true),
.last 20 (0,true),
.cycle 1 39 true (-1),
.cycle 41 9 true (7),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 2, 2, 2, 2, 64],64⟩,
.last 25 (0,true)
])
theorem kid11_part159_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part159) = true := by rfl

def kid11_part160 : Audit := .split 19 (0,true) (byMove [
.proven (BB6.Agent11Raw121Pumps.M4128.table) (fun m hm => BB6.Agent11Raw121Pumps.M4128.never m hm),
.last 50 (5,true),
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 8 false (1),
.cycle 15 7 false (1),
.cycle 0 26 true (-1),
.cycle 16 4 true (-1),
.cycle 15 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[8, 16, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 20 (5,true),
.cycle 15 6 false (1),
.cycle 17 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.cycle 20 1 false (-2),
.last 21 (5,true),
.cycle 15 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 1, 64],[1, 1, 1, 16, 16, 64, 64],64⟩,
.cycle 15 5 false (1),
.cycle 18 2 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[8, 16, 16, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 20 (5,true)
])
theorem kid11_part160_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part160) = true := by rfl

def kid11_part161 : Audit := .cycle 16 3 false (0)
theorem kid11_part161_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part161) = true := by rfl

def kid11_part162 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part162_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part162) = true := by rfl

def kid11_part163 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part163_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part163) = true := by rfl

def kid11_part164 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 4096, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part164_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part164) = true := by rfl

def kid11_part165 : Audit := .split 19 (5,true) (byMove [
.last 24 (0,true),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.cycle 21 1 false (-1),
.cycle 20 1 false (-2),
.cycle 15 8 false (1),
.cycle 15 7 false (1),
.last 20 (0,true),
.cycle 16 4 true (-1),
.cycle 15 8 false (1),
.far true 1 ⟨0,[0, 0],[2, 10, 10, 8, 10, 1, 64],[64, 2, 32, 2, 2, 10, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.cycle 23 9 true (3),
.cycle 15 6 false (1),
.cycle 17 3 false (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[128, 256, 8, 0, 32, 1024, 128, 256, 32768, 1024, 131072, 16777216, 524288, 1048576, 2097152, 1024, 8388608, 1024, 524288, 1048576, 2097152, 4195328, 8388608, 20972544, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 16777216, 4194304, 4194304, 4194304, 16777216, 20972544, 20972544, 4194304, 4194304, 20972544, 16777216],33388544⟩,
.cycle 20 1 false (-2),
.cycle 19 2 true (-2),
.cycle 15 7 false (1),
.last 20 (0,true),
.cycle 15 5 false (1),
.cycle 18 2 true (-1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 1, 64],[64, 2, 32, 2, 2, 2, 64],64⟩,
.last 27 (0,true)
])
theorem kid11_part165_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part165) = true := by rfl

def kid11_part166 : Audit := .split 19 (0,true) (byMove [
.far false 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 0, 1],[128, 256, 8, 4195328, 32, 4194304, 524288, 1048576, 32768, 4194304, 131072, 1088, 8192, 16384, 32768, 4260864, 131072, 1751119296, 128, 256, 134217728, 1024, 536870912, 1073742848, 128, 256, 8, 4194304, 32, 4194304, 1073741824],[1048576, 262144, 64, 1024, 1024, 1073741824, 671088640, 4194304, 262144, 4194304, 4194304, 1073741824, 1751119296, 1751119296, 4096, 65536, 65536, 1073741824, 4194304, 1024, 64, 1024, 1024, 1073741824, 1048576, 262144, 64, 1024, 1024, 1073741824, 1073741824],1185676622⟩,
.cycle 15 5 false (1),
.cycle 13 9 false (3),
.last 22 (5,true),
.last 22 (5,true),
.last 20 (5,true),
.cycle 0 24 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 3, 64],[2, 3, 1, 16, 16, 64, 64],64⟩,
.cycle 6 24 true (-1),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.last 20 (5,true),
.cycle 15 8 false (1),
.cycle 15 5 false (1),
.cycle 18 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 17, 1, 16, 16, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 5120, 4096],[4096, 64, 64, 1024, 1024, 4096, 1024, 1024, 64, 1024, 1024, 4096, 4096],6144⟩,
.last 20 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 1, 64],[1, 1, 1, 16, 16, 64, 64],64⟩,
.cycle 13 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 5, 64],[4, 5, 1, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 25, 64],[8, 25, 1, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[16, 17, 1, 16, 16, 64, 64],64⟩,
.last 20 (5,true)
])
theorem kid11_part166_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part166) = true := by rfl

def kid11_part167 : Audit := .cycle 14 5 false (2)
theorem kid11_part167_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part167) = true := by rfl

def kid11_part168 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 256, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 256, 256, 1024, 1024, 4096, 4096, 256, 256, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part168_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part168) = true := by rfl

def kid11_part169 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 512, 512, 1024, 1024, 4096, 4096, 1024, 512, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part169_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part169) = true := by rfl

def kid11_part170 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part170_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part170) = true := by rfl

def kid11_part171 : Audit := .split 19 (5,true) (byMove [
.last 20 (0,true),
.cycle 15 5 false (1),
.last 22 (0,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 32, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 2048, 2048, 1024, 1024, 32, 4096, 32, 2048, 1024, 1024, 32, 4096],6144⟩,
.cycle 13 13 false (3),
.cycle 15 9 false (1),
.last 20 (0,true),
.last 54 (0,true),
.cycle 6 24 true (-1),
.cycle 6 16 true (-1),
.cycle 6 16 true (-1),
.cycle 21 18 true (3),
.last 20 (0,true),
.cycle 15 5 false (1),
.cycle 18 2 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 2048, 2048, 1024, 1024, 1024, 4096, 1024, 2048, 1024, 1024, 1024, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 2048, 2048, 1024, 1024, 0, 4096, 1024, 2048, 1024, 1024, 1024, 4096],6144⟩,
.cycle 15 9 false (1),
.last 20 (0,true),
.cycle 13 7 false (3),
.last 57 (0,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1536, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 2048, 2048, 1024, 1024, 512, 4096, 1536, 2048, 1024, 1024, 512, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 2048, 2048, 1024, 1024, 1024, 4096, 1024, 2048, 1024, 1024, 1024, 4096],6144⟩,
.last 25 (0,true)
])
theorem kid11_part171_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part171) = true := by rfl

def kid11_part147 : Audit := .split 18 (2,true) (byMove [(kid11_part148),(kid11_part149),(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171)])

theorem kid11_part147_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part147) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) 18 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part148),(kid11_part149),(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part148_checked

  · exact kid11_part154_checked

  · exact kid11_part160_checked

  · exact kid11_part166_checked

  · exact kid11_part149_checked

  · exact kid11_part155_checked

  · exact kid11_part161_checked

  · exact kid11_part167_checked

  · exact kid11_part150_checked

  · exact kid11_part156_checked

  · exact kid11_part162_checked

  · exact kid11_part168_checked

  · exact kid11_part151_checked

  · exact kid11_part157_checked

  · exact kid11_part163_checked

  · exact kid11_part169_checked

  · exact kid11_part152_checked

  · exact kid11_part158_checked

  · exact kid11_part164_checked

  · exact kid11_part170_checked

  · exact kid11_part153_checked

  · exact kid11_part159_checked

  · exact kid11_part165_checked

  · exact kid11_part171_checked

def kid11_part173 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 6 17 false (5),
.cycle 0 17 false (5),
.cycle 35 1 false (-1),
.cycle 26 16 false (2),
.last 14 (5,true),
.cycle 0 21 true (0),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 15 (5,true),
.cycle 22 13 false (2),
.cycle 15 8 false (1),
.cycle 15 3 false (1),
.cycle 14 5 false (2),
.last 17 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 10 4 true (3),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid11_part173_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part173) = true := by rfl

def kid11_part174 : Audit := .split 21 (5,true) (byMove [
.cycle 32 28 true (4),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 6, 1, 64],[64, 4, 2, 6, 6, 2, 64],64⟩,
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 14, 1, 64],[64, 4, 2, 6, 6, 4, 64],64⟩,
.cycle 18 35 true (0),
.cycle 18 10 true (0),
.last 23 (0,true),
.cycle 0 38 true (-1),
.cycle 18 34 true (0),
.cycle 30 28 true (4),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 14, 1, 64],[64, 4, 2, 6, 6, 14, 64],64⟩,
.cycle 22 18 true (4),
.cycle 38 17 true (4),
.cycle 18 8 true (0),
.cycle 44 17 true (2),
.cycle 22 12 true (2),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 14, 1, 64],[64, 4, 2, 6, 6, 8, 64],64⟩,
.cycle 20 2 true (2),
.last 23 (0,true),
.cycle 18 38 true (0),
.cycle 1 38 true (-1),
.cycle 18 30 true (0),
.cycle 18 16 true (0),
.cycle 22 10 true (4),
.last 23 (0,true)
])
theorem kid11_part174_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part174) = true := by rfl

def kid11_part175 : Audit := .cycle 18 1 false (0)
theorem kid11_part175_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part175) = true := by rfl

def kid11_part176 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (0,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 14 12 true (3),
.cycle 14 9 true (3),
.cycle 10 6 true (3),
.cycle 8 11 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.last 17 (0,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (0,true)
])
theorem kid11_part176_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part176) = true := by rfl

def kid11_part177 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (0,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 28 true (2),
.far true 1 ⟨0,[0, 0],[16, 0, 8, 8, 16, 1, 64],[64, 4, 16, 0, 0, 16, 64],64⟩,
.cycle 10 6 true (3),
.cycle 7 11 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.last 17 (0,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (0,true)
])
theorem kid11_part177_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part177) = true := by rfl

def kid11_part178 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 6 17 false (5),
.cycle 16 4 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.last 18 (0,true),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 26 (0,true),
.cycle 29 4 false (1),
.last 14 (0,true),
.cycle 15 3 false (1),
.cycle 16 4 false (0),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 17 4 false (-1),
.cycle 10 4 true (3),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 8 8 true (3),
.last 15 (0,true)
])
theorem kid11_part178_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part178) = true := by rfl

def kid11_part179 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.cycle 0 16 true (0),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true)
])
theorem kid11_part179_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part179) = true := by rfl

def kid11_part180 : Audit := .cycle 8 8 true (4)
theorem kid11_part180_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part180) = true := by rfl

def kid11_part181 : Audit := .cycle 6 16 true (2)
theorem kid11_part181_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part181) = true := by rfl

def kid11_part182 : Audit := .cycle 8 6 true (4)
theorem kid11_part182_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part182) = true := by rfl

def kid11_part183 : Audit := .cycle 7 6 true (3)
theorem kid11_part183_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part183) = true := by rfl

def kid11_part184 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.cycle 9 7 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 13 2 true (4),
.last 15 (0,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true)
])
theorem kid11_part184_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part184) = true := by rfl

def kid11_part185 : Audit := .split 13 (0,true) (byMove [
.last 26 (5,true),
.last 22 (5,true),
.cycle 16 3 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 7 10 true (3),
.cycle 29 3 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 17 3 false (0),
.cycle 15 3 false (1),
.cycle 16 3 false (0),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 23 3 false (1),
.cycle 12 2 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true)
])
theorem kid11_part185_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part185) = true := by rfl

def kid11_part186 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part186_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part186) = true := by rfl

def kid11_part187 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part187_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part187) = true := by rfl

def kid11_part188 : Audit := .cycle 5 8 true (1)
theorem kid11_part188_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part188) = true := by rfl

def kid11_part189 : Audit := .cycle 6 8 true (2)
theorem kid11_part189_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part189) = true := by rfl

def kid11_part190 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 21 24 true (3),
.cycle 16 4 false (0),
.cycle 7 17 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 7 10 true (3),
.last 16 (0,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 73 4 false (9),
.last 14 (0,true),
.cycle 15 3 false (1),
.cycle 16 4 false (0),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 23 4 false (1),
.cycle 12 2 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 17 (0,true)
])
theorem kid11_part190_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part190) = true := by rfl

def kid11_part191 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 20 12 true (-1),
.cycle 0 15 true (0),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 17 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[17, 17, 1, 16, 16, 64, 64],64⟩,
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true)
])
theorem kid11_part191_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part191) = true := by rfl

def kid11_part192 : Audit := .cycle 11 2 true (4)
theorem kid11_part192_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part192) = true := by rfl

def kid11_part193 : Audit := .cycle 2 12 true (1)
theorem kid11_part193_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part193) = true := by rfl

def kid11_part194 : Audit := .cycle 8 6 true (4)
theorem kid11_part194_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part194) = true := by rfl

def kid11_part195 : Audit := .cycle 7 6 true (3)
theorem kid11_part195_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part195) = true := by rfl

def kid11_part196 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 20 12 true (-1),
.last 16 (0,true),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 14 (0,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 1024, 2048, 1024, 1024, 2048, 4096, 1024, 2048, 1024, 1024, 1024, 4096],6144⟩,
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true)
])
theorem kid11_part196_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part196) = true := by rfl

def kid11_part172 : Audit := .split 12 (2,true) (byMove [(kid11_part173),(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182),(kid11_part183),(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196)])

theorem kid11_part172_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part172) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part173),(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182),(kid11_part183),(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part173_checked

  · exact kid11_part179_checked

  · exact kid11_part185_checked

  · exact kid11_part191_checked

  · exact kid11_part174_checked

  · exact kid11_part180_checked

  · exact kid11_part186_checked

  · exact kid11_part192_checked

  · exact kid11_part175_checked

  · exact kid11_part181_checked

  · exact kid11_part187_checked

  · exact kid11_part193_checked

  · exact kid11_part176_checked

  · exact kid11_part182_checked

  · exact kid11_part188_checked

  · exact kid11_part194_checked

  · exact kid11_part177_checked

  · exact kid11_part183_checked

  · exact kid11_part189_checked

  · exact kid11_part195_checked

  · exact kid11_part178_checked

  · exact kid11_part184_checked

  · exact kid11_part190_checked

  · exact kid11_part196_checked

def kid11_part197 : Audit := .cycle 7 6 true (3)
theorem kid11_part197_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part197) = true := by rfl

def kid11_part198 : Audit := .cycle 6 6 true (2)
theorem kid11_part198_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part198) = true := by rfl

def kid11_part200 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 6 17 false (5),
.last 14 (2,true),
.cycle 35 1 false (-1),
.last 42 (2,true),
.cycle 0 17 false (5),
.last 19 (2,true),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.last 35 (2,true),
.last 22 (2,true),
.last 18 (2,true),
.last 14 (2,true),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 19 (2,true),
.cycle 10 4 true (3),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 12 4 true (3)
])
theorem kid11_part200_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part200) = true := by rfl

def kid11_part201 : Audit := .split 41 (0,true) (byMove [
.last 44 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.cycle 43 1 false (-1),
.cycle 42 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.cycle 15 30 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[2, 56, 64, 16, 16, 56, 64],64⟩,
.last 42 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[8, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[16, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[32, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.last 43 (2,true),
.last 182 (2,true),
.cycle 42 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1032, 128, 256, 8, 1024, 32, 64, 4096],[64, 1088, 4096, 1024, 1024, 8, 64, 1032, 4096, 1024, 1024, 1184, 4096],4096⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[2, 56, 64, 16, 16, 56, 64],64⟩,
.last 42 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[8, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[16, 56, 64, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[32, 56, 64, 16, 16, 56, 64],64⟩
])
theorem kid11_part201_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part201) = true := by rfl

def kid11_part202 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 6 17 false (5),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 41 1 false (-1),
.cycle 18 1 false (0),
.cycle 6 16 true (2),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 6 16 true (2),
.cycle 34 1 false (0),
.last 14 (0,true),
.cycle 25 1 false (-3),
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 12, 1, 64],[64, 32, 4, 4, 4, 4, 64],64⟩,
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.cycle 18 1 false (0),
.cycle 10 4 true (3),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 2 14 true (1),
.last 15 (0,true)
])
theorem kid11_part202_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part202) = true := by rfl

def kid11_part203 : Audit := .cycle 7 11 true (3)
theorem kid11_part203_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part203) = true := by rfl

def kid11_part204 : Audit := .cycle 8 8 true (3)
theorem kid11_part204_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part204) = true := by rfl

def kid11_part205 : Audit := .cycle 16 4 false (0)
theorem kid11_part205_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part205) = true := by rfl

def kid11_part206 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 29 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 20 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 0 17 true (0)
])
theorem kid11_part206_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part206) = true := by rfl

def kid11_part207 : Audit := .split 15 (0,true) (byMove [
.cycle 9 21 false (5),
.cycle 18 17 false (5),
.last 16 (2,true),
.cycle 49 1 false (-1),
.cycle 50 5 false (0),
.last 18 (2,true),
.cycle 0 18 true (0),
.cycle 25 5 false (1),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 43 5 false (2),
.cycle 19 5 false (0),
.last 22 (2,true),
.last 16 (2,true),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 20 5 false (1),
.cycle 0 18 true (0),
.cycle 31 5 false (1),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 12 4 true (3)
])
theorem kid11_part207_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part207) = true := by rfl

def kid11_part208 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 10 4 true (4),
.cycle 31 8 false (1),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 6 18 true (2),
.last 15 (0,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true)
])
theorem kid11_part208_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part208) = true := by rfl

def kid11_part209 : Audit := .cycle 8 6 true (4)
theorem kid11_part209_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part209) = true := by rfl

def kid11_part210 : Audit := .cycle 7 6 true (3)
theorem kid11_part210_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part210) = true := by rfl

def kid11_part211 : Audit := .cycle 9 5 true (4)
theorem kid11_part211_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part211) = true := by rfl

def kid11_part212 : Audit := .split 13 (0,true) (byMove [
.cycle 10 17 false (5),
.cycle 16 13 false (4),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 37 3 false (0),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 25 3 false (0),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 29 3 false (1),
.cycle 17 3 false (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 16 3 false (0),
.cycle 0 16 true (0),
.cycle 23 3 false (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part212_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part212) = true := by rfl

def kid11_part213 : Audit := .split 18 (2,true) (byMove [
.last 19 (0,true),
.cycle 15 7 false (1),
.cycle 21 1 false (-1),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 8, 2048, 2048, 128, 262144, 2048, 32768, 2176, 2176, 128, 262144, 2048, 32768, 2176, 2176, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 16, 2048, 2048, 128, 262144, 2048, 65536, 2176, 2176, 128, 262144, 2048, 65536, 2176, 2176, 128, 262144],274432⟩,
.cycle 16 3 false (0),
.last 19 (0,true),
.last 21 (0,true),
.far true 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 2176, 16779392, 512, 2097152, 128, 262144, 25692288, 25692288, 28051648, 2097152, 25692288, 262144, 16777216],[16777216, 2048, 512, 2048, 2048, 128, 16777216, 2048, 512, 2176, 2176, 128, 16777216, 8388608, 2240, 2176, 2176, 524288, 16777216, 8388608, 28052160, 25692288, 25692288, 524288, 16777216],31334400⟩,
.last 35 (0,true),
.last 35 (0,true),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 128, 2048, 2048, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144, 2048, 128, 2176, 2176, 128, 262144],274432⟩,
.last 19 (0,true),
.cycle 15 7 false (1),
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2432, 2432, 512, 512, 128, 64, 128, 256, 320, 512, 256, 64, 264576, 264576, 512, 512, 128, 64, 262144],[262144, 2048, 256, 2048, 2048, 128, 262144, 2048, 256, 2432, 2432, 128, 262144, 2048, 256, 2304, 2304, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 512, 2048, 2048, 128, 262144, 2048, 512, 2176, 2176, 128, 262144, 2048, 512, 2176, 2176, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 1024, 2048, 2048, 128, 262144, 2048, 1024, 2176, 2176, 128, 262144, 2048, 1024, 2176, 2176, 128, 262144],274432⟩,
.cycle 16 3 false (0),
.last 19 (0,true),
.cycle 15 9 false (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[128, 256, 8, 0, 32, 256, 128, 256, 32768, 1024, 131072, 16777216, 524288, 1048576, 2097152, 1024, 8388608, 256, 524288, 1048576, 2097152, 4195328, 8388608, 17826048, 16777216],[16777216, 256, 256, 1024, 1024, 256, 16777216, 256, 256, 1024, 1024, 256, 16777216, 16777216, 1048576, 4194304, 4194304, 256, 16777216, 17826048, 1048576, 4194304, 4194304, 17826048, 16777216],33388544⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 2176, 2048, 2048, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144],274432⟩,
.far true 3 ⟨0,[0, 1, 2, 1, 2, 1],[2176, 2176, 512, 512, 128, 64, 128, 2176, 2240, 512, 2176, 64, 264320, 264320, 512, 512, 128, 64, 262144],[262144, 2048, 2048, 2048, 2048, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144, 2048, 2176, 2176, 2176, 128, 262144],274432⟩,
.cycle 14 5 false (2)
])
theorem kid11_part213_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part213) = true := by rfl

def kid11_part214 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.last 34 (0,true),
.cycle 18 1 false (0),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.cycle 20 14 true (1),
.last 14 (0,true),
.last 16 (0,true),
.cycle 6 20 true (2),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 7 10 true (3),
.last 14 (0,true),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[128, 256, 8, 0, 32, 1024, 128, 256, 32768, 1024, 131072, 16777216, 524288, 1048576, 2097152, 1024, 8388608, 1024, 524288, 1048576, 2097152, 4195328, 8388608, 20972544, 16777216],[16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 16777216, 1024, 4194304, 4194304, 4194304, 16777216, 20972544, 20972544, 4194304, 4194304, 20972544, 16777216],33388544⟩,
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 12, 1, 64],[64, 32, 4, 4, 4, 4, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16777216, 128, 256, 2097152, 1024, 8388608, 16777216, 128, 256, 8, 65536, 32, 65536, 16777216],[16777216, 16843776, 16843776, 1024, 1024, 1024, 16777216, 65536, 65536, 65536, 65536, 16843776, 16777216, 16843776, 16843776, 1024, 1024, 1024, 16777216, 16777216, 16777216, 1024, 1024, 1024, 16777216],22719870⟩,
.last 14 (0,true),
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 12, 1, 64],[64, 32, 4, 4, 4, 4, 64],64⟩,
.cycle 2 14 true (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part214_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part214) = true := by rfl

def kid11_part215 : Audit := .cycle 5 8 true (1)
theorem kid11_part215_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part215) = true := by rfl

def kid11_part216 : Audit := .cycle 6 8 true (2)
theorem kid11_part216_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part216) = true := by rfl

def kid11_part217 : Audit := .cycle 16 4 false (0)
theorem kid11_part217_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part217) = true := by rfl

def kid11_part218 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 23 6 false (1),
.last 14 (2,true),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 17 5 false (1),
.cycle 23 6 false (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 0 17 true (0)
])
theorem kid11_part218_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part218) = true := by rfl

def kid11_part219 : Audit := .cycle 11 2 true (4)
theorem kid11_part219_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part219) = true := by rfl

def kid11_part220 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 23 6 false (1),
.cycle 20 1 false (0),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 14 (0,true),
.cycle 23 6 false (1),
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 12, 1, 64],[64, 32, 4, 4, 4, 4, 64],64⟩,
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (0,true)
])
theorem kid11_part220_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part220) = true := by rfl

def kid11_part221 : Audit := .cycle 8 6 true (4)
theorem kid11_part221_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part221) = true := by rfl

def kid11_part222 : Audit := .cycle 7 6 true (3)
theorem kid11_part222_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part222) = true := by rfl

def kid11_part223 : Audit := .split 15 (0,true) (byMove [
.cycle 0 21 false (6),
.cycle 27 14 false (3),
.last 16 (2,true),
.cycle 17 7 true (4),
.cycle 12 14 true (4),
.cycle 25 10 false (2),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[2, 32, 64, 16, 16, 32, 64],64⟩,
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 13 3 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 12 7 true (3),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 12 5 true (4),
.cycle 0 17 true (0),
.cycle 11 5 true (4),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 13 3 true (5)
])
theorem kid11_part223_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part223) = true := by rfl

def kid11_part199 : Audit := .split 12 (5,true) (byMove [(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223)])

theorem kid11_part199_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part199) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part200_checked

  · exact kid11_part206_checked

  · exact kid11_part212_checked

  · exact kid11_part218_checked

  · exact kid11_part201_checked

  · exact kid11_part207_checked

  · exact kid11_part213_checked

  · exact kid11_part219_checked

  · exact kid11_part202_checked

  · exact kid11_part208_checked

  · exact kid11_part214_checked

  · exact kid11_part220_checked

  · exact kid11_part203_checked

  · exact kid11_part209_checked

  · exact kid11_part215_checked

  · exact kid11_part221_checked

  · exact kid11_part204_checked

  · exact kid11_part210_checked

  · exact kid11_part216_checked

  · exact kid11_part222_checked

  · exact kid11_part205_checked

  · exact kid11_part211_checked

  · exact kid11_part217_checked

  · exact kid11_part223_checked

def kid11_part224 : Audit := .cycle 0 12 true (0)
theorem kid11_part224_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part224) = true := by rfl

def kid11_part225 : Audit := .cycle 1 11 true (1)
theorem kid11_part225_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part225) = true := by rfl

def kid11_part226 : Audit := .cycle 2 10 true (1)
theorem kid11_part226_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part226) = true := by rfl

def kid11_part227 : Audit := .cycle 7 7 true (3)
theorem kid11_part227_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part227) = true := by rfl

def kid11_part228 : Audit := .cycle 8 4 true (4)
theorem kid11_part228_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part228) = true := by rfl

def kid11_part230 : Audit := .cycle 0 19 false (6)
theorem kid11_part230_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part230) = true := by rfl

def kid11_part231 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 2048, 128, 256, 8, 1024, 32, 1024, 4096],[8, 2048, 4096, 1024, 1024, 4096, 1024, 2048, 4096, 1024, 1024, 4096, 4096],4096⟩
theorem kid11_part231_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part231) = true := by rfl

def kid11_part232 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 false (6),
.last 32 (5,true),
.cycle 20 1 false (0),
.last 20 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.cycle 10 5 true (4),
.cycle 1 16 true (1),
.cycle 8 9 true (4),
.cycle 6 13 true (2),
.last 16 (5,true),
.last 18 (5,true),
.cycle 17 5 false (1),
.last 16 (5,true),
.last 26 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.cycle 10 5 true (4),
.cycle 1 16 true (1),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.last 16 (5,true),
.cycle 30 1 false (0)
])
theorem kid11_part232_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part232) = true := by rfl

def kid11_part233 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 39 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 19 true (2),
.cycle 6 16 true (2),
.cycle 8 9 true (4),
.cycle 9 8 true (4),
.cycle 10 7 true (4),
.last 18 (2,true),
.cycle 8 11 true (4),
.cycle 4 13 true (1),
.cycle 15 2 true (5),
.cycle 39 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 15 7 true (4)
])
theorem kid11_part233_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part233) = true := by rfl

def kid11_part234 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 32 17 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 19 true (2),
.cycle 6 16 true (2),
.cycle 8 9 true (4),
.cycle 9 8 true (4),
.cycle 10 7 true (4),
.last 18 (2,true),
.cycle 8 11 true (4),
.cycle 4 13 true (1),
.cycle 15 2 true (5),
.cycle 40 6 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 12 12 true (4)
])
theorem kid11_part234_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part234) = true := by rfl

def kid11_part235 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 32, 64, 16, 16, 56, 64],64⟩,
.last 15 (2,true),
.cycle 8 14 true (3),
.cycle 7 14 true (3),
.cycle 18 6 false (0),
.cycle 10 5 true (4),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 6 13 true (2),
.cycle 8 9 true (4),
.cycle 9 10 true (4),
.cycle 17 5 false (1),
.cycle 14 2 true (3),
.last 15 (2,true),
.cycle 4 15 true (1),
.cycle 17 2 true (5),
.cycle 16 6 false (2),
.cycle 10 5 true (4),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.cycle 8 9 true (4),
.cycle 24 8 false (2)
])
theorem kid11_part235_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part235) = true := by rfl

def kid11_part236 : Audit := .cycle 0 15 true (0)
theorem kid11_part236_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part236) = true := by rfl

def kid11_part237 : Audit := .cycle 11 3 true (5)
theorem kid11_part237_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part237) = true := by rfl

def kid11_part238 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 24 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 10 5 true (4),
.last 18 (5,true),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.last 16 (5,true),
.last 33 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part238_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part238) = true := by rfl

def kid11_part239 : Audit := .cycle 8 7 true (4)
theorem kid11_part239_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part239) = true := by rfl

def kid11_part240 : Audit := .cycle 7 7 true (3)
theorem kid11_part240_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part240) = true := by rfl

def kid11_part241 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 24 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 10 5 true (4),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.cycle 14 2 true (5),
.cycle 29 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part241_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part241) = true := by rfl

def kid11_part242 : Audit := .split 21 (5,true) (byMove [
.cycle 17 5 false (1),
.cycle 17 7 false (1),
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 17 11 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 33, 64],[33, 32, 64, 16, 16, 1, 64],64⟩,
.cycle 30 24 true (6),
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 25 10 true (5),
.cycle 17 5 false (1),
.cycle 20 2 true (0),
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.cycle 19 6 false (1),
.cycle 15 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 34, 64],[34, 32, 64, 16, 16, 2, 64],64⟩,
.last 22 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 32, 64, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[48, 32, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩
])
theorem kid11_part242_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part242) = true := by rfl

def kid11_part243 : Audit := .split 15 (5,true) (byMove [
.last 30 (2,true),
.last 40 (2,true),
.last 16 (2,true),
.cycle 7 14 true (3),
.cycle 8 11 true (4),
.cycle 19 8 false (1),
.last 18 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 9 8 true (4),
.last 30 (2,true),
.cycle 14 2 true (4),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 18 6 false (2),
.cycle 0 19 true (0),
.cycle 11 5 true (4),
.last 16 (2,true),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 12 5 true (4)
])
theorem kid11_part243_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part243) = true := by rfl

def kid11_part244 : Audit := .split 14 (2,true) (byMove [
.cycle 16 5 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 2048, 128, 256, 8, 1024, 32, 1024, 4096],[1024, 2048, 8, 1024, 1024, 4096, 1024, 2048, 1024, 1024, 1024, 4096, 4096],4096⟩,
.cycle 20 1 false (0),
.last 17 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 7 11 true (3),
.last 16 (5,true),
.cycle 6 21 true (2),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true),
.last 21 (5,true),
.last 16 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[16, 32, 16, 16, 16, 64, 64],64⟩,
.cycle 6 11 true (2),
.cycle 6 11 true (2),
.last 15 (5,true),
.cycle 13 2 true (4),
.last 16 (5,true),
.cycle 2 15 true (1),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true)
])
theorem kid11_part244_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part244) = true := by rfl

def kid11_part245 : Audit := .cycle 5 9 true (1)
theorem kid11_part245_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part245) = true := by rfl

def kid11_part246 : Audit := .cycle 6 9 true (2)
theorem kid11_part246_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part246) = true := by rfl

def kid11_part247 : Audit := .split 14 (5,true) (byMove [
.last 21 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 32, 64, 16, 16, 56, 64],64⟩,
.last 15 (2,true),
.cycle 7 18 true (3),
.cycle 7 16 true (3),
.cycle 18 6 false (0),
.cycle 18 9 false (3),
.cycle 1 16 true (1),
.last 15 (2,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 9 8 true (4),
.cycle 16 5 false (2),
.cycle 14 2 true (3),
.last 15 (2,true),
.cycle 6 11 true (2),
.cycle 6 11 true (2),
.cycle 16 6 false (2),
.cycle 13 2 true (4),
.cycle 1 16 true (1),
.last 15 (2,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 12 5 true (4)
])
theorem kid11_part247_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part247) = true := by rfl

def kid11_part248 : Audit := .cycle 0 15 true (0)
theorem kid11_part248_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part248) = true := by rfl

def kid11_part249 : Audit := .cycle 11 3 true (5)
theorem kid11_part249_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part249) = true := by rfl

def kid11_part250 : Audit := .split 14 (2,true) (byMove [
.cycle 2 14 true (1),
.cycle 11 4 true (5),
.cycle 22 1 false (0),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 13 2 true (5),
.last 16 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[4, 32, 16, 16, 16, 64, 64],64⟩,
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part250_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part250) = true := by rfl

def kid11_part251 : Audit := .cycle 8 7 true (4)
theorem kid11_part251_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part251) = true := by rfl

def kid11_part252 : Audit := .cycle 7 7 true (3)
theorem kid11_part252_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part252) = true := by rfl

def kid11_part253 : Audit := .split 14 (5,true) (byMove [
.cycle 12 4 true (5),
.cycle 11 4 true (5),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 18 8 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 13 2 true (5),
.cycle 14 2 true (5),
.last 15 (2,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 18 6 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part253_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part253) = true := by rfl

def kid11_part229 : Audit := .split 13 (0,true) (byMove [(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part239),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253)])

theorem kid11_part229_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part229) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) 13 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (0,true) (some mv)) (byMove [(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part239),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part230_checked

  · exact kid11_part236_checked

  · exact kid11_part242_checked

  · exact kid11_part248_checked

  · exact kid11_part231_checked

  · exact kid11_part237_checked

  · exact kid11_part243_checked

  · exact kid11_part249_checked

  · exact kid11_part232_checked

  · exact kid11_part238_checked

  · exact kid11_part244_checked

  · exact kid11_part250_checked

  · exact kid11_part233_checked

  · exact kid11_part239_checked

  · exact kid11_part245_checked

  · exact kid11_part251_checked

  · exact kid11_part234_checked

  · exact kid11_part240_checked

  · exact kid11_part246_checked

  · exact kid11_part252_checked

  · exact kid11_part235_checked

  · exact kid11_part241_checked

  · exact kid11_part247_checked

  · exact kid11_part253_checked

def kid11_part109 : Audit := .split 11 (1,true) (byMove [(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116),(kid11_part117),(kid11_part118),(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part147),(kid11_part172),(kid11_part197),(kid11_part198),(kid11_part199),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229)])

theorem kid11_part109_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (kid11_part109) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116),(kid11_part117),(kid11_part118),(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part147),(kid11_part172),(kid11_part197),(kid11_part198),(kid11_part199),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part110_checked

  · exact kid11_part116_checked

  · exact kid11_part122_checked

  · exact kid11_part224_checked

  · exact kid11_part111_checked

  · exact kid11_part117_checked

  · exact kid11_part147_checked

  · exact kid11_part225_checked

  · exact kid11_part112_checked

  · exact kid11_part118_checked

  · exact kid11_part172_checked

  · exact kid11_part226_checked

  · exact kid11_part113_checked

  · exact kid11_part119_checked

  · exact kid11_part197_checked

  · exact kid11_part227_checked

  · exact kid11_part114_checked

  · exact kid11_part120_checked

  · exact kid11_part198_checked

  · exact kid11_part228_checked

  · exact kid11_part115_checked

  · exact kid11_part121_checked

  · exact kid11_part199_checked

  · exact kid11_part229_checked

def kid11_part256 : Audit := .cycle 0 17 false (5)
theorem kid11_part256_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part256) = true := by rfl

def kid11_part257 : Audit := .split 13 (1,true) (byMove [
.cycle 0 32 false (5),
.cycle 14 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 14 32 false (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 18 true (1),
.cycle 14 27 false (4),
.last 21 (5,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[40, 20, 20, 16, 16, 64, 64],64⟩,
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 16 (5,true)
])
theorem kid11_part257_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part257) = true := by rfl

def kid11_part258 : Audit := .cycle 18 1 false (0)
theorem kid11_part258_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part258) = true := by rfl

def kid11_part259 : Audit := .cycle 8 6 true (3)
theorem kid11_part259_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part259) = true := by rfl

def kid11_part260 : Audit := .cycle 7 6 true (3)
theorem kid11_part260_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part260) = true := by rfl

def kid11_part261 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.last 20 (1,true),
.cycle 29 4 false (1),
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 15 (1,true)
])
theorem kid11_part261_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part261) = true := by rfl

def kid11_part262 : Audit := .cycle 0 13 true (0)
theorem kid11_part262_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part262) = true := by rfl

def kid11_part263 : Audit := .cycle 1 12 true (1)
theorem kid11_part263_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part263) = true := by rfl

def kid11_part264 : Audit := .cycle 6 13 true (2)
theorem kid11_part264_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part264) = true := by rfl

def kid11_part265 : Audit := .cycle 3 10 true (1)
theorem kid11_part265_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part265) = true := by rfl

def kid11_part266 : Audit := .cycle 8 5 true (4)
theorem kid11_part266_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part266) = true := by rfl

def kid11_part267 : Audit := .cycle 9 4 true (4)
theorem kid11_part267_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part267) = true := by rfl

def kid11_part268 : Audit := .split 18 (1,true) (byMove [
.cycle 16 3 false (0),
.far false 6 ⟨0,[0, 1, 2, 3, 4, 4, 5, 3, 4, 4, 4, 4],[128, 256, 8, 0, 32, 34359738368, 524288, 1048576, 32768, 4194304, 131072, 268435456, 33554432, 67108864, 134217728, 4194304, 536870912, 34359738368, 524288, 1048576, 8589934592, 4194304, 34359738368, 68723671040, 33554432, 67108864, 134217728, 272629760, 536870912, 104090042368, 33554432, 67108864, 134217728, 4194304, 536870912, 34359738368, 68719476736],[4194304, 32768, 1048576, 1024, 1024, 68719476736, 4194304, 4194304, 34359738368, 4194304, 4194304, 68719476736, 34359738368, 8589934592, 1048576, 268435456, 268435456, 68719476736, 4194304, 34359738368, 34359738368, 4194304, 4194304, 68719476736, 104090042368, 104090042368, 104090042368, 268435456, 268435456, 68719476736, 34359738368, 8589934592, 1048576, 268435456, 268435456, 68719476736, 68719476736],94480988160⟩,
.cycle 34 18 false (2),
.last 21 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 31 true (-1),
.cycle 19 20 true (1),
.cycle 14 9 false (2),
.cycle 6 15 true (-1),
.cycle 6 15 true (-1),
.last 19 (5,true),
.cycle 16 3 false (0),
.cycle 16 6 false (0),
.cycle 15 8 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 16, 36, 16, 16, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 32, 128, 256, 8, 1024, 32, 5120, 4096],[1024, 4096, 256, 1024, 1024, 4096, 1024, 1024, 32, 1024, 1024, 4096, 4096],6144⟩,
.last 19 (5,true),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 6, 64],[2, 2, 4, 16, 16, 64, 64],64⟩,
.cycle 15 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[24, 8, 52, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 16, 36, 16, 16, 64, 64],64⟩,
.last 19 (5,true)
])
theorem kid11_part268_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part268) = true := by rfl

def kid11_part269 : Audit := .split 13 (1,true) (byMove [
.cycle 16 3 false (0),
.last 40 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 29 3 false (1),
.cycle 1 14 true (1),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 16 3 false (0),
.cycle 17 3 false (0),
.last 21 (5,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 1 14 true (1),
.cycle 23 3 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true)
])
theorem kid11_part269_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part269) = true := by rfl

def kid11_part270 : Audit := .split 20 (5,true) (byMove [
.cycle 10 22 true (-1),
.cycle 36 5 false (2),
.cycle 42 5 false (2),
.cycle 13 14 true (-1),
.cycle 23 5 false (2),
.last 22 (1,true),
.last 22 (1,true),
.cycle 6 77 true (-1),
.cycle 66 5 false (2),
.cycle 36 5 false (2),
.cycle 42 28 true (-1),
.cycle 23 22 true (1),
.last 22 (1,true),
.cycle 21 5 false (2),
.cycle 21 18 true (1),
.cycle 38 5 false (2),
.cycle 19 2 true (1),
.last 22 (1,true),
.last 22 (1,true),
.cycle 1 34 true (-1),
.cycle 6 62 true (-1),
.cycle 46 14 true (4),
.cycle 21 16 true (1),
.last 22 (1,true)
])
theorem kid11_part270_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part270) = true := by rfl

def kid11_part271 : Audit := .cycle 7 7 true (3)
theorem kid11_part271_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part271) = true := by rfl

def kid11_part272 : Audit := .cycle 6 7 true (2)
theorem kid11_part272_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part272) = true := by rfl

def kid11_part273 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 7 12 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 16 (1,true),
.last 14 (1,true),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 20 (1,true),
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 37 4 false (1),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 17 4 false (-1),
.cycle 12 2 true (3),
.last 14 (1,true),
.cycle 23 4 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 16 (1,true)
])
theorem kid11_part273_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part273) = true := by rfl

def kid11_part274 : Audit := .cycle 0 13 true (0)
theorem kid11_part274_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part274) = true := by rfl

def kid11_part275 : Audit := .cycle 1 12 true (1)
theorem kid11_part275_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part275) = true := by rfl

def kid11_part276 : Audit := .cycle 2 11 true (1)
theorem kid11_part276_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part276) = true := by rfl

def kid11_part277 : Audit := .cycle 7 8 true (3)
theorem kid11_part277_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part277) = true := by rfl

def kid11_part278 : Audit := .cycle 8 5 true (4)
theorem kid11_part278_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part278) = true := by rfl

def kid11_part279 : Audit := .split 14 (1,true) (byMove [
.cycle 21 9 false (2),
.cycle 15 17 false (3),
.cycle 24 1 false (0),
.last 17 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 12 3 true (4),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true),
.last 16 (5,true),
.cycle 18 5 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[32, 20, 20, 16, 16, 64, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.last 15 (5,true),
.cycle 12 3 true (4),
.cycle 1 15 true (1),
.cycle 11 4 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true)
])
theorem kid11_part279_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part279) = true := by rfl

def kid11_part255 : Audit := .split 12 (0,true) (byMove [(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262),(kid11_part263),(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278),(kid11_part279)])

theorem kid11_part255_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part255) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262),(kid11_part263),(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278),(kid11_part279)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part256_checked

  · exact kid11_part262_checked

  · exact kid11_part268_checked

  · exact kid11_part274_checked

  · exact kid11_part257_checked

  · exact kid11_part263_checked

  · exact kid11_part269_checked

  · exact kid11_part275_checked

  · exact kid11_part258_checked

  · exact kid11_part264_checked

  · exact kid11_part270_checked

  · exact kid11_part276_checked

  · exact kid11_part259_checked

  · exact kid11_part265_checked

  · exact kid11_part271_checked

  · exact kid11_part277_checked

  · exact kid11_part260_checked

  · exact kid11_part266_checked

  · exact kid11_part272_checked

  · exact kid11_part278_checked

  · exact kid11_part261_checked

  · exact kid11_part267_checked

  · exact kid11_part273_checked

  · exact kid11_part279_checked

def kid11_part280 : Audit := .split 12 (1,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 17 false (5),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 0 40 false (5),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 0 19 true (0),
.cycle 0 33 false (5),
.cycle 16 3 false (0),
.cycle 0 25 false (5),
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 21 7 false (1)
]),
.cycle 13 15 false (3),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 34 4 false (0),
.cycle 29 4 false (1),
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 17 4 false (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 24 4 false (0)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.split 13 (0,true) (byMove [
.last 26 (5,true),
.last 24 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 12 4 true (3),
.cycle 1 14 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 16 3 false (0),
.cycle 16 6 false (0),
.last 21 (5,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 14 (5,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 21 5 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 14 (5,true)
]),
.cycle 16 3 false (0),
.split 20 (5,true) (byMove [
.cycle 22 9 true (2),
.cycle 17 23 true (-1),
.cycle 17 29 true (-1),
.cycle 13 14 true (-1),
.cycle 41 9 true (1),
.cycle 13 16 true (-1),
.cycle 22 9 true (2),
.cycle 24 9 true (2),
.cycle 21 9 true (3),
.cycle 17 23 true (-1),
.cycle 28 9 true (4),
.cycle 33 9 true (3),
.cycle 14 8 true (-1),
.cycle 39 9 true (1),
.cycle 25 9 true (3),
.cycle 17 25 true (-1),
.cycle 19 2 true (1),
.cycle 17 39 true (-1),
.cycle 17 31 true (-1),
.cycle 21 9 true (1),
.cycle 21 9 true (3),
.cycle 34 14 true (2),
.cycle 23 9 true (3),
.cycle 36 16 true (2)
]),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 18 1 false (0),
.cycle 7 12 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 20 4 false (0),
.cycle 1 14 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 34 4 false (0),
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 22 11 true (2),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 12 2 true (3),
.cycle 23 4 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 13 5 true (3)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (4),
.split 15 (5,true) (byMove [
.last 16 (0,true),
.cycle 12 4 true (4),
.cycle 16 31 false (4),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 19 8 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (4),
.cycle 9 7 true (4),
.last 16 (0,true),
.cycle 14 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[64, 32, 24, 16, 16, 16, 64],64⟩,
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 19 8 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (4),
.cycle 13 3 true (4)
])
])
theorem kid11_part280_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part280) = true := by rfl

def kid11_part281 : Audit := .cycle 18 1 false (0)
theorem kid11_part281_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part281) = true := by rfl

def kid11_part282 : Audit := .cycle 8 5 true (4)
theorem kid11_part282_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part282) = true := by rfl

def kid11_part283 : Audit := .cycle 7 5 true (3)
theorem kid11_part283_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part283) = true := by rfl

def kid11_part284 : Audit := .split 12 (5,true) (byMove [
.split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 0 40 false (5),
.cycle 0 17 false (5),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 0 19 true (0),
.cycle 0 33 false (5),
.last 18 (1,true),
.last 14 (1,true),
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 37 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.last 15 (1,true)
]),
.split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 14 32 false (4),
.cycle 16 19 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 1 18 true (1),
.cycle 14 27 false (4),
.last 14 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.cycle 14 8 true (-1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 1 21 true (-1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 12 4 true (3)
]),
.cycle 18 1 false (0),
.cycle 8 6 true (3),
.cycle 7 6 true (3),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 6 13 true (2),
.cycle 3 10 true (1),
.cycle 8 5 true (4),
.cycle 9 4 true (4),
.split 13 (0,true) (byMove [
.last 28 (1,true),
.last 14 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.last 18 (1,true),
.last 18 (1,true),
.cycle 0 15 true (0),
.last 14 (1,true),
.last 16 (1,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.last 16 (1,true),
.last 18 (1,true),
.last 14 (1,true),
.last 23 (1,true),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.last 18 (1,true),
.cycle 0 15 true (0),
.last 14 (1,true),
.last 26 (1,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
]),
.split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 26 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 37 3 false (0),
.cycle 16 3 false (0),
.last 14 (0,true),
.cycle 1 14 true (1),
.cycle 25 3 false (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 29 3 false (1),
.last 14 (0,true),
.cycle 17 3 false (0),
.cycle 28 3 false (-1),
.cycle 5 9 true (1),
.cycle 6 9 true (2),
.cycle 16 3 false (0),
.last 14 (0,true),
.cycle 1 14 true (1),
.cycle 23 3 false (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 12 2 true (3)
]),
.split 34 (1,true) (byMove [
.cycle 56 12 false (1),
.cycle 21 15 true (1),
.cycle 54 12 false (2),
.cycle 19 19 true (0),
.cycle 35 12 false (2),
.cycle 37 12 false (0),
.last 35 (0,true),
.cycle 62 12 false (4),
.cycle 36 12 false (2),
.cycle 22 13 true (2),
.cycle 23 13 true (2),
.cycle 20 15 true (1),
.last 37 (0,true),
.cycle 35 12 false (2),
.cycle 76 12 false (0),
.cycle 38 15 true (2),
.cycle 39 15 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 16, 48, 16, 16, 16, 64],64⟩,
.last 35 (0,true),
.cycle 20 20 true (1),
.cycle 47 12 false (2),
.cycle 22 13 true (2),
.cycle 23 13 true (2),
.cycle 39 12 false (1)
]),
.cycle 7 7 true (3),
.cycle 6 7 true (2),
.cycle 16 4 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 7 8 true (3),
.cycle 8 5 true (4),
.split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 15 17 false (3),
.cycle 24 1 false (0),
.cycle 16 7 true (3),
.cycle 12 18 true (3),
.cycle 24 6 false (1),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 25 7 false (1),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 12 3 true (4),
.last 15 (0,true),
.cycle 18 5 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 48, 16, 16, 32, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 12 5 true (3),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 11 4 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 12 3 true (4)
])
])
theorem kid11_part284_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part284) = true := by rfl

def kid11_part285 : Audit := .cycle 0 12 true (0)
theorem kid11_part285_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part285) = true := by rfl

def kid11_part286 : Audit := .cycle 1 11 true (1)
theorem kid11_part286_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part286) = true := by rfl

def kid11_part287 : Audit := .cycle 6 12 true (2)
theorem kid11_part287_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part287) = true := by rfl

def kid11_part288 : Audit := .cycle 3 9 true (1)
theorem kid11_part288_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part288) = true := by rfl

def kid11_part289 : Audit := .cycle 8 4 true (4)
theorem kid11_part289_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part289) = true := by rfl

def kid11_part290 : Audit := .cycle 9 3 true (4)
theorem kid11_part290_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part290) = true := by rfl

def kid11_part292 : Audit := .cycle 0 17 false (5)
theorem kid11_part292_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part292) = true := by rfl

def kid11_part293 : Audit := .split 13 (1,true) (byMove [
.last 41 (5,true),
.cycle 14 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.last 44 (5,true),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 8 12 true (3),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 15 (5,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[8, 32, 32, 1024, 1024, 4096, 1024, 32, 1024, 1024, 1024, 4096, 4096],6144⟩,
.last 21 (5,true),
.last 27 (5,true),
.last 20 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid11_part293_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part293) = true := by rfl

def kid11_part294 : Audit := .cycle 18 1 false (0)
theorem kid11_part294_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part294) = true := by rfl

def kid11_part295 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 14 12 true (3),
.cycle 14 9 true (3),
.last 17 (1,true),
.cycle 10 6 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (1,true)
])
theorem kid11_part295_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part295) = true := by rfl

def kid11_part296 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 28 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 32, 128, 256, 8, 1024, 32, 4096, 4096],[32, 4096, 4096, 1024, 1024, 32, 32, 4096, 32, 1024, 1024, 32, 4096],6144⟩,
.last 17 (1,true),
.cycle 10 6 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.last 17 (1,true)
])
theorem kid11_part296_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part296) = true := by rfl

def kid11_part297 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.last 15 (1,true),
.last 18 (1,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 26 (1,true),
.cycle 29 4 false (1),
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 24 12 true (4),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 17 4 false (-1),
.last 15 (1,true),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 8 8 true (3),
.last 15 (1,true)
])
theorem kid11_part297_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part297) = true := by rfl

def kid11_part298 : Audit := .cycle 0 14 true (0)
theorem kid11_part298_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part298) = true := by rfl

def kid11_part299 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 12 4 true (4),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.last 15 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true)
])
theorem kid11_part299_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part299) = true := by rfl

def kid11_part300 : Audit := .split 15 (1,true) (byMove [
.cycle 6 17 true (2),
.cycle 16 19 false (4),
.cycle 33 3 false (1),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 8 8 true (4),
.cycle 9 7 true (4),
.cycle 12 4 true (4),
.cycle 19 7 false (1),
.cycle 33 3 false (1),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (4),
.last 18 (5,true)
])
theorem kid11_part300_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part300) = true := by rfl

def kid11_part301 : Audit := .cycle 8 6 true (4)
theorem kid11_part301_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part301) = true := by rfl

def kid11_part302 : Audit := .cycle 7 6 true (3)
theorem kid11_part302_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part302) = true := by rfl

def kid11_part303 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 15 (1,true),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 13 2 true (4),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true)
])
theorem kid11_part303_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part303) = true := by rfl

def kid11_part304 : Audit := .split 18 (1,true) (byMove [
.cycle 16 3 false (0),
.far false 5 ⟨0,[0, 1, 2, 3, 4, 4, 0, 1, 4, 4],[128, 256, 8, 4195328, 32, 4194304, 524288, 1048576, 32768, 4194304, 131072, 1342177280, 33554432, 67108864, 134217728, 1024, 536870912, 1024, 128, 256, 8, 1024, 32, 4194304, 33554432, 67108864, 134217728, 272630784, 536870912, 2017592352, 1073741824],[1024, 32768, 1024, 1024, 1024, 1073741824, 4194304, 1024, 4194304, 4194304, 4194304, 1073741824, 131072, 8, 131072, 268435456, 268435456, 1073741824, 1024, 131072, 1024, 1024, 1024, 1073741824, 2017592352, 2017592352, 2017592352, 268435456, 268435456, 1073741824, 1073741824],2130802688⟩,
.cycle 17 3 false (0),
.last 21 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 34 true (-1),
.cycle 19 21 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[4, 4, 4, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[24, 8, 24, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 19 (5,true),
.cycle 16 3 false (0),
.cycle 16 6 false (0),
.cycle 17 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 5120, 4096],[1024, 4096, 1024, 1024, 1024, 4096, 1024, 1024, 1024, 1024, 1024, 4096, 4096],6144⟩,
.last 19 (5,true),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 2, 64],[2, 2, 2, 16, 16, 64, 64],64⟩,
.cycle 15 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[24, 8, 24, 16, 16, 64, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.last 19 (5,true)
])
theorem kid11_part304_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part304) = true := by rfl

def kid11_part305 : Audit := .split 13 (1,true) (byMove [
.cycle 16 3 false (0),
.last 40 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 29 3 false (1),
.cycle 1 15 true (1),
.cycle 6 20 true (2),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 16 3 false (0),
.cycle 17 3 false (0),
.cycle 33 3 false (1),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 1 15 true (1),
.cycle 23 3 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true)
])
theorem kid11_part305_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part305) = true := by rfl

def kid11_part306 : Audit := .far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16842752, 8192, 16384, 8, 65536, 32, 16777216, 128, 256, 2097152, 1024, 8388608, 16777216, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 16777216, 1024, 1024, 16777216, 16777216, 16777216, 65536, 65536, 65536, 16777216, 1024, 16777216, 16777216, 1024, 1024, 16777216, 1024, 16777216, 16777216, 1024, 1024, 16777216, 16777216],22719870⟩
theorem kid11_part306_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part306) = true := by rfl

def kid11_part307 : Audit := .cycle 5 8 true (1)
theorem kid11_part307_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part307) = true := by rfl

def kid11_part308 : Audit := .cycle 6 8 true (2)
theorem kid11_part308_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part308) = true := by rfl

def kid11_part309 : Audit := .split 13 (5,true) (byMove [
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 7 17 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 73 4 false (9),
.cycle 16 4 false (0),
.last 14 (1,true),
.cycle 33 4 false (1),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 17 4 false (-1),
.cycle 12 2 true (3),
.last 14 (1,true),
.cycle 23 4 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 17 (1,true)
])
theorem kid11_part309_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part309) = true := by rfl

def kid11_part310 : Audit := .cycle 0 14 true (0)
theorem kid11_part310_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part310) = true := by rfl

def kid11_part311 : Audit := .split 13 (1,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 17 false (4),
.cycle 25 3 false (1),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 12 2 true (4),
.cycle 17 5 false (1),
.cycle 25 3 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 16 (5,true)
])
theorem kid11_part311_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part311) = true := by rfl

def kid11_part312 : Audit := .cycle 11 2 true (4)
theorem kid11_part312_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part312) = true := by rfl

def kid11_part313 : Audit := .cycle 8 6 true (4)
theorem kid11_part313_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part313) = true := by rfl

def kid11_part314 : Audit := .cycle 7 6 true (3)
theorem kid11_part314_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part314) = true := by rfl

def kid11_part315 : Audit := .split 13 (5,true) (byMove [
.last 16 (1,true),
.last 14 (1,true),
.last 28 (1,true),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 12 2 true (4),
.last 14 (1,true),
.last 28 (1,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true)
])
theorem kid11_part315_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part315) = true := by rfl

def kid11_part291 : Audit := .split 12 (0,true) (byMove [(kid11_part292),(kid11_part293),(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part315)])

theorem kid11_part291_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part291) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part292),(kid11_part293),(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part315)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part292_checked

  · exact kid11_part298_checked

  · exact kid11_part304_checked

  · exact kid11_part310_checked

  · exact kid11_part293_checked

  · exact kid11_part299_checked

  · exact kid11_part305_checked

  · exact kid11_part311_checked

  · exact kid11_part294_checked

  · exact kid11_part300_checked

  · exact kid11_part306_checked

  · exact kid11_part312_checked

  · exact kid11_part295_checked

  · exact kid11_part301_checked

  · exact kid11_part307_checked

  · exact kid11_part313_checked

  · exact kid11_part296_checked

  · exact kid11_part302_checked

  · exact kid11_part308_checked

  · exact kid11_part314_checked

  · exact kid11_part297_checked

  · exact kid11_part303_checked

  · exact kid11_part309_checked

  · exact kid11_part315_checked

def kid11_part317 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 17 false (5),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 31 10 false (2),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 10 8 true (3),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.last 15 (5,true),
.cycle 25 9 false (2),
.cycle 16 3 false (0),
.cycle 16 8 false (1),
.last 20 (5,true),
.last 17 (5,true),
.last 17 (5,true),
.last 14 (5,true),
.cycle 0 17 true (0),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 21 7 false (1)
])
theorem kid11_part317_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part317) = true := by rfl

def kid11_part318 : Audit := .cycle 13 15 false (3)
theorem kid11_part318_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part318) = true := by rfl

def kid11_part319 : Audit := .cycle 18 1 false (0)
theorem kid11_part319_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part319) = true := by rfl

def kid11_part320 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 33 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 14 12 true (3),
.cycle 14 9 true (3),
.cycle 8 11 true (3),
.cycle 10 6 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.cycle 33 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 14 7 true (3)
])
theorem kid11_part320_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part320) = true := by rfl

def kid11_part321 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 32 5 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 28 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 7 11 true (3),
.cycle 10 6 true (3),
.cycle 8 10 true (3),
.cycle 4 12 true (1),
.cycle 14 2 true (4),
.cycle 32 5 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 12 16 true (3)
])
theorem kid11_part321_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part321) = true := by rfl

def kid11_part322 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 24 4 false (0),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 52 4 false (0),
.cycle 29 4 false (1),
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 24 12 true (4),
.cycle 4 14 true (1),
.cycle 16 2 true (4),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 8 8 true (3),
.cycle 24 4 false (0)
])
theorem kid11_part322_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part322) = true := by rfl

def kid11_part323 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 0 16 true (0),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.last 15 (5,true),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part323_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part323) = true := by rfl

def kid11_part324 : Audit := .cycle 1 13 true (1)
theorem kid11_part324_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part324) = true := by rfl

def kid11_part325 : Audit := .cycle 10 4 true (4)
theorem kid11_part325_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part325) = true := by rfl

def kid11_part326 : Audit := .cycle 8 6 true (4)
theorem kid11_part326_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part326) = true := by rfl

def kid11_part327 : Audit := .cycle 7 6 true (3)
theorem kid11_part327_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part327) = true := by rfl

def kid11_part328 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 9 7 true (4),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 13 2 true (4),
.cycle 24 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part328_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part328) = true := by rfl

def kid11_part329 : Audit := .split 13 (0,true) (byMove [
.last 26 (5,true),
.last 24 (5,true),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 12 4 true (3),
.cycle 27 7 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 16 3 false (0),
.cycle 16 6 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 16, 16, 16, 64, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 14 (5,true),
.cycle 0 16 true (0),
.cycle 12 2 true (3),
.cycle 21 5 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true)
])
theorem kid11_part329_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part329) = true := by rfl

def kid11_part330 : Audit := .cycle 16 3 false (0)
theorem kid11_part330_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part330) = true := by rfl

def kid11_part331 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 64, 64],64⟩
theorem kid11_part331_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part331) = true := by rfl

def kid11_part332 : Audit := .cycle 5 8 true (1)
theorem kid11_part332_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part332) = true := by rfl

def kid11_part333 : Audit := .cycle 6 8 true (2)
theorem kid11_part333_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part333) = true := by rfl

def kid11_part334 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 18 1 false (0),
.cycle 7 17 true (2),
.cycle 42 4 false (0),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 20 4 false (0),
.cycle 30 4 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 73 4 false (9),
.last 14 (0,true),
.cycle 16 4 false (0),
.cycle 33 4 false (1),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 17 4 false (-1),
.last 14 (0,true),
.cycle 12 2 true (3),
.cycle 23 4 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 5 true (3)
])
theorem kid11_part334_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part334) = true := by rfl

def kid11_part335 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 0 15 true (0),
.cycle 23 5 false (1),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.cycle 16 5 false (2),
.cycle 12 2 true (4),
.cycle 23 5 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part335_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part335) = true := by rfl

def kid11_part336 : Audit := .cycle 1 13 true (1)
theorem kid11_part336_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part336) = true := by rfl

def kid11_part337 : Audit := .cycle 11 2 true (4)
theorem kid11_part337_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part337) = true := by rfl

def kid11_part338 : Audit := .cycle 8 6 true (4)
theorem kid11_part338_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part338) = true := by rfl

def kid11_part339 : Audit := .cycle 7 6 true (3)
theorem kid11_part339_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part339) = true := by rfl

def kid11_part340 : Audit := .split 13 (5,true) (byMove [
.last 14 (0,true),
.cycle 12 4 true (4),
.cycle 23 5 false (1),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 14 (0,true),
.cycle 12 2 true (4),
.cycle 23 5 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 17 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part340_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part340) = true := by rfl

def kid11_part316 : Audit := .split 12 (1,true) (byMove [(kid11_part317),(kid11_part318),(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part336),(kid11_part337),(kid11_part338),(kid11_part339),(kid11_part340)])

theorem kid11_part316_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part316) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid11_part317),(kid11_part318),(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part336),(kid11_part337),(kid11_part338),(kid11_part339),(kid11_part340)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part317_checked

  · exact kid11_part323_checked

  · exact kid11_part329_checked

  · exact kid11_part335_checked

  · exact kid11_part318_checked

  · exact kid11_part324_checked

  · exact kid11_part330_checked

  · exact kid11_part336_checked

  · exact kid11_part319_checked

  · exact kid11_part325_checked

  · exact kid11_part331_checked

  · exact kid11_part337_checked

  · exact kid11_part320_checked

  · exact kid11_part326_checked

  · exact kid11_part332_checked

  · exact kid11_part338_checked

  · exact kid11_part321_checked

  · exact kid11_part327_checked

  · exact kid11_part333_checked

  · exact kid11_part339_checked

  · exact kid11_part322_checked

  · exact kid11_part328_checked

  · exact kid11_part334_checked

  · exact kid11_part340_checked

def kid11_part341 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 4096, 4096],[4096, 4096, 1024, 1024, 1024, 4096, 4096, 4096, 1024, 1024, 1024, 4096, 4096],6144⟩
theorem kid11_part341_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part341) = true := by rfl

def kid11_part342 : Audit := .cycle 7 6 true (3)
theorem kid11_part342_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part342) = true := by rfl

def kid11_part343 : Audit := .cycle 6 6 true (2)
theorem kid11_part343_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part343) = true := by rfl

def kid11_part345 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 31 10 false (2),
.cycle 0 17 false (5),
.last 15 (1,true),
.cycle 10 8 true (3),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 25 9 false (2),
.last 18 (1,true),
.last 14 (1,true),
.cycle 14 19 false (3),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 16 9 false (1),
.last 15 (1,true),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.last 15 (1,true)
])
theorem kid11_part345_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part345) = true := by rfl

def kid11_part346 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.cycle 1 233 false (7),
.cycle 0 16 true (0),
.cycle 8 12 true (3),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[64, 32, 16, 16, 16, 24, 64],64⟩,
.last 14 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.cycle 1 25 true (-1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.cycle 0 16 true (0),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 12 4 true (3)
])
theorem kid11_part346_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part346) = true := by rfl

def kid11_part347 : Audit := .cycle 18 1 false (0)
theorem kid11_part347_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part347) = true := by rfl

def kid11_part348 : Audit := .cycle 7 11 true (3)
theorem kid11_part348_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part348) = true := by rfl

def kid11_part349 : Audit := .cycle 8 8 true (3)
theorem kid11_part349_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part349) = true := by rfl

def kid11_part350 : Audit := .cycle 16 4 false (0)
theorem kid11_part350_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part350) = true := by rfl

def kid11_part351 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 15 (1,true),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true)
])
theorem kid11_part351_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part351) = true := by rfl

def kid11_part352 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 29 5 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 16 (0,true),
.cycle 10 4 true (4),
.cycle 8 8 true (4),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 20 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 1 16 true (1)
])
theorem kid11_part352_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part352) = true := by rfl

def kid11_part353 : Audit := .split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 27 19 false (3),
.cycle 22 1 false (0),
.cycle 49 1 false (-1),
.cycle 50 5 false (0),
.cycle 7 12 true (2),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 25 5 false (1),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 43 5 false (2),
.last 16 (0,true),
.cycle 19 5 false (0),
.cycle 41 5 false (1),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 20 5 false (1),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 31 5 false (1),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 12 4 true (3)
])
theorem kid11_part353_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part353) = true := by rfl

def kid11_part354 : Audit := .cycle 8 6 true (4)
theorem kid11_part354_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part354) = true := by rfl

def kid11_part355 : Audit := .cycle 7 6 true (3)
theorem kid11_part355_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part355) = true := by rfl

def kid11_part356 : Audit := .cycle 9 5 true (4)
theorem kid11_part356_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part356) = true := by rfl

def kid11_part357 : Audit := .split 13 (0,true) (byMove [
.last 28 (1,true),
.last 14 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.last 18 (1,true),
.last 18 (1,true),
.cycle 0 16 true (0),
.last 14 (1,true),
.last 16 (1,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.last 16 (1,true),
.last 18 (1,true),
.last 14 (1,true),
.last 36 (1,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 18 (1,true),
.cycle 0 16 true (0),
.last 14 (1,true),
.last 26 (1,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part357_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part357) = true := by rfl

def kid11_part358 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 26 15 false (3),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 37 3 false (0),
.cycle 16 3 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 25 3 false (0),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 29 3 false (1),
.last 14 (0,true),
.cycle 17 3 false (0),
.cycle 33 3 false (1),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 16 3 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 23 3 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (3)
])
theorem kid11_part358_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part358) = true := by rfl

def kid11_part359 : Audit := .far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16777216, 128, 256, 2097152, 1024, 8388608, 16777216, 128, 256, 8, 65536, 32, 65536, 16777216],[16777216, 16777216, 16843776, 1024, 1024, 1024, 16777216, 16777216, 65536, 65536, 65536, 16843776, 16777216, 16777216, 16843776, 1024, 1024, 1024, 16777216, 16777216, 16777216, 1024, 1024, 1024, 16777216],22719870⟩
theorem kid11_part359_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part359) = true := by rfl

def kid11_part360 : Audit := .cycle 5 8 true (1)
theorem kid11_part360_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part360) = true := by rfl

def kid11_part361 : Audit := .cycle 6 8 true (2)
theorem kid11_part361_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part361) = true := by rfl

def kid11_part362 : Audit := .cycle 16 4 false (0)
theorem kid11_part362_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part362) = true := by rfl

def kid11_part363 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.last 14 (1,true),
.cycle 23 6 false (1),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 20 (1,true),
.last 14 (1,true),
.cycle 23 6 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.last 15 (1,true)
])
theorem kid11_part363_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part363) = true := by rfl

def kid11_part364 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 17 false (4),
.cycle 23 6 false (1),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.last 14 (0,true),
.cycle 17 5 false (1),
.cycle 23 6 false (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 1 16 true (1)
])
theorem kid11_part364_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part364) = true := by rfl

def kid11_part365 : Audit := .cycle 11 2 true (4)
theorem kid11_part365_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part365) = true := by rfl

def kid11_part366 : Audit := .cycle 8 6 true (4)
theorem kid11_part366_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part366) = true := by rfl

def kid11_part367 : Audit := .cycle 7 6 true (3)
theorem kid11_part367_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part367) = true := by rfl

def kid11_part368 : Audit := .split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 16 19 false (4),
.cycle 27 14 false (3),
.cycle 17 7 true (4),
.cycle 12 14 true (4),
.cycle 25 10 false (2),
.last 16 (0,true),
.cycle 1 16 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 4, 32, 16, 16, 32, 64],64⟩,
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 13 3 true (5),
.last 16 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 12 7 true (3),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 12 5 true (4),
.last 16 (0,true),
.cycle 1 16 true (1),
.cycle 11 5 true (4),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 13 3 true (5)
])
theorem kid11_part368_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part368) = true := by rfl

def kid11_part344 : Audit := .split 12 (5,true) (byMove [(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366),(kid11_part367),(kid11_part368)])

theorem kid11_part344_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part344) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366),(kid11_part367),(kid11_part368)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part345_checked

  · exact kid11_part351_checked

  · exact kid11_part357_checked

  · exact kid11_part363_checked

  · exact kid11_part346_checked

  · exact kid11_part352_checked

  · exact kid11_part358_checked

  · exact kid11_part364_checked

  · exact kid11_part347_checked

  · exact kid11_part353_checked

  · exact kid11_part359_checked

  · exact kid11_part365_checked

  · exact kid11_part348_checked

  · exact kid11_part354_checked

  · exact kid11_part360_checked

  · exact kid11_part366_checked

  · exact kid11_part349_checked

  · exact kid11_part355_checked

  · exact kid11_part361_checked

  · exact kid11_part367_checked

  · exact kid11_part350_checked

  · exact kid11_part356_checked

  · exact kid11_part362_checked

  · exact kid11_part368_checked

def kid11_part369 : Audit := .cycle 0 12 true (0)
theorem kid11_part369_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part369) = true := by rfl

def kid11_part370 : Audit := .cycle 1 11 true (1)
theorem kid11_part370_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part370) = true := by rfl

def kid11_part371 : Audit := .cycle 2 10 true (1)
theorem kid11_part371_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part371) = true := by rfl

def kid11_part372 : Audit := .cycle 7 7 true (3)
theorem kid11_part372_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part372) = true := by rfl

def kid11_part373 : Audit := .cycle 8 4 true (4)
theorem kid11_part373_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part373) = true := by rfl

def kid11_part375 : Audit := .split 14 (0,true) (byMove [
.cycle 0 19 false (6),
.last 48 (5,true),
.cycle 24 1 false (0),
.last 20 (5,true),
.last 20 (5,true),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 6 13 true (2),
.last 16 (5,true),
.last 18 (5,true),
.cycle 18 3 false (0),
.cycle 17 5 false (1),
.last 16 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.last 16 (5,true),
.last 32 (5,true)
])
theorem kid11_part375_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part375) = true := by rfl

def kid11_part376 : Audit := .cycle 14 17 false (4)
theorem kid11_part376_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part376) = true := by rfl

def kid11_part377 : Audit := .cycle 30 1 false (0)
theorem kid11_part377_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part377) = true := by rfl

def kid11_part378 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 39 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 19 true (2),
.cycle 6 16 true (2),
.cycle 8 9 true (4),
.cycle 9 8 true (4),
.cycle 8 12 true (4),
.cycle 10 7 true (4),
.cycle 8 11 true (4),
.cycle 4 13 true (1),
.cycle 15 2 true (5),
.cycle 39 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 15 7 true (4)
])
theorem kid11_part378_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part378) = true := by rfl

def kid11_part379 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 32 17 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 19 true (2),
.cycle 6 16 true (2),
.cycle 8 9 true (4),
.cycle 9 8 true (4),
.cycle 7 12 true (3),
.cycle 10 7 true (4),
.cycle 8 11 true (4),
.cycle 4 13 true (1),
.cycle 15 2 true (5),
.cycle 40 6 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (4),
.cycle 12 12 true (4)
])
theorem kid11_part379_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part379) = true := by rfl

def kid11_part380 : Audit := .split 14 (5,true) (byMove [
.last 15 (0,true),
.cycle 6 42 false (6),
.cycle 24 1 false (0),
.cycle 8 14 true (3),
.cycle 7 14 true (3),
.cycle 18 6 false (0),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 6 13 true (2),
.cycle 8 9 true (4),
.cycle 9 10 true (4),
.last 15 (0,true),
.cycle 17 5 false (1),
.cycle 14 2 true (3),
.cycle 4 15 true (1),
.cycle 17 2 true (5),
.cycle 16 6 false (2),
.cycle 0 18 true (0),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.cycle 8 9 true (4),
.cycle 24 8 false (2)
])
theorem kid11_part380_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part380) = true := by rfl

def kid11_part381 : Audit := .split 14 (0,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 24 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 0 17 true (0),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.last 16 (5,true),
.last 33 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part381_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part381) = true := by rfl

def kid11_part382 : Audit := .cycle 1 14 true (1)
theorem kid11_part382_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part382) = true := by rfl

def kid11_part383 : Audit := .cycle 11 3 true (5)
theorem kid11_part383_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part383) = true := by rfl

def kid11_part384 : Audit := .cycle 8 7 true (4)
theorem kid11_part384_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part384) = true := by rfl

def kid11_part385 : Audit := .cycle 7 7 true (3)
theorem kid11_part385_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part385) = true := by rfl

def kid11_part386 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 24 9 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 17 true (2),
.cycle 6 14 true (2),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 9 8 true (4),
.cycle 10 5 true (4),
.cycle 8 9 true (4),
.cycle 4 11 true (1),
.cycle 14 2 true (5),
.cycle 29 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part386_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part386) = true := by rfl

def kid11_part387 : Audit := .split 14 (0,true) (byMove [
.last 31 (5,true),
.last 23 (5,true),
.cycle 24 1 false (0),
.last 17 (5,true),
.last 17 (5,true),
.last 15 (5,true),
.cycle 0 17 true (0),
.cycle 13 4 true (4),
.last 16 (5,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true),
.cycle 18 3 false (0),
.last 21 (5,true),
.last 16 (5,true),
.cycle 6 11 true (2),
.cycle 6 11 true (2),
.last 15 (5,true),
.cycle 0 17 true (0),
.cycle 13 2 true (4),
.last 16 (5,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true)
])
theorem kid11_part387_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part387) = true := by rfl

def kid11_part388 : Audit := .split 21 (5,true) (byMove [
.last 22 (0,true),
.cycle 17 5 false (1),
.cycle 17 7 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 17 11 false (1),
.last 22 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 34, 64],[64, 34, 32, 16, 16, 2, 64],64⟩,
.cycle 20 36 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 32, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 25 10 true (5),
.last 22 (0,true),
.cycle 17 5 false (1),
.cycle 20 2 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.cycle 19 6 false (1),
.last 22 (0,true),
.cycle 15 7 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[64, 36, 32, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 32, 16, 16, 8, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩
])
theorem kid11_part388_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part388) = true := by rfl

def kid11_part389 : Audit := .split 15 (5,true) (byMove [
.last 16 (0,true),
.cycle 20 28 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 7 14 true (3),
.cycle 8 11 true (4),
.cycle 19 8 false (1),
.last 16 (0,true),
.cycle 8 11 true (4),
.cycle 7 14 true (3),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 9 8 true (4),
.last 16 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 48, 64],64⟩,
.cycle 14 2 true (4),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 18 6 false (2),
.last 16 (0,true),
.cycle 1 18 true (1),
.cycle 11 5 true (4),
.cycle 8 9 true (4),
.cycle 7 9 true (3),
.cycle 12 5 true (4)
])
theorem kid11_part389_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part389) = true := by rfl

def kid11_part390 : Audit := .cycle 5 9 true (1)
theorem kid11_part390_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part390) = true := by rfl

def kid11_part391 : Audit := .cycle 6 9 true (2)
theorem kid11_part391_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part391) = true := by rfl

def kid11_part392 : Audit := .split 14 (5,true) (byMove [
.last 15 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 32, 16, 16, 56, 64],64⟩,
.cycle 24 1 false (0),
.cycle 7 18 true (3),
.cycle 7 16 true (3),
.cycle 18 6 false (0),
.last 15 (0,true),
.cycle 18 9 false (3),
.cycle 6 17 true (2),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 9 8 true (4),
.last 15 (0,true),
.cycle 16 5 false (2),
.cycle 14 2 true (3),
.cycle 6 11 true (2),
.cycle 6 11 true (2),
.cycle 16 6 false (2),
.last 15 (0,true),
.cycle 13 2 true (4),
.cycle 2 15 true (1),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 12 5 true (4)
])
theorem kid11_part392_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part392) = true := by rfl

def kid11_part393 : Audit := .split 14 (0,true) (byMove [
.cycle 0 21 false (6),
.cycle 0 16 true (0),
.cycle 11 4 true (5),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 18 5 false (2),
.cycle 13 2 true (5),
.last 16 (5,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part393_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part393) = true := by rfl

def kid11_part394 : Audit := .cycle 1 14 true (1)
theorem kid11_part394_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part394) = true := by rfl

def kid11_part395 : Audit := .cycle 11 3 true (5)
theorem kid11_part395_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part395) = true := by rfl

def kid11_part396 : Audit := .cycle 8 7 true (4)
theorem kid11_part396_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part396) = true := by rfl

def kid11_part397 : Audit := .cycle 7 7 true (3)
theorem kid11_part397_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part397) = true := by rfl

def kid11_part398 : Audit := .split 14 (5,true) (byMove [
.last 15 (0,true),
.cycle 12 4 true (5),
.cycle 11 4 true (5),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 18 8 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.last 15 (0,true),
.cycle 13 2 true (5),
.cycle 14 2 true (5),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 18 6 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 12 3 true (5)
])
theorem kid11_part398_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part398) = true := by rfl

def kid11_part374 : Audit := .split 13 (1,true) (byMove [(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398)])

theorem kid11_part374_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part374) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) 13 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some mv)) (byMove [(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part375_checked

  · exact kid11_part381_checked

  · exact kid11_part387_checked

  · exact kid11_part393_checked

  · exact kid11_part376_checked

  · exact kid11_part382_checked

  · exact kid11_part388_checked

  · exact kid11_part394_checked

  · exact kid11_part377_checked

  · exact kid11_part383_checked

  · exact kid11_part389_checked

  · exact kid11_part395_checked

  · exact kid11_part378_checked

  · exact kid11_part384_checked

  · exact kid11_part390_checked

  · exact kid11_part396_checked

  · exact kid11_part379_checked

  · exact kid11_part385_checked

  · exact kid11_part391_checked

  · exact kid11_part397_checked

  · exact kid11_part380_checked

  · exact kid11_part386_checked

  · exact kid11_part392_checked

  · exact kid11_part398_checked

def kid11_part254 : Audit := .split 11 (2,true) (byMove [(kid11_part255),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part285),(kid11_part286),(kid11_part287),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part316),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part369),(kid11_part370),(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374)])

theorem kid11_part254_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (kid11_part254) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part255),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part285),(kid11_part286),(kid11_part287),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part316),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part369),(kid11_part370),(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part255_checked

  · exact kid11_part285_checked

  · exact kid11_part291_checked

  · exact kid11_part369_checked

  · exact kid11_part280_checked

  · exact kid11_part286_checked

  · exact kid11_part316_checked

  · exact kid11_part370_checked

  · exact kid11_part281_checked

  · exact kid11_part287_checked

  · exact kid11_part341_checked

  · exact kid11_part371_checked

  · exact kid11_part282_checked

  · exact kid11_part288_checked

  · exact kid11_part342_checked

  · exact kid11_part372_checked

  · exact kid11_part283_checked

  · exact kid11_part289_checked

  · exact kid11_part343_checked

  · exact kid11_part373_checked

  · exact kid11_part284_checked

  · exact kid11_part290_checked

  · exact kid11_part344_checked

  · exact kid11_part374_checked

def kid11_part399 : Audit := .cycle 8 4 true (4)
theorem kid11_part399_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (kid11_part399) = true := by rfl

def kid11_part400 : Audit := .cycle 4 6 true (1)
theorem kid11_part400_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (kid11_part400) = true := by rfl

def kid11_part402 : Audit := .cycle 0 12 true (0)
theorem kid11_part402_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part402) = true := by rfl

def kid11_part403 : Audit := .cycle 1 11 true (1)
theorem kid11_part403_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part403) = true := by rfl

def kid11_part404 : Audit := .cycle 2 10 true (1)
theorem kid11_part404_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part404) = true := by rfl

def kid11_part405 : Audit := .cycle 7 7 true (3)
theorem kid11_part405_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part405) = true := by rfl

def kid11_part406 : Audit := .cycle 8 4 true (4)
theorem kid11_part406_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part406) = true := by rfl

def kid11_part407 : Audit := .cycle 6 7 true (2)
theorem kid11_part407_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part407) = true := by rfl

def kid11_part408 : Audit := .cycle 0 12 true (0)
theorem kid11_part408_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part408) = true := by rfl

def kid11_part409 : Audit := .cycle 1 11 true (1)
theorem kid11_part409_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part409) = true := by rfl

def kid11_part410 : Audit := .cycle 6 14 true (2)
theorem kid11_part410_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part410) = true := by rfl

def kid11_part411 : Audit := .cycle 6 11 true (2)
theorem kid11_part411_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part411) = true := by rfl

def kid11_part412 : Audit := .cycle 8 4 true (4)
theorem kid11_part412_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part412) = true := by rfl

def kid11_part413 : Audit := .cycle 9 3 true (4)
theorem kid11_part413_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part413) = true := by rfl

def kid11_part415 : Audit := .split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 0 36 false (5),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 18 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.cycle 18 3 false (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 18 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 6 10 true (2)
])
theorem kid11_part415_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part415) = true := by rfl

def kid11_part416 : Audit := .cycle 14 17 false (4)
theorem kid11_part416_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part416) = true := by rfl

def kid11_part417 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 37 1 false (-1),
.cycle 20 1 false (0),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 16 (0,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.last 15 (0,true),
.cycle 23 1 false (-1),
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 4, 16, 64],[64, 4, 4, 4, 4, 1, 64],64⟩,
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 16 (0,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 6 10 true (2)
])
theorem kid11_part417_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part417) = true := by rfl

def kid11_part418 : Audit := .cycle 8 7 true (4)
theorem kid11_part418_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part418) = true := by rfl

def kid11_part419 : Audit := .cycle 7 7 true (3)
theorem kid11_part419_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part419) = true := by rfl

def kid11_part420 : Audit := .split 15 (0,true) (byMove [
.cycle 10 17 false (5),
.cycle 33 11 true (1),
.last 16 (2,true),
.cycle 37 1 false (-1),
.cycle 40 3 false (0),
.cycle 18 3 false (0),
.cycle 0 17 true (0),
.cycle 6 12 true (2),
.last 16 (2,true),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 31 3 false (1),
.cycle 19 3 false (0),
.last 20 (2,true),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 18 3 false (0),
.cycle 0 17 true (0),
.cycle 25 3 false (1),
.last 16 (2,true),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 14 2 true (3)
])
theorem kid11_part420_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part420) = true := by rfl

def kid11_part421 : Audit := .cycle 0 14 true (0)
theorem kid11_part421_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part421) = true := by rfl

def kid11_part422 : Audit := .cycle 1 13 true (1)
theorem kid11_part422_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part422) = true := by rfl

def kid11_part423 : Audit := .cycle 6 14 true (2)
theorem kid11_part423_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part423) = true := by rfl

def kid11_part424 : Audit := .cycle 3 11 true (1)
theorem kid11_part424_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part424) = true := by rfl

def kid11_part425 : Audit := .cycle 8 6 true (4)
theorem kid11_part425_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part425) = true := by rfl

def kid11_part426 : Audit := .cycle 9 5 true (4)
theorem kid11_part426_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part426) = true := by rfl

def kid11_part427 : Audit := .split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 17 16 false (3),
.last 15 (2,true),
.cycle 10 6 true (3),
.cycle 10 6 true (3),
.cycle 18 6 false (0),
.cycle 0 16 true (0),
.cycle 12 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 11 4 true (4),
.cycle 18 3 false (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 18 6 false (0),
.cycle 0 16 true (0),
.cycle 13 2 true (4),
.last 15 (2,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 14 2 true (4)
])
theorem kid11_part427_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part427) = true := by rfl

def kid11_part428 : Audit := .split 20 (2,true) (byMove [
.last 21 (0,true),
.cycle 18 3 false (0),
.cycle 23 1 false (-1),
.cycle 16 9 false (2),
.cycle 16 9 false (2),
.cycle 17 6 false (1),
.last 21 (0,true),
.cycle 21 31 true (0),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 10, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.cycle 16 7 false (2),
.last 21 (0,true),
.cycle 18 3 false (0),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 6, 16, 64],[64, 2, 4, 6, 6, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 8, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 16, 2, 2, 1, 64],64⟩,
.cycle 17 6 false (1),
.last 21 (0,true),
.cycle 16 5 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[64, 2, 2, 2, 2, 1, 64],64⟩,
.last 22 (0,true)
])
theorem kid11_part428_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part428) = true := by rfl

def kid11_part429 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 20 8 true (0),
.cycle 20 1 false (0),
.cycle 10 6 true (3),
.cycle 10 6 true (3),
.last 16 (0,true),
.last 15 (0,true),
.cycle 8 10 true (4),
.cycle 6 18 true (2),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 11 4 true (4),
.last 15 (0,true),
.far true 1 ⟨0,[0, 0],[6, 6, 14, 8, 6, 16, 64],[64, 4, 2, 6, 6, 1, 64],64⟩,
.far true 1 ⟨0,[0, 0],[4, 4, 8, 8, 4, 16, 64],[64, 4, 4, 4, 4, 1, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.last 16 (0,true),
.last 15 (0,true),
.cycle 13 2 true (4),
.cycle 2 14 true (1),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 16 (0,true)
])
theorem kid11_part429_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part429) = true := by rfl

def kid11_part430 : Audit := .cycle 7 8 true (3)
theorem kid11_part430_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part430) = true := by rfl

def kid11_part431 : Audit := .cycle 6 8 true (2)
theorem kid11_part431_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part431) = true := by rfl

def kid11_part432 : Audit := .split 15 (0,true) (byMove [
.cycle 10 17 false (5),
.cycle 40 3 false (0),
.last 16 (2,true),
.cycle 37 1 false (-1),
.cycle 40 3 false (0),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.cycle 6 14 true (2),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 31 3 false (1),
.cycle 19 3 false (0),
.last 20 (2,true),
.last 16 (2,true),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 18 3 false (0),
.cycle 0 18 true (0),
.cycle 25 3 false (1),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 14 2 true (3)
])
theorem kid11_part432_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part432) = true := by rfl

def kid11_part433 : Audit := .cycle 0 14 true (0)
theorem kid11_part433_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part433) = true := by rfl

def kid11_part434 : Audit := .cycle 1 13 true (1)
theorem kid11_part434_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part434) = true := by rfl

def kid11_part435 : Audit := .cycle 2 12 true (1)
theorem kid11_part435_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part435) = true := by rfl

def kid11_part436 : Audit := .cycle 7 9 true (3)
theorem kid11_part436_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part436) = true := by rfl

def kid11_part437 : Audit := .cycle 8 6 true (4)
theorem kid11_part437_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part437) = true := by rfl

def kid11_part438 : Audit := .cycle 6 9 true (2)
theorem kid11_part438_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part438) = true := by rfl

def kid11_part414 : Audit := .split 13 (1,true) (byMove [(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418),(kid11_part419),(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428),(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438)])

theorem kid11_part414_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part414) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) 13 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418),(kid11_part419),(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428),(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part415_checked

  · exact kid11_part421_checked

  · exact kid11_part427_checked

  · exact kid11_part433_checked

  · exact kid11_part416_checked

  · exact kid11_part422_checked

  · exact kid11_part428_checked

  · exact kid11_part434_checked

  · exact kid11_part417_checked

  · exact kid11_part423_checked

  · exact kid11_part429_checked

  · exact kid11_part435_checked

  · exact kid11_part418_checked

  · exact kid11_part424_checked

  · exact kid11_part430_checked

  · exact kid11_part436_checked

  · exact kid11_part419_checked

  · exact kid11_part425_checked

  · exact kid11_part431_checked

  · exact kid11_part437_checked

  · exact kid11_part420_checked

  · exact kid11_part426_checked

  · exact kid11_part432_checked

  · exact kid11_part438_checked

def kid11_part439 : Audit := .split 13 (2,true) (byMove [
.split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.last 20 (1,true),
.last 15 (1,true),
.cycle 23 5 false (2),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 6 10 true (2)
]),
.split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 15 17 false (3),
.cycle 20 1 false (0),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 18 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 15 true (2),
.cycle 3 12 true (1),
.cycle 8 7 true (4),
.cycle 9 6 true (4),
.last 15 (0,true),
.cycle 18 3 false (0),
.cycle 41 11 true (1),
.cycle 7 9 true (3),
.cycle 6 9 true (2),
.cycle 18 6 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 7 10 true (3),
.cycle 8 7 true (4),
.cycle 6 10 true (2)
]),
.cycle 20 1 false (0),
.cycle 8 7 true (4),
.cycle 7 7 true (3),
.split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 28 15 false (3),
.cycle 20 1 false (0),
.cycle 37 1 false (-1),
.cycle 40 3 false (0),
.cycle 18 3 false (0),
.last 16 (0,true),
.cycle 1 16 true (1),
.cycle 6 12 true (2),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 31 3 false (1),
.last 16 (0,true),
.cycle 19 3 false (0),
.cycle 31 3 false (-1),
.cycle 5 11 true (1),
.cycle 6 11 true (2),
.cycle 18 3 false (0),
.last 16 (0,true),
.cycle 1 16 true (1),
.cycle 25 3 false (1),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 14 2 true (3)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 8 6 true (4),
.cycle 9 5 true (4),
.split 14 (0,true) (byMove [
.cycle 0 19 false (5),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 10 6 true (3),
.cycle 10 6 true (3),
.last 16 (1,true),
.cycle 0 16 true (0),
.last 15 (1,true),
.last 17 (1,true),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 11 4 true (4),
.last 20 (1,true),
.last 15 (1,true),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16842752, 8192, 16384, 8, 65536, 32, 65536, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 16777216, 1024, 1024, 16842752, 16777216, 16777216, 65536, 65536, 65536, 16777216, 1024, 16777216, 16777216, 1024, 1024, 16777216, 1024, 16777216, 16777216, 1024, 1024, 65536, 16777216],22717822⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.last 16 (1,true),
.cycle 0 16 true (0),
.last 15 (1,true),
.cycle 13 2 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.last 16 (1,true)
]),
.split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 15 17 false (3),
.cycle 20 1 false (0),
.cycle 10 6 true (3),
.cycle 10 6 true (3),
.cycle 18 6 false (0),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 12 4 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 11 4 true (4),
.last 15 (0,true),
.cycle 18 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 18 6 false (0),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 13 2 true (4),
.cycle 8 8 true (4),
.cycle 7 8 true (3),
.cycle 14 2 true (4)
]),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 1024, 4096],[4096, 4096, 1024, 1024, 1024, 1024, 4096, 4096, 1024, 1024, 1024, 4096, 4096],4096⟩,
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 28 15 false (3),
.cycle 20 1 false (0),
.cycle 37 1 false (-1),
.cycle 40 3 false (0),
.cycle 18 3 false (0),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 6 14 true (2),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 31 3 false (1),
.last 16 (0,true),
.cycle 19 3 false (0),
.cycle 37 3 false (1),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 18 3 false (0),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 25 3 false (1),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 14 2 true (3)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (4),
.cycle 6 9 true (2)
])
theorem kid11_part439_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part439) = true := by rfl

def kid11_part440 : Audit := .cycle 8 6 true (4)
theorem kid11_part440_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part440) = true := by rfl

def kid11_part441 : Audit := .cycle 4 8 true (1)
theorem kid11_part441_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part441) = true := by rfl

def kid11_part442 : Audit := .cycle 10 2 true (4)
theorem kid11_part442_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part442) = true := by rfl

def kid11_part443 : Audit := .cycle 6 8 true (2)
theorem kid11_part443_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part443) = true := by rfl

def kid11_part444 : Audit := .cycle 0 12 true (0)
theorem kid11_part444_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part444) = true := by rfl

def kid11_part445 : Audit := .cycle 1 11 true (1)
theorem kid11_part445_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part445) = true := by rfl

def kid11_part446 : Audit := .cycle 2 10 true (1)
theorem kid11_part446_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part446) = true := by rfl

def kid11_part447 : Audit := .cycle 7 7 true (3)
theorem kid11_part447_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part447) = true := by rfl

def kid11_part448 : Audit := .cycle 8 4 true (4)
theorem kid11_part448_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part448) = true := by rfl

def kid11_part449 : Audit := .cycle 6 7 true (2)
theorem kid11_part449_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part449) = true := by rfl

def kid11_part401 : Audit := .split 11 (5,true) (byMove [(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449)])

theorem kid11_part401_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (kid11_part401) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part402_checked

  · exact kid11_part408_checked

  · exact kid11_part414_checked

  · exact kid11_part444_checked

  · exact kid11_part403_checked

  · exact kid11_part409_checked

  · exact kid11_part439_checked

  · exact kid11_part445_checked

  · exact kid11_part404_checked

  · exact kid11_part410_checked

  · exact kid11_part440_checked

  · exact kid11_part446_checked

  · exact kid11_part405_checked

  · exact kid11_part411_checked

  · exact kid11_part441_checked

  · exact kid11_part447_checked

  · exact kid11_part406_checked

  · exact kid11_part412_checked

  · exact kid11_part442_checked

  · exact kid11_part448_checked

  · exact kid11_part407_checked

  · exact kid11_part413_checked

  · exact kid11_part443_checked

  · exact kid11_part449_checked

def kid11_part452 : Audit := .split 27 (2,true) (byMove [
.cycle 0 34 false (5),
.last 28 (1,true),
.cycle 35 1 false (-1),
.cycle 0 38 false (6),
.cycle 0 38 false (6),
.cycle 0 34 false (5),
.cycle 0 28 true (-1),
.cycle 0 66 false (12),
.cycle 0 48 false (9),
.cycle 0 44 false (8),
.cycle 67 8 true (4),
.cycle 0 36 false (6),
.cycle 0 34 false (5),
.last 28 (1,true),
.cycle 0 52 false (7),
.cycle 0 40 false (7),
.cycle 0 40 false (7),
.cycle 0 34 false (5),
.cycle 0 50 false (11),
.cycle 0 48 false (10),
.cycle 0 46 false (9),
.cycle 0 42 false (8),
.cycle 0 38 false (7),
.cycle 0 36 false (6)
])
theorem kid11_part452_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part452) = true := by rfl

def kid11_part453 : Audit := .split 13 (1,true) (byMove [
.cycle 46 32 false (3),
.last 39 (2,true),
.last 14 (2,true),
.last 21 (2,true),
.last 21 (2,true),
.last 27 (2,true),
.last 16 (2,true),
.cycle 6 24 true (1),
.cycle 6 16 true (0),
.last 23 (2,true),
.last 21 (2,true),
.last 19 (2,true),
.last 24 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.cycle 54 1 false (-2),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],[128, 256, 8, 65536, 32, 16842752, 8192, 16384, 8, 65536, 32, 16777216, 8192, 16384, 2097152, 65536, 8388608, 65536, 128, 256, 8, 65536, 32, 65536, 16777216],[2097160, 16384, 16777216, 1024, 1024, 16384, 2097152, 65536, 16777216, 65536, 65536, 65536, 8388608, 65536, 16777216, 65536, 65536, 65536, 2097152, 16384, 16777216, 1024, 1024, 16384, 16777216],20974640⟩,
.last 17 (2,true),
.last 16 (2,true),
.cycle 6 24 true (1),
.cycle 6 14 true (1),
.last 21 (2,true),
.last 54 (2,true),
.last 29 (2,true)
])
theorem kid11_part453_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part453) = true := by rfl

def kid11_part454 : Audit := .split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 67 1 false (-1),
.cycle 67 1 false (-1),
.cycle 34 1 false (-2),
.cycle 2 16 true (1),
.cycle 1 33 true (1),
.cycle 6 16 true (0),
.cycle 3 21 true (0),
.cycle 6 18 true (-1),
.cycle 57 1 false (-1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 0 19 true (0),
.cycle 1 33 true (1),
.cycle 6 14 true (1),
.cycle 7 17 true (1),
.cycle 20 1 false (0),
.cycle 18 1 false (0)
])
theorem kid11_part454_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part454) = true := by rfl

def kid11_part455 : Audit := .cycle 19 1 false (-1)
theorem kid11_part455_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part455) = true := by rfl

def kid11_part456 : Audit := .cycle 20 1 false (0)
theorem kid11_part456_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part456) = true := by rfl

def kid11_part457 : Audit := .cycle 15 1 false (-1)
theorem kid11_part457_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part457) = true := by rfl

def kid11_part458 : Audit := .split 14 (1,true) (byMove [
.cycle 0 19 true (0),
.cycle 6 16 true (2),
.last 15 (2,true),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 26 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 17 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.last 18 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 0 17 true (0)
])
theorem kid11_part458_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part458) = true := by rfl

def kid11_part459 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 15 (1,true),
.cycle 0 24 true (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 17 12 true (3),
.cycle 1 15 true (1),
.last 15 (1,true),
.cycle 6 18 true (2),
.cycle 13 8 true (3),
.cycle 13 8 true (3),
.cycle 0 16 true (0),
.last 16 (1,true),
.last 15 (1,true),
.cycle 5 12 true (1),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 8 true (2),
.cycle 1 15 true (1),
.last 15 (1,true),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 1 16 true (1)
])
theorem kid11_part459_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part459) = true := by rfl

def kid11_part460 : Audit := .cycle 7 8 true (2)
theorem kid11_part460_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part460) = true := by rfl

def kid11_part461 : Audit := .cycle 6 12 true (1)
theorem kid11_part461_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part461) = true := by rfl

def kid11_part462 : Audit := .split 17 (2,true) (byMove [
.cycle 12 15 true (2),
.last 18 (1,true),
.cycle 2 18 true (1),
.cycle 8 11 true (2),
.cycle 7 11 true (2),
.cycle 35 1 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (2),
.cycle 3 15 true (1),
.cycle 25 8 true (4),
.cycle 9 9 true (2),
.cycle 6 22 true (2),
.last 18 (1,true),
.cycle 5 16 true (1),
.cycle 7 12 true (2),
.cycle 6 12 true (2),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (2),
.cycle 8 10 true (2),
.cycle 0 23 true (0)
])
theorem kid11_part462_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part462) = true := by rfl

def kid11_part463 : Audit := .cycle 17 1 false (1)
theorem kid11_part463_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part463) = true := by rfl

def kid11_part464 : Audit := .split 16 (1,true) (byMove [
.cycle 14 3 false (0),
.last 31 (2,true),
.last 17 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.last 27 (2,true),
.cycle 0 28 true (-1),
.last 20 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.last 20 (2,true),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.last 25 (2,true),
.last 25 (2,true),
.last 20 (2,true),
.cycle 12 5 false (2),
.last 20 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.last 23 (2,true),
.cycle 13 5 false (1)
])
theorem kid11_part464_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part464) = true := by rfl

def kid11_part465 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.last 27 (2,true),
.last 14 (2,true),
.last 28 (2,true),
.last 28 (2,true),
.last 23 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.last 26 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.last 21 (2,true),
.last 21 (2,true),
.last 17 (2,true),
.cycle 12 2 true (1),
.last 16 (2,true),
.last 14 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.last 20 (2,true)
])
theorem kid11_part465_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part465) = true := by rfl

def kid11_part466 : Audit := .split 13 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 60, 64],[60, 64, 60, 16, 16, 60, 64],64⟩,
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 15 29 true (1),
.cycle 48 1 false (0),
.cycle 47 11 false (1),
.cycle 0 22 true (0),
.last 14 (1,true),
.cycle 6 30 true (1),
.cycle 3 17 true (1),
.cycle 29 8 true (4),
.cycle 9 23 true (1),
.far false 5 ⟨0,[0, 1, 2, 3, 0, 1, 4, 1, 0, 1],[128, 256, 8, 4195328, 32, 1077937152, 524288, 1048576, 32768, 4194304, 131072, 1077936128, 128, 256, 8, 1024, 32, 1073742848, 128, 256, 134217728, 1024, 536870912, 256, 128, 256, 8, 4194304, 32, 4194304, 1073741824],[1024, 1073741824, 1073741824, 1024, 1024, 1048576, 1073741824, 1073741824, 4194304, 4194304, 4194304, 131072, 1024, 1073741824, 1073741824, 1024, 1024, 256, 1024, 1073741824, 1073741824, 1024, 1024, 1073741824, 1024, 1073741824, 1073741824, 1024, 1024, 1048576, 1073741824],1454108030⟩,
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 16, 16, 16, 36, 64],64⟩,
.cycle 7 16 true (0),
.cycle 6 16 true (0),
.cycle 30 1 false (-2),
.cycle 12 2 true (1),
.last 14 (1,true),
.cycle 2 28 true (1),
.cycle 7 15 true (1),
.cycle 8 12 true (1),
.cycle 11 17 false (3)
])
theorem kid11_part466_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part466) = true := by rfl

def kid11_part467 : Audit := .split 19 (2,true) (byMove [
.cycle 7 15 true (1),
.last 20 (1,true),
.cycle 26 1 false (0),
.cycle 8 13 true (1),
.cycle 7 13 true (1),
.cycle 7 16 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (1),
.cycle 3 17 true (1),
.cycle 29 8 true (4),
.cycle 9 11 true (1),
.cycle 5 16 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 16, 16, 16, 36, 64],64⟩,
.cycle 7 14 true (1),
.cycle 6 14 true (1),
.cycle 0 26 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (1),
.cycle 8 12 true (1),
.cycle 0 27 true (0)
])
theorem kid11_part467_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part467) = true := by rfl

def kid11_part468 : Audit := .split 19 (2,true) (byMove [
.cycle 6 15 true (1),
.last 20 (1,true),
.cycle 26 1 false (0),
.cycle 8 13 true (1),
.cycle 7 13 true (1),
.cycle 6 16 true (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 6 20 true (1),
.cycle 3 17 true (1),
.cycle 29 8 true (4),
.cycle 9 11 true (1),
.cycle 6 16 true (1),
.last 20 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 60, 64],[60, 64, 16, 16, 16, 60, 64],64⟩,
.cycle 7 14 true (1),
.cycle 6 14 true (1),
.cycle 0 26 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 7 15 true (1),
.cycle 8 12 true (1),
.cycle 0 27 true (0)
])
theorem kid11_part468_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part468) = true := by rfl

def kid11_part469 : Audit := .cycle 15 1 false (-1)
theorem kid11_part469_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part469) = true := by rfl

def kid11_part470 : Audit := .split 14 (1,true) (byMove [
.cycle 0 19 true (0),
.cycle 15 17 false (3),
.last 15 (2,true),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 19 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (2,true),
.last 22 (2,true),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 0 18 true (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 0 17 true (0)
])
theorem kid11_part470_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part470) = true := by rfl

def kid11_part471 : Audit := .split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 13 12 true (2),
.cycle 1 15 true (1),
.last 15 (1,true),
.cycle 6 18 true (2),
.cycle 13 8 true (3),
.cycle 13 8 true (3),
.cycle 0 16 true (0),
.last 16 (1,true),
.last 15 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[2, 64, 16, 16, 16, 4, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (2),
.cycle 1 15 true (1),
.last 15 (1,true),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 1 16 true (1)
])
theorem kid11_part471_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part471) = true := by rfl

def kid11_part472 : Audit := .cycle 7 8 true (2)
theorem kid11_part472_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part472) = true := by rfl

def kid11_part473 : Audit := .cycle 6 10 true (2)
theorem kid11_part473_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part473) = true := by rfl

def kid11_part474 : Audit := .split 17 (2,true) (byMove [
.cycle 8 11 true (2),
.last 18 (1,true),
.cycle 24 1 false (0),
.cycle 8 11 true (2),
.cycle 7 11 true (2),
.cycle 8 12 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 6 18 true (2),
.cycle 3 15 true (1),
.cycle 25 8 true (4),
.cycle 9 9 true (2),
.cycle 7 12 true (2),
.last 18 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 52, 64],[16, 64, 16, 16, 16, 36, 64],64⟩,
.cycle 7 12 true (2),
.cycle 6 12 true (2),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 7 13 true (2),
.cycle 8 10 true (2),
.cycle 0 23 true (0)
])
theorem kid11_part474_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part474) = true := by rfl

def kid11_part475 : Audit := .split 23 (2,true) (byMove [
.cycle 15 9 false (2),
.last 24 (1,true),
.cycle 27 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[32, 64, 32, 16, 16, 36, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[32, 64, 36, 16, 16, 36, 64],64⟩,
.cycle 17 7 false (1),
.cycle 0 40 true (-1),
.last 24 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[32, 64, 4, 16, 16, 4, 64],64⟩,
.cycle 6 20 true (-1),
.cycle 6 20 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 36, 64],[32, 64, 32, 16, 16, 36, 64],64⟩,
.cycle 14 11 false (2),
.last 24 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[32, 64, 16, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[32, 64, 16, 16, 16, 20, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[32, 64, 20, 16, 16, 20, 64],64⟩,
.cycle 17 7 false (1),
.cycle 10 17 false (4),
.last 24 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[32, 64, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[32, 64, 8, 16, 16, 28, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[32, 64, 16, 16, 16, 20, 64],64⟩,
.cycle 11 13 false (3)
])
theorem kid11_part475_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part475) = true := by rfl

def kid11_part451 : Audit := .split 12 (0,true) (byMove [(kid11_part452),(kid11_part453),(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475)])

theorem kid11_part451_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part451) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part452),(kid11_part453),(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part452_checked

  · exact kid11_part458_checked

  · exact kid11_part464_checked

  · exact kid11_part470_checked

  · exact kid11_part453_checked

  · exact kid11_part459_checked

  · exact kid11_part465_checked

  · exact kid11_part471_checked

  · exact kid11_part454_checked

  · exact kid11_part460_checked

  · exact kid11_part466_checked

  · exact kid11_part472_checked

  · exact kid11_part455_checked

  · exact kid11_part461_checked

  · exact kid11_part467_checked

  · exact kid11_part473_checked

  · exact kid11_part456_checked

  · exact kid11_part462_checked

  · exact kid11_part468_checked

  · exact kid11_part474_checked

  · exact kid11_part457_checked

  · exact kid11_part463_checked

  · exact kid11_part469_checked

  · exact kid11_part475_checked

def kid11_part477 : Audit := .split 13 (0,true) (byMove [
.cycle 32 10 true (4),
.cycle 32 10 true (4),
.last 14 (2,true),
.cycle 32 10 true (4),
.cycle 32 10 true (4),
.cycle 28 1 false (-2),
.last 16 (2,true),
.cycle 14 10 true (2),
.cycle 6 16 true (0),
.cycle 28 10 true (4),
.cycle 19 20 true (-1),
.cycle 30 10 true (4),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.cycle 6 20 true (-1),
.cycle 6 20 true (-1),
.cycle 6 20 true (-1),
.last 16 (2,true),
.cycle 14 10 true (2),
.cycle 6 14 true (1),
.cycle 26 10 true (4),
.cycle 6 18 true (-1),
.cycle 30 10 true (4)
])
theorem kid11_part477_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part477) = true := by rfl

def kid11_part478 : Audit := .cycle 90 60 false (7)
theorem kid11_part478_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part478) = true := by rfl

def kid11_part479 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 22 24 true (2),
.cycle 22 24 true (2),
.cycle 28 1 false (-2),
.last 17 (0,true),
.cycle 14 24 true (2),
.cycle 6 16 true (0),
.cycle 14 24 true (0),
.cycle 6 44 true (-1),
.cycle 20 24 true (2),
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 22 1 false (0),
.cycle 6 20 true (-1),
.last 17 (0,true),
.cycle 14 24 true (2),
.cycle 6 14 true (1),
.cycle 16 24 true (2),
.cycle 20 1 false (0),
.cycle 18 1 false (0)
])
theorem kid11_part479_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part479) = true := by rfl

def kid11_part480 : Audit := .cycle 19 1 false (-1)
theorem kid11_part480_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part480) = true := by rfl

def kid11_part481 : Audit := .cycle 20 1 false (0)
theorem kid11_part481_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part481) = true := by rfl

def kid11_part482 : Audit := .cycle 15 1 false (-1)
theorem kid11_part482_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part482) = true := by rfl

def kid11_part483 : Audit := .split 15 (0,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 7 16 true (2),
.cycle 7 21 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 20 true (2),
.cycle 5 17 true (1),
.cycle 0 18 true (0),
.last 17 (2,true),
.cycle 7 18 true (2),
.cycle 4 12 true (1),
.cycle 1 17 true (1),
.cycle 7 14 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 7 16 true (2),
.cycle 7 21 true (2)
])
theorem kid11_part483_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part483) = true := by rfl

def kid11_part484 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 1 18 true (1),
.cycle 1 23 true (1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 6 16 true (2),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 7 16 true (2),
.cycle 7 16 true (2),
.cycle 1 15 true (1),
.last 15 (0,true),
.cycle 1 17 true (1),
.cycle 5 12 true (1),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 7 12 true (2),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 1 16 true (1)
])
theorem kid11_part484_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part484) = true := by rfl

def kid11_part485 : Audit := .cycle 7 8 true (2)
theorem kid11_part485_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part485) = true := by rfl

def kid11_part486 : Audit := .cycle 6 12 true (1)
theorem kid11_part486_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part486) = true := by rfl

def kid11_part487 : Audit := .cycle 7 18 true (2)
theorem kid11_part487_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part487) = true := by rfl

def kid11_part488 : Audit := .cycle 17 1 false (1)
theorem kid11_part488_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part488) = true := by rfl

def kid11_part489 : Audit := .split 13 (0,true) (byMove [
.cycle 0 174 false (15),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.last 14 (2,true),
.cycle 6 18 true (0),
.cycle 6 18 true (0),
.cycle 50 1 false (-2),
.cycle 0 20 true (0),
.cycle 12 4 true (1),
.last 14 (2,true),
.cycle 12 22 true (1),
.cycle 12 22 true (1),
.cycle 6 16 true (1),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 12 24 true (0),
.cycle 12 24 true (0),
.cycle 87 1 false (-3),
.cycle 0 20 true (0),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 12 22 true (1),
.cycle 12 22 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part489_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part489) = true := by rfl

def kid11_part490 : Audit := .split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 14 3 false (0),
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 32, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.last 17 (0,true),
.cycle 17 23 true (0),
.cycle 18 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 24, 8, 16, 16, 56, 64],64⟩,
.cycle 19 20 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 32, 16, 16, 56, 64],64⟩,
.last 17 (0,true),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 16, 16, 16, 16, 40, 64],64⟩,
.cycle 20 22 true (2),
.cycle 19 22 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 56, 56, 16, 16, 56, 64],64⟩,
.last 17 (0,true),
.cycle 12 5 false (2),
.cycle 18 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[64, 24, 8, 16, 16, 56, 64],64⟩,
.cycle 19 20 true (3),
.cycle 13 5 false (1)
])
theorem kid11_part490_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part490) = true := by rfl

def kid11_part491 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 49 20 true (5),
.cycle 16 1 false (0),
.cycle 6 18 true (0),
.cycle 6 18 true (0),
.cycle 23 20 true (3),
.last 14 (0,true),
.cycle 14 20 true (1),
.cycle 15 20 true (3),
.cycle 14 20 true (2),
.cycle 15 20 true (3),
.cycle 6 16 true (1),
.last 14 (0,true),
.cycle 19 20 true (3),
.cycle 19 20 true (3),
.cycle 17 20 true (3),
.cycle 17 20 true (3),
.cycle 19 20 true (3),
.last 14 (0,true),
.cycle 12 2 true (1),
.cycle 15 20 true (3),
.cycle 14 20 true (2),
.cycle 15 20 true (3),
.cycle 29 20 true (3)
])
theorem kid11_part491_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part491) = true := by rfl

def kid11_part492 : Audit := .cycle 14 22 true (2)
theorem kid11_part492_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part492) = true := by rfl

def kid11_part493 : Audit := .cycle 6 36 true (1)
theorem kid11_part493_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part493) = true := by rfl

def kid11_part494 : Audit := .cycle 15 1 false (-1)
theorem kid11_part494_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part494) = true := by rfl

def kid11_part495 : Audit := .split 15 (0,true) (byMove [
.cycle 0 21 false (5),
.cycle 0 17 true (0),
.last 16 (2,true),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 7 26 true (2),
.cycle 9 7 true (2),
.cycle 18 5 false (2),
.cycle 14 2 true (4),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 0 20 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 0 21 true (0)
])
theorem kid11_part495_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part495) = true := by rfl

def kid11_part496 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 1 18 true (1),
.cycle 20 1 false (0),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 7 20 true (2),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 7 16 true (2),
.cycle 7 16 true (2),
.cycle 1 15 true (1),
.last 15 (0,true),
.cycle 1 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 2, 16, 16, 16, 12, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (2),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 1 16 true (1)
])
theorem kid11_part496_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part496) = true := by rfl

def kid11_part497 : Audit := .cycle 7 8 true (2)
theorem kid11_part497_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part497) = true := by rfl

def kid11_part498 : Audit := .cycle 6 10 true (2)
theorem kid11_part498_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part498) = true := by rfl

def kid11_part499 : Audit := .cycle 7 18 true (2)
theorem kid11_part499_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part499) = true := by rfl

def kid11_part500 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 32, 64, 16, 16, 24, 64],64⟩
theorem kid11_part500_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part500) = true := by rfl

def kid11_part476 : Audit := .split 12 (1,true) (byMove [(kid11_part477),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488),(kid11_part489),(kid11_part490),(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500)])

theorem kid11_part476_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part476) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid11_part477),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488),(kid11_part489),(kid11_part490),(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part477_checked

  · exact kid11_part483_checked

  · exact kid11_part489_checked

  · exact kid11_part495_checked

  · exact kid11_part478_checked

  · exact kid11_part484_checked

  · exact kid11_part490_checked

  · exact kid11_part496_checked

  · exact kid11_part479_checked

  · exact kid11_part485_checked

  · exact kid11_part491_checked

  · exact kid11_part497_checked

  · exact kid11_part480_checked

  · exact kid11_part486_checked

  · exact kid11_part492_checked

  · exact kid11_part498_checked

  · exact kid11_part481_checked

  · exact kid11_part487_checked

  · exact kid11_part493_checked

  · exact kid11_part499_checked

  · exact kid11_part482_checked

  · exact kid11_part488_checked

  · exact kid11_part494_checked

  · exact kid11_part500_checked

def kid11_part502 : Audit := .split 13 (0,true) (byMove [
.cycle 0 42 false (7),
.last 14 (1,true),
.cycle 43 1 false (-1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.last 19 (1,true),
.cycle 14 10 true (2),
.cycle 6 16 true (0),
.cycle 6 20 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 5 false (2),
.cycle 6 20 true (-1),
.cycle 6 20 true (-1),
.cycle 16 1 false (0),
.last 19 (1,true),
.cycle 14 10 true (2),
.cycle 6 14 true (1),
.cycle 6 18 true (1),
.cycle 6 18 true (-1),
.cycle 6 22 true (-1)
])
theorem kid11_part502_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part502) = true := by rfl

def kid11_part503 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 53 38 false (3),
.cycle 29 1 false (-1),
.cycle 20 1 false (0),
.cycle 20 1 false (0),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.cycle 6 24 true (1),
.cycle 6 16 true (0),
.cycle 6 20 true (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 91 1 false (-1),
.cycle 54 1 false (-2),
.cycle 57 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.cycle 6 24 true (1),
.cycle 6 14 true (1),
.cycle 6 18 true (1),
.cycle 53 1 false (-1),
.cycle 51 1 false (-1)
])
theorem kid11_part503_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part503) = true := by rfl

def kid11_part504 : Audit := .cycle 16 1 false (0)
theorem kid11_part504_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part504) = true := by rfl

def kid11_part505 : Audit := .cycle 19 1 false (-1)
theorem kid11_part505_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part505) = true := by rfl

def kid11_part506 : Audit := .cycle 20 1 false (0)
theorem kid11_part506_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part506) = true := by rfl

def kid11_part507 : Audit := .cycle 15 1 false (-1)
theorem kid11_part507_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part507) = true := by rfl

def kid11_part508 : Audit := .split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 6 16 true (2),
.cycle 0 19 true (0),
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.cycle 2 22 true (1),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 6 20 true (2),
.cycle 6 20 true (2),
.cycle 2 14 true (1),
.last 15 (0,true),
.last 18 (0,true),
.last 16 (0,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 6 16 true (1),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 0 17 true (0)
])
theorem kid11_part508_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part508) = true := by rfl

def kid11_part509 : Audit := .split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 6 20 true (1),
.cycle 6 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 24 true (1),
.cycle 6 21 true (1),
.last 18 (0,true),
.cycle 1 17 true (1),
.cycle 6 22 true (2),
.cycle 4 12 true (1),
.cycle 2 16 true (1),
.cycle 6 18 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 6 20 true (2),
.cycle 6 17 true (2)
])
theorem kid11_part509_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part509) = true := by rfl

def kid11_part510 : Audit := .cycle 7 8 true (2)
theorem kid11_part510_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part510) = true := by rfl

def kid11_part511 : Audit := .cycle 6 12 true (1)
theorem kid11_part511_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part511) = true := by rfl

def kid11_part512 : Audit := .cycle 6 16 true (1)
theorem kid11_part512_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part512) = true := by rfl

def kid11_part513 : Audit := .cycle 17 1 false (1)
theorem kid11_part513_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part513) = true := by rfl

def kid11_part514 : Audit := .split 13 (0,true) (byMove [
.cycle 6 20 true (-1),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 24 true (0),
.cycle 6 24 true (0),
.cycle 16 1 false (0),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 16 true (1),
.cycle 6 16 true (1),
.cycle 6 22 true (0),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 18 true (0),
.cycle 6 18 true (0),
.cycle 16 1 false (0),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 2 true (1),
.cycle 6 16 true (1),
.cycle 6 16 true (1),
.last 20 (1,true)
])
theorem kid11_part514_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part514) = true := by rfl

def kid11_part515 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 1 212 false (11),
.cycle 19 1 false (-1),
.cycle 6 24 true (0),
.cycle 6 24 true (0),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 1 19 true (1),
.cycle 12 4 true (1),
.cycle 6 16 true (1),
.cycle 6 16 true (1),
.cycle 6 22 true (0),
.last 14 (0,true),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 16, 16, 16, 16, 48, 64],64⟩,
.cycle 6 18 true (0),
.cycle 6 18 true (0),
.cycle 16 1 false (0),
.last 14 (0,true),
.cycle 1 19 true (1),
.cycle 12 2 true (1),
.cycle 6 16 true (1),
.cycle 6 16 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part515_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part515) = true := by rfl

def kid11_part516 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 64, 16, 16, 16, 48, 64],64⟩
theorem kid11_part516_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part516) = true := by rfl

def kid11_part517 : Audit := .cycle 6 16 true (1)
theorem kid11_part517_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part517) = true := by rfl

def kid11_part518 : Audit := .cycle 6 16 true (1)
theorem kid11_part518_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part518) = true := by rfl

def kid11_part519 : Audit := .cycle 15 1 false (-1)
theorem kid11_part519_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part519) = true := by rfl

def kid11_part520 : Audit := .split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 15 17 false (3),
.cycle 0 19 true (0),
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.cycle 0 20 true (0),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 6 20 true (2),
.cycle 6 20 true (2),
.cycle 2 14 true (1),
.last 15 (0,true),
.last 21 (0,true),
.last 16 (0,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (2),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 8 8 true (2),
.cycle 7 8 true (2),
.cycle 0 17 true (0)
])
theorem kid11_part520_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part520) = true := by rfl

def kid11_part521 : Audit := .split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 16 19 false (4),
.cycle 1 16 true (1),
.cycle 8 9 true (2),
.cycle 7 9 true (2),
.cycle 1 17 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 6 30 true (2),
.cycle 9 7 true (2),
.last 16 (0,true),
.cycle 18 5 false (2),
.cycle 14 2 true (4),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 1 19 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (2),
.cycle 8 8 true (2),
.cycle 1 20 true (1)
])
theorem kid11_part521_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part521) = true := by rfl

def kid11_part522 : Audit := .cycle 7 8 true (2)
theorem kid11_part522_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part522) = true := by rfl

def kid11_part523 : Audit := .cycle 6 10 true (2)
theorem kid11_part523_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part523) = true := by rfl

def kid11_part524 : Audit := .cycle 6 14 true (2)
theorem kid11_part524_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part524) = true := by rfl

def kid11_part525 : Audit := .cycle 22 1 false (0)
theorem kid11_part525_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part525) = true := by rfl

def kid11_part501 : Audit := .split 12 (2,true) (byMove [(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525)])

theorem kid11_part501_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part501) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part502_checked

  · exact kid11_part508_checked

  · exact kid11_part514_checked

  · exact kid11_part520_checked

  · exact kid11_part503_checked

  · exact kid11_part509_checked

  · exact kid11_part515_checked

  · exact kid11_part521_checked

  · exact kid11_part504_checked

  · exact kid11_part510_checked

  · exact kid11_part516_checked

  · exact kid11_part522_checked

  · exact kid11_part505_checked

  · exact kid11_part511_checked

  · exact kid11_part517_checked

  · exact kid11_part523_checked

  · exact kid11_part506_checked

  · exact kid11_part512_checked

  · exact kid11_part518_checked

  · exact kid11_part524_checked

  · exact kid11_part507_checked

  · exact kid11_part513_checked

  · exact kid11_part519_checked

  · exact kid11_part525_checked

def kid11_part526 : Audit := .cycle 7 15 true (2)
theorem kid11_part526_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part526) = true := by rfl

def kid11_part527 : Audit := .cycle 34 1 false (0)
theorem kid11_part527_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part527) = true := by rfl

def kid11_part528 : Audit := .cycle 15 1 false (-1)
theorem kid11_part528_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part528) = true := by rfl

def kid11_part530 : Audit := .split 15 (2,true) (byMove [
.cycle 0 21 false (5),
.last 16 (1,true),
.cycle 22 1 false (0),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 7 18 true (3),
.cycle 9 7 true (3),
.cycle 0 21 false (5),
.last 16 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 256, 4096],[256, 4096, 1024, 1024, 1024, 1, 1064, 4096, 1024, 1024, 1024, 1, 4096],4096⟩,
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 0 19 true (0)
])
theorem kid11_part530_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part530) = true := by rfl

def kid11_part531 : Audit := .cycle 8 8 true (3)
theorem kid11_part531_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part531) = true := by rfl

def kid11_part532 : Audit := .cycle 6 12 true (2)
theorem kid11_part532_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part532) = true := by rfl

def kid11_part533 : Audit := .cycle 0 18 true (0)
theorem kid11_part533_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part533) = true := by rfl

def kid11_part534 : Audit := .cycle 29 1 false (1)
theorem kid11_part534_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part534) = true := by rfl

def kid11_part535 : Audit := .cycle 22 1 false (0)
theorem kid11_part535_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part535) = true := by rfl

def kid11_part536 : Audit := .cycle 0 14 true (0)
theorem kid11_part536_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part536) = true := by rfl

def kid11_part537 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 1 22 true (1),
.cycle 12 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part537_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part537) = true := by rfl

def kid11_part538 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 6 31 true (1),
.last 15 (1,true),
.last 16 (1,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 23 true (2)
])
theorem kid11_part538_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part538) = true := by rfl

def kid11_part539 : Audit := .cycle 8 6 true (3)
theorem kid11_part539_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part539) = true := by rfl

def kid11_part540 : Audit := .cycle 7 6 true (3)
theorem kid11_part540_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part540) = true := by rfl

def kid11_part541 : Audit := .cycle 0 14 true (0)
theorem kid11_part541_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part541) = true := by rfl

def kid11_part542 : Audit := .split 14 (1,true) (byMove [
.cycle 18 3 false (0),
.cycle 15 17 false (3),
.last 15 (2,true),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.cycle 0 18 true (0),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.cycle 18 3 false (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (3),
.cycle 18 5 false (2),
.cycle 1 15 true (1),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0)
])
theorem kid11_part542_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part542) = true := by rfl

def kid11_part543 : Audit := .split 14 (2,true) (byMove [
.last 16 (1,true),
.last 15 (1,true),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.last 17 (1,true),
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 6 18 true (2),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0),
.last 16 (1,true),
.last 15 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 1024, 4096],[1024, 4096, 1024, 1024, 1024, 1, 4096, 4096, 1024, 1024, 1024, 1, 4096],4096⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (3),
.last 16 (1,true),
.last 15 (1,true),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 0 16 true (0)
])
theorem kid11_part543_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part543) = true := by rfl

def kid11_part544 : Audit := .cycle 7 8 true (3)
theorem kid11_part544_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part544) = true := by rfl

def kid11_part545 : Audit := .cycle 6 10 true (2)
theorem kid11_part545_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part545) = true := by rfl

def kid11_part546 : Audit := .cycle 0 18 true (0)
theorem kid11_part546_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part546) = true := by rfl

def kid11_part547 : Audit := .cycle 22 1 false (0)
theorem kid11_part547_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part547) = true := by rfl

def kid11_part548 : Audit := .cycle 0 14 true (0)
theorem kid11_part548_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part548) = true := by rfl

def kid11_part549 : Audit := .split 13 (1,true) (byMove [
.cycle 1 14 true (1),
.cycle 1 14 true (1),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 12 2 true (4),
.last 16 (2,true),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part549_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part549) = true := by rfl

def kid11_part550 : Audit := .split 13 (2,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 12 2 true (4),
.last 14 (1,true),
.cycle 7 10 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 2 15 true (1)
])
theorem kid11_part550_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part550) = true := by rfl

def kid11_part551 : Audit := .cycle 8 6 true (3)
theorem kid11_part551_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part551) = true := by rfl

def kid11_part552 : Audit := .cycle 7 6 true (3)
theorem kid11_part552_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part552) = true := by rfl

def kid11_part553 : Audit := .cycle 0 14 true (0)
theorem kid11_part553_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part553) = true := by rfl

def kid11_part529 : Audit := .split 12 (0,true) (byMove [(kid11_part530),(kid11_part531),(kid11_part532),(kid11_part533),(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553)])

theorem kid11_part529_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part529) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (0,true) (some mv)) (byMove [(kid11_part530),(kid11_part531),(kid11_part532),(kid11_part533),(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part530_checked

  · exact kid11_part536_checked

  · exact kid11_part542_checked

  · exact kid11_part548_checked

  · exact kid11_part531_checked

  · exact kid11_part537_checked

  · exact kid11_part543_checked

  · exact kid11_part549_checked

  · exact kid11_part532_checked

  · exact kid11_part538_checked

  · exact kid11_part544_checked

  · exact kid11_part550_checked

  · exact kid11_part533_checked

  · exact kid11_part539_checked

  · exact kid11_part545_checked

  · exact kid11_part551_checked

  · exact kid11_part534_checked

  · exact kid11_part540_checked

  · exact kid11_part546_checked

  · exact kid11_part552_checked

  · exact kid11_part535_checked

  · exact kid11_part541_checked

  · exact kid11_part547_checked

  · exact kid11_part553_checked

def kid11_part555 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.last 17 (0,true),
.cycle 22 1 false (0),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 7 18 true (3),
.cycle 9 7 true (3),
.last 16 (0,true),
.last 17 (0,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 1024, 128, 256, 8, 1024, 32, 256, 4096],[4096, 256, 1024, 1024, 1024, 2, 4096, 4096, 1024, 1024, 1024, 2, 4096],4096⟩,
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 0 19 true (0)
])
theorem kid11_part555_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part555) = true := by rfl

def kid11_part556 : Audit := .cycle 8 8 true (3)
theorem kid11_part556_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part556) = true := by rfl

def kid11_part557 : Audit := .cycle 6 12 true (2)
theorem kid11_part557_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part557) = true := by rfl

def kid11_part558 : Audit := .cycle 1 17 true (1)
theorem kid11_part558_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part558) = true := by rfl

def kid11_part559 : Audit := .cycle 29 1 false (1)
theorem kid11_part559_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part559) = true := by rfl

def kid11_part560 : Audit := .cycle 22 1 false (0)
theorem kid11_part560_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part560) = true := by rfl

def kid11_part561 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 0 23 true (0),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part561_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part561) = true := by rfl

def kid11_part562 : Audit := .cycle 1 13 true (1)
theorem kid11_part562_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part562) = true := by rfl

def kid11_part563 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 6 31 true (1),
.cycle 6 16 true (2),
.cycle 12 4 true (4),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 23 true (2)
])
theorem kid11_part563_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part563) = true := by rfl

def kid11_part564 : Audit := .cycle 8 6 true (3)
theorem kid11_part564_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part564) = true := by rfl

def kid11_part565 : Audit := .cycle 7 6 true (3)
theorem kid11_part565_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part565) = true := by rfl

def kid11_part566 : Audit := .cycle 1 13 true (1)
theorem kid11_part566_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part566) = true := by rfl

def kid11_part567 : Audit := .split 15 (0,true) (byMove [
.last 35 (2,true),
.last 28 (2,true),
.last 16 (2,true),
.cycle 1 27 true (1),
.cycle 62 1 false (0),
.last 18 (2,true),
.cycle 0 18 true (0),
.cycle 12 4 true (3),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 1 21 true (1),
.cycle 18 3 false (0),
.last 23 (2,true),
.last 16 (2,true),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 31 1 false (-1),
.cycle 0 18 true (0),
.cycle 14 2 true (3),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 1 21 true (1)
])
theorem kid11_part567_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part567) = true := by rfl

def kid11_part568 : Audit := .split 14 (2,true) (byMove [
.last 15 (0,true),
.cycle 18 3 false (0),
.cycle 20 1 false (0),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 1 18 true (1),
.last 15 (0,true),
.cycle 1 17 true (1),
.cycle 6 18 true (2),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 1 15 true (1),
.last 15 (0,true),
.cycle 18 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (3),
.last 15 (0,true),
.cycle 18 5 false (2),
.cycle 2 14 true (1),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 1 15 true (1)
])
theorem kid11_part568_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part568) = true := by rfl

def kid11_part569 : Audit := .cycle 7 8 true (3)
theorem kid11_part569_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part569) = true := by rfl

def kid11_part570 : Audit := .cycle 6 10 true (2)
theorem kid11_part570_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part570) = true := by rfl

def kid11_part571 : Audit := .cycle 1 17 true (1)
theorem kid11_part571_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part571) = true := by rfl

def kid11_part572 : Audit := .cycle 22 1 false (0)
theorem kid11_part572_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part572) = true := by rfl

def kid11_part573 : Audit := .split 13 (0,true) (byMove [
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 20 5 false (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part573_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part573) = true := by rfl

def kid11_part574 : Audit := .cycle 1 13 true (1)
theorem kid11_part574_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part574) = true := by rfl

def kid11_part575 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 2 13 true (1),
.cycle 2 13 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 14 (0,true),
.cycle 12 2 true (4),
.cycle 7 10 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 2 15 true (1)
])
theorem kid11_part575_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part575) = true := by rfl

def kid11_part576 : Audit := .cycle 8 6 true (3)
theorem kid11_part576_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part576) = true := by rfl

def kid11_part577 : Audit := .cycle 7 6 true (3)
theorem kid11_part577_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part577) = true := by rfl

def kid11_part578 : Audit := .cycle 1 13 true (1)
theorem kid11_part578_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part578) = true := by rfl

def kid11_part554 : Audit := .split 12 (1,true) (byMove [(kid11_part555),(kid11_part556),(kid11_part557),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part562),(kid11_part563),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578)])

theorem kid11_part554_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part554) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some mv)) (byMove [(kid11_part555),(kid11_part556),(kid11_part557),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part562),(kid11_part563),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part555_checked

  · exact kid11_part561_checked

  · exact kid11_part567_checked

  · exact kid11_part573_checked

  · exact kid11_part556_checked

  · exact kid11_part562_checked

  · exact kid11_part568_checked

  · exact kid11_part574_checked

  · exact kid11_part557_checked

  · exact kid11_part563_checked

  · exact kid11_part569_checked

  · exact kid11_part575_checked

  · exact kid11_part558_checked

  · exact kid11_part564_checked

  · exact kid11_part570_checked

  · exact kid11_part576_checked

  · exact kid11_part559_checked

  · exact kid11_part565_checked

  · exact kid11_part571_checked

  · exact kid11_part577_checked

  · exact kid11_part560_checked

  · exact kid11_part566_checked

  · exact kid11_part572_checked

  · exact kid11_part578_checked

def kid11_part580 : Audit := .split 16 (0,true) (byMove [
.cycle 0 21 false (5),
.last 17 (1,true),
.cycle 22 1 false (0),
.cycle 8 10 true (3),
.cycle 7 10 true (3),
.cycle 6 18 true (2),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 6 17 true (2),
.cycle 3 14 true (1),
.cycle 6 33 true (2),
.cycle 9 8 true (3),
.last 22 (1,true),
.last 17 (1,true),
.cycle 78 5 false (2),
.cycle 7 11 true (3),
.cycle 6 11 true (2),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 7 12 true (3),
.cycle 8 9 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part580_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part580) = true := by rfl

def kid11_part581 : Audit := .cycle 8 8 true (3)
theorem kid11_part581_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part581) = true := by rfl

def kid11_part582 : Audit := .cycle 6 12 true (2)
theorem kid11_part582_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part582) = true := by rfl

def kid11_part583 : Audit := .cycle 6 20 true (2)
theorem kid11_part583_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part583) = true := by rfl

def kid11_part584 : Audit := .cycle 29 1 false (1)
theorem kid11_part584_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part584) = true := by rfl

def kid11_part585 : Audit := .cycle 22 1 false (0)
theorem kid11_part585_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part585) = true := by rfl

def kid11_part586 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 0 23 true (0),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 6 20 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part586_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part586) = true := by rfl

def kid11_part587 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 36 1 false (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 18 true (2),
.cycle 6 15 true (2),
.cycle 6 18 true (2),
.cycle 1 22 true (1),
.last 16 (0,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 6 20 true (2),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part587_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part587) = true := by rfl

def kid11_part588 : Audit := .cycle 6 18 true (2)
theorem kid11_part588_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part588) = true := by rfl

def kid11_part589 : Audit := .cycle 8 6 true (3)
theorem kid11_part589_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part589) = true := by rfl

def kid11_part590 : Audit := .cycle 7 6 true (3)
theorem kid11_part590_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part590) = true := by rfl

def kid11_part591 : Audit := .cycle 6 18 true (2)
theorem kid11_part591_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part591) = true := by rfl

def kid11_part592 : Audit := .split 14 (1,true) (byMove [
.last 15 (0,true),
.cycle 15 17 false (3),
.last 16 (0,true),
.cycle 6 20 true (2),
.cycle 6 20 true (2),
.cycle 8 10 true (3),
.last 15 (0,true),
.cycle 1 15 true (1),
.cycle 6 18 true (2),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 6 18 true (2),
.last 15 (0,true),
.last 21 (0,true),
.last 16 (0,true),
.cycle 5 10 true (1),
.cycle 6 10 true (2),
.cycle 11 4 true (3),
.last 15 (0,true),
.cycle 1 15 true (1),
.last 16 (0,true),
.cycle 8 8 true (3),
.cycle 7 8 true (3),
.cycle 6 16 true (2)
])
theorem kid11_part592_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part592) = true := by rfl

def kid11_part593 : Audit := .split 15 (1,true) (byMove [
.last 16 (0,true),
.cycle 121 80 false (7),
.cycle 23 1 false (-1),
.cycle 6 30 true (2),
.cycle 62 1 false (0),
.cycle 7 12 true (2),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 12 4 true (3),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 6 26 true (2),
.last 16 (0,true),
.cycle 18 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 31 1 false (-1),
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 14 2 true (3),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 6 22 true (2)
])
theorem kid11_part593_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part593) = true := by rfl

def kid11_part594 : Audit := .cycle 7 8 true (3)
theorem kid11_part594_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part594) = true := by rfl

def kid11_part595 : Audit := .cycle 6 10 true (2)
theorem kid11_part595_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part595) = true := by rfl

def kid11_part596 : Audit := .cycle 6 22 true (2)
theorem kid11_part596_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part596) = true := by rfl

def kid11_part597 : Audit := .cycle 22 1 false (0)
theorem kid11_part597_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part597) = true := by rfl

def kid11_part598 : Audit := .split 13 (0,true) (byMove [
.cycle 0 15 true (0),
.last 14 (1,true),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 6 17 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part598_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part598) = true := by rfl

def kid11_part599 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 1 14 true (1),
.cycle 1 14 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 6 17 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 14 (0,true),
.cycle 20 5 false (2),
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part599_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part599) = true := by rfl

def kid11_part600 : Audit := .cycle 2 12 true (1)
theorem kid11_part600_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part600) = true := by rfl

def kid11_part601 : Audit := .cycle 8 6 true (3)
theorem kid11_part601_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part601) = true := by rfl

def kid11_part602 : Audit := .cycle 7 6 true (3)
theorem kid11_part602_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part602) = true := by rfl

def kid11_part603 : Audit := .cycle 6 14 true (2)
theorem kid11_part603_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part603) = true := by rfl

def kid11_part579 : Audit := .split 12 (2,true) (byMove [(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585),(kid11_part586),(kid11_part587),(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part602),(kid11_part603)])

theorem kid11_part579_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part579) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585),(kid11_part586),(kid11_part587),(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part602),(kid11_part603)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part580_checked

  · exact kid11_part586_checked

  · exact kid11_part592_checked

  · exact kid11_part598_checked

  · exact kid11_part581_checked

  · exact kid11_part587_checked

  · exact kid11_part593_checked

  · exact kid11_part599_checked

  · exact kid11_part582_checked

  · exact kid11_part588_checked

  · exact kid11_part594_checked

  · exact kid11_part600_checked

  · exact kid11_part583_checked

  · exact kid11_part589_checked

  · exact kid11_part595_checked

  · exact kid11_part601_checked

  · exact kid11_part584_checked

  · exact kid11_part590_checked

  · exact kid11_part596_checked

  · exact kid11_part602_checked

  · exact kid11_part585_checked

  · exact kid11_part591_checked

  · exact kid11_part597_checked

  · exact kid11_part603_checked

def kid11_part604 : Audit := .cycle 7 6 true (3)
theorem kid11_part604_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part604) = true := by rfl

def kid11_part605 : Audit := .cycle 6 6 true (2)
theorem kid11_part605_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part605) = true := by rfl

def kid11_part606 : Audit := .cycle 53 1 false (9)
theorem kid11_part606_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part606) = true := by rfl

def kid11_part608 : Audit := .split 65 (1,true) (byMove [
.cycle 0 74 false (7),
.cycle 0 144 false (7),
.last 66 (2,true),
.cycle 0 90 false (8),
.cycle 0 90 false (8),
.cycle 0 74 false (7),
.last 69 (2,true),
.cycle 72 12 true (7),
.last 66 (2,true),
.last 75 (2,true),
.last 75 (2,true),
.cycle 0 84 false (8),
.cycle 0 74 false (7),
.last 75 (2,true),
.last 66 (2,true),
.cycle 0 84 false (9),
.cycle 0 84 false (9),
.cycle 0 74 false (7),
.cycle 0 76 false (7),
.cycle 0 92 false (12),
.last 66 (2,true),
.cycle 0 82 false (9),
.cycle 0 82 false (9),
.cycle 0 76 false (7)
])
theorem kid11_part608_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part608) = true := by rfl

def kid11_part609 : Audit := .split 13 (1,true) (byMove [
.cycle 0 30 false (5),
.cycle 26 66 false (4),
.last 14 (2,true),
.cycle 60 1 false (-2),
.cycle 61 1 false (-1),
.cycle 13 3 false (1),
.cycle 14 10 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.cycle 5 22 true (1),
.cycle 44 1 false (0),
.cycle 13 16 false (3),
.last 16 (2,true),
.last 14 (2,true),
.cycle 6 16 true (0),
.cycle 6 16 true (0),
.cycle 13 3 false (1),
.cycle 0 20 true (0),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 6 12 true (1),
.cycle 108 7 false (0)
])
theorem kid11_part609_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part609) = true := by rfl

def kid11_part610 : Audit := .split 13 (2,true) (byMove [
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 20 (1,true),
.last 20 (1,true),
.last 16 (1,true),
.last 15 (1,true),
.last 16 (1,true),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.last 17 (1,true),
.last 18 (1,true),
.cycle 16 1 false (0),
.last 14 (1,true),
.last 21 (1,true),
.last 19 (1,true),
.last 19 (1,true),
.last 16 (1,true),
.last 15 (1,true),
.last 16 (1,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.last 17 (1,true),
.cycle 18 1 false (0)
])
theorem kid11_part610_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part610) = true := by rfl

def kid11_part611 : Audit := .split 17 (1,true) (byMove [
.cycle 25 1 false (-1),
.cycle 17 34 false (3),
.last 18 (2,true),
.cycle 8 21 true (1),
.cycle 7 21 true (1),
.cycle 27 1 false (-1),
.cycle 0 26 true (0),
.cycle 1 19 true (1),
.last 18 (2,true),
.cycle 14 14 true (2),
.cycle 14 14 true (2),
.cycle 9 15 true (1),
.cycle 12 6 true (1),
.last 22 (2,true),
.last 18 (2,true),
.cycle 6 14 true (1),
.cycle 6 14 true (1),
.cycle 27 1 false (-1),
.cycle 0 24 true (0),
.cycle 1 19 true (1),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 18 15 true (2)
])
theorem kid11_part611_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part611) = true := by rfl

def kid11_part612 : Audit := .split 17 (1,true) (byMove [
.cycle 26 1 false (0),
.cycle 17 34 false (3),
.last 18 (2,true),
.cycle 8 21 true (1),
.cycle 7 21 true (1),
.cycle 28 1 false (0),
.cycle 36 1 false (0),
.cycle 1 19 true (1),
.last 18 (2,true),
.cycle 6 32 true (0),
.cycle 6 32 true (0),
.cycle 9 15 true (1),
.cycle 12 6 true (1),
.last 22 (2,true),
.last 18 (2,true),
.cycle 6 14 true (1),
.cycle 6 14 true (1),
.cycle 28 1 false (0),
.cycle 0 24 true (0),
.cycle 1 19 true (1),
.last 18 (2,true),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 18 15 true (2)
])
theorem kid11_part612_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part612) = true := by rfl

def kid11_part613 : Audit := .cycle 15 1 false (-1)
theorem kid11_part613_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part613) = true := by rfl

def kid11_part614 : Audit := .cycle 0 16 true (0)
theorem kid11_part614_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part614) = true := by rfl

def kid11_part615 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.cycle 8 19 true (1),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 9 11 true (2),
.cycle 12 4 true (2),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 6 14 true (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 16 7 true (4)
])
theorem kid11_part615_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part615) = true := by rfl

def kid11_part616 : Audit := .split 13 (2,true) (byMove [
.last 25 (1,true),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.last 20 (1,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 6 22 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 16 (1,true),
.last 15 (1,true),
.last 16 (1,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.last 17 (1,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 23 (1,true)
])
theorem kid11_part616_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part616) = true := by rfl

def kid11_part617 : Audit := .cycle 5 8 true (1)
theorem kid11_part617_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part617) = true := by rfl

def kid11_part618 : Audit := .cycle 6 8 true (2)
theorem kid11_part618_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part618) = true := by rfl

def kid11_part619 : Audit := .split 15 (1,true) (byMove [
.cycle 25 1 false (1),
.cycle 15 32 false (3),
.last 16 (2,true),
.cycle 8 19 true (2),
.cycle 7 19 true (2),
.cycle 23 3 false (1),
.cycle 0 20 true (0),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 9 13 true (2),
.cycle 12 4 true (2),
.last 20 (2,true),
.last 16 (2,true),
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 23 3 false (1),
.cycle 0 20 true (0),
.cycle 1 17 true (1),
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 16 11 true (3)
])
theorem kid11_part619_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part619) = true := by rfl

def kid11_part620 : Audit := .split 16 (1,true) (byMove [
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 56, 64],[56, 56, 64, 16, 16, 56, 64],64⟩,
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 15 3 false (0),
.cycle 0 32 true (-1),
.cycle 17 19 true (1),
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[24, 8, 64, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[32, 32, 64, 16, 16, 32, 64],64⟩,
.cycle 14 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (0),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 2, 64],[2, 2, 64, 16, 16, 2, 64],64⟩,
.last 17 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[24, 8, 64, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 16, 64],64⟩,
.cycle 13 5 false (1)
])
theorem kid11_part620_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part620) = true := by rfl

def kid11_part621 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.cycle 1 63 false (7),
.last 14 (2,true),
.cycle 8 27 true (0),
.cycle 7 27 true (0),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.last 14 (2,true),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 9 17 true (1),
.last 16 (2,true),
.last 16 (2,true),
.last 14 (2,true),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 13 3 false (1),
.cycle 12 2 true (1),
.cycle 1 17 true (1),
.last 14 (2,true),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.last 20 (2,true)
])
theorem kid11_part621_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part621) = true := by rfl

def kid11_part622 : Audit := .split 13 (2,true) (byMove [
.last 20 (1,true),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 18 (1,true),
.last 18 (1,true),
.last 16 (1,true),
.cycle 6 12 true (1),
.last 14 (1,true),
.cycle 6 26 true (0),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.last 16 (1,true),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16777216, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 16777216, 1024, 1024, 16777216, 16777216, 16777216, 65536, 65536, 65536, 65536, 1024, 16777216, 16777216, 1024, 1024, 16777216, 1024, 16777216, 16777216, 1024, 1024, 16777216, 16777216],22719870⟩,
.last 14 (1,true),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16842752, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 1024, 1024, 1024, 16777216, 65536, 16777216, 65536, 65536, 65536, 65536, 1024, 16777216, 1024, 1024, 1024, 1024, 1024, 16777216, 1024, 1024, 1024, 16777216, 16777216],22719870⟩,
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.last 16 (1,true),
.cycle 12 2 true (1),
.last 14 (1,true),
.cycle 2 16 true (1),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16842752, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 2048, 1024, 1024, 16777216, 65536, 16777216, 131072, 65536, 65536, 65536, 1024, 16777216, 2048, 1024, 1024, 1024, 1024, 16777216, 2048, 1024, 1024, 16777216, 16777216],22719870⟩
])
theorem kid11_part622_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part622) = true := by rfl

def kid11_part623 : Audit := .cycle 6 10 true (1)
theorem kid11_part623_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part623) = true := by rfl

def kid11_part624 : Audit := .cycle 6 10 true (1)
theorem kid11_part624_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part624) = true := by rfl

def kid11_part625 : Audit := .cycle 15 1 false (-1)
theorem kid11_part625_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part625) = true := by rfl

def kid11_part626 : Audit := .cycle 0 16 true (0)
theorem kid11_part626_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part626) = true := by rfl

def kid11_part627 : Audit := .split 13 (1,true) (byMove [
.last 16 (2,true),
.cycle 13 30 false (3),
.last 14 (2,true),
.cycle 8 17 true (2),
.cycle 7 17 true (2),
.cycle 19 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 9 11 true (2),
.cycle 12 2 true (2),
.last 18 (2,true),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 19 3 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part627_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part627) = true := by rfl

def kid11_part628 : Audit := .split 13 (2,true) (byMove [
.cycle 7 10 true (2),
.last 14 (1,true),
.cycle 18 1 false (0),
.last 18 (1,true),
.last 18 (1,true),
.last 22 (1,true),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 6 20 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 16 (1,true),
.cycle 12 2 true (2),
.last 14 (1,true),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16842752, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[256, 16777216, 1024, 1024, 1024, 16777216, 16384, 16777216, 65536, 65536, 65536, 65536, 256, 16777216, 1024, 1024, 1024, 1024, 256, 16777216, 1024, 1024, 1024, 16777216, 16777216],22719870⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 22 (1,true),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part628_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part628) = true := by rfl

def kid11_part629 : Audit := .cycle 5 8 true (1)
theorem kid11_part629_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part629) = true := by rfl

def kid11_part630 : Audit := .cycle 6 8 true (2)
theorem kid11_part630_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part630) = true := by rfl

def kid11_part631 : Audit := .cycle 11 2 true (2)
theorem kid11_part631_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part631) = true := by rfl

def kid11_part607 : Audit := .split 12 (0,true) (byMove [(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614),(kid11_part615),(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631)])

theorem kid11_part607_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part607) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (0,true) (some mv)) (byMove [(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614),(kid11_part615),(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part608_checked

  · exact kid11_part614_checked

  · exact kid11_part620_checked

  · exact kid11_part626_checked

  · exact kid11_part609_checked

  · exact kid11_part615_checked

  · exact kid11_part621_checked

  · exact kid11_part627_checked

  · exact kid11_part610_checked

  · exact kid11_part616_checked

  · exact kid11_part622_checked

  · exact kid11_part628_checked

  · exact kid11_part611_checked

  · exact kid11_part617_checked

  · exact kid11_part623_checked

  · exact kid11_part629_checked

  · exact kid11_part612_checked

  · exact kid11_part618_checked

  · exact kid11_part624_checked

  · exact kid11_part630_checked

  · exact kid11_part613_checked

  · exact kid11_part619_checked

  · exact kid11_part625_checked

  · exact kid11_part631_checked

def kid11_part633 : Audit := .split 13 (0,true) (byMove [
.last 65 (2,true),
.cycle 0 190 false (9),
.last 14 (2,true),
.last 20 (2,true),
.last 20 (2,true),
.last 16 (2,true),
.cycle 0 23 true (0),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.last 17 (2,true),
.last 18 (2,true),
.cycle 14 3 false (0),
.last 17 (2,true),
.last 14 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.last 16 (2,true),
.cycle 0 23 true (0),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.last 17 (2,true),
.last 19 (2,true)
])
theorem kid11_part633_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part633) = true := by rfl

def kid11_part634 : Audit := .split 25 (2,true) (byMove [
.last 26 (0,true),
.cycle 26 66 false (4),
.cycle 31 1 false (-1),
.cycle 37 82 false (7),
.cycle 36 82 false (7),
.cycle 11 15 false (3),
.last 26 (0,true),
.cycle 23 10 true (2),
.cycle 135 88 false (5),
.cycle 165 104 false (7),
.cycle 165 104 false (7),
.cycle 32 76 false (7),
.last 26 (0,true),
.cycle 61 66 false (3),
.cycle 135 90 false (3),
.cycle 113 76 false (3),
.cycle 113 76 false (3),
.cycle 11 15 false (3),
.last 26 (0,true),
.cycle 26 68 false (4),
.cycle 123 82 false (5),
.cycle 109 74 false (3),
.cycle 109 74 false (3),
.cycle 26 68 false (5)
])
theorem kid11_part634_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part634) = true := by rfl

def kid11_part635 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 60 1 false (-2),
.cycle 61 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 23 true (0),
.cycle 6 16 true (1),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.cycle 6 26 true (1),
.cycle 44 1 false (0),
.last 14 (0,true),
.cycle 16 1 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 48, 16, 16, 16, 16, 64],64⟩,
.cycle 6 16 true (0),
.cycle 6 16 true (0),
.cycle 13 3 false (1),
.cycle 0 23 true (0),
.cycle 1 19 true (1),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 6 12 true (1),
.cycle 18 1 false (0)
])
theorem kid11_part635_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part635) = true := by rfl

def kid11_part636 : Audit := .split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 25 1 false (-1),
.cycle 22 1 false (0),
.cycle 8 21 true (1),
.cycle 7 21 true (1),
.cycle 27 1 false (-1),
.last 18 (0,true),
.cycle 1 25 true (1),
.cycle 6 24 true (1),
.cycle 14 14 true (2),
.cycle 14 14 true (2),
.cycle 9 15 true (1),
.last 18 (0,true),
.cycle 12 6 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 14 true (1),
.cycle 6 14 true (1),
.cycle 27 1 false (-1),
.last 18 (0,true),
.cycle 1 23 true (1),
.cycle 2 18 true (1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 18 15 true (2)
])
theorem kid11_part636_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part636) = true := by rfl

def kid11_part637 : Audit := .split 17 (2,true) (byMove [
.last 18 (0,true),
.cycle 26 1 false (0),
.cycle 22 1 false (0),
.cycle 8 21 true (1),
.cycle 7 21 true (1),
.cycle 28 1 false (0),
.last 18 (0,true),
.cycle 36 1 false (0),
.cycle 6 24 true (1),
.cycle 6 32 true (0),
.cycle 6 32 true (0),
.cycle 9 15 true (1),
.last 18 (0,true),
.cycle 12 6 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 48, 16, 16, 16, 16, 64],64⟩,
.cycle 6 14 true (1),
.cycle 6 14 true (1),
.cycle 28 1 false (0),
.last 18 (0,true),
.cycle 1 23 true (1),
.cycle 2 18 true (1),
.cycle 7 12 true (1),
.cycle 6 12 true (1),
.cycle 18 15 true (2)
])
theorem kid11_part637_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part637) = true := by rfl

def kid11_part638 : Audit := .cycle 15 1 false (-1)
theorem kid11_part638_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part638) = true := by rfl

def kid11_part639 : Audit := .split 13 (0,true) (byMove [
.last 16 (2,true),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.last 20 (2,true),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 16 (2,true),
.cycle 0 22 true (0),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.last 17 (2,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 23 (2,true)
])
theorem kid11_part639_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part639) = true := by rfl

def kid11_part640 : Audit := .cycle 1 15 true (1)
theorem kid11_part640_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part640) = true := by rfl

def kid11_part641 : Audit := .split 13 (2,true) (byMove [
.last 17 (0,true),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.cycle 8 19 true (1),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 6 22 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 9 11 true (2),
.cycle 6 22 true (2),
.cycle 12 4 true (2),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 6 14 true (2),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 16 7 true (4)
])
theorem kid11_part641_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part641) = true := by rfl

def kid11_part642 : Audit := .cycle 5 8 true (1)
theorem kid11_part642_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part642) = true := by rfl

def kid11_part643 : Audit := .cycle 6 8 true (2)
theorem kid11_part643_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part643) = true := by rfl

def kid11_part644 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 8 19 true (2),
.cycle 7 19 true (2),
.cycle 23 3 false (1),
.last 16 (0,true),
.cycle 1 19 true (1),
.cycle 6 22 true (2),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 9 13 true (2),
.last 16 (0,true),
.cycle 12 4 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 32, 16, 16, 16, 16, 64],64⟩,
.cycle 6 12 true (2),
.cycle 6 12 true (2),
.cycle 23 3 false (1),
.last 16 (0,true),
.cycle 1 19 true (1),
.cycle 2 16 true (1),
.cycle 7 10 true (2),
.cycle 6 10 true (2),
.cycle 16 11 true (3)
])
theorem kid11_part644_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part644) = true := by rfl

def kid11_part645 : Audit := .split 13 (0,true) (byMove [
.cycle 6 14 true (-1),
.last 24 (2,true),
.last 14 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.cycle 0 18 true (0),
.cycle 12 4 true (1),
.last 14 (2,true),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.last 16 (2,true),
.cycle 14 3 false (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.last 16 (2,true),
.cycle 0 18 true (0),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part645_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part645) = true := by rfl

def kid11_part646 : Audit := .split 16 (2,true) (byMove [
.last 17 (0,true),
.cycle 14 3 false (0),
.cycle 19 1 false (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.cycle 15 3 false (0),
.last 17 (0,true),
.cycle 17 27 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 32, 64],[64, 32, 32, 16, 16, 32, 64],64⟩,
.last 17 (0,true),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 15 3 false (0),
.last 17 (0,true),
.cycle 12 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[64, 4, 4, 16, 16, 4, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 24, 8, 16, 16, 24, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 13 5 false (1)
])
theorem kid11_part646_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part646) = true := by rfl

def kid11_part647 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 18 60 false (6),
.cycle 16 1 false (0),
.cycle 8 27 true (0),
.cycle 7 27 true (0),
.cycle 13 3 false (1),
.last 14 (0,true),
.cycle 6 12 true (1),
.cycle 6 26 true (0),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 9 17 true (1),
.last 14 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 13 3 false (1),
.last 14 (0,true),
.cycle 12 2 true (1),
.cycle 2 16 true (1),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 48, 64],[64, 48, 32, 16, 16, 48, 64],64⟩
])
theorem kid11_part647_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part647) = true := by rfl

def kid11_part648 : Audit := .cycle 6 10 true (1)
theorem kid11_part648_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part648) = true := by rfl

def kid11_part649 : Audit := .cycle 6 10 true (1)
theorem kid11_part649_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part649) = true := by rfl

def kid11_part650 : Audit := .cycle 15 1 false (-1)
theorem kid11_part650_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part650) = true := by rfl

def kid11_part651 : Audit := .split 13 (0,true) (byMove [
.last 28 (2,true),
.cycle 0 19 true (0),
.last 14 (2,true),
.last 18 (2,true),
.last 18 (2,true),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.last 16 (2,true),
.cycle 14 5 false (2),
.cycle 12 2 true (2),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.last 22 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part651_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part651) = true := by rfl

def kid11_part652 : Audit := .cycle 1 15 true (1)
theorem kid11_part652_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part652) = true := by rfl

def kid11_part653 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 7 10 true (2),
.cycle 18 1 false (0),
.cycle 8 17 true (2),
.cycle 7 17 true (2),
.cycle 19 3 false (1),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 6 20 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 9 11 true (2),
.last 14 (0,true),
.cycle 12 2 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 4, 16, 16, 16, 16, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 19 3 false (1),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part653_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part653) = true := by rfl

def kid11_part654 : Audit := .cycle 5 8 true (1)
theorem kid11_part654_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part654) = true := by rfl

def kid11_part655 : Audit := .cycle 6 8 true (2)
theorem kid11_part655_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part655) = true := by rfl

def kid11_part656 : Audit := .cycle 11 2 true (2)
theorem kid11_part656_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part656) = true := by rfl

def kid11_part632 : Audit := .split 12 (1,true) (byMove [(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655),(kid11_part656)])

theorem kid11_part632_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part632) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655),(kid11_part656)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part633_checked

  · exact kid11_part639_checked

  · exact kid11_part645_checked

  · exact kid11_part651_checked

  · exact kid11_part634_checked

  · exact kid11_part640_checked

  · exact kid11_part646_checked

  · exact kid11_part652_checked

  · exact kid11_part635_checked

  · exact kid11_part641_checked

  · exact kid11_part647_checked

  · exact kid11_part653_checked

  · exact kid11_part636_checked

  · exact kid11_part642_checked

  · exact kid11_part648_checked

  · exact kid11_part654_checked

  · exact kid11_part637_checked

  · exact kid11_part643_checked

  · exact kid11_part649_checked

  · exact kid11_part655_checked

  · exact kid11_part638_checked

  · exact kid11_part644_checked

  · exact kid11_part650_checked

  · exact kid11_part656_checked

def kid11_part658 : Audit := .split 13 (0,true) (byMove [
.cycle 64 12 true (4),
.last 14 (1,true),
.cycle 37 1 false (-1),
.cycle 39 1 false (-1),
.cycle 40 1 false (0),
.cycle 37 1 false (-1),
.last 15 (1,true),
.cycle 1 22 true (1),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.cycle 5 12 true (1),
.cycle 35 1 false (1),
.last 16 (1,true),
.last 14 (1,true),
.cycle 12 5 false (2),
.cycle 15 16 true (1),
.cycle 16 16 true (2),
.cycle 68 1 false (-2),
.last 15 (1,true),
.cycle 1 22 true (1),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 5 12 true (1),
.cycle 12 7 false (2)
])
theorem kid11_part658_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part658) = true := by rfl

def kid11_part659 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 144 92 false (4),
.cycle 16 18 true (-1),
.cycle 39 1 false (-1),
.cycle 40 1 false (0),
.cycle 37 1 false (-1),
.last 16 (0,true),
.cycle 1 22 true (1),
.cycle 5 10 true (1),
.cycle 6 14 true (0),
.cycle 5 12 true (1),
.cycle 35 1 false (1),
.last 14 (0,true),
.cycle 14 3 false (0),
.cycle 16 14 true (0),
.cycle 15 16 true (1),
.cycle 16 16 true (2),
.cycle 86 1 false (-2),
.last 16 (0,true),
.cycle 1 22 true (1),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 5 12 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 32, 24, 16, 16, 16, 64],64⟩
])
theorem kid11_part659_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part659) = true := by rfl

def kid11_part660 : Audit := .cycle 16 1 false (0)
theorem kid11_part660_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part660) = true := by rfl

def kid11_part661 : Audit := .cycle 5 12 true (1)
theorem kid11_part661_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part661) = true := by rfl

def kid11_part662 : Audit := .cycle 5 12 true (1)
theorem kid11_part662_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part662) = true := by rfl

def kid11_part663 : Audit := .cycle 15 1 false (-1)
theorem kid11_part663_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part663) = true := by rfl

def kid11_part664 : Audit := .split 13 (0,true) (byMove [
.cycle 0 18 true (0),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.cycle 16 16 true (2),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 6 22 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 10 true (2),
.last 15 (1,true),
.cycle 0 22 true (0),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 5 12 true (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 17 true (2)
])
theorem kid11_part664_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part664) = true := by rfl

def kid11_part665 : Audit := .split 13 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 7 10 true (2),
.cycle 6 14 true (1),
.cycle 16 16 true (2),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 6 22 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 10 true (2),
.last 16 (0,true),
.cycle 1 21 true (1),
.cycle 5 10 true (1),
.cycle 6 12 true (1),
.cycle 5 12 true (1),
.cycle 18 1 false (0),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 17 true (2)
])
theorem kid11_part665_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part665) = true := by rfl

def kid11_part666 : Audit := .cycle 6 22 true (1)
theorem kid11_part666_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part666) = true := by rfl

def kid11_part667 : Audit := .cycle 5 8 true (1)
theorem kid11_part667_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part667) = true := by rfl

def kid11_part668 : Audit := .cycle 6 8 true (2)
theorem kid11_part668_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part668) = true := by rfl

def kid11_part669 : Audit := .cycle 5 10 true (1)
theorem kid11_part669_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part669) = true := by rfl

def kid11_part670 : Audit := .split 13 (0,true) (byMove [
.cycle 6 14 true (-1),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 6 16 true (-1),
.cycle 0 18 true (0),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 6 12 true (1),
.last 16 (1,true),
.last 14 (1,true),
.last 16 (1,true),
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 31 1 false (-1),
.cycle 0 18 true (0),
.last 14 (1,true),
.cycle 12 2 true (1),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.last 20 (1,true)
])
theorem kid11_part670_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part670) = true := by rfl

def kid11_part671 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 1 218 false (15),
.cycle 19 1 false (-1),
.cycle 6 14 true (0),
.cycle 6 14 true (0),
.cycle 6 16 true (-1),
.last 14 (0,true),
.cycle 1 17 true (1),
.cycle 12 4 true (1),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 6 12 true (1),
.last 14 (0,true),
.cycle 14 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 16, 64],64⟩,
.cycle 6 12 true (0),
.cycle 6 12 true (0),
.cycle 31 1 false (-1),
.last 14 (0,true),
.cycle 1 17 true (1),
.cycle 12 2 true (1),
.cycle 6 10 true (1),
.cycle 6 10 true (1),
.cycle 15 5 false (1)
])
theorem kid11_part671_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part671) = true := by rfl

def kid11_part672 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 64, 16, 16, 16, 16, 64],64⟩
theorem kid11_part672_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part672) = true := by rfl

def kid11_part673 : Audit := .cycle 6 10 true (1)
theorem kid11_part673_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part673) = true := by rfl

def kid11_part674 : Audit := .cycle 6 10 true (1)
theorem kid11_part674_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part674) = true := by rfl

def kid11_part675 : Audit := .cycle 15 1 false (-1)
theorem kid11_part675_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part675) = true := by rfl

def kid11_part676 : Audit := .split 13 (0,true) (byMove [
.cycle 27 12 true (3),
.last 14 (1,true),
.last 16 (1,true),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.cycle 31 14 true (3),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 6 16 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 10 true (2),
.last 18 (1,true),
.last 14 (1,true),
.cycle 12 2 true (2),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 1, 16, 16, 16, 64],64⟩,
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part676_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part676) = true := by rfl

def kid11_part677 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 129 56 false (3),
.cycle 1 18 true (1),
.cycle 7 12 true (2),
.cycle 7 12 true (2),
.cycle 31 14 true (3),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 7 10 true (2),
.last 14 (0,true),
.cycle 14 5 false (2),
.cycle 12 2 true (2),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 2, 16, 16, 16, 64],64⟩,
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 8 true (2),
.cycle 6 8 true (2),
.cycle 14 7 true (3)
])
theorem kid11_part677_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part677) = true := by rfl

def kid11_part678 : Audit := .cycle 2 14 true (1)
theorem kid11_part678_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part678) = true := by rfl

def kid11_part679 : Audit := .cycle 5 8 true (1)
theorem kid11_part679_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part679) = true := by rfl

def kid11_part680 : Audit := .cycle 6 8 true (2)
theorem kid11_part680_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part680) = true := by rfl

def kid11_part681 : Audit := .cycle 11 2 true (2)
theorem kid11_part681_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part681) = true := by rfl

def kid11_part657 : Audit := .split 12 (2,true) (byMove [(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668),(kid11_part669),(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681)])

theorem kid11_part657_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part657) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668),(kid11_part669),(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part658_checked

  · exact kid11_part664_checked

  · exact kid11_part670_checked

  · exact kid11_part676_checked

  · exact kid11_part659_checked

  · exact kid11_part665_checked

  · exact kid11_part671_checked

  · exact kid11_part677_checked

  · exact kid11_part660_checked

  · exact kid11_part666_checked

  · exact kid11_part672_checked

  · exact kid11_part678_checked

  · exact kid11_part661_checked

  · exact kid11_part667_checked

  · exact kid11_part673_checked

  · exact kid11_part679_checked

  · exact kid11_part662_checked

  · exact kid11_part668_checked

  · exact kid11_part674_checked

  · exact kid11_part680_checked

  · exact kid11_part663_checked

  · exact kid11_part669_checked

  · exact kid11_part675_checked

  · exact kid11_part681_checked

def kid11_part682 : Audit := .cycle 6 8 true (2)
theorem kid11_part682_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part682) = true := by rfl

def kid11_part683 : Audit := .cycle 6 8 true (2)
theorem kid11_part683_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part683) = true := by rfl

def kid11_part684 : Audit := .cycle 15 1 false (-1)
theorem kid11_part684_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part684) = true := by rfl

def kid11_part686 : Audit := .cycle 0 17 false (5)
theorem kid11_part686_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,0⟩)) (kid11_part686) = true := by rfl

def kid11_part687 : Audit := .split 13 (1,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 1024, 32, 427456, 128, 256, 32768, 1024, 131072, 163968, 128, 256, 8, 1024, 32, 1344, 262144],[32768, 256, 262144, 1024, 1024, 64, 163968, 1344, 262144, 1024, 1024, 64, 32768, 256, 262144, 1024, 1024, 64, 262144],327728⟩,
.cycle 14 15 false (3),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.last 17 (2,true),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 29 1 false (1),
.cycle 15 20 false (5),
.last 18 (2,true),
.last 14 (2,true),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 10 4 true (3)
])
theorem kid11_part687_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,1⟩)) (kid11_part687) = true := by rfl

def kid11_part688 : Audit := .split 13 (2,true) (byMove [
.cycle 18 1 false (0),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.cycle 0 19 true (0),
.last 15 (1,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 0 16 true (0),
.cycle 29 1 false (1),
.cycle 18 1 false (0),
.last 14 (1,true),
.cycle 19 26 true (1),
.cycle 0 18 true (0),
.cycle 0 18 true (0),
.cycle 23 1 false (-1),
.last 15 (1,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 10 4 true (3)
])
theorem kid11_part688_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,2⟩)) (kid11_part688) = true := by rfl

def kid11_part689 : Audit := .cycle 0 16 true (0)
theorem kid11_part689_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,3⟩)) (kid11_part689) = true := by rfl

def kid11_part690 : Audit := .cycle 0 16 true (0)
theorem kid11_part690_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (kid11_part690) = true := by rfl

def kid11_part691 : Audit := .split 15 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 16 19 false (4),
.last 16 (2,true),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 7 18 true (3),
.cycle 9 7 true (3),
.cycle 12 4 true (3),
.last 22 (2,true),
.last 16 (2,true),
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 0 19 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part691_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,5⟩)) (kid11_part691) = true := by rfl

def kid11_part692 : Audit := .cycle 0 14 true (0)
theorem kid11_part692_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,0⟩)) (kid11_part692) = true := by rfl

def kid11_part693 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 0 21 true (0),
.cycle 12 4 true (4),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part693_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,1⟩)) (kid11_part693) = true := by rfl

def kid11_part694 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 17 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 0 21 true (0),
.last 15 (1,true),
.last 16 (1,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 0 16 true (0),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 17 true (2)
])
theorem kid11_part694_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,2⟩)) (kid11_part694) = true := by rfl

def kid11_part695 : Audit := .cycle 8 6 true (3)
theorem kid11_part695_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,3⟩)) (kid11_part695) = true := by rfl

def kid11_part696 : Audit := .cycle 7 6 true (3)
theorem kid11_part696_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (kid11_part696) = true := by rfl

def kid11_part697 : Audit := .cycle 0 14 true (0)
theorem kid11_part697_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,5⟩)) (kid11_part697) = true := by rfl

def kid11_part698 : Audit := .split 18 (1,true) (byMove [
.cycle 16 3 false (0),
.far false 5 ⟨0,[0, 1, 2, 3, 2, 4, 2, 3, 4, 4],[128, 256, 8, 0, 32, 0, 524288, 1048576, 32768, 4194304, 131072, 4194304, 33554432, 67108864, 32768, 4194304, 131072, 4194304, 524288, 1048576, 32768, 4194304, 131072, 4194304, 33554432, 67108864, 134217728, 268435456, 536870912, 2135031808, 1073741824],[4194304, 32768, 1073741824, 1024, 1024, 64, 4194304, 4194304, 1073741824, 4194304, 4194304, 262144, 2135031808, 134250496, 1073741824, 268435456, 268435456, 16777216, 4194304, 4325376, 1073741824, 4194304, 4194304, 262144, 2135031808, 2135031808, 1073741824, 268435456, 268435456, 16777216, 1073741824],2130718720⟩,
.last 19 (2,true),
.cycle 15 58 true (-1),
.cycle 15 58 true (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1024, 32, 128, 128, 256, 8, 1024, 32, 128, 4096],[128, 256, 4096, 1024, 1024, 64, 128, 128, 4096, 1024, 1024, 64, 4096],4096⟩,
.cycle 0 34 true (-1),
.cycle 19 21 true (1),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[24, 8, 64, 16, 16, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 1, 64],64⟩,
.cycle 15 46 true (-1),
.cycle 16 3 false (0),
.last 21 (2,true),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 17, 64],[17, 17, 64, 16, 16, 1, 64],64⟩,
.cycle 15 5 false (1),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 2, 64],[2, 2, 64, 16, 16, 1, 64],64⟩,
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[24, 8, 64, 16, 16, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 16, 64, 16, 16, 1, 64],64⟩,
.cycle 13 7 false (3)
])
theorem kid11_part698_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,0⟩)) (kid11_part698) = true := by rfl

def kid11_part699 : Audit := .split 13 (1,true) (byMove [
.last 18 (2,true),
.cycle 105 70 false (7),
.last 14 (2,true),
.cycle 0 24 true (0),
.cycle 48 1 false (0),
.cycle 0 21 true (0),
.last 16 (2,true),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 18 true (0),
.last 18 (2,true),
.last 18 (2,true),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.cycle 12 2 true (3),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 18 true (0)
])
theorem kid11_part699_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,1⟩)) (kid11_part699) = true := by rfl

def kid11_part700 : Audit := .split 13 (2,true) (byMove [
.last 22 (1,true),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 0 24 true (0),
.cycle 48 1 false (0),
.last 16 (1,true),
.cycle 7 10 true (3),
.last 14 (1,true),
.cycle 6 20 true (2),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 18 true (0),
.far false 4 ⟨0,[0, 1, 0, 2, 3, 1, 0, 1],[128, 256, 8, 66560, 32, 16843776, 8192, 16384, 8, 65536, 32, 16777216, 128, 256, 2097152, 1024, 8388608, 1024, 128, 256, 8, 65536, 32, 65536, 16777216],[1024, 16777216, 16777216, 1024, 1024, 64, 16777216, 16777216, 65536, 65536, 65536, 4096, 1024, 16777216, 16777216, 1024, 1024, 64, 1024, 16777216, 16777216, 1024, 1024, 64, 16777216],22719870⟩,
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[16, 64, 16, 16, 16, 1, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.cycle 12 2 true (3),
.last 14 (1,true),
.cycle 2 14 true (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 18 true (0)
])
theorem kid11_part700_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,2⟩)) (kid11_part700) = true := by rfl

def kid11_part701 : Audit := .cycle 5 8 true (1)
theorem kid11_part701_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,3⟩)) (kid11_part701) = true := by rfl

def kid11_part702 : Audit := .cycle 6 8 true (2)
theorem kid11_part702_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,4⟩)) (kid11_part702) = true := by rfl

def kid11_part703 : Audit := .cycle 11 2 true (3)
theorem kid11_part703_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,false,5⟩)) (kid11_part703) = true := by rfl

def kid11_part704 : Audit := .cycle 0 14 true (0)
theorem kid11_part704_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,0⟩)) (kid11_part704) = true := by rfl

def kid11_part705 : Audit := .split 13 (1,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 17 false (4),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 12 2 true (4),
.last 20 (2,true),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part705_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,1⟩)) (kid11_part705) = true := by rfl

def kid11_part706 : Audit := .split 13 (2,true) (byMove [
.cycle 2 13 true (1),
.last 14 (1,true),
.cycle 20 1 false (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 12 2 true (4),
.last 14 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[4, 64, 16, 16, 16, 1, 64],64⟩,
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 2 15 true (1)
])
theorem kid11_part706_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (kid11_part706) = true := by rfl

def kid11_part707 : Audit := .cycle 8 6 true (3)
theorem kid11_part707_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,3⟩)) (kid11_part707) = true := by rfl

def kid11_part708 : Audit := .cycle 7 6 true (3)
theorem kid11_part708_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,4⟩)) (kid11_part708) = true := by rfl

def kid11_part709 : Audit := .cycle 0 14 true (0)
theorem kid11_part709_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,5⟩)) (kid11_part709) = true := by rfl

def kid11_part685 : Audit := .split 12 (0,true) (byMove [(kid11_part686),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part690),(kid11_part691),(kid11_part692),(kid11_part693),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709)])

theorem kid11_part685_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part685) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) 12 (0,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (0,true) (some mv)) (byMove [(kid11_part686),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part690),(kid11_part691),(kid11_part692),(kid11_part693),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part686_checked

  · exact kid11_part692_checked

  · exact kid11_part698_checked

  · exact kid11_part704_checked

  · exact kid11_part687_checked

  · exact kid11_part693_checked

  · exact kid11_part699_checked

  · exact kid11_part705_checked

  · exact kid11_part688_checked

  · exact kid11_part694_checked

  · exact kid11_part700_checked

  · exact kid11_part706_checked

  · exact kid11_part689_checked

  · exact kid11_part695_checked

  · exact kid11_part701_checked

  · exact kid11_part707_checked

  · exact kid11_part690_checked

  · exact kid11_part696_checked

  · exact kid11_part702_checked

  · exact kid11_part708_checked

  · exact kid11_part691_checked

  · exact kid11_part697_checked

  · exact kid11_part703_checked

  · exact kid11_part709_checked

def kid11_part711 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.cycle 0 17 false (5),
.last 14 (2,true),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.cycle 1 37 true (1),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.cycle 16 3 false (0),
.last 19 (2,true),
.last 14 (2,true),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 23 1 false (-1),
.cycle 0 17 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (3)
])
theorem kid11_part711_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid11_part711) = true := by rfl

def kid11_part712 : Audit := .cycle 13 15 false (3)
theorem kid11_part712_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid11_part712) = true := by rfl

def kid11_part713 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 18 1 false (0),
.cycle 18 1 false (0),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.cycle 1 37 true (1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 1 15 true (1),
.cycle 29 1 false (1),
.last 14 (0,true),
.cycle 18 1 false (0),
.cycle 1 23 true (-1),
.cycle 1 17 true (1),
.cycle 1 17 true (1),
.cycle 23 1 false (-1),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (3)
])
theorem kid11_part713_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid11_part713) = true := by rfl

def kid11_part714 : Audit := .cycle 1 15 true (1)
theorem kid11_part714_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid11_part714) = true := by rfl

def kid11_part715 : Audit := .cycle 1 15 true (1)
theorem kid11_part715_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid11_part715) = true := by rfl

def kid11_part716 : Audit := .split 15 (2,true) (byMove [
.last 16 (0,true),
.cycle 1 17 true (1),
.cycle 22 1 false (0),
.cycle 8 9 true (3),
.cycle 7 9 true (3),
.cycle 1 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 6 16 true (2),
.cycle 3 13 true (1),
.cycle 7 18 true (3),
.cycle 9 7 true (3),
.last 16 (0,true),
.cycle 12 4 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 62, 64],[64, 62, 16, 16, 16, 2, 64],64⟩,
.cycle 7 10 true (3),
.cycle 6 10 true (2),
.cycle 1 18 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 7 11 true (3),
.cycle 8 8 true (3),
.cycle 1 19 true (1)
])
theorem kid11_part716_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid11_part716) = true := by rfl

def kid11_part717 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 1 20 true (1),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part717_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid11_part717) = true := by rfl

def kid11_part718 : Audit := .cycle 1 13 true (1)
theorem kid11_part718_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid11_part718) = true := by rfl

def kid11_part719 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 17 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 1 20 true (1),
.cycle 6 16 true (2),
.cycle 12 4 true (4),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 6 17 true (2)
])
theorem kid11_part719_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid11_part719) = true := by rfl

def kid11_part720 : Audit := .cycle 8 6 true (3)
theorem kid11_part720_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid11_part720) = true := by rfl

def kid11_part721 : Audit := .cycle 7 6 true (3)
theorem kid11_part721_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid11_part721) = true := by rfl

def kid11_part722 : Audit := .cycle 1 13 true (1)
theorem kid11_part722_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid11_part722) = true := by rfl

def kid11_part723 : Audit := .split 13 (0,true) (byMove [
.last 31 (2,true),
.last 26 (2,true),
.last 14 (2,true),
.cycle 1 23 true (1),
.cycle 48 1 false (0),
.last 16 (2,true),
.cycle 0 16 true (0),
.cycle 12 4 true (3),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.cycle 16 3 false (0),
.last 21 (2,true),
.last 14 (2,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.cycle 12 2 true (3),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1)
])
theorem kid11_part723_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid11_part723) = true := by rfl

def kid11_part724 : Audit := .split 18 (2,true) (byMove [
.last 19 (0,true),
.cycle 16 3 false (0),
.cycle 21 1 false (-1),
.cycle 1 49 true (-1),
.cycle 1 49 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 62, 64],[64, 62, 62, 16, 16, 2, 64],64⟩,
.last 19 (0,true),
.cycle 19 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[64, 4, 4, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[64, 24, 8, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 1 39 true (-1),
.last 19 (0,true),
.cycle 16 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 18, 64],[64, 18, 18, 16, 16, 2, 64],64⟩,
.cycle 15 5 false (1),
.last 19 (0,true),
.cycle 14 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 4, 64],[64, 4, 4, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 24, 64],[64, 24, 8, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 13 7 false (3)
])
theorem kid11_part724_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid11_part724) = true := by rfl

def kid11_part725 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 1 29 true (-1),
.cycle 18 1 false (0),
.cycle 1 23 true (1),
.cycle 48 1 false (0),
.cycle 1 20 true (1),
.last 14 (0,true),
.cycle 7 10 true (3),
.cycle 6 20 true (2),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1),
.last 14 (0,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 2, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.last 14 (0,true),
.cycle 12 2 true (3),
.cycle 2 14 true (1),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 17 true (1)
])
theorem kid11_part725_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid11_part725) = true := by rfl

def kid11_part726 : Audit := .cycle 5 8 true (1)
theorem kid11_part726_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid11_part726) = true := by rfl

def kid11_part727 : Audit := .cycle 6 8 true (2)
theorem kid11_part727_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid11_part727) = true := by rfl

def kid11_part728 : Audit := .cycle 11 2 true (3)
theorem kid11_part728_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid11_part728) = true := by rfl

def kid11_part729 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.cycle 0 15 true (0),
.last 14 (2,true),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.cycle 16 5 false (2),
.cycle 12 2 true (4),
.last 14 (2,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part729_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid11_part729) = true := by rfl

def kid11_part730 : Audit := .cycle 1 13 true (1)
theorem kid11_part730_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid11_part730) = true := by rfl

def kid11_part731 : Audit := .split 13 (2,true) (byMove [
.last 14 (0,true),
.cycle 2 13 true (1),
.cycle 20 1 false (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 1 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 14 (0,true),
.cycle 12 2 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 20, 64],[64, 4, 16, 16, 16, 2, 64],64⟩,
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 14 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 2 15 true (1)
])
theorem kid11_part731_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid11_part731) = true := by rfl

def kid11_part732 : Audit := .cycle 8 6 true (3)
theorem kid11_part732_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid11_part732) = true := by rfl

def kid11_part733 : Audit := .cycle 7 6 true (3)
theorem kid11_part733_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid11_part733) = true := by rfl

def kid11_part734 : Audit := .cycle 1 13 true (1)
theorem kid11_part734_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid11_part734) = true := by rfl

def kid11_part710 : Audit := .split 12 (1,true) (byMove [(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714),(kid11_part715),(kid11_part716),(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721),(kid11_part722),(kid11_part723),(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734)])

theorem kid11_part710_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part710) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714),(kid11_part715),(kid11_part716),(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721),(kid11_part722),(kid11_part723),(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part711_checked

  · exact kid11_part717_checked

  · exact kid11_part723_checked

  · exact kid11_part729_checked

  · exact kid11_part712_checked

  · exact kid11_part718_checked

  · exact kid11_part724_checked

  · exact kid11_part730_checked

  · exact kid11_part713_checked

  · exact kid11_part719_checked

  · exact kid11_part725_checked

  · exact kid11_part731_checked

  · exact kid11_part714_checked

  · exact kid11_part720_checked

  · exact kid11_part726_checked

  · exact kid11_part732_checked

  · exact kid11_part715_checked

  · exact kid11_part721_checked

  · exact kid11_part727_checked

  · exact kid11_part733_checked

  · exact kid11_part716_checked

  · exact kid11_part722_checked

  · exact kid11_part728_checked

  · exact kid11_part734_checked

def kid11_part736 : Audit := .split 13 (0,true) (byMove [
.cycle 0 17 false (5),
.last 14 (1,true),
.cycle 0 17 false (5),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.cycle 6 14 true (2),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 2 14 true (1),
.cycle 29 1 false (1),
.last 18 (1,true),
.last 14 (1,true),
.cycle 14 5 false (2),
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.cycle 23 1 false (-1),
.last 15 (1,true),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (3)
])
theorem kid11_part736_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part736) = true := by rfl

def kid11_part737 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 15 false (3),
.cycle 33 1 false (-1),
.cycle 35 1 false (-1),
.cycle 36 1 false (0),
.cycle 6 14 true (2),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 2 14 true (1),
.cycle 29 1 false (1),
.last 14 (0,true),
.cycle 16 3 false (0),
.cycle 18 30 true (0),
.cycle 2 16 true (1),
.cycle 2 16 true (1),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 16 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (3)
])
theorem kid11_part737_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part737) = true := by rfl

def kid11_part738 : Audit := .cycle 18 1 false (0)
theorem kid11_part738_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part738) = true := by rfl

def kid11_part739 : Audit := .cycle 2 14 true (1)
theorem kid11_part739_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part739) = true := by rfl

def kid11_part740 : Audit := .cycle 2 14 true (1)
theorem kid11_part740_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part740) = true := by rfl

def kid11_part741 : Audit := .cycle 8 8 true (3)
theorem kid11_part741_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part741) = true := by rfl

def kid11_part742 : Audit := .split 13 (0,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 2 19 true (1),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part742_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part742) = true := by rfl

def kid11_part743 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 16 true (2),
.cycle 6 13 true (2),
.cycle 6 16 true (2),
.cycle 2 19 true (1),
.last 16 (0,true),
.cycle 1 15 true (1),
.cycle 8 8 true (3),
.cycle 4 10 true (1),
.cycle 2 14 true (1),
.cycle 10 4 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part743_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part743) = true := by rfl

def kid11_part744 : Audit := .cycle 6 16 true (2)
theorem kid11_part744_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part744) = true := by rfl

def kid11_part745 : Audit := .cycle 8 6 true (3)
theorem kid11_part745_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part745) = true := by rfl

def kid11_part746 : Audit := .cycle 7 6 true (3)
theorem kid11_part746_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part746) = true := by rfl

def kid11_part747 : Audit := .cycle 2 12 true (1)
theorem kid11_part747_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part747) = true := by rfl

def kid11_part748 : Audit := .split 13 (0,true) (byMove [
.cycle 0 38 false (5),
.last 14 (1,true),
.last 18 (1,true),
.cycle 2 22 true (1),
.cycle 48 1 false (0),
.cycle 7 10 true (2),
.cycle 0 16 true (0),
.last 14 (1,true),
.last 16 (1,true),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 16 true (1),
.last 18 (1,true),
.last 14 (1,true),
.last 18 (1,true),
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 12 2 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 16 true (1)
])
theorem kid11_part748_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part748) = true := by rfl

def kid11_part749 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 105 70 false (7),
.cycle 21 1 false (-1),
.cycle 2 22 true (1),
.cycle 48 1 false (0),
.cycle 7 10 true (2),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 12 4 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 16 true (1),
.last 14 (0,true),
.cycle 16 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 16, 16, 16, 16, 4, 64],64⟩,
.cycle 6 10 true (2),
.cycle 6 10 true (2),
.cycle 23 1 false (-1),
.last 14 (0,true),
.cycle 1 15 true (1),
.cycle 12 2 true (3),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 2 16 true (1)
])
theorem kid11_part749_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part749) = true := by rfl

def kid11_part750 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 32, 16, 64],[64, 64, 16, 16, 16, 4, 64],64⟩
theorem kid11_part750_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part750) = true := by rfl

def kid11_part751 : Audit := .cycle 5 8 true (1)
theorem kid11_part751_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part751) = true := by rfl

def kid11_part752 : Audit := .cycle 6 8 true (2)
theorem kid11_part752_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part752) = true := by rfl

def kid11_part753 : Audit := .cycle 11 2 true (3)
theorem kid11_part753_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part753) = true := by rfl

def kid11_part754 : Audit := .split 13 (0,true) (byMove [
.cycle 0 19 false (5),
.last 14 (1,true),
.cycle 0 15 true (0),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 20 (1,true),
.last 14 (1,true),
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 0 17 true (0)
])
theorem kid11_part754_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part754) = true := by rfl

def kid11_part755 : Audit := .split 13 (1,true) (byMove [
.last 14 (0,true),
.cycle 14 17 false (4),
.cycle 1 14 true (1),
.cycle 8 7 true (3),
.cycle 7 7 true (3),
.cycle 2 13 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 6 14 true (2),
.cycle 3 11 true (1),
.cycle 7 14 true (3),
.cycle 9 5 true (3),
.last 14 (0,true),
.cycle 16 5 false (2),
.cycle 12 2 true (4),
.cycle 7 8 true (3),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 7 9 true (3),
.cycle 8 6 true (3),
.cycle 1 16 true (1)
])
theorem kid11_part755_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part755) = true := by rfl

def kid11_part756 : Audit := .cycle 2 12 true (1)
theorem kid11_part756_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part756) = true := by rfl

def kid11_part757 : Audit := .cycle 8 6 true (3)
theorem kid11_part757_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part757) = true := by rfl

def kid11_part758 : Audit := .cycle 7 6 true (3)
theorem kid11_part758_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part758) = true := by rfl

def kid11_part759 : Audit := .cycle 2 12 true (1)
theorem kid11_part759_checked : zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part759) = true := by rfl

def kid11_part735 : Audit := .split 12 (2,true) (byMove [(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747),(kid11_part748),(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759)])

theorem kid11_part735_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part735) = true := by

  change (zipQueryOK 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747),(kid11_part748),(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part736_checked

  · exact kid11_part742_checked

  · exact kid11_part748_checked

  · exact kid11_part754_checked

  · exact kid11_part737_checked

  · exact kid11_part743_checked

  · exact kid11_part749_checked

  · exact kid11_part755_checked

  · exact kid11_part738_checked

  · exact kid11_part744_checked

  · exact kid11_part750_checked

  · exact kid11_part756_checked

  · exact kid11_part739_checked

  · exact kid11_part745_checked

  · exact kid11_part751_checked

  · exact kid11_part757_checked

  · exact kid11_part740_checked

  · exact kid11_part746_checked

  · exact kid11_part752_checked

  · exact kid11_part758_checked

  · exact kid11_part741_checked

  · exact kid11_part747_checked

  · exact kid11_part753_checked

  · exact kid11_part759_checked

def kid11_part760 : Audit := .cycle 7 6 true (3)
theorem kid11_part760_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part760) = true := by rfl

def kid11_part761 : Audit := .cycle 6 6 true (2)
theorem kid11_part761_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part761) = true := by rfl

def kid11_part762 : Audit := .cycle 12 3 true (4)
theorem kid11_part762_checked : zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part762) = true := by rfl

def kid11_part450 : Audit := .split 11 (5,true) (byMove [(kid11_part451),(kid11_part476),(kid11_part501),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part554),(kid11_part579),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part632),(kid11_part657),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685),(kid11_part710),(kid11_part735),(kid11_part760),(kid11_part761),(kid11_part762)])

theorem kid11_part450_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (kid11_part450) = true := by

  change (zipQueryOK 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 4063 (refine (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part451),(kid11_part476),(kid11_part501),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part554),(kid11_part579),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part632),(kid11_part657),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685),(kid11_part710),(kid11_part735),(kid11_part760),(kid11_part761),(kid11_part762)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part451_checked

  · exact kid11_part529_checked

  · exact kid11_part607_checked

  · exact kid11_part685_checked

  · exact kid11_part476_checked

  · exact kid11_part554_checked

  · exact kid11_part632_checked

  · exact kid11_part710_checked

  · exact kid11_part501_checked

  · exact kid11_part579_checked

  · exact kid11_part657_checked

  · exact kid11_part735_checked

  · exact kid11_part526_checked

  · exact kid11_part604_checked

  · exact kid11_part682_checked

  · exact kid11_part760_checked

  · exact kid11_part527_checked

  · exact kid11_part605_checked

  · exact kid11_part683_checked

  · exact kid11_part761_checked

  · exact kid11_part528_checked

  · exact kid11_part606_checked

  · exact kid11_part684_checked

  · exact kid11_part762_checked

def kid11_part763 : Audit := .cycle 0 10 true (0)
theorem kid11_part763_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,0⟩)) (kid11_part763) = true := by rfl

def kid11_part764 : Audit := .cycle 1 9 true (1)
theorem kid11_part764_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,1⟩)) (kid11_part764) = true := by rfl

def kid11_part765 : Audit := .cycle 2 8 true (1)
theorem kid11_part765_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,2⟩)) (kid11_part765) = true := by rfl

def kid11_part766 : Audit := .cycle 7 5 true (3)
theorem kid11_part766_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,3⟩)) (kid11_part766) = true := by rfl

def kid11_part767 : Audit := .cycle 8 2 true (4)
theorem kid11_part767_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (kid11_part767) = true := by rfl

def kid11_part768 : Audit := .cycle 9 1 true (5)
theorem kid11_part768_checked : zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some ⟨true,true,5⟩)) (kid11_part768) = true := by rfl

def kid11 : Audit := .split 9 (5,false) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part4),(kid11_part5),(kid11_part6),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part254),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part450),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767),(kid11_part768)])

theorem check11 : zipCheck 4063 (child121 ⟨false,true,5⟩) (kid11) = true := by

  change (zipQueryOK 4063 (child121 ⟨false,true,5⟩) 9 (5,false) && allMoves (fun mv => zipCheck 4063 (refine (child121 ⟨false,true,5⟩) (5,false) (some mv)) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part4),(kid11_part5),(kid11_part6),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part254),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part450),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767),(kid11_part768)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1_checked

  · exact kid11_part103_checked

  · exact kid11_part109_checked

  · exact kid11_part763_checked

  · exact kid11_part2_checked

  · exact kid11_part104_checked

  · exact kid11_part254_checked

  · exact kid11_part764_checked

  · exact kid11_part3_checked

  · exact kid11_part105_checked

  · exact kid11_part399_checked

  · exact kid11_part765_checked

  · exact kid11_part4_checked

  · exact kid11_part106_checked

  · exact kid11_part400_checked

  · exact kid11_part766_checked

  · exact kid11_part5_checked

  · exact kid11_part107_checked

  · exact kid11_part401_checked

  · exact kid11_part767_checked

  · exact kid11_part6_checked

  · exact kid11_part108_checked

  · exact kid11_part450_checked

  · exact kid11_part768_checked

end BB6.Agent11Raw121
