import Raw39B0RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid11_part1 : Audit := .cycle 0 9 true (0)
theorem kid11_part1_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,0⟩)) (kid11_part1) = true := by rfl

def kid11_part2 : Audit := .cycle 1 8 true (1)
theorem kid11_part2_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,1⟩)) (kid11_part2) = true := by rfl

def kid11_part4 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 46, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 32 1 false (6),
.cycle 25 1 false (3),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 0 22 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 4, 64],[8, 8, 16, 8, 8, 1, 64],80⟩,
.cycle 0 30 true (0),
.cycle 29 1 false (5),
.last 22 (4,false),
.cycle 31 1 false (5),
.cycle 26 1 false (4),
.cycle 0 24 true (0),
.last 23 (4,false),
.cycle 33 1 false (7),
.last 23 (4,false),
.cycle 17 5 false (4),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 0 53 true (0),
.last 22 (4,false),
.last 27 (4,false)
]),
.cycle 32 1 false (6),
.cycle 0 21 true (0),
.cycle 0 52 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.last 47 (4,true),
.last 23 (4,true),
.cycle 30 1 false (2),
.cycle 0 22 true (0),
.last 44 (4,true),
.cycle 9 13 true (0),
.cycle 0 29 true (0),
.cycle 21 1 true (5),
.cycle 0 31 true (0),
.cycle 2 23 true (0),
.cycle 19 3 true (3),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 23 (4,true),
.cycle 30 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 42 (4,true),
.last 48 (4,true),
.cycle 21 1 true (5),
.cycle 20 3 true (4)
]),
.cycle 2 20 true (0),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 0 49 true (0),
.split 21 (4,true) (byMove [
.cycle 18 8 true (2),
.cycle 25 1 false (3),
.last 23 (4,false),
.cycle 34 1 false (6),
.last 23 (4,false),
.cycle 0 27 true (0),
.cycle 0 49 true (0),
.cycle 0 32 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 0 25 true (0),
.cycle 16 6 true (2),
.last 23 (4,false),
.cycle 27 1 false (5),
.last 23 (4,false),
.cycle 17 5 false (4),
.cycle 0 56 true (0),
.cycle 2 22 true (0),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.last 23 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 288, 4096, 288, 128, 256, 8, 2, 4096, 4104, 4096],[2, 32, 4096, 1, 2048, 256, 2, 32, 256, 1, 2048, 256, 4096],7184⟩
]),
.cycle 17 8 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.split 21 (4,false) (byMove [
.last 44 (4,true),
.cycle 2 22 true (0),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 45 (4,true),
.cycle 0 22 true (0),
.last 43 (4,true),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.cycle 21 1 true (5),
.cycle 2 21 true (0),
.cycle 0 33 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 46 (4,true),
.last 22 (4,true),
.cycle 19 5 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.last 47 (4,true),
.cycle 21 1 true (5),
.cycle 20 3 true (4)
]),
.cycle 20 2 true (4)
])
theorem kid11_part4_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part4) = true := by rfl

def kid11_part5 : Audit := .cycle 0 21 true (0)
theorem kid11_part5_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part5) = true := by rfl

def kid11_part6 : Audit := .cycle 19 1 false (3)
theorem kid11_part6_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part6) = true := by rfl

def kid11_part7 : Audit := .cycle 18 1 false (2)
theorem kid11_part7_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part7) = true := by rfl

def kid11_part8 : Audit := .split 18 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 30 1 false (6),
.split 20 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 32 1 false (6),
.cycle 0 21 true (0),
.cycle 62 1 false (12),
.cycle 39 1 false (9),
.cycle 28 1 false (6),
.last 44 (4,true),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.cycle 33 1 false (7),
.cycle 34 1 false (8),
.cycle 32 1 false (8),
.last 21 (4,true),
.cycle 17 4 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.last 43 (4,true),
.cycle 20 2 true (4)
]),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 30 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 21 1 true (3),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 30 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 21 1 true (5),
.cycle 23 1 false (5),
.cycle 32 1 false (6),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.cycle 21 1 true (5),
.last 22 (2,true)
]),
.cycle 21 1 false (3),
.cycle 41 1 false (5),
.split 20 (2,true) (byMove [
.cycle 0 25 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 0 26 true (0),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 0 53 true (0),
.cycle 21 36 true (3),
.cycle 0 23 true (0),
.cycle 37 1 false (5),
.last 24 (4,true),
.cycle 41 1 false (5),
.cycle 25 1 false (3),
.cycle 16 5 false (3),
.cycle 40 1 false (8),
.cycle 36 1 false (8),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 2 22 true (0),
.cycle 1 22 true (0),
.cycle 0 23 true (0),
.cycle 4 17 true (0),
.cycle 16 9 false (3),
.cycle 20 2 true (2)
]),
.cycle 32 1 false (6),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 2 20 true (0),
.split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 4, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 52 true (0),
.cycle 1 29 true (0),
.cycle 3 18 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 1 32 true (0),
.cycle 1 23 true (0),
.cycle 29 1 false (5),
.cycle 1 49 true (0),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 1 21 true (0),
.cycle 20 2 true (4)
]),
.cycle 0 21 true (0),
.cycle 25 1 false (5),
.split 20 (4,true) (byMove [
.last 45 (2,true),
.cycle 31 1 false (5),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 23 1 true (1),
.cycle 25 1 false (1),
.cycle 0 21 true (0),
.cycle 52 1 true (8),
.cycle 29 1 true (5),
.cycle 3 18 true (0),
.cycle 21 1 true (5),
.cycle 2 20 true (0),
.cycle 32 1 true (4),
.cycle 23 1 true (3),
.last 21 (2,true),
.cycle 49 1 true (7),
.cycle 21 3 false (3),
.cycle 25 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 21 1 true (5),
.last 22 (2,true)
]),
.split 20 (2,true) (byMove [
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 23 1 false (1),
.cycle 32 1 false (6),
.cycle 68 1 false (12),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 23 (4,true),
.cycle 23 1 false (3),
.cycle 45 1 false (5),
.cycle 16 7 false (3),
.cycle 34 1 false (6),
.cycle 21 1 false (1),
.last 23 (4,true),
.cycle 23 1 false (1),
.cycle 2 22 true (0),
.cycle 1 22 true (0),
.cycle 0 23 true (0),
.cycle 27 1 false (5),
.last 23 (4,true),
.cycle 19 2 true (2)
])
])
theorem kid11_part8_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part8) = true := by rfl

def kid11_part9 : Audit := .cycle 20 1 false (2)
theorem kid11_part9_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part9) = true := by rfl

def kid11_part10 : Audit := .cycle 28 1 false (8)
theorem kid11_part10_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part10) = true := by rfl

def kid11_part11 : Audit := .cycle 21 1 false (5)
theorem kid11_part11_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part11) = true := by rfl

def kid11_part12 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (5),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 true (3),
.cycle 22 1 false (4),
.cycle 31 1 false (5),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 19 1 true (3),
.cycle 18 3 false (4)
]),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 29 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 true (5),
.cycle 22 1 false (6),
.cycle 31 1 false (7),
.cycle 18 3 true (4),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 19 1 true (5),
.cycle 18 3 true (4)
]),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.cycle 24 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 18 2 true (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 22 1 false (6),
.cycle 9 14 true (0),
.last 22 (4,true),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 53 1 false (11),
.cycle 30 1 false (6),
.last 21 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 30 1 false (8)
]),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.split 19 (4,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 18 2 true (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 22 1 false (6),
.cycle 0 20 true (0),
.last 39 (4,true),
.cycle 29 1 false (9),
.cycle 27 1 false (7),
.cycle 19 1 true (5),
.cycle 29 1 false (7),
.cycle 24 1 false (6),
.cycle 23 1 false (7),
.last 21 (4,true),
.cycle 31 1 false (9),
.last 20 (4,true),
.cycle 17 3 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.last 43 (4,true),
.cycle 19 1 true (5),
.cycle 18 3 true (4)
]),
.cycle 18 2 true (4)
])
theorem kid11_part12_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part12) = true := by rfl

def kid11_part13 : Audit := .cycle 0 19 true (0)
theorem kid11_part13_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part13) = true := by rfl

def kid11_part14 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (5),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 true (3),
.cycle 22 1 false (4),
.cycle 31 1 false (5),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 19 1 true (3),
.last 21 (2,true)
]),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 29 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 true (5),
.cycle 22 1 false (6),
.cycle 31 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 22 1 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 19 1 true (5),
.last 21 (2,true)
]),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.split 20 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.cycle 18 3 false (4),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 52 (4,false),
.last 29 (4,false),
.cycle 28 1 false (6),
.last 21 (4,false),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.last 23 (4,false),
.cycle 34 1 false (8),
.cycle 32 1 false (8),
.cycle 18 3 false (4),
.cycle 17 4 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.last 21 (4,false),
.cycle 20 2 true (4)
]),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (3),
.cycle 24 1 false (6),
.cycle 16 31 true (2),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 22 1 false (2),
.cycle 0 53 true (0),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 3 false (4),
.last 23 (2,true)
]),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.split 19 (4,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (4),
.cycle 24 1 false (4),
.cycle 0 20 true (0),
.cycle 18 21 true (4),
.cycle 30 1 false (10),
.cycle 27 1 false (7),
.cycle 19 1 true (5),
.cycle 29 1 false (7),
.cycle 24 1 false (6),
.last 24 (2,true),
.last 20 (2,true),
.cycle 31 1 false (9),
.cycle 18 3 true (4),
.cycle 17 3 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 18 26 true (4),
.cycle 19 1 true (5),
.last 21 (2,true)
]),
.split 20 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 30 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 30 1 false (8),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.last 21 (4,false),
.cycle 23 1 false (5),
.cycle 32 1 false (6),
.last 25 (4,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.last 21 (4,false),
.cycle 19 2 true (4)
])
])
theorem kid11_part14_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part14) = true := by rfl

def kid11_part15 : Audit := .cycle 21 1 false (5)
theorem kid11_part15_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part15) = true := by rfl

def kid11_part16 : Audit := .cycle 2 22 true (0)
theorem kid11_part16_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part16) = true := by rfl

def kid11_part17 : Audit := .split 19 (2,true) (byMove [
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 32 1 false (6),
.split 20 (4,true) (byMove [
.cycle 0 25 true (0),
.cycle 41 1 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 23 1 false (1),
.cycle 32 1 false (6),
.cycle 33 1 false (7),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 23 1 false (3),
.cycle 45 1 false (5),
.cycle 18 3 false (3),
.cycle 34 1 false (6),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 23 1 false (1),
.cycle 2 22 true (0),
.cycle 1 23 true (0),
.cycle 0 23 true (0),
.cycle 27 1 false (5),
.last 21 (4,false),
.last 23 (4,false)
]),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 9 12 true (0),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.last 47 (4,false),
.cycle 9 12 true (0),
.last 30 (4,false),
.last 21 (4,false),
.last 32 (4,false),
.cycle 2 22 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.cycle 27 1 false (5),
.last 21 (4,false),
.last 23 (4,false),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.last 42 (4,false),
.cycle 5 42 true (0),
.last 21 (4,false),
.last 23 (4,false)
]),
.cycle 2 22 true (0),
.cycle 29 1 false (5),
.cycle 16 4 true (2),
.cycle 27 1 false (5),
.cycle 25 1 false (5),
.split 20 (4,true) (byMove [
.cycle 18 8 true (1),
.cycle 14 36 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 23 1 false (1),
.cycle 25 1 false (5),
.cycle 29 1 false (5),
.last 22 (4,false),
.cycle 32 1 false (8),
.last 23 (4,false),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.cycle 18 3 false (3),
.cycle 27 1 false (5),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 23 1 false (1),
.cycle 29 28 true (3),
.cycle 2 26 true (0),
.cycle 19 2 true (2),
.cycle 0 53 true (0),
.last 23 (4,false),
.cycle 16 6 true (2)
]),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 2 20 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.split 20 (4,true) (byMove [
.last 46 (4,false),
.cycle 31 1 false (5),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 23 (4,false),
.last 26 (4,false),
.cycle 0 21 true (0),
.last 54 (4,false),
.last 31 (4,false),
.cycle 3 18 true (0),
.last 21 (4,false),
.cycle 2 20 true (0),
.last 34 (4,false),
.last 25 (4,false),
.cycle 19 2 true (3),
.last 51 (4,false),
.last 23 (4,false),
.cycle 16 6 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.last 21 (4,false),
.last 23 (4,false)
]),
.cycle 24 2 true (4)
])
theorem kid11_part17_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part17) = true := by rfl

def kid11_part18 : Audit := .cycle 30 1 false (8)
theorem kid11_part18_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part18) = true := by rfl

def kid11_part19 : Audit := .cycle 18 1 false (2)
theorem kid11_part19_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part19) = true := by rfl

def kid11_part21 : Audit := .split 21 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 4, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 45 1 false (5),
.cycle 25 1 false (1),
.cycle 0 56 true (0),
.last 22 (4,true),
.last 23 (4,true),
.cycle 0 53 true (0),
.cycle 30 28 true (3),
.cycle 9 14 true (0),
.cycle 0 23 true (0),
.last 22 (4,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 4, 64],[8, 9, 9, 8, 64, 16, 64],64⟩,
.cycle 22 15 true (2),
.cycle 16 12 true (1),
.cycle 41 1 false (5),
.cycle 5 17 true (0),
.last 22 (4,true),
.last 23 (4,true),
.cycle 0 60 true (0),
.cycle 2 22 true (0),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part21_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part21) = true := by rfl

def kid11_part22 : Audit := .cycle 14 32 true (0)
theorem kid11_part22_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part22) = true := by rfl

def kid11_part23 : Audit := .cycle 20 1 false (2)
theorem kid11_part23_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part23) = true := by rfl

def kid11_part24 : Audit := .cycle 19 1 false (1)
theorem kid11_part24_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part24) = true := by rfl

def kid11_part25 : Audit := .cycle 18 1 false (2)
theorem kid11_part25_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part25) = true := by rfl

def kid11_part26 : Audit := .cycle 21 1 false (1)
theorem kid11_part26_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part26) = true := by rfl

def kid11_part27 : Audit := .cycle 23 1 false (5)
theorem kid11_part27_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part27) = true := by rfl

def kid11_part28 : Audit := .cycle 25 1 false (5)
theorem kid11_part28_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part28) = true := by rfl

def kid11_part29 : Audit := .split 19 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 4, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 0 23 true (0),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.cycle 16 6 true (2),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 0 54 true (0),
.cycle 30 1 false (6),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part29_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part29) = true := by rfl

def kid11_part30 : Audit := .cycle 30 1 false (8)
theorem kid11_part30_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part30) = true := by rfl

def kid11_part31 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 23 1 true (3),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (5),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 22 1 false (2),
.cycle 0 54 true (0),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (5),
.cycle 19 2 true (3)
])
theorem kid11_part31_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part31) = true := by rfl

def kid11_part32 : Audit := .cycle 17 2 true (2)
theorem kid11_part32_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part32) = true := by rfl

def kid11_part33 : Audit := .cycle 15 8 true (1)
theorem kid11_part33_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part33) = true := by rfl

def kid11_part34 : Audit := .split 20 (2,true) (byMove [
.cycle 37 1 false (7),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 16 10 true (1),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 6 15 true (0),
.cycle 21 13 true (2),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 2, 4, 64],[8, 10, 8, 8, 64, 16, 64],64⟩,
.cycle 14 32 true (0),
.last 21 (4,true),
.cycle 16 7 false (3),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 37 1 false (5),
.cycle 33 1 false (5),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 29 28 true (3),
.cycle 16 11 false (4),
.cycle 2 21 true (0),
.cycle 0 53 true (0),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid11_part34_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part34) = true := by rfl

def kid11_part35 : Audit := .cycle 25 1 false (5)
theorem kid11_part35_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part35) = true := by rfl

def kid11_part36 : Audit := .cycle 19 1 false (1)
theorem kid11_part36_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part36) = true := by rfl

def kid11_part37 : Audit := .cycle 18 1 false (2)
theorem kid11_part37_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part37) = true := by rfl

def kid11_part38 : Audit := .cycle 21 1 false (1)
theorem kid11_part38_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part38) = true := by rfl

def kid11_part39 : Audit := .cycle 27 24 true (3)
theorem kid11_part39_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part39) = true := by rfl

def kid11_part40 : Audit := .cycle 2 22 true (0)
theorem kid11_part40_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part40) = true := by rfl

def kid11_part41 : Audit := .split 19 (2,true) (byMove [
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 32 1 false (6),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 9 12 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 2 22 true (0),
.cycle 29 1 false (5),
.cycle 16 4 true (2),
.cycle 27 1 false (5),
.cycle 25 1 false (5),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 2 20 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part41_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part41) = true := by rfl

def kid11_part42 : Audit := .cycle 0 47 true (0)
theorem kid11_part42_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part42) = true := by rfl

def kid11_part43 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 23 1 false (3),
.last 20 (2,true),
.cycle 32 1 false (6),
.cycle 28 1 true (0),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (5),
.cycle 2 22 true (0),
.cycle 29 1 false (5),
.cycle 16 4 true (2),
.last 20 (2,true),
.cycle 25 1 false (5),
.cycle 18 3 false (3),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 2 20 true (0),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 true (5),
.cycle 19 2 true (3)
])
theorem kid11_part43_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part43) = true := by rfl

def kid11_part44 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 14 36 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 23 (2,true),
.cycle 23 1 false (1),
.cycle 25 1 false (5),
.cycle 29 1 false (5),
.last 21 (2,true),
.cycle 32 1 false (8),
.last 25 (2,true),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.last 22 (2,true),
.cycle 27 1 false (5),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 23 1 false (1),
.cycle 29 28 true (3),
.cycle 2 26 true (0),
.last 21 (2,true),
.cycle 0 53 true (0),
.last 25 (2,true),
.cycle 19 2 true (2)
])
theorem kid11_part44_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part44) = true := by rfl

def kid11_part20 : Audit := .split 18 (4,false) (byMove [(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43),(kid11_part44)])

theorem kid11_part20_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part20) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part21),(kid11_part22),(kid11_part23),(kid11_part24),(kid11_part25),(kid11_part26),(kid11_part27),(kid11_part28),(kid11_part29),(kid11_part30),(kid11_part31),(kid11_part32),(kid11_part33),(kid11_part34),(kid11_part35),(kid11_part36),(kid11_part37),(kid11_part38),(kid11_part39),(kid11_part40),(kid11_part41),(kid11_part42),(kid11_part43),(kid11_part44)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid11_part26_checked

  · exact kid11_part32_checked

  · exact kid11_part38_checked

  · exact kid11_part44_checked

def kid11_part45 : Audit := .cycle 20 1 false (2)
theorem kid11_part45_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part45) = true := by rfl

def kid11_part46 : Audit := .cycle 0 48 true (0)
theorem kid11_part46_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part46) = true := by rfl

def kid11_part47 : Audit := .cycle 28 1 false (6)
theorem kid11_part47_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part47) = true := by rfl

def kid11_part48 : Audit := .split 18 (2,true) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (5),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 22 1 false (4),
.cycle 31 1 false (5),
.cycle 18 3 false (4),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.last 20 (4,false),
.last 22 (4,false)
]),
.cycle 28 1 false (6),
.cycle 0 19 true (0),
.cycle 56 1 false (12),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.last 21 (4,true),
.cycle 25 1 false (3),
.cycle 0 20 true (0),
.last 40 (4,true),
.cycle 9 11 true (0),
.cycle 35 1 false (9),
.cycle 19 1 true (5),
.cycle 37 1 false (9),
.cycle 2 21 true (0),
.cycle 18 3 true (4),
.cycle 0 22 true (0),
.cycle 26 1 false (6),
.last 21 (4,true),
.cycle 25 1 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.last 38 (4,true),
.last 44 (4,true),
.cycle 19 1 true (5),
.cycle 18 3 true (4)
]),
.cycle 28 1 false (6),
.cycle 23 1 false (5),
.cycle 29 1 false (7),
.cycle 32 1 false (8),
.cycle 30 1 false (8),
.split 19 (4,true) (byMove [
.cycle 18 8 true (2),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 29 1 false (7),
.cycle 16 27 true (2),
.cycle 18 3 false (4),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 60 1 false (12),
.cycle 30 1 false (6),
.cycle 18 2 true (3),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 2 19 true (0)
]),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.split 19 (4,false) (byMove [
.last 40 (4,true),
.cycle 30 1 false (6),
.cycle 18 2 true (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 2 19 true (0),
.cycle 0 20 true (0),
.last 39 (4,true),
.last 48 (4,true),
.cycle 3 17 true (0),
.cycle 19 1 true (5),
.cycle 2 19 true (0),
.cycle 39 1 false (9),
.last 40 (4,true),
.last 21 (4,true),
.last 42 (4,true),
.last 20 (4,true),
.cycle 17 3 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.last 43 (4,true),
.cycle 19 1 true (5),
.cycle 18 3 true (4)
]),
.cycle 18 2 true (4)
])
theorem kid11_part48_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part48) = true := by rfl

def kid11_part49 : Audit := .cycle 0 19 true (0)
theorem kid11_part49_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part49) = true := by rfl

def kid11_part51 : Audit := .cycle 29 1 false (7)
theorem kid11_part51_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part51) = true := by rfl

def kid11_part52 : Audit := .cycle 22 1 false (4)
theorem kid11_part52_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part52) = true := by rfl

def kid11_part53 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 29 1 false (5),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 22 1 false (4),
.cycle 31 1 false (5),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.last 20 (4,false),
.cycle 19 2 true (3)
])
theorem kid11_part53_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part53) = true := by rfl

def kid11_part54 : Audit := .cycle 0 20 true (0)
theorem kid11_part54_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part54) = true := by rfl

def kid11_part55 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 30 1 false (4),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 30 1 false (6),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 true (2),
.cycle 23 1 false (3),
.cycle 32 1 false (4),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.cycle 20 1 true (2),
.last 22 (2,true)
])
theorem kid11_part55_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part55) = true := by rfl

def kid11_part56 : Audit := .split 20 (4,false) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 24 1 false (2),
.cycle 19 2 true (3),
.cycle 0 21 true (0),
.cycle 19 32 true (3),
.cycle 19 9 true (3),
.cycle 28 1 false (6),
.cycle 20 1 true (4),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.cycle 19 3 true (3),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 24 1 false (2),
.cycle 17 4 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 20 1 true (4),
.last 22 (2,true)
])
theorem kid11_part56_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part56) = true := by rfl

def kid11_part57 : Audit := .cycle 0 19 true (0)
theorem kid11_part57_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part57) = true := by rfl

def kid11_part58 : Audit := .split 48 (4,false) (byMove [
.cycle 59 1 false (13),
.cycle 52 1 false (10),
.last 49 (2,true),
.cycle 0 50 true (0),
.cycle 59 1 false (13),
.cycle 47 2 true (9),
.cycle 0 49 true (0),
.cycle 19 30 true (3),
.cycle 40 9 true (6),
.cycle 56 1 false (12),
.cycle 48 1 true (10),
.cycle 58 1 false (12),
.cycle 53 1 false (11),
.cycle 46 3 true (8),
.last 49 (2,true),
.cycle 60 1 false (14),
.cycle 53 1 false (11),
.cycle 17 32 true (3),
.cycle 0 49 true (0),
.cycle 1 48 true (0),
.cycle 2 47 true (0),
.cycle 46 26 true (8),
.cycle 48 1 true (10),
.last 50 (2,true)
])
theorem kid11_part58_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part58) = true := by rfl

def kid11_part59 : Audit := .split 27 (4,false) (byMove [
.cycle 38 1 false (10),
.cycle 31 1 false (7),
.last 28 (2,true),
.cycle 0 29 true (0),
.cycle 30 1 false (8),
.cycle 26 2 true (6),
.cycle 0 28 true (0),
.last 47 (2,true),
.cycle 19 9 true (3),
.cycle 35 1 false (9),
.cycle 27 1 true (7),
.cycle 37 1 false (9),
.cycle 32 1 false (8),
.cycle 25 3 true (5),
.last 28 (2,true),
.cycle 39 1 false (11),
.last 29 (2,true),
.cycle 17 11 true (3),
.cycle 0 28 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.last 51 (2,true),
.cycle 27 1 true (7),
.last 29 (2,true)
])
theorem kid11_part59_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part59) = true := by rfl

def kid11_part60 : Audit := .cycle 26 1 false (6)
theorem kid11_part60_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part60) = true := by rfl

def kid11_part61 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 22 1 false (4),
.last 21 (2,true),
.cycle 0 20 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1072, 2, 1072, 128, 256, 8, 2, 2, 4096, 4096],[2, 32, 4096, 1, 16, 1024, 2, 32, 4096, 1, 16, 1024, 4096],6144⟩,
.cycle 9 11 true (0),
.cycle 35 1 false (9),
.cycle 19 1 true (5),
.cycle 39 1 false (9),
.cycle 2 21 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 26 1 false (6),
.cycle 24 1 false (6),
.last 21 (2,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1072, 256, 1072, 128, 256, 8, 2, 256, 4096, 4096],[2, 32, 4096, 1, 16, 1024, 2, 32, 4096, 1, 16, 1024, 4096],6144⟩,
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 1072, 512, 1072, 128, 256, 8, 2, 512, 4096, 4096],[2, 32, 4096, 1, 16, 1024, 2, 32, 4096, 1, 16, 1024, 4096],6144⟩,
.cycle 19 1 true (5),
.last 21 (2,true)
])
theorem kid11_part61_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part61) = true := by rfl

def kid11_part62 : Audit := .cycle 28 1 false (6)
theorem kid11_part62_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part62) = true := by rfl

def kid11_part63 : Audit := .cycle 23 1 false (5)
theorem kid11_part63_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part63) = true := by rfl

def kid11_part64 : Audit := .split 21 (4,false) (byMove [
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.last 24 (2,true),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 16 25 true (2),
.cycle 19 9 true (3),
.cycle 29 1 false (7),
.cycle 21 1 true (5),
.cycle 31 1 false (7),
.cycle 26 1 false (6),
.cycle 19 3 true (3),
.last 22 (2,true),
.cycle 33 1 false (9),
.last 24 (2,true),
.cycle 17 5 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 16 32 true (2),
.cycle 21 1 true (5),
.last 23 (2,true)
])
theorem kid11_part64_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part64) = true := by rfl

def kid11_part65 : Audit := .split 19 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 256, 128, 256, 32768, 524290, 16777216, 32768, 128, 256, 2097152, 32, 16777216, 32, 128, 256, 8, 1024, 16777216, 1024, 16777216],[2, 32, 256, 1, 1, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 262144, 1024, 2, 32, 256, 1, 1, 1024, 16777216],31540240⟩,
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 0 21 true (0),
.cycle 0 23 true (0),
.last 21 (4,false),
.last 23 (4,false),
.cycle 16 6 true (2),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 22 1 false (2),
.last 52 (4,false),
.cycle 30 1 false (6),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.cycle 18 2 true (3),
.last 21 (4,false)
])
theorem kid11_part65_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part65) = true := by rfl

def kid11_part66 : Audit := .cycle 30 1 false (8)
theorem kid11_part66_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part66) = true := by rfl

def kid11_part67 : Audit := .split 20 (4,false) (byMove [
.last 23 (2,true),
.cycle 14 36 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 25 1 false (5),
.cycle 16 29 true (2),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 19 2 true (2),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.last 22 (2,true),
.cycle 27 1 false (5),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 0 33 true (0),
.cycle 1 23 true (0),
.last 21 (2,true),
.cycle 21 30 true (2),
.cycle 18 3 false (4),
.cycle 18 5 false (4)
])
theorem kid11_part67_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part67) = true := by rfl

def kid11_part68 : Audit := .cycle 17 2 true (3)
theorem kid11_part68_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part68) = true := by rfl

def kid11_part69 : Audit := .cycle 0 19 true (0)
theorem kid11_part69_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part69) = true := by rfl

def kid11_part70 : Audit := .cycle 1 18 true (0)
theorem kid11_part70_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part70) = true := by rfl

def kid11_part71 : Audit := .cycle 2 17 true (0)
theorem kid11_part71_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part71) = true := by rfl

def kid11_part72 : Audit := .cycle 20 22 true (3)
theorem kid11_part72_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part72) = true := by rfl

def kid11_part73 : Audit := .split 19 (4,false) (byMove [
.cycle 18 22 true (3),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 18 2 true (4),
.cycle 19 2 true (4),
.cycle 0 20 true (0),
.cycle 18 21 true (4),
.cycle 19 9 true (4),
.cycle 3 17 true (0),
.cycle 19 1 true (5),
.cycle 2 19 true (0),
.cycle 36 1 false (8),
.cycle 19 3 true (4),
.last 20 (2,true),
.cycle 18 25 true (3),
.cycle 18 3 true (4),
.cycle 17 3 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 18 26 true (4),
.cycle 19 1 true (5),
.last 21 (2,true)
])
theorem kid11_part73_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part73) = true := by rfl

def kid11_part74 : Audit := .split 20 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 24 (4,false),
.last 22 (4,false),
.cycle 0 21 true (0),
.last 41 (4,false),
.last 29 (4,false),
.cycle 28 1 false (6),
.last 21 (4,false),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.last 23 (4,false),
.cycle 34 1 false (8),
.cycle 32 1 false (8),
.last 23 (4,false),
.cycle 17 4 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.last 21 (4,false),
.cycle 19 2 true (4)
])
theorem kid11_part74_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part74) = true := by rfl

def kid11_part50 : Audit := .split 18 (4,true) (byMove [(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part68),(kid11_part69),(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74)])

theorem kid11_part50_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part50) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part51),(kid11_part52),(kid11_part53),(kid11_part54),(kid11_part55),(kid11_part56),(kid11_part57),(kid11_part58),(kid11_part59),(kid11_part60),(kid11_part61),(kid11_part62),(kid11_part63),(kid11_part64),(kid11_part65),(kid11_part66),(kid11_part67),(kid11_part68),(kid11_part69),(kid11_part70),(kid11_part71),(kid11_part72),(kid11_part73),(kid11_part74)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part51_checked

  · exact kid11_part57_checked

  · exact kid11_part63_checked

  · exact kid11_part69_checked

  · exact kid11_part52_checked

  · exact kid11_part58_checked

  · exact kid11_part64_checked

  · exact kid11_part70_checked

  · exact kid11_part53_checked

  · exact kid11_part59_checked

  · exact kid11_part65_checked

  · exact kid11_part71_checked

  · exact kid11_part54_checked

  · exact kid11_part60_checked

  · exact kid11_part66_checked

  · exact kid11_part72_checked

  · exact kid11_part55_checked

  · exact kid11_part61_checked

  · exact kid11_part67_checked

  · exact kid11_part73_checked

  · exact kid11_part56_checked

  · exact kid11_part62_checked

  · exact kid11_part68_checked

  · exact kid11_part74_checked

def kid11_part75 : Audit := .split 20 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 31 1 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.cycle 31 1 false (7),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 24 1 false (4),
.cycle 33 1 false (5),
.cycle 20 3 false (4),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 30 1 false (6),
.cycle 34 1 false (8),
.last 22 (4,false),
.last 24 (4,false)
]),
.cycle 26 1 false (2),
.cycle 0 21 true (0),
.cycle 17 22 true (3),
.cycle 32 1 false (8),
.cycle 28 1 false (6),
.split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 30 1 false (6),
.cycle 34 1 false (8),
.last 23 (4,true),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.cycle 17 25 true (3),
.cycle 9 13 true (0),
.cycle 32 1 false (8),
.cycle 21 1 true (5),
.cycle 36 1 false (8),
.cycle 2 23 true (0),
.cycle 20 3 true (4),
.cycle 0 24 true (0),
.cycle 28 1 false (6),
.last 23 (4,true),
.cycle 27 1 false (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 17 22 true (3),
.cycle 17 30 true (3),
.cycle 21 1 true (5),
.cycle 19 3 true (4)
]),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.cycle 20 6 true (3),
.cycle 34 1 false (8),
.cycle 32 1 false (8),
.split 21 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 25 (4,false),
.last 27 (4,false),
.cycle 20 3 false (4),
.cycle 34 1 false (8),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (2),
.cycle 17 24 true (3),
.cycle 32 1 false (6),
.cycle 20 2 true (3),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 18 4 true (3)
]),
.cycle 17 4 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.split 21 (4,false) (byMove [
.cycle 17 24 true (3),
.cycle 32 1 false (6),
.cycle 20 2 true (4),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 18 4 true (4),
.cycle 0 22 true (0),
.cycle 17 23 true (3),
.cycle 18 11 true (4),
.cycle 3 19 true (0),
.cycle 21 1 true (5),
.cycle 2 21 true (0),
.cycle 40 1 false (8),
.cycle 18 5 true (4),
.last 23 (4,true),
.cycle 17 27 true (3),
.last 22 (4,true),
.cycle 17 5 true (3),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 17 28 true (3),
.cycle 21 1 true (5),
.cycle 19 3 true (4)
]),
.cycle 19 2 true (4)
])
theorem kid11_part75_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part75) = true := by rfl

def kid11_part3 : Audit := .split 17 (5,true) (byMove [(kid11_part4),(kid11_part5),(kid11_part6),(kid11_part7),(kid11_part8),(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part20),(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part75)])

theorem kid11_part3_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (kid11_part3) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,2⟩)) (5,true) (some mv)) (byMove [(kid11_part4),(kid11_part5),(kid11_part6),(kid11_part7),(kid11_part8),(kid11_part9),(kid11_part10),(kid11_part11),(kid11_part12),(kid11_part13),(kid11_part14),(kid11_part15),(kid11_part16),(kid11_part17),(kid11_part18),(kid11_part19),(kid11_part20),(kid11_part45),(kid11_part46),(kid11_part47),(kid11_part48),(kid11_part49),(kid11_part50),(kid11_part75)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part4_checked

  · exact kid11_part10_checked

  · exact kid11_part16_checked

  · exact kid11_part46_checked

  · exact kid11_part5_checked

  · exact kid11_part11_checked

  · exact kid11_part17_checked

  · exact kid11_part47_checked

  · exact kid11_part6_checked

  · exact kid11_part12_checked

  · exact kid11_part18_checked

  · exact kid11_part48_checked

  · exact kid11_part7_checked

  · exact kid11_part13_checked

  · exact kid11_part19_checked

  · exact kid11_part49_checked

  · exact kid11_part8_checked

  · exact kid11_part14_checked

  · exact kid11_part20_checked

  · exact kid11_part50_checked

  · exact kid11_part9_checked

  · exact kid11_part15_checked

  · exact kid11_part45_checked

  · exact kid11_part75_checked

def kid11_part77 : Audit := .cycle 0 16 true (0)
theorem kid11_part77_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part77) = true := by rfl

def kid11_part78 : Audit := .cycle 24 1 false (4)
theorem kid11_part78_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part78) = true := by rfl

def kid11_part79 : Audit := .cycle 17 1 false (3)
theorem kid11_part79_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part79) = true := by rfl

def kid11_part80 : Audit := .cycle 16 1 false (2)
theorem kid11_part80_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part80) = true := by rfl

def kid11_part81 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 25 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 25 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 true (2),
.cycle 18 1 false (2),
.cycle 31 1 false (5),
.split 18 (2,true) (byMove [
.cycle 28 1 false (4),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 0 19 true (0),
.cycle 17 21 true (1),
.cycle 9 11 true (0),
.cycle 25 1 false (3),
.cycle 16 3 true (1),
.cycle 31 1 false (5),
.cycle 22 1 false (2),
.cycle 14 5 false (3),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 11 31 true (0),
.cycle 14 9 false (3),
.cycle 0 21 true (0)
]),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 24 1 false (4),
.cycle 28 1 false (6),
.cycle 16 1 true (2),
.cycle 0 19 true (0)
])
theorem kid11_part81_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part81) = true := by rfl

def kid11_part82 : Audit := .cycle 17 1 false (1)
theorem kid11_part82_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part82) = true := by rfl

def kid11_part83 : Audit := .cycle 0 16 true (0)
theorem kid11_part83_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part83) = true := by rfl

def kid11_part84 : Audit := .cycle 24 1 false (6)
theorem kid11_part84_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part84) = true := by rfl

def kid11_part85 : Audit := .cycle 17 1 false (5)
theorem kid11_part85_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part85) = true := by rfl

def kid11_part86 : Audit := .cycle 16 1 false (4)
theorem kid11_part86_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part86) = true := by rfl

def kid11_part87 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 25 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 25 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.cycle 16 1 true (4),
.cycle 18 1 false (4),
.cycle 31 1 false (7),
.split 18 (2,true) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 15 4 true (3),
.cycle 0 19 true (0),
.last 35 (4,true),
.cycle 9 11 true (0),
.cycle 25 1 false (5),
.cycle 16 3 true (3),
.cycle 31 1 false (7),
.cycle 22 1 false (4),
.cycle 14 5 true (2),
.cycle 31 1 false (7),
.cycle 29 1 false (7),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.last 39 (4,true),
.cycle 14 6 true (2),
.cycle 0 21 true (0)
]),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 16 1 false (4),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 24 1 false (6),
.cycle 28 1 false (8),
.cycle 16 1 true (4),
.cycle 0 19 true (0)
])
theorem kid11_part87_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part87) = true := by rfl

def kid11_part88 : Audit := .cycle 17 1 false (3)
theorem kid11_part88_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part88) = true := by rfl

def kid11_part89 : Audit := .cycle 30 1 false (6)
theorem kid11_part89_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part89) = true := by rfl

def kid11_part90 : Audit := .split 17 (2,true) (byMove [
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 27 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 0 19 true (0),
.cycle 27 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.last 19 (4,false),
.cycle 20 1 false (2),
.cycle 33 1 false (5),
.cycle 16 3 false (3),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.last 19 (4,false),
.cycle 0 21 true (0)
]),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 44 1 false (6),
.cycle 9 10 true (0),
.cycle 24 1 false (4),
.split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.last 20 (4,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.last 38 (4,true),
.last 30 (4,true),
.cycle 9 10 true (0),
.cycle 18 1 true (4),
.cycle 26 1 false (4),
.last 44 (4,true),
.cycle 16 3 true (2),
.cycle 0 21 true (0),
.cycle 24 1 false (4),
.last 20 (4,true),
.cycle 35 1 false (7),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.last 36 (4,true),
.last 42 (4,true),
.cycle 18 1 true (4),
.cycle 0 21 true (0)
]),
.cycle 30 1 false (6),
.cycle 21 1 false (3),
.cycle 14 4 true (2),
.cycle 30 1 false (6),
.cycle 28 1 false (6),
.split 18 (4,true) (byMove [
.cycle 16 8 true (1),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.last 20 (4,false),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 15 4 true (2),
.cycle 13 12 true (1),
.cycle 16 3 false (3),
.cycle 30 1 false (6),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 48 1 false (6),
.cycle 32 1 false (6),
.cycle 17 2 true (2),
.cycle 0 20 true (0),
.last 20 (4,false),
.cycle 14 6 true (2)
]),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.split 18 (4,false) (byMove [
.last 38 (4,true),
.cycle 32 1 false (6),
.cycle 17 2 true (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 14 6 true (2),
.cycle 0 19 true (0),
.last 37 (4,true),
.cycle 9 11 true (0),
.cycle 3 16 true (0),
.cycle 18 1 true (4),
.last 42 (4,true),
.cycle 28 1 false (4),
.cycle 14 5 true (2),
.last 20 (4,true),
.last 40 (4,true),
.last 19 (4,true),
.last 24 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.last 41 (4,true),
.cycle 18 1 true (4),
.cycle 0 21 true (0)
]),
.cycle 0 20 true (0)
])
theorem kid11_part90_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part90) = true := by rfl

def kid11_part91 : Audit := .cycle 0 18 true (0)
theorem kid11_part91_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part91) = true := by rfl

def kid11_part92 : Audit := .cycle 16 1 false (2)
theorem kid11_part92_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part92) = true := by rfl

def kid11_part94 : Audit := .split 19 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 33 1 false (5),
.cycle 23 1 false (1),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 3 39 true (0),
.cycle 9 12 true (0),
.cycle 3 17 true (0),
.cycle 0 21 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 9, 8, 64, 16, 64],64⟩,
.cycle 29 1 false (3),
.cycle 14 12 true (1),
.cycle 27 1 false (3),
.cycle 12 31 true (0),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.last 42 (4,true),
.cycle 0 22 true (0)
])
theorem kid11_part94_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part94) = true := by rfl

def kid11_part95 : Audit := .cycle 0 20 true (0)
theorem kid11_part95_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part95) = true := by rfl

def kid11_part96 : Audit := .cycle 18 1 false (2)
theorem kid11_part96_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part96) = true := by rfl

def kid11_part97 : Audit := .cycle 17 1 false (1)
theorem kid11_part97_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part97) = true := by rfl

def kid11_part98 : Audit := .cycle 16 1 false (2)
theorem kid11_part98_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part98) = true := by rfl

def kid11_part99 : Audit := .cycle 18 1 false (0)
theorem kid11_part99_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part99) = true := by rfl

def kid11_part100 : Audit := .cycle 26 1 false (6)
theorem kid11_part100_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part100) = true := by rfl

def kid11_part101 : Audit := .cycle 19 1 false (3)
theorem kid11_part101_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part101) = true := by rfl

def kid11_part102 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (4),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 20 1 false (6),
.cycle 19 1 false (3),
.cycle 32 1 false (6),
.cycle 14 6 true (2),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 9 11 true (0),
.cycle 0 20 true (0)
])
theorem kid11_part102_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part102) = true := by rfl

def kid11_part103 : Audit := .cycle 0 18 true (0)
theorem kid11_part103_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part103) = true := by rfl

def kid11_part104 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 true (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 18 1 true (4),
.cycle 19 1 false (3),
.cycle 32 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 18 1 true (4),
.cycle 0 20 true (0)
])
theorem kid11_part104_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part104) = true := by rfl

def kid11_part105 : Audit := .cycle 15 2 true (2)
theorem kid11_part105_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part105) = true := by rfl

def kid11_part106 : Audit := .cycle 13 8 true (1)
theorem kid11_part106_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part106) = true := by rfl

def kid11_part107 : Audit := .split 18 (2,true) (byMove [
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 34 1 false (6),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 13 27 true (1),
.cycle 27 1 false (3),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 2, 8, 64],[8, 10, 8, 8, 64, 16, 64],64⟩,
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 14 7 false (3),
.cycle 13 6 true (1),
.cycle 14 5 false (3),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 3 39 true (0),
.cycle 39 11 false (5),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.last 19 (4,true),
.last 20 (4,true)
])
theorem kid11_part107_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part107) = true := by rfl

def kid11_part108 : Audit := .cycle 28 1 false (6)
theorem kid11_part108_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part108) = true := by rfl

def kid11_part109 : Audit := .cycle 17 1 false (1)
theorem kid11_part109_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part109) = true := by rfl

def kid11_part110 : Audit := .cycle 16 1 false (2)
theorem kid11_part110_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part110) = true := by rfl

def kid11_part111 : Audit := .cycle 18 1 false (0)
theorem kid11_part111_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part111) = true := by rfl

def kid11_part112 : Audit := .cycle 44 1 false (6)
theorem kid11_part112_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part112) = true := by rfl

def kid11_part113 : Audit := .cycle 30 1 false (6)
theorem kid11_part113_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part113) = true := by rfl

def kid11_part114 : Audit := .split 17 (2,true) (byMove [
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 44 1 false (6),
.cycle 9 10 true (0),
.cycle 24 1 false (4),
.last 36 (4,true),
.cycle 30 1 false (6),
.cycle 21 1 false (3),
.cycle 14 4 true (2),
.cycle 30 1 false (6),
.cycle 28 1 false (6),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 2 17 true (0),
.cycle 0 20 true (0)
])
theorem kid11_part114_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part114) = true := by rfl

def kid11_part115 : Audit := .cycle 0 18 true (0)
theorem kid11_part115_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part115) = true := by rfl

def kid11_part116 : Audit := .split 17 (4,true) (byMove [
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 true (1),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 44 1 false (6),
.cycle 9 10 true (0),
.cycle 24 1 false (4),
.cycle 18 1 true (4),
.cycle 30 1 false (6),
.cycle 21 1 false (3),
.cycle 14 4 true (2),
.last 18 (2,true),
.cycle 28 1 false (6),
.cycle 16 3 false (3),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.cycle 18 1 true (4),
.cycle 0 20 true (0)
])
theorem kid11_part116_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part116) = true := by rfl

def kid11_part117 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 36 1 false (6),
.cycle 20 1 false (0),
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 23 true (0),
.cycle 15 4 true (2),
.cycle 13 12 true (1),
.last 20 (2,true),
.cycle 30 1 false (6),
.cycle 19 1 false (1),
.cycle 16 3 false (3),
.cycle 20 1 false (0),
.cycle 48 1 false (6),
.cycle 32 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 23 true (0),
.cycle 17 2 true (2)
])
theorem kid11_part117_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part117) = true := by rfl

def kid11_part93 : Audit := .split 16 (4,false) (byMove [(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116),(kid11_part117)])

theorem kid11_part93_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part93) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) 16 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part94),(kid11_part95),(kid11_part96),(kid11_part97),(kid11_part98),(kid11_part99),(kid11_part100),(kid11_part101),(kid11_part102),(kid11_part103),(kid11_part104),(kid11_part105),(kid11_part106),(kid11_part107),(kid11_part108),(kid11_part109),(kid11_part110),(kid11_part111),(kid11_part112),(kid11_part113),(kid11_part114),(kid11_part115),(kid11_part116),(kid11_part117)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part94_checked

  · exact kid11_part100_checked

  · exact kid11_part106_checked

  · exact kid11_part112_checked

  · exact kid11_part95_checked

  · exact kid11_part101_checked

  · exact kid11_part107_checked

  · exact kid11_part113_checked

  · exact kid11_part96_checked

  · exact kid11_part102_checked

  · exact kid11_part108_checked

  · exact kid11_part114_checked

  · exact kid11_part97_checked

  · exact kid11_part103_checked

  · exact kid11_part109_checked

  · exact kid11_part115_checked

  · exact kid11_part98_checked

  · exact kid11_part104_checked

  · exact kid11_part110_checked

  · exact kid11_part116_checked

  · exact kid11_part99_checked

  · exact kid11_part105_checked

  · exact kid11_part111_checked

  · exact kid11_part117_checked

def kid11_part118 : Audit := .cycle 17 1 false (1)
theorem kid11_part118_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part118) = true := by rfl

def kid11_part119 : Audit := .cycle 0 16 true (0)
theorem kid11_part119_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part119) = true := by rfl

def kid11_part120 : Audit := .cycle 1 15 true (0)
theorem kid11_part120_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part120) = true := by rfl

def kid11_part121 : Audit := .cycle 23 1 false (5)
theorem kid11_part121_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part121) = true := by rfl

def kid11_part122 : Audit := .cycle 27 1 false (7)
theorem kid11_part122_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part122) = true := by rfl

def kid11_part124 : Audit := .cycle 26 1 false (6)
theorem kid11_part124_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part124) = true := by rfl

def kid11_part125 : Audit := .cycle 19 1 false (3)
theorem kid11_part125_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part125) = true := by rfl

def kid11_part126 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 32 1 false (6),
.cycle 14 6 true (2),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 16 2 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part126_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part126) = true := by rfl

def kid11_part127 : Audit := .cycle 0 18 true (0)
theorem kid11_part127_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part127) = true := by rfl

def kid11_part128 : Audit := .split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 19 1 false (3),
.cycle 32 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 16 2 true (3),
.cycle 0 20 true (0)
])
theorem kid11_part128_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part128) = true := by rfl

def kid11_part129 : Audit := .cycle 15 2 true (3)
theorem kid11_part129_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part129) = true := by rfl

def kid11_part130 : Audit := .cycle 0 17 true (0)
theorem kid11_part130_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part130) = true := by rfl

def kid11_part131 : Audit := .split 33 (4,true) (byMove [
.cycle 43 1 false (9),
.cycle 36 1 false (6),
.last 34 (2,true),
.cycle 0 35 true (0),
.cycle 44 1 false (8),
.cycle 15 19 true (3),
.cycle 0 34 true (0),
.cycle 17 17 true (3),
.cycle 9 26 true (0),
.cycle 40 1 false (8),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 6, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 46 1 false (10),
.cycle 37 1 false (7),
.cycle 14 20 true (2),
.last 34 (2,true),
.cycle 44 1 false (10),
.cycle 14 22 true (2),
.cycle 32 2 true (6),
.cycle 0 34 true (0),
.cycle 1 33 true (0),
.cycle 2 32 true (0),
.cycle 0 56 true (0),
.cycle 16 18 true (3),
.cycle 0 36 true (0)
])
theorem kid11_part131_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part131) = true := by rfl

def kid11_part132 : Audit := .cycle 9 9 true (0)
theorem kid11_part132_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part132) = true := by rfl

def kid11_part133 : Audit := .cycle 23 1 false (5)
theorem kid11_part133_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part133) = true := by rfl

def kid11_part134 : Audit := .cycle 16 1 true (4)
theorem kid11_part134_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part134) = true := by rfl

def kid11_part135 : Audit := .cycle 29 1 false (7)
theorem kid11_part135_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part135) = true := by rfl

def kid11_part136 : Audit := .cycle 20 1 false (4)
theorem kid11_part136_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part136) = true := by rfl

def kid11_part137 : Audit := .cycle 14 3 true (2)
theorem kid11_part137_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part137) = true := by rfl

def kid11_part138 : Audit := .split 17 (2,true) (byMove [
.last 38 (4,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 35 1 false (7),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.cycle 20 1 false (6),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 true (3),
.cycle 14 5 true (2),
.last 22 (4,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.last 35 (4,true),
.cycle 31 1 false (7),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 true (3)
])
theorem kid11_part138_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part138) = true := by rfl

def kid11_part139 : Audit := .cycle 27 1 false (7)
theorem kid11_part139_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part139) = true := by rfl

def kid11_part140 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 false (5),
.cycle 15 3 true (3),
.cycle 14 5 true (2),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 36 true (0),
.cycle 31 1 false (7),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 3 true (3),
.cycle 15 3 true (3)
])
theorem kid11_part140_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part140) = true := by rfl

def kid11_part141 : Audit := .split 18 (4,true) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 22 1 false (0),
.cycle 15 4 true (3),
.cycle 0 19 true (0),
.cycle 17 17 true (3),
.cycle 9 11 true (0),
.cycle 25 1 false (5),
.cycle 36 1 false (8),
.cycle 31 1 false (7),
.cycle 22 1 false (4),
.cycle 14 5 true (2),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 22 1 false (0),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 0 41 true (0),
.cycle 16 3 true (3),
.cycle 0 21 true (0)
])
theorem kid11_part141_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part141) = true := by rfl

def kid11_part142 : Audit := .cycle 0 17 true (0)
theorem kid11_part142_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part142) = true := by rfl

def kid11_part143 : Audit := .cycle 1 16 true (0)
theorem kid11_part143_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part143) = true := by rfl

def kid11_part144 : Audit := .cycle 2 15 true (0)
theorem kid11_part144_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part144) = true := by rfl

def kid11_part145 : Audit := .split 37 (4,true) (byMove [
.last 40 (2,true),
.cycle 40 1 false (6),
.last 38 (2,true),
.cycle 53 1 false (11),
.last 44 (2,true),
.cycle 0 41 true (0),
.cycle 19 19 true (3),
.cycle 46 1 false (8),
.last 38 (2,true),
.cycle 0 39 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 14, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 15 23 true (3),
.cycle 13 25 true (1),
.cycle 14 27 true (2),
.last 38 (2,true),
.cycle 42 1 false (8),
.cycle 5 35 true (0),
.cycle 36 2 true (6),
.cycle 0 56 true (0),
.cycle 17 23 true (3),
.last 38 (2,true),
.cycle 0 39 true (0),
.cycle 16 23 true (3),
.cycle 15 23 true (3)
])
theorem kid11_part145_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part145) = true := by rfl

def kid11_part146 : Audit := .cycle 16 1 true (4)
theorem kid11_part146_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part146) = true := by rfl

def kid11_part147 : Audit := .cycle 0 19 true (0)
theorem kid11_part147_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part147) = true := by rfl

def kid11_part123 : Audit := .split 16 (4,false) (byMove [(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142),(kid11_part143),(kid11_part144),(kid11_part145),(kid11_part146),(kid11_part147)])

theorem kid11_part123_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part123) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) 16 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part124),(kid11_part125),(kid11_part126),(kid11_part127),(kid11_part128),(kid11_part129),(kid11_part130),(kid11_part131),(kid11_part132),(kid11_part133),(kid11_part134),(kid11_part135),(kid11_part136),(kid11_part137),(kid11_part138),(kid11_part139),(kid11_part140),(kid11_part141),(kid11_part142),(kid11_part143),(kid11_part144),(kid11_part145),(kid11_part146),(kid11_part147)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid11_part129_checked

  · exact kid11_part135_checked

  · exact kid11_part141_checked

  · exact kid11_part147_checked

def kid11_part148 : Audit := .cycle 0 18 true (0)
theorem kid11_part148_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part148) = true := by rfl

def kid11_part76 : Audit := .split 15 (5,true) (byMove [(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91),(kid11_part92),(kid11_part93),(kid11_part118),(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part123),(kid11_part148)])

theorem kid11_part76_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (kid11_part76) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,3⟩)) (5,true) (some mv)) (byMove [(kid11_part77),(kid11_part78),(kid11_part79),(kid11_part80),(kid11_part81),(kid11_part82),(kid11_part83),(kid11_part84),(kid11_part85),(kid11_part86),(kid11_part87),(kid11_part88),(kid11_part89),(kid11_part90),(kid11_part91),(kid11_part92),(kid11_part93),(kid11_part118),(kid11_part119),(kid11_part120),(kid11_part121),(kid11_part122),(kid11_part123),(kid11_part148)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part77_checked

  · exact kid11_part83_checked

  · exact kid11_part89_checked

  · exact kid11_part119_checked

  · exact kid11_part78_checked

  · exact kid11_part84_checked

  · exact kid11_part90_checked

  · exact kid11_part120_checked

  · exact kid11_part79_checked

  · exact kid11_part85_checked

  · exact kid11_part91_checked

  · exact kid11_part121_checked

  · exact kid11_part80_checked

  · exact kid11_part86_checked

  · exact kid11_part92_checked

  · exact kid11_part122_checked

  · exact kid11_part81_checked

  · exact kid11_part87_checked

  · exact kid11_part93_checked

  · exact kid11_part123_checked

  · exact kid11_part82_checked

  · exact kid11_part88_checked

  · exact kid11_part118_checked

  · exact kid11_part148_checked

def kid11_part150 : Audit := .cycle 0 10 true (0)
theorem kid11_part150_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part150) = true := by rfl

def kid11_part151 : Audit := .cycle 1 9 true (1)
theorem kid11_part151_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part151) = true := by rfl

def kid11_part152 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 28 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 28 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 33 1 false (3),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 25 1 false (1),
.cycle 26 1 false (0),
.cycle 0 23 true (0),
.cycle 33 1 false (5),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 25 1 false (3),
.cycle 26 1 false (2),
.cycle 18 5 false (4),
.cycle 16 9 false (4),
.cycle 0 25 true (0),
.cycle 23 1 false (1),
.cycle 25 1 false (1),
.cycle 26 1 false (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 32 1 false (4),
.cycle 36 1 false (6),
.cycle 21 2 true (2),
.last 24 (4,true)
]),
.split 19 (2,true) (byMove [
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 20 true (0),
.cycle 52 1 false (6),
.cycle 10 10 true (0),
.cycle 28 1 false (4),
.cycle 30 1 false (4),
.cycle 26 1 false (2),
.cycle 25 1 false (3),
.cycle 16 4 true (2),
.cycle 34 1 false (6),
.cycle 32 1 false (6),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (2),
.cycle 19 2 true (3),
.last 21 (4,true)
]),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 22 1 false (4),
.cycle 23 1 false (3),
.cycle 18 5 false (4),
.cycle 16 6 true (2),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.cycle 18 2 true (3),
.last 21 (4,true)
]),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 30 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 30 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 22 1 false (4),
.cycle 23 1 false (3),
.last 24 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 23 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 29 1 false (5),
.cycle 33 1 false (7),
.last 21 (2,true),
.cycle 18 2 true (3)
])
])
theorem kid11_part152_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part152) = true := by rfl

def kid11_part153 : Audit := .cycle 17 1 false (1)
theorem kid11_part153_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part153) = true := by rfl

def kid11_part154 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (4),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 21 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 11 5 false (1),
.split 14 (2,true) (byMove [
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 9 15 false (4),
.last 22 (5,true),
.cycle 21 1 false (1),
.cycle 10 5 false (2),
.cycle 11 5 false (1),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 27 1 false (3),
.cycle 25 1 false (3),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.cycle 2 13 false (4),
.cycle 9 19 false (5),
.last 18 (5,true),
.last 18 (5,true)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 11 2 true (0),
.cycle 12 2 true (0)
])
theorem kid11_part154_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part154) = true := by rfl

def kid11_part155 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (4),
.cycle 20 2 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 20 2 false (4),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 10 5 false (2),
.split 14 (2,true) (byMove [
.cycle 23 2 false (3),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.last 27 (4,true),
.cycle 12 10 true (-1),
.cycle 20 2 false (2),
.last 17 (4,true),
.cycle 10 5 false (2),
.cycle 17 2 false (1),
.cycle 12 4 true (-1),
.cycle 26 2 false (4),
.cycle 24 2 false (4),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 17 true (-1),
.cycle 12 16 true (-1),
.cycle 2 13 false (4),
.cycle 8 19 false (5),
.cycle 12 6 true (-1),
.last 16 (4,true)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 2 false (3),
.cycle 23 2 false (5),
.cycle 11 2 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 2 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 22 2 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 2 false (1),
.cycle 15 2 false (1),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 2 false (3),
.cycle 25 2 false (5),
.cycle 11 4 true (0),
.cycle 13 2 true (0)
])
])
theorem kid11_part155_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part155) = true := by rfl

def kid11_part156 : Audit := .cycle 0 10 true (0)
theorem kid11_part156_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part156) = true := by rfl

def kid11_part157 : Audit := .cycle 1 9 true (1)
theorem kid11_part157_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part157) = true := by rfl

def kid11_part159 : Audit := .split 22 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 1, 64],64⟩,
.cycle 0 28 true (0),
.cycle 26 1 false (2),
.cycle 0 36 true (0),
.last 23 (4,true),
.cycle 0 28 true (0),
.cycle 0 51 true (0),
.cycle 0 63 true (0),
.cycle 0 44 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 0 30 true (0),
.cycle 5 18 true (0),
.last 23 (4,true),
.cycle 19 8 true (2),
.cycle 0 63 true (0),
.cycle 0 34 true (0),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.last 53 (4,true)
])
theorem kid11_part159_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part159) = true := by rfl

def kid11_part160 : Audit := .cycle 0 55 true (0)
theorem kid11_part160_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part160) = true := by rfl

def kid11_part161 : Audit := .cycle 21 1 false (3)
theorem kid11_part161_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part161) = true := by rfl

def kid11_part162 : Audit := .cycle 20 1 false (2)
theorem kid11_part162_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part162) = true := by rfl

def kid11_part163 : Audit := .cycle 34 1 false (10)
theorem kid11_part163_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part163) = true := by rfl

def kid11_part164 : Audit := .cycle 23 1 false (3)
theorem kid11_part164_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part164) = true := by rfl

def kid11_part165 : Audit := .cycle 25 1 false (7)
theorem kid11_part165_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part165) = true := by rfl

def kid11_part166 : Audit := .cycle 32 1 false (10)
theorem kid11_part166_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part166) = true := by rfl

def kid11_part167 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 23 1 false (7),
.cycle 47 1 false (11),
.cycle 31 1 false (7),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.cycle 20 2 true (3),
.cycle 36 1 false (10),
.cycle 0 57 true (0),
.cycle 33 1 false (9),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 31 1 false (9)
])
theorem kid11_part167_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part167) = true := by rfl

def kid11_part168 : Audit := .cycle 32 1 false (10)
theorem kid11_part168_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part168) = true := by rfl

def kid11_part169 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 0 24 true (0),
.cycle 24 1 false (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 24 1 false (8),
.cycle 24 1 false (8),
.cycle 9 15 true (0),
.last 22 (2,true),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.last 22 (2,true),
.cycle 36 1 false (10),
.cycle 0 57 true (0),
.cycle 34 1 false (10),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 26 true (4),
.cycle 32 2 true (8)
])
theorem kid11_part169_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part169) = true := by rfl

def kid11_part170 : Audit := .cycle 25 1 false (7)
theorem kid11_part170_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part170) = true := by rfl

def kid11_part171 : Audit := .cycle 24 12 true (4)
theorem kid11_part171_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part171) = true := by rfl

def kid11_part172 : Audit := .split 21 (2,true) (byMove [
.cycle 39 1 false (9),
.cycle 38 1 false (10),
.cycle 24 1 false (2),
.cycle 0 29 true (0),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 6 16 true (0),
.cycle 48 14 true (8),
.cycle 10 14 true (0),
.cycle 0 55 true (0),
.last 22 (4,true),
.cycle 25 12 true (4),
.cycle 37 1 false (7),
.cycle 18 4 true (2),
.cycle 44 1 false (10),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.cycle 2 22 true (0),
.cycle 22 32 true (3),
.last 22 (4,true),
.last 33 (4,true)
])
theorem kid11_part172_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part172) = true := by rfl

def kid11_part173 : Audit := .cycle 27 1 false (7)
theorem kid11_part173_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part173) = true := by rfl

def kid11_part174 : Audit := .cycle 20 1 false (2)
theorem kid11_part174_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part174) = true := by rfl

def kid11_part175 : Audit := .split 21 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 61 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 36 1 false (10),
.cycle 25 1 false (3),
.cycle 27 1 false (7),
.cycle 36 1 false (10),
.cycle 25 1 false (7),
.cycle 34 1 false (10),
.last 22 (4,true),
.cycle 31 1 false (7),
.cycle 28 14 true (4),
.cycle 18 6 true (2),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 31 1 false (7),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.cycle 2 22 true (0),
.cycle 5 83 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part175_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part175) = true := by rfl

def kid11_part176 : Audit := .cycle 29 1 false (7)
theorem kid11_part176_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part176) = true := by rfl

def kid11_part177 : Audit := .cycle 0 57 true (0)
theorem kid11_part177_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part177) = true := by rfl

def kid11_part178 : Audit := .cycle 1 21 true (0)
theorem kid11_part178_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part178) = true := by rfl

def kid11_part179 : Audit := .split 20 (2,true) (byMove [
.cycle 35 1 false (9),
.cycle 0 26 true (0),
.cycle 23 1 false (3),
.cycle 43 1 false (11),
.last 21 (4,true),
.cycle 0 24 true (0),
.cycle 0 73 true (0),
.cycle 31 47 true (5),
.cycle 49 1 false (13),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 60 true (3),
.cycle 33 1 false (9),
.cycle 35 1 false (9),
.cycle 29 1 false (7),
.cycle 27 1 false (7),
.last 21 (4,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 18 36 true (2),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 2 20 true (0)
])
theorem kid11_part179_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part179) = true := by rfl

def kid11_part180 : Audit := .cycle 5 73 true (0)
theorem kid11_part180_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part180) = true := by rfl

def kid11_part181 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 26 true (0),
.last 21 (2,true),
.cycle 25 9 true (4),
.cycle 24 1 false (4),
.last 23 (2,true),
.cycle 44 9 true (8),
.cycle 55 9 true (11),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 9 13 true (0),
.cycle 21 9 true (5),
.cycle 21 9 true (3),
.cycle 24 9 true (4),
.last 21 (2,true),
.cycle 27 1 false (7),
.last 23 (2,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 23 9 true (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 9 true (5),
.cycle 21 9 true (5)
])
theorem kid11_part181_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part181) = true := by rfl

def kid11_part182 : Audit := .split 23 (4,true) (byMove [
.cycle 19 26 true (3),
.cycle 47 1 false (9),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 28 1 false (4),
.cycle 33 1 false (3),
.cycle 0 24 true (0),
.cycle 19 25 true (3),
.cycle 19 26 true (3),
.cycle 3 21 true (0),
.cycle 20 13 true (4),
.cycle 19 30 true (3),
.cycle 45 1 false (9),
.last 29 (2,true),
.last 24 (2,true),
.cycle 19 29 true (3),
.last 27 (2,true),
.cycle 20 4 true (4),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 19 30 true (3),
.cycle 21 11 true (5),
.cycle 22 2 true (5)
])
theorem kid11_part182_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part182) = true := by rfl

def kid11_part158 : Audit := .split 19 (5,true) (byMove [(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171),(kid11_part172),(kid11_part173),(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182)])

theorem kid11_part158_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part158) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part159),(kid11_part160),(kid11_part161),(kid11_part162),(kid11_part163),(kid11_part164),(kid11_part165),(kid11_part166),(kid11_part167),(kid11_part168),(kid11_part169),(kid11_part170),(kid11_part171),(kid11_part172),(kid11_part173),(kid11_part174),(kid11_part175),(kid11_part176),(kid11_part177),(kid11_part178),(kid11_part179),(kid11_part180),(kid11_part181),(kid11_part182)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part159_checked

  · exact kid11_part165_checked

  · exact kid11_part171_checked

  · exact kid11_part177_checked

  · exact kid11_part160_checked

  · exact kid11_part166_checked

  · exact kid11_part172_checked

  · exact kid11_part178_checked

  · exact kid11_part161_checked

  · exact kid11_part167_checked

  · exact kid11_part173_checked

  · exact kid11_part179_checked

  · exact kid11_part162_checked

  · exact kid11_part168_checked

  · exact kid11_part174_checked

  · exact kid11_part180_checked

  · exact kid11_part163_checked

  · exact kid11_part169_checked

  · exact kid11_part175_checked

  · exact kid11_part181_checked

  · exact kid11_part164_checked

  · exact kid11_part170_checked

  · exact kid11_part176_checked

  · exact kid11_part182_checked

def kid11_part184 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 1, 64],64⟩,
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 32 1 false (6),
.cycle 0 21 true (0),
.cycle 0 52 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.cycle 0 29 true (0),
.cycle 3 20 true (0),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 0 49 true (0),
.last 21 (4,true),
.cycle 17 8 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 3 19 true (0),
.last 22 (4,true)
])
theorem kid11_part184_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part184) = true := by rfl

def kid11_part185 : Audit := .cycle 0 21 true (0)
theorem kid11_part185_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part185) = true := by rfl

def kid11_part186 : Audit := .cycle 19 1 false (3)
theorem kid11_part186_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part186) = true := by rfl

def kid11_part187 : Audit := .cycle 18 1 false (2)
theorem kid11_part187_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part187) = true := by rfl

def kid11_part188 : Audit := .cycle 19 1 false (3)
theorem kid11_part188_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part188) = true := by rfl

def kid11_part189 : Audit := .cycle 20 1 false (2)
theorem kid11_part189_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part189) = true := by rfl

def kid11_part190 : Audit := .cycle 28 1 false (8)
theorem kid11_part190_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part190) = true := by rfl

def kid11_part191 : Audit := .cycle 21 1 false (5)
theorem kid11_part191_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part191) = true := by rfl

def kid11_part192 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 20 1 false (6),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.cycle 24 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 0 21 true (0),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.cycle 27 1 false (7),
.last 20 (4,true)
])
theorem kid11_part192_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part192) = true := by rfl

def kid11_part193 : Audit := .cycle 0 19 true (0)
theorem kid11_part193_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part193) = true := by rfl

def kid11_part194 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 20 1 false (6),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 0 21 true (0),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.cycle 27 1 false (7),
.cycle 18 2 true (4)
])
theorem kid11_part194_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part194) = true := by rfl

def kid11_part195 : Audit := .cycle 21 1 false (5)
theorem kid11_part195_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part195) = true := by rfl

def kid11_part196 : Audit := .cycle 3 22 true (0)
theorem kid11_part196_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part196) = true := by rfl

def kid11_part197 : Audit := .split 19 (2,true) (byMove [
.cycle 33 1 false (7),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 32 1 false (6),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 10 12 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 3 22 true (0),
.cycle 29 1 false (5),
.cycle 16 4 true (2),
.cycle 27 1 false (5),
.cycle 25 1 false (5),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 3 20 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 26 (4,true)
])
theorem kid11_part197_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part197) = true := by rfl

def kid11_part198 : Audit := .cycle 30 1 false (8)
theorem kid11_part198_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part198) = true := by rfl

def kid11_part199 : Audit := .cycle 18 1 false (2)
theorem kid11_part199_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part199) = true := by rfl

def kid11_part200 : Audit := .cycle 30 1 false (8)
theorem kid11_part200_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part200) = true := by rfl

def kid11_part201 : Audit := .cycle 20 1 false (2)
theorem kid11_part201_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part201) = true := by rfl

def kid11_part202 : Audit := .cycle 0 48 true (0)
theorem kid11_part202_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part202) = true := by rfl

def kid11_part203 : Audit := .cycle 28 1 false (6)
theorem kid11_part203_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part203) = true := by rfl

def kid11_part204 : Audit := .split 18 (2,true) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 28 1 false (6),
.cycle 0 19 true (0),
.cycle 56 1 false (12),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.cycle 23 1 false (5),
.cycle 29 1 false (7),
.cycle 32 1 false (8),
.cycle 30 1 false (8),
.last 19 (4,true),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 3 17 true (0),
.last 20 (4,true)
])
theorem kid11_part204_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part204) = true := by rfl

def kid11_part205 : Audit := .cycle 0 19 true (0)
theorem kid11_part205_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part205) = true := by rfl

def kid11_part206 : Audit := .split 18 (4,true) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 false (3),
.cycle 28 1 false (6),
.cycle 0 19 true (0),
.cycle 56 1 false (12),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.cycle 23 1 false (5),
.cycle 29 1 false (7),
.last 19 (2,true),
.cycle 30 1 false (8),
.cycle 32 1 false (8),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 3 17 true (0),
.cycle 18 2 true (4)
])
theorem kid11_part206_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part206) = true := by rfl

def kid11_part207 : Audit := .split 20 (4,true) (byMove [
.cycle 31 1 false (7),
.cycle 24 1 false (4),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 23 1 false (3),
.cycle 26 1 false (2),
.cycle 0 21 true (0),
.cycle 17 22 true (3),
.cycle 32 1 false (8),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 30 1 false (6),
.cycle 25 1 false (5),
.last 26 (2,true),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 34 1 false (8),
.cycle 17 4 true (3),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.cycle 3 19 true (0),
.cycle 19 2 true (4)
])
theorem kid11_part207_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part207) = true := by rfl

def kid11_part183 : Audit := .split 17 (5,true) (byMove [(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196),(kid11_part197),(kid11_part198),(kid11_part199),(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207)])

theorem kid11_part183_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part183) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some mv)) (byMove [(kid11_part184),(kid11_part185),(kid11_part186),(kid11_part187),(kid11_part188),(kid11_part189),(kid11_part190),(kid11_part191),(kid11_part192),(kid11_part193),(kid11_part194),(kid11_part195),(kid11_part196),(kid11_part197),(kid11_part198),(kid11_part199),(kid11_part200),(kid11_part201),(kid11_part202),(kid11_part203),(kid11_part204),(kid11_part205),(kid11_part206),(kid11_part207)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part184_checked

  · exact kid11_part190_checked

  · exact kid11_part196_checked

  · exact kid11_part202_checked

  · exact kid11_part185_checked

  · exact kid11_part191_checked

  · exact kid11_part197_checked

  · exact kid11_part203_checked

  · exact kid11_part186_checked

  · exact kid11_part192_checked

  · exact kid11_part198_checked

  · exact kid11_part204_checked

  · exact kid11_part187_checked

  · exact kid11_part193_checked

  · exact kid11_part199_checked

  · exact kid11_part205_checked

  · exact kid11_part188_checked

  · exact kid11_part194_checked

  · exact kid11_part200_checked

  · exact kid11_part206_checked

  · exact kid11_part189_checked

  · exact kid11_part195_checked

  · exact kid11_part201_checked

  · exact kid11_part207_checked

def kid11_part208 : Audit := .cycle 9 1 true (3)
theorem kid11_part208_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part208) = true := by rfl

def kid11_part209 : Audit := .cycle 8 2 true (3)
theorem kid11_part209_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part209) = true := by rfl

def kid11_part210 : Audit := .cycle 6 8 true (2)
theorem kid11_part210_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part210) = true := by rfl

def kid11_part212 : Audit := .cycle 1 12 true (1)
theorem kid11_part212_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part212) = true := by rfl

def kid11_part213 : Audit := .split 21 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 28 5 false (3),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 22 5 false (0),
.cycle 22 5 false (0),
.cycle 0 22 true (0),
.cycle 28 5 false (5),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 22 5 false (2),
.cycle 22 5 false (2),
.cycle 17 6 true (0),
.cycle 22 5 false (1),
.cycle 0 24 true (0),
.cycle 22 1 false (0),
.cycle 22 5 false (0),
.cycle 22 5 false (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 27 5 false (4),
.cycle 31 5 false (6),
.cycle 19 3 true (0),
.last 23 (4,true)
])
theorem kid11_part213_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part213) = true := by rfl

def kid11_part214 : Audit := .cycle 25 1 false (1)
theorem kid11_part214_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part214) = true := by rfl

def kid11_part215 : Audit := .cycle 0 13 true (0)
theorem kid11_part215_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part215) = true := by rfl

def kid11_part216 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 9 4 true (2),
.last 21 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 12 2 true (2)
])
theorem kid11_part216_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part216) = true := by rfl

def kid11_part217 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 29 1 false (3),
.cycle 20 1 false (4),
.cycle 9 4 true (2),
.cycle 21 5 false (2),
.cycle 12 6 true (1),
.cycle 17 3 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (2),
.last 14 (4,true)
])
theorem kid11_part217_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part217) = true := by rfl

def kid11_part218 : Audit := .cycle 0 12 true (0)
theorem kid11_part218_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part218) = true := by rfl

def kid11_part219 : Audit := .cycle 1 11 true (1)
theorem kid11_part219_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part219) = true := by rfl

def kid11_part220 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 9 11 true (2),
.cycle 8 12 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 37 1 false (9),
.cycle 45 1 false (9),
.cycle 9 11 true (2),
.cycle 8 12 true (2),
.cycle 18 6 true (4),
.cycle 10 10 true (2),
.cycle 0 22 true (0),
.cycle 28 1 false (2),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 2, 16, 64],[0, 2, 8, 0, 64, 16, 64],64⟩,
.cycle 0 26 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (4),
.last 21 (4,true)
])
theorem kid11_part220_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part220) = true := by rfl

def kid11_part221 : Audit := .cycle 3 9 true (1)
theorem kid11_part221_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part221) = true := by rfl

def kid11_part222 : Audit := .cycle 9 3 true (2)
theorem kid11_part222_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part222) = true := by rfl

def kid11_part223 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 25 1 false (3),
.cycle 29 1 false (1),
.cycle 23 7 false (1),
.cycle 16 8 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 29 1 false (7),
.cycle 0 25 true (0),
.cycle 9 7 true (2),
.cycle 8 8 true (2),
.cycle 12 6 true (2),
.cycle 10 6 true (2),
.cycle 0 18 true (0),
.cycle 22 1 false (2),
.cycle 22 7 false (2),
.cycle 16 8 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 1 18 true (1),
.cycle 13 3 true (2),
.last 17 (4,true)
])
theorem kid11_part223_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part223) = true := by rfl

def kid11_part224 : Audit := .cycle 6 6 true (2)
theorem kid11_part224_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part224) = true := by rfl

def kid11_part225 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 23 1 false (3),
.cycle 25 1 false (1),
.cycle 20 5 false (1),
.cycle 16 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 35 1 false (7),
.cycle 0 23 true (0),
.cycle 9 5 true (2),
.cycle 8 6 true (2),
.cycle 12 6 true (2),
.cycle 10 4 true (2),
.cycle 0 16 true (0),
.cycle 20 1 false (2),
.cycle 20 5 false (1),
.cycle 16 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (2),
.last 15 (4,true)
])
theorem kid11_part225_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part225) = true := by rfl

def kid11_part226 : Audit := .cycle 1 15 true (1)
theorem kid11_part226_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part226) = true := by rfl

def kid11_part227 : Audit := .cycle 1 13 true (1)
theorem kid11_part227_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part227) = true := by rfl

def kid11_part228 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 19 1 false (1),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 21 (5,true),
.cycle 0 14 true (0),
.cycle 9 5 true (2),
.last 13 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 1 13 true (1),
.last 17 (5,true),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part228_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part228) = true := by rfl

def kid11_part229 : Audit := .split 12 (5,true) (byMove [
.cycle 10 8 true (1),
.cycle 0 16 true (0),
.cycle 21 1 false (3),
.cycle 19 1 false (1),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.cycle 0 20 true (0),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (2),
.cycle 14 6 true (2),
.cycle 17 3 false (1),
.cycle 1 15 true (1),
.cycle 18 1 false (2),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 1 17 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 15 (4,true)
])
theorem kid11_part229_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part229) = true := by rfl

def kid11_part230 : Audit := .cycle 0 12 true (0)
theorem kid11_part230_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part230) = true := by rfl

def kid11_part231 : Audit := .cycle 1 11 true (1)
theorem kid11_part231_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part231) = true := by rfl

def kid11_part232 : Audit := .cycle 2 10 true (1)
theorem kid11_part232_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part232) = true := by rfl

def kid11_part233 : Audit := .cycle 1 14 true (1)
theorem kid11_part233_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part233) = true := by rfl

def kid11_part234 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 24 9 false (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 43 (4,true),
.cycle 49 1 false (9),
.cycle 9 6 true (2),
.cycle 8 7 true (2),
.cycle 12 6 true (3),
.cycle 10 5 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 21 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (3),
.last 16 (4,true)
])
theorem kid11_part234_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part234) = true := by rfl

def kid11_part235 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.last 25 (5,true),
.cycle 33 1 false (1),
.cycle 0 15 true (0),
.last 17 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 9 5 true (2),
.last 17 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 17 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 16 (5,true),
.cycle 12 2 true (3)
])
theorem kid11_part235_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part235) = true := by rfl

def kid11_part211 : Audit := .split 11 (2,true) (byMove [(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229),(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235)])

theorem kid11_part211_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part211) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part212),(kid11_part213),(kid11_part214),(kid11_part215),(kid11_part216),(kid11_part217),(kid11_part218),(kid11_part219),(kid11_part220),(kid11_part221),(kid11_part222),(kid11_part223),(kid11_part224),(kid11_part225),(kid11_part226),(kid11_part227),(kid11_part228),(kid11_part229),(kid11_part230),(kid11_part231),(kid11_part232),(kid11_part233),(kid11_part234),(kid11_part235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part212_checked

  · exact kid11_part218_checked

  · exact kid11_part224_checked

  · exact kid11_part230_checked

  · exact kid11_part213_checked

  · exact kid11_part219_checked

  · exact kid11_part225_checked

  · exact kid11_part231_checked

  · exact kid11_part214_checked

  · exact kid11_part220_checked

  · exact kid11_part226_checked

  · exact kid11_part232_checked

  · exact kid11_part215_checked

  · exact kid11_part221_checked

  · exact kid11_part227_checked

  · exact kid11_part233_checked

  · exact kid11_part216_checked

  · exact kid11_part222_checked

  · exact kid11_part228_checked

  · exact kid11_part234_checked

  · exact kid11_part217_checked

  · exact kid11_part223_checked

  · exact kid11_part229_checked

  · exact kid11_part235_checked

def kid11_part236 : Audit := .cycle 0 12 true (0)
theorem kid11_part236_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part236) = true := by rfl

def kid11_part237 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 25 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 25 1 false (5),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 31 1 false (5),
.split 17 (2,true) (byMove [
.cycle 28 1 false (4),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 45 1 false (5),
.cycle 10 10 true (0),
.cycle 25 1 false (3),
.cycle 25 1 false (3),
.cycle 31 1 false (5),
.cycle 22 1 false (2),
.cycle 14 4 true (2),
.cycle 31 1 false (5),
.cycle 29 1 false (5),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 19 21 true (2),
.last 40 (4,true),
.last 19 (4,true)
]),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 24 1 false (4),
.cycle 28 1 false (6),
.cycle 28 1 false (6),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 27 1 false (3),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 27 1 false (5),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 33 1 false (5),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.cycle 30 1 false (6),
.cycle 16 2 true (3)
])
])
theorem kid11_part237_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part237) = true := by rfl

def kid11_part239 : Audit := .split 15 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 32768, 128, 256, 32768, 2, 256, 32768, 128, 256, 8, 32, 256, 32768, 262144],[2, 32, 256, 1, 256, 262144, 8192, 131072, 256, 4096, 256, 262144, 2, 32, 256, 1, 256, 262144, 262144],278540⟩,
.cycle 11 7 false (1),
.cycle 19 1 false (-1),
.last 19 (5,true),
.last 47 (5,true),
.last 16 (5,true),
.cycle 6 20 true (-1),
.last 17 (5,true),
.last 27 (5,true),
.last 39 (5,true),
.cycle 14 27 true (0),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 22 (5,true),
.last 19 (5,true),
.cycle 12 8 true (-1),
.last 16 (5,true),
.last 44 (5,true),
.last 17 (5,true),
.cycle 14 16 true (0),
.last 38 (5,true),
.cycle 16 5 true (1),
.last 16 (5,true)
])
theorem kid11_part239_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part239) = true := by rfl

def kid11_part240 : Audit := .split 29 (5,true) (byMove [
.cycle 0 30 true (-2),
.cycle 30 25 true (-3),
.cycle 41 1 false (1),
.cycle 38 1 false (0),
.cycle 19 11 false (3),
.cycle 8 22 false (4),
.cycle 0 30 true (-2),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 3, 2, 2],[33554432, 4194304, 2097152, 512, 1024, 16, 8192, 1073741824, 33554432, 2097152, 4194304, 65536, 1111564288, 1111564288, 1113694208, 32768, 65536, 65536, 33554432, 1073741824, 4194304, 2097152, 4194304, 268435456, 1073741824, 33554432, 2097152, 32768, 65536, 65536, 1073741824],[4194304, 1024, 1073741824, 33554432, 2, 4194304, 4194304, 4194304, 1073741824, 4194304, 8192, 4194304, 1111564288, 1111564288, 1073741824, 1111564288, 8192, 1111564288, 4194304, 4194304, 1073741824, 4194304, 33554432, 4194304, 1073741824, 65536, 1073741824, 33554432, 8192, 1073741824, 1073741824],1091072192⟩,
.last 42 (2,true),
.cycle 44 1 false (4),
.cycle 23 84 true (-4),
.far true 5 ⟨0,[0, 1, 2, 3, 2, 2, 4, 3, 2, 2],[33554432, 4194304, 2097152, 512, 1024, 16, 8192, 1073741824, 33554432, 2097152, 4194304, 65536, 1107369984, 1111564288, 1113694208, 32768, 65536, 65536, 33554432, 1073741824, 4194304, 2097152, 4194304, 268435456, 1073741824, 33554432, 2097152, 32768, 65536, 65536, 1073741824],[4194304, 1024, 1073741824, 33554432, 2, 1024, 4194304, 4194304, 1073741824, 4194304, 8192, 4194304, 1111564288, 65536, 1073741824, 1111564288, 8192, 65536, 4194304, 4194304, 1073741824, 4194304, 33554432, 4194304, 1073741824, 65536, 1073741824, 33554432, 8192, 65536, 1073741824],1091072192⟩,
.cycle 0 38 true (-2),
.last 31 (2,true),
.cycle 0 32 true (-2),
.cycle 38 1 false (0),
.cycle 19 11 false (3),
.cycle 8 22 false (4),
.last 59 (2,true),
.cycle 1 29 true (-2),
.last 51 (2,true),
.last 234 (2,true),
.cycle 0 35 true (-2),
.cycle 173 17 false (1)
])
theorem kid11_part240_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part240) = true := by rfl

def kid11_part241 : Audit := .cycle 14 1 false (0)
theorem kid11_part241_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part241) = true := by rfl

def kid11_part242 : Audit := .cycle 13 1 false (-1)
theorem kid11_part242_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part242) = true := by rfl

def kid11_part243 : Audit := .cycle 13 1 false (-1)
theorem kid11_part243_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part243) = true := by rfl

def kid11_part244 : Audit := .cycle 14 1 false (-2)
theorem kid11_part244_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part244) = true := by rfl

def kid11_part245 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 24 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 24 1 false (6),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.cycle 30 1 false (6),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 23 1 false (5),
.cycle 27 1 false (7),
.cycle 27 1 false (7),
.cycle 0 18 true (0)
])
theorem kid11_part245_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part245) = true := by rfl

def kid11_part246 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 24 1 false (6),
.cycle 17 1 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 24 1 false (6),
.cycle 17 1 false (3),
.cycle 37 1 false (3),
.last 16 (2,true),
.cycle 26 1 false (6),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 39 true (0),
.cycle 21 1 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 43 1 false (7),
.cycle 14 19 true (2)
])
theorem kid11_part246_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part246) = true := by rfl

def kid11_part247 : Audit := .split 13 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 32768, 128, 256, 32768, 2, 256, 8, 128, 256, 8, 32, 256, 32768, 262144],[2, 32, 256, 1, 4, 262144, 8192, 131072, 256, 4096, 16384, 262144, 2, 32, 256, 1, 4, 262144, 262144],280588⟩,
.last 39 (5,true),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (3),
.last 15 (5,true),
.cycle 17 1 false (5),
.cycle 24 1 false (6),
.cycle 16 1 false (4),
.last 14 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 38 (5,true),
.last 15 (5,true),
.cycle 2 14 true (0),
.last 34 (5,true),
.cycle 14 3 true (2),
.last 14 (5,true)
])
theorem kid11_part247_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part247) = true := by rfl

def kid11_part248 : Audit := .cycle 17 1 false (3)
theorem kid11_part248_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part248) = true := by rfl

def kid11_part249 : Audit := .cycle 16 1 false (4)
theorem kid11_part249_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part249) = true := by rfl

def kid11_part250 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 43 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (3),
.cycle 24 1 false (6),
.last 14 (2,true),
.cycle 24 1 false (6),
.cycle 16 1 false (4),
.cycle 17 1 false (3),
.cycle 19 6 true (2),
.last 15 (2,true),
.cycle 19 1 false (3),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 39 true (0),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 5 55 true (0),
.cycle 14 3 true (2),
.cycle 39 1 false (3)
])
theorem kid11_part250_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part250) = true := by rfl

def kid11_part251 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 47 true (-1),
.cycle 24 1 false (2),
.last 20 (2,true),
.cycle 11 5 false (1),
.cycle 11 10 false (1),
.cycle 0 30 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 4, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 16 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 43, 43, 47, 64],[2, 32, 64, 1, 32, 8, 64],64⟩,
.cycle 9 11 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 19 16 true (1),
.last 17 (2,true),
.cycle 0 36 true (-2),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 11 10 false (1),
.cycle 14 45 true (0),
.cycle 1 17 true (-1),
.last 16 (2,true),
.cycle 5 61 true (-1),
.cycle 18 5 true (2),
.cycle 6 52 true (-1)
])
theorem kid11_part251_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part251) = true := by rfl

def kid11_part252 : Audit := .split 14 (2,true) (byMove [
.cycle 33 1 false (5),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 18 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 28 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.last 18 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 30 (5,true),
.last 24 (5,true),
.last 17 (5,true),
.last 15 (5,true)
])
theorem kid11_part252_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part252) = true := by rfl

def kid11_part253 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (-1),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 18 true (-1),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 19 1 false (3),
.cycle 34 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.last 31 (2,true),
.cycle 1 17 true (-1),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 31 1 false (7),
.cycle 0 22 true (-1)
])
theorem kid11_part253_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part253) = true := by rfl

def kid11_part254 : Audit := .cycle 13 1 false (-1)
theorem kid11_part254_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part254) = true := by rfl

def kid11_part255 : Audit := .cycle 13 1 false (-1)
theorem kid11_part255_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part255) = true := by rfl

def kid11_part256 : Audit := .cycle 14 1 false (-2)
theorem kid11_part256_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part256) = true := by rfl

def kid11_part257 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 35 true (0),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 16 6 true (0),
.cycle 0 43 true (0),
.cycle 0 16 true (0),
.cycle 22 14 true (0),
.last 26 (2,true),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.cycle 8 8 true (0),
.cycle 14 25 true (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 22 1 false (2),
.cycle 10 6 true (0),
.last 21 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.last 32 (2,true),
.cycle 0 70 true (0),
.cycle 0 36 true (0),
.cycle 0 18 true (0)
])
theorem kid11_part257_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part257) = true := by rfl

def kid11_part258 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 23 1 false (3),
.last 19 (2,true),
.cycle 15 4 true (0),
.cycle 0 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 35, 6, 64],[2, 32, 64, 1, 2, 1, 64],64⟩,
.cycle 7 8 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 8 8 true (0),
.cycle 19 4 true (2),
.last 16 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 35, 35, 384, 128, 256, 8, 2, 32, 256, 4096],[2, 32, 4096, 1, 128, 1, 2, 32, 4096, 1, 128, 4096, 4096],4096⟩,
.cycle 20 1 false (2),
.cycle 11 4 true (0),
.last 18 (2,true),
.cycle 0 39 true (0),
.cycle 15 4 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 1 17 true (0)
])
theorem kid11_part258_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part258) = true := by rfl

def kid11_part259 : Audit := .split 13 (2,true) (byMove [
.cycle 29 1 false (5),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.last 17 (5,true),
.last 39 (5,true),
.last 14 (5,true),
.cycle 6 8 true (0),
.last 15 (5,true),
.last 25 (5,true),
.last 35 (5,true),
.cycle 18 16 true (2),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.cycle 12 2 true (0),
.last 14 (5,true),
.last 38 (5,true),
.last 15 (5,true),
.cycle 2 14 true (0),
.last 34 (5,true),
.cycle 14 3 true (2),
.last 14 (5,true)
])
theorem kid11_part259_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part259) = true := by rfl

def kid11_part260 : Audit := .cycle 5 8 true (0)
theorem kid11_part260_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part260) = true := by rfl

def kid11_part261 : Audit := .cycle 14 3 true (2)
theorem kid11_part261_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part261) = true := by rfl

def kid11_part262 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 29 1 false (5),
.cycle 14 2 true (0),
.cycle 16 1 false (-2),
.cycle 6 8 true (0),
.cycle 22 14 true (0),
.last 14 (2,true),
.cycle 0 37 true (0),
.cycle 20 2 true (4),
.cycle 8 8 true (0),
.cycle 45 1 false (3),
.last 17 (2,true),
.last 14 (2,true),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.cycle 16 1 false (-2),
.cycle 0 39 true (0),
.cycle 1 15 true (0),
.last 14 (2,true),
.cycle 5 55 true (0),
.cycle 14 3 true (2),
.cycle 16 2 true (3)
])
theorem kid11_part262_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part262) = true := by rfl

def kid11_part238 : Audit := .split 12 (4,true) (byMove [(kid11_part239),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253),(kid11_part254),(kid11_part255),(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262)])

theorem kid11_part238_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part238) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part239),(kid11_part240),(kid11_part241),(kid11_part242),(kid11_part243),(kid11_part244),(kid11_part245),(kid11_part246),(kid11_part247),(kid11_part248),(kid11_part249),(kid11_part250),(kid11_part251),(kid11_part252),(kid11_part253),(kid11_part254),(kid11_part255),(kid11_part256),(kid11_part257),(kid11_part258),(kid11_part259),(kid11_part260),(kid11_part261),(kid11_part262)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part239_checked

  · exact kid11_part245_checked

  · exact kid11_part251_checked

  · exact kid11_part257_checked

  · exact kid11_part240_checked

  · exact kid11_part246_checked

  · exact kid11_part252_checked

  · exact kid11_part258_checked

  · exact kid11_part241_checked

  · exact kid11_part247_checked

  · exact kid11_part253_checked

  · exact kid11_part259_checked

  · exact kid11_part242_checked

  · exact kid11_part248_checked

  · exact kid11_part254_checked

  · exact kid11_part260_checked

  · exact kid11_part243_checked

  · exact kid11_part249_checked

  · exact kid11_part255_checked

  · exact kid11_part261_checked

  · exact kid11_part244_checked

  · exact kid11_part250_checked

  · exact kid11_part256_checked

  · exact kid11_part262_checked

def kid11_part264 : Audit := .split 15 (2,true) (byMove [
.cycle 0 20 true (-1),
.cycle 10 7 false (2),
.cycle 19 1 false (-1),
.cycle 0 21 true (-1),
.last 16 (4,true),
.cycle 0 26 true (-1),
.cycle 0 24 true (-1),
.last 30 (4,true),
.cycle 0 18 true (-1),
.cycle 0 22 true (-1),
.last 18 (4,true),
.cycle 10 12 true (-1),
.last 21 (4,true),
.cycle 0 22 true (-1),
.cycle 22 2 false (2),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 4, 4, 4, 4, 4, 4],[4096, 2048, 2097152, 512, 2048, 16, 4096, 2048, 4096, 2097152, 8388608, 65536, 4096, 65536, 549755813888, 512, 2048, 268435456, 4398868666368, 2048, 65536, 549755813888, 2199023255552, 17179869184, 4398868666368, 4398868666368, 4399004981248, 134217728, 536870912, 268435456, 4096, 4398046511104, 134217728, 134217728, 536870912, 268435456, 65536, 4398868666368, 65536, 134217728, 536870912, 268435456, 4398046511104],[65536, 2048, 512, 4096, 4398046511104, 1, 65536, 4398868666368, 2097152, 2048, 4398046511104, 4096, 65536, 2048, 512, 4096, 4398046511104, 16777216, 4398868666368, 4096, 549755813888, 2048, 4398046511104, 1073741824, 4398868666368, 4398868666368, 134217728, 4398868666368, 4398046511104, 16777216, 65536, 536870912, 134217728, 4398868666368, 4398046511104, 16777216, 4096, 4096, 134217728, 4398868666368, 4398046511104, 16777216, 4398046511104],4537750650880⟩,
.last 16 (4,true),
.cycle 12 8 true (-1),
.cycle 14 24 true (0),
.cycle 14 17 true (0),
.cycle 0 18 true (-1),
.cycle 4 24 true (-1),
.last 21 (4,true),
.last 17 (4,true)
])
theorem kid11_part264_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part264) = true := by rfl

def kid11_part265 : Audit := .cycle 0 24 true (-1)
theorem kid11_part265_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part265) = true := by rfl

def kid11_part266 : Audit := .cycle 14 1 false (0)
theorem kid11_part266_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part266) = true := by rfl

def kid11_part267 : Audit := .cycle 13 1 false (-1)
theorem kid11_part267_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part267) = true := by rfl

def kid11_part268 : Audit := .cycle 13 2 false (-1)
theorem kid11_part268_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part268) = true := by rfl

def kid11_part269 : Audit := .cycle 13 2 false (-1)
theorem kid11_part269_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part269) = true := by rfl

def kid11_part270 : Audit := .split 15 (2,true) (byMove [
.cycle 24 2 false (6),
.cycle 17 2 false (3),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 28 (4,true),
.cycle 0 24 true (0),
.cycle 21 2 false (5),
.last 18 (4,true),
.cycle 27 2 false (7),
.cycle 18 2 false (4),
.cycle 0 18 true (0),
.cycle 27 2 false (7),
.cycle 25 2 false (7),
.last 16 (4,true),
.cycle 25 2 false (7),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 4 32 true (0),
.cycle 6 32 true (0),
.last 17 (4,true)
])
theorem kid11_part270_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part270) = true := by rfl

def kid11_part271 : Audit := .cycle 14 2 false (2)
theorem kid11_part271_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part271) = true := by rfl

def kid11_part272 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 23 1 false (5),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 0 20 true (0),
.last 28 (4,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.cycle 10 6 true (0),
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 0 20 true (0),
.cycle 1 15 true (0),
.cycle 0 16 true (0),
.cycle 18 2 false (4),
.last 17 (4,true),
.last 15 (4,true)
])
theorem kid11_part272_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part272) = true := by rfl

def kid11_part273 : Audit := .cycle 0 20 true (0)
theorem kid11_part273_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part273) = true := by rfl

def kid11_part274 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 22 2 false (4),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 0 20 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 14 2 false (2),
.cycle 14 2 false (2),
.cycle 10 6 true (0),
.last 15 (2,true),
.cycle 0 24 true (0),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 0 20 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 18 2 false (4),
.cycle 17 3 true (3),
.cycle 13 2 true (1)
])
theorem kid11_part274_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part274) = true := by rfl

def kid11_part275 : Audit := .cycle 14 2 false (2)
theorem kid11_part275_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part275) = true := by rfl

def kid11_part276 : Audit := .cycle 10 16 true (-1)
theorem kid11_part276_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part276) = true := by rfl

def kid11_part277 : Audit := .split 14 (2,true) (byMove [
.cycle 0 22 true (-1),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 10 8 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 18 true (-1),
.last 19 (4,true),
.cycle 0 18 true (-1),
.cycle 0 24 true (-1),
.last 15 (4,true),
.cycle 12 10 true (-1),
.cycle 22 2 false (2),
.cycle 12 4 true (-1),
.cycle 20 2 false (2),
.cycle 18 2 false (2),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 20 true (-1),
.cycle 12 8 true (-1),
.cycle 0 18 true (-1),
.cycle 0 24 true (-1),
.last 15 (4,true),
.last 21 (4,true)
])
theorem kid11_part277_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part277) = true := by rfl

def kid11_part278 : Audit := .split 17 (2,true) (byMove [
.cycle 26 2 false (6),
.cycle 19 2 false (3),
.cycle 20 1 false (2),
.cycle 0 19 true (-1),
.last 18 (4,true),
.cycle 0 21 true (-1),
.cycle 0 18 true (-1),
.last 30 (4,true),
.cycle 0 28 true (-1),
.cycle 23 2 false (5),
.last 20 (4,true),
.cycle 31 2 false (7),
.cycle 20 2 false (4),
.cycle 0 22 true (-1),
.cycle 29 2 false (7),
.cycle 27 2 false (7),
.last 18 (4,true),
.cycle 29 2 false (7),
.last 37 (4,true),
.cycle 64 58 true (6),
.cycle 2 16 true (-1),
.cycle 4 36 true (-1),
.last 21 (4,true),
.last 19 (4,true)
])
theorem kid11_part278_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part278) = true := by rfl

def kid11_part279 : Audit := .cycle 13 1 false (-1)
theorem kid11_part279_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part279) = true := by rfl

def kid11_part280 : Audit := .cycle 13 2 false (-1)
theorem kid11_part280_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part280) = true := by rfl

def kid11_part281 : Audit := .cycle 13 2 false (-1)
theorem kid11_part281_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part281) = true := by rfl

def kid11_part282 : Audit := .split 15 (2,true) (byMove [
.cycle 0 38 true (0),
.last 20 (4,true),
.cycle 23 2 false (3),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.last 28 (4,true),
.cycle 0 24 true (0),
.last 26 (4,true),
.last 18 (4,true),
.last 32 (4,true),
.cycle 6 10 true (0),
.cycle 0 18 true (0),
.last 34 (4,true),
.last 32 (4,true),
.last 16 (4,true),
.last 30 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 4 32 true (0),
.last 31 (4,true),
.last 17 (4,true)
])
theorem kid11_part282_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part282) = true := by rfl

def kid11_part283 : Audit := .cycle 10 4 true (0)
theorem kid11_part283_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part283) = true := by rfl

def kid11_part284 : Audit := .split 13 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 28 2 false (6),
.cycle 0 20 true (0),
.last 28 (4,true),
.cycle 0 16 true (0),
.cycle 26 2 false (6),
.last 16 (4,true),
.cycle 10 4 true (0),
.cycle 16 2 false (2),
.cycle 0 18 true (0),
.cycle 31 2 false (7),
.cycle 27 2 false (7),
.last 14 (4,true),
.cycle 12 2 true (0),
.cycle 0 20 true (0),
.cycle 1 15 true (0),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.last 17 (4,true),
.last 15 (4,true)
])
theorem kid11_part284_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part284) = true := by rfl

def kid11_part285 : Audit := .cycle 0 20 true (0)
theorem kid11_part285_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part285) = true := by rfl

def kid11_part286 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 15 2 false (1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 11 4 true (0),
.cycle 0 20 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 28 2 false (6),
.cycle 17 2 false (1),
.cycle 10 4 true (0),
.cycle 16 2 false (2),
.cycle 20 5 true (2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 15 2 false (-1),
.cycle 12 2 true (0),
.cycle 0 20 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 17 3 true (3),
.cycle 13 2 true (1)
])
theorem kid11_part286_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part286) = true := by rfl

def kid11_part287 : Audit := .split 15 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 17 2 false (1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 17 2 false (-1),
.cycle 19 2 false (-1),
.cycle 0 24 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 24 1 false (4),
.cycle 19 2 false (1),
.cycle 10 6 true (0),
.cycle 18 2 false (2),
.last 21 (2,true),
.last 16 (2,true),
.last 19 (2,true),
.cycle 17 2 false (-1),
.cycle 12 4 true (0),
.cycle 0 24 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 4 12 true (0),
.cycle 18 5 true (2),
.cycle 14 2 true (1)
])
theorem kid11_part287_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part287) = true := by rfl

def kid11_part263 : Audit := .split 12 (5,true) (byMove [(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278),(kid11_part279),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part285),(kid11_part286),(kid11_part287)])

theorem kid11_part263_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part263) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part264),(kid11_part265),(kid11_part266),(kid11_part267),(kid11_part268),(kid11_part269),(kid11_part270),(kid11_part271),(kid11_part272),(kid11_part273),(kid11_part274),(kid11_part275),(kid11_part276),(kid11_part277),(kid11_part278),(kid11_part279),(kid11_part280),(kid11_part281),(kid11_part282),(kid11_part283),(kid11_part284),(kid11_part285),(kid11_part286),(kid11_part287)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part264_checked

  · exact kid11_part270_checked

  · exact kid11_part276_checked

  · exact kid11_part282_checked

  · exact kid11_part265_checked

  · exact kid11_part271_checked

  · exact kid11_part277_checked

  · exact kid11_part283_checked

  · exact kid11_part266_checked

  · exact kid11_part272_checked

  · exact kid11_part278_checked

  · exact kid11_part284_checked

  · exact kid11_part267_checked

  · exact kid11_part273_checked

  · exact kid11_part279_checked

  · exact kid11_part285_checked

  · exact kid11_part268_checked

  · exact kid11_part274_checked

  · exact kid11_part280_checked

  · exact kid11_part286_checked

  · exact kid11_part269_checked

  · exact kid11_part275_checked

  · exact kid11_part281_checked

  · exact kid11_part287_checked

def kid11_part288 : Audit := .cycle 0 10 true (0)
theorem kid11_part288_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part288) = true := by rfl

def kid11_part289 : Audit := .cycle 1 9 true (1)
theorem kid11_part289_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part289) = true := by rfl

def kid11_part290 : Audit := .cycle 2 8 true (1)
theorem kid11_part290_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part290) = true := by rfl

def kid11_part291 : Audit := .cycle 1 12 true (1)
theorem kid11_part291_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part291) = true := by rfl

def kid11_part292 : Audit := .cycle 9 1 true (3)
theorem kid11_part292_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part292) = true := by rfl

def kid11_part294 : Audit := .cycle 0 12 true (0)
theorem kid11_part294_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part294) = true := by rfl

def kid11_part295 : Audit := .cycle 1 11 true (1)
theorem kid11_part295_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part295) = true := by rfl

def kid11_part296 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 32 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 24 1 false (4),
.cycle 25 1 false (3),
.last 26 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.last 23 (2,true),
.cycle 23 1 false (3)
])
theorem kid11_part296_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part296) = true := by rfl

def kid11_part297 : Audit := .cycle 21 1 false (1)
theorem kid11_part297_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part297) = true := by rfl

def kid11_part298 : Audit := .cycle 18 3 false (0)
theorem kid11_part298_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part298) = true := by rfl

def kid11_part299 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (4),
.cycle 24 4 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 4 false (0),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 24 4 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 4 false (2),
.cycle 17 4 false (1),
.cycle 12 7 false (2),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 19 4 false (-1),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 4 false (3),
.cycle 27 4 false (5),
.cycle 13 4 true (0),
.cycle 17 4 false (1)
])
theorem kid11_part299_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part299) = true := by rfl

def kid11_part300 : Audit := .cycle 0 12 true (0)
theorem kid11_part300_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part300) = true := by rfl

def kid11_part301 : Audit := .cycle 1 11 true (1)
theorem kid11_part301_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part301) = true := by rfl

def kid11_part302 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 59 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 40 1 false (10),
.cycle 27 1 false (3),
.cycle 29 1 false (7),
.cycle 36 1 false (10),
.last 22 (2,true),
.cycle 36 1 false (10),
.last 23 (2,true),
.cycle 29 1 false (7),
.cycle 26 14 true (4),
.last 23 (2,true),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.last 25 (2,true),
.cycle 35 1 false (7),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 22 (2,true),
.cycle 5 79 true (0),
.last 23 (2,true),
.cycle 21 26 true (3)
])
theorem kid11_part302_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part302) = true := by rfl

def kid11_part303 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 false (5),
.cycle 25 1 false (5),
.cycle 3 26 true (0),
.last 21 (2,true),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 36 1 false (8),
.cycle 24 1 false (2),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 30 1 false (6),
.cycle 32 1 false (6)
])
theorem kid11_part303_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part303) = true := by rfl

def kid11_part304 : Audit := .cycle 9 3 true (3)
theorem kid11_part304_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part304) = true := by rfl

def kid11_part305 : Audit := .cycle 8 4 true (3)
theorem kid11_part305_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part305) = true := by rfl

def kid11_part306 : Audit := .cycle 6 12 true (2)
theorem kid11_part306_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part306) = true := by rfl

def kid11_part307 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.last 27 (5,true),
.cycle 29 1 false (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 9 5 true (2),
.last 19 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 19 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid11_part307_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part307) = true := by rfl

def kid11_part308 : Audit := .cycle 0 14 true (0)
theorem kid11_part308_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part308) = true := by rfl

def kid11_part309 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 29 1 false (3),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 29 1 false (5),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 37 1 false (5),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.cycle 34 1 false (6),
.cycle 20 1 false (2)
])
theorem kid11_part309_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part309) = true := by rfl

def kid11_part310 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 26 7 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 34 (2,true),
.cycle 3 11 true (1),
.cycle 9 5 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 18 3 false (0),
.cycle 15 7 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 22 5 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 0, 64],[2, 32, 64, 1, 32, 32, 64],64⟩
])
theorem kid11_part310_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part310) = true := by rfl

def kid11_part311 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 0 30 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 17 4 false (0),
.cycle 17 4 false (-1),
.last 19 (2,true),
.cycle 18 4 false (2),
.last 17 (2,true),
.cycle 0 26 true (0),
.cycle 17 4 false (1),
.cycle 18 4 false (2),
.cycle 12 20 true (-1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 17 1 false (-1),
.cycle 19 4 false (-1),
.cycle 17 4 false (-1),
.last 19 (2,true),
.cycle 12 6 true (0),
.last 17 (2,true),
.cycle 0 26 true (0),
.cycle 15 2 true (0),
.cycle 14 4 true (0)
])
theorem kid11_part311_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part311) = true := by rfl

def kid11_part312 : Audit := .cycle 0 12 true (0)
theorem kid11_part312_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part312) = true := by rfl

def kid11_part313 : Audit := .cycle 1 11 true (1)
theorem kid11_part313_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part313) = true := by rfl

def kid11_part314 : Audit := .cycle 2 10 true (1)
theorem kid11_part314_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part314) = true := by rfl

def kid11_part315 : Audit := .cycle 1 14 true (1)
theorem kid11_part315_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part315) = true := by rfl

def kid11_part316 : Audit := .cycle 9 3 true (3)
theorem kid11_part316_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part316) = true := by rfl

def kid11_part317 : Audit := .cycle 10 2 true (3)
theorem kid11_part317_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part317) = true := by rfl

def kid11_part293 : Audit := .split 11 (4,true) (byMove [(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part315),(kid11_part316),(kid11_part317)])

theorem kid11_part293_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part293) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (4,true) (some mv)) (byMove [(kid11_part294),(kid11_part295),(kid11_part296),(kid11_part297),(kid11_part298),(kid11_part299),(kid11_part300),(kid11_part301),(kid11_part302),(kid11_part303),(kid11_part304),(kid11_part305),(kid11_part306),(kid11_part307),(kid11_part308),(kid11_part309),(kid11_part310),(kid11_part311),(kid11_part312),(kid11_part313),(kid11_part314),(kid11_part315),(kid11_part316),(kid11_part317)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid11_part298_checked

  · exact kid11_part304_checked

  · exact kid11_part310_checked

  · exact kid11_part316_checked

  · exact kid11_part299_checked

  · exact kid11_part305_checked

  · exact kid11_part311_checked

  · exact kid11_part317_checked

def kid11_part149 : Audit := .split 9 (4,false) (byMove [(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part183),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part263),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part292),(kid11_part293)])

theorem kid11_part149_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (kid11_part149) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part150),(kid11_part151),(kid11_part152),(kid11_part153),(kid11_part154),(kid11_part155),(kid11_part156),(kid11_part157),(kid11_part158),(kid11_part183),(kid11_part208),(kid11_part209),(kid11_part210),(kid11_part211),(kid11_part236),(kid11_part237),(kid11_part238),(kid11_part263),(kid11_part288),(kid11_part289),(kid11_part290),(kid11_part291),(kid11_part292),(kid11_part293)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part150_checked

  · exact kid11_part156_checked

  · exact kid11_part210_checked

  · exact kid11_part288_checked

  · exact kid11_part151_checked

  · exact kid11_part157_checked

  · exact kid11_part211_checked

  · exact kid11_part289_checked

  · exact kid11_part152_checked

  · exact kid11_part158_checked

  · exact kid11_part236_checked

  · exact kid11_part290_checked

  · exact kid11_part153_checked

  · exact kid11_part183_checked

  · exact kid11_part237_checked

  · exact kid11_part291_checked

  · exact kid11_part154_checked

  · exact kid11_part208_checked

  · exact kid11_part238_checked

  · exact kid11_part292_checked

  · exact kid11_part155_checked

  · exact kid11_part209_checked

  · exact kid11_part263_checked

  · exact kid11_part293_checked

def kid11_part319 : Audit := .cycle 0 13 false (4)
theorem kid11_part319_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part319) = true := by rfl

def kid11_part320 : Audit := .cycle 20 1 false (2)
theorem kid11_part320_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part320) = true := by rfl

def kid11_part321 : Audit := .cycle 14 1 false (0)
theorem kid11_part321_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part321) = true := by rfl

def kid11_part322 : Audit := .cycle 13 1 false (-1)
theorem kid11_part322_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part322) = true := by rfl

def kid11_part323 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (4),
.cycle 21 1 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 21 1 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 1 false (0),
.cycle 10 6 false (2),
.split 15 (2,true) (byMove [
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 17 false (4),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 12 19 false (4),
.cycle 8 16 false (4),
.cycle 12 11 true (-2),
.cycle 21 1 false (1),
.cycle 13 3 true (-2),
.cycle 10 6 false (2),
.cycle 18 1 false (0),
.cycle 12 5 false (0),
.cycle 27 1 false (3),
.cycle 25 1 false (3),
.last 16 (4,true),
.cycle 12 4 false (0),
.last 29 (4,true),
.last 28 (4,true),
.cycle 2 14 false (4),
.cycle 8 20 false (4),
.cycle 12 9 false (0),
.last 18 (4,true)
]),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.split 27 (4,true) (byMove [
.cycle 0 28 false (4),
.cycle 35 1 false (1),
.cycle 29 1 false (-1),
.cycle 28 1 false (-2),
.cycle 13 15 false (4),
.cycle 28 1 false (-2),
.cycle 0 28 true (-1),
.cycle 35 1 false (3),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 13 15 true (-1),
.cycle 28 1 false (0),
.cycle 10 20 false (4),
.last 29 (2,true),
.cycle 0 30 true (-2),
.cycle 28 1 false (-2),
.cycle 8 30 false (4),
.cycle 28 1 false (-2),
.cycle 14 14 true (-1),
.cycle 1 27 false (4),
.cycle 34 1 false (2),
.cycle 38 1 false (4),
.cycle 13 15 true (-1),
.cycle 11 17 false (4)
]),
.cycle 1 13 false (4),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 13 1 true (-1),
.cycle 11 3 false (1)
])
theorem kid11_part323_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part323) = true := by rfl

def kid11_part324 : Audit := .cycle 13 1 false (-1)
theorem kid11_part324_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part324) = true := by rfl

def kid11_part325 : Audit := .cycle 0 13 true (0)
theorem kid11_part325_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part325) = true := by rfl

def kid11_part326 : Audit := .cycle 20 1 false (4)
theorem kid11_part326_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part326) = true := by rfl

def kid11_part327 : Audit := .cycle 14 1 false (2)
theorem kid11_part327_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part327) = true := by rfl

def kid11_part328 : Audit := .cycle 13 1 false (1)
theorem kid11_part328_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part328) = true := by rfl

def kid11_part329 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 14 1 false (2),
.cycle 10 6 true (0),
.split 15 (2,true) (byMove [
.cycle 24 1 false (4),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.last 16 (4,true),
.cycle 12 4 true (0),
.cycle 0 16 true (0),
.cycle 8 16 true (0),
.cycle 12 11 true (0),
.cycle 21 1 false (3),
.cycle 13 3 true (0),
.cycle 10 6 true (0),
.cycle 18 1 false (2),
.cycle 12 5 true (0),
.cycle 27 1 false (5),
.cycle 25 1 false (5),
.last 16 (4,true),
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 8 20 true (0),
.cycle 12 6 true (0),
.cycle 11 5 true (0)
]),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 24 1 false (6),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
])
theorem kid11_part329_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part329) = true := by rfl

def kid11_part330 : Audit := .cycle 13 1 false (1)
theorem kid11_part330_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part330) = true := by rfl

def kid11_part331 : Audit := .cycle 10 5 false (2)
theorem kid11_part331_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part331) = true := by rfl

def kid11_part332 : Audit := .split 14 (2,true) (byMove [
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.split 15 (4,true) (byMove [
.cycle 0 16 false (4),
.cycle 23 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 0 16 true (-1),
.cycle 23 1 false (3),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 1 false (0),
.cycle 10 8 false (2),
.cycle 13 3 false (0),
.cycle 0 18 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 12 18 true (-1),
.cycle 1 15 false (4),
.cycle 22 1 false (2),
.cycle 26 1 false (4),
.last 16 (4,false),
.cycle 11 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 8 15 false (4),
.cycle 12 10 true (-1),
.cycle 20 1 false (2),
.split 15 (4,false) (byMove [
.cycle 12 18 true (-1),
.cycle 1 15 false (4),
.cycle 22 1 false (2),
.cycle 26 1 false (4),
.last 17 (4,true),
.cycle 11 5 false (1),
.cycle 0 16 true (-1),
.cycle 8 17 false (5),
.last 27 (4,true),
.cycle 12 10 true (-1),
.cycle 15 1 true (1),
.cycle 9 7 false (3),
.cycle 12 10 true (-1),
.cycle 13 3 true (-1),
.cycle 0 18 true (-1),
.cycle 20 1 false (2),
.last 17 (4,true),
.cycle 11 5 false (1),
.cycle 12 18 true (-1),
.cycle 1 15 true (-1),
.cycle 8 15 false (4),
.cycle 8 21 false (6),
.cycle 15 1 true (1),
.cycle 11 5 true (-1)
]),
.cycle 10 5 false (2),
.cycle 17 1 false (1),
.cycle 12 4 true (-1),
.cycle 26 1 false (4),
.cycle 24 1 false (4),
.split 15 (4,true) (byMove [
.cycle 13 8 true (-2),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 24 1 false (4),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 0 17 true (-1),
.last 17 (4,false),
.cycle 12 4 true (-1),
.cycle 12 12 true (-2),
.cycle 13 3 false (0),
.cycle 26 1 false (4),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 8 17 false (4),
.cycle 10 7 false (2),
.cycle 14 2 true (-1),
.cycle 0 17 true (-1),
.last 17 (4,false),
.cycle 12 6 true (-1)
]),
.cycle 12 3 false (0),
.cycle 12 17 true (-1),
.cycle 12 16 true (-1),
.cycle 2 13 false (4),
.cycle 8 19 false (5),
.split 15 (4,false) (byMove [
.cycle 8 17 false (4),
.cycle 10 7 false (2),
.cycle 14 2 true (0),
.cycle 0 17 true (-1),
.last 16 (4,true),
.cycle 12 6 true (-1),
.cycle 0 16 true (-1),
.cycle 12 18 true (-1),
.cycle 12 11 true (-1),
.cycle 3 13 false (4),
.cycle 15 1 true (1),
.cycle 12 8 true (-1),
.cycle 9 9 false (3),
.cycle 12 5 true (-1),
.last 17 (4,true),
.cycle 8 19 false (5),
.last 16 (4,true),
.last 21 (4,true),
.cycle 12 18 true (-1),
.cycle 12 17 true (-1),
.cycle 12 16 true (-1),
.cycle 12 22 true (-1),
.cycle 15 1 true (1),
.cycle 12 7 true (-1)
]),
.cycle 12 6 true (-1)
])
theorem kid11_part332_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part332) = true := by rfl

def kid11_part333 : Audit := .cycle 0 15 true (-1)
theorem kid11_part333_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part333) = true := by rfl

def kid11_part334 : Audit := .cycle 13 1 false (-1)
theorem kid11_part334_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part334) = true := by rfl

def kid11_part336 : Audit := .split 16 (2,true) (byMove [
.cycle 8 18 false (4),
.cycle 10 8 false (2),
.cycle 20 1 false (-2),
.cycle 0 36 true (-2),
.last 17 (4,true),
.last 18 (4,true),
.cycle 15 17 true (-1),
.last 30 (4,true),
.cycle 12 12 true (-2),
.cycle 3 14 false (4),
.last 31 (4,true),
.last 20 (4,true),
.cycle 9 10 false (3),
.cycle 12 12 true (-2),
.cycle 23 1 false (1),
.cycle 8 20 false (4),
.last 17 (4,true),
.last 18 (4,true),
.last 30 (4,true),
.last 29 (4,true),
.last 28 (4,true),
.last 34 (4,true),
.last 32 (4,true),
.last 19 (4,true)
])
theorem kid11_part336_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part336) = true := by rfl

def kid11_part337 : Audit := .cycle 0 17 true (-2)
theorem kid11_part337_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part337) = true := by rfl

def kid11_part338 : Audit := .cycle 15 1 false (-1)
theorem kid11_part338_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part338) = true := by rfl

def kid11_part339 : Audit := .cycle 14 1 false (-2)
theorem kid11_part339_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part339) = true := by rfl

def kid11_part340 : Audit := .cycle 13 1 false (-1)
theorem kid11_part340_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part340) = true := by rfl

def kid11_part341 : Audit := .cycle 14 1 false (-2)
theorem kid11_part341_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part341) = true := by rfl

def kid11_part342 : Audit := .cycle 22 1 false (4)
theorem kid11_part342_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part342) = true := by rfl

def kid11_part343 : Audit := .cycle 15 1 false (1)
theorem kid11_part343_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part343) = true := by rfl

def kid11_part344 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 22 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 17 1 false (3),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.cycle 12 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 15 1 false (-1),
.last 28 (4,true),
.cycle 1 14 true (-1),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 12 11 true (-1),
.cycle 11 4 true (-1)
])
theorem kid11_part344_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part344) = true := by rfl

def kid11_part345 : Audit := .cycle 0 15 true (-1)
theorem kid11_part345_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part345) = true := by rfl

def kid11_part346 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 true (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 22 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 true (1),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 15 1 false (-1),
.cycle 8 30 true (-1),
.cycle 1 14 true (-1),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 15 1 true (1),
.cycle 11 4 true (-1)
])
theorem kid11_part346_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part346) = true := by rfl

def kid11_part347 : Audit := .cycle 12 2 true (-1)
theorem kid11_part347_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part347) = true := by rfl

def kid11_part348 : Audit := .cycle 12 8 true (-2)
theorem kid11_part348_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part348) = true := by rfl

def kid11_part349 : Audit := .split 15 (2,true) (byMove [
.cycle 27 1 false (3),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 10 9 false (2),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 8 18 false (4),
.cycle 9 8 false (3),
.far true 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[1024, 32, 512, 512, 128, 32, 1152, 32, 32, 512, 128, 131072, 1024, 1024, 512, 2097152, 524288, 8388608, 29885568, 29885600, 31982752, 2097152, 524288, 8388608, 16777216],[32, 32, 512, 128, 16777216, 1024, 32, 128, 512, 32, 16777216, 1024, 32, 8388608, 32, 160, 16777216, 4194304, 29885600, 8912896, 31983264, 29885600, 16777216, 4194304, 16777216],22872064⟩,
.cycle 0 17 true (-2),
.last 16 (4,true),
.cycle 12 7 false (0),
.cycle 12 6 true (-2),
.cycle 12 5 false (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 16 (4,true),
.cycle 12 4 false (0),
.last 30 (4,true),
.last 20 (4,true),
.last 28 (4,true),
.last 47 (4,true),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part349_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part349) = true := by rfl

def kid11_part350 : Audit := .cycle 24 1 false (4)
theorem kid11_part350_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part350) = true := by rfl

def kid11_part351 : Audit := .cycle 14 1 false (-2)
theorem kid11_part351_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part351) = true := by rfl

def kid11_part352 : Audit := .cycle 13 1 false (-1)
theorem kid11_part352_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part352) = true := by rfl

def kid11_part353 : Audit := .cycle 14 1 false (-2)
theorem kid11_part353_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part353) = true := by rfl

def kid11_part354 : Audit := .cycle 8 15 false (4)
theorem kid11_part354_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part354) = true := by rfl

def kid11_part355 : Audit := .cycle 10 5 false (2)
theorem kid11_part355_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part355) = true := by rfl

def kid11_part356 : Audit := .split 14 (2,true) (byMove [
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 8 15 false (4),
.cycle 12 10 true (-1),
.cycle 20 1 false (2),
.cycle 8 15 false (4),
.cycle 10 5 false (2),
.cycle 17 1 false (1),
.cycle 12 4 true (-1),
.cycle 26 1 false (4),
.cycle 24 1 false (4),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 28 (4,true),
.last 27 (4,true),
.cycle 2 13 false (4),
.cycle 8 19 false (5),
.last 27 (4,true),
.last 17 (4,true)
])
theorem kid11_part356_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part356) = true := by rfl

def kid11_part357 : Audit := .cycle 0 15 true (-1)
theorem kid11_part357_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part357) = true := by rfl

def kid11_part358 : Audit := .split 14 (4,true) (byMove [
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 16 1 true (-2),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 8 15 false (4),
.cycle 12 10 true (-1),
.cycle 20 1 false (2),
.cycle 15 1 true (1),
.cycle 10 5 false (2),
.cycle 17 1 false (1),
.cycle 12 4 true (-1),
.last 15 (2,true),
.cycle 24 1 false (4),
.cycle 13 3 false (0),
.cycle 12 3 false (0),
.cycle 8 45 false (5),
.cycle 10 19 false (4),
.cycle 2 13 false (4),
.cycle 8 19 false (5),
.cycle 15 1 true (1),
.cycle 16 2 true (-1)
])
theorem kid11_part358_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part358) = true := by rfl

def kid11_part359 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 6 false (1),
.cycle 16 1 false (-2),
.cycle 24 1 false (4),
.cycle 17 1 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 11 7 true (-1),
.cycle 12 4 true (-1),
.cycle 12 12 true (-2),
.last 17 (2,true),
.cycle 26 1 false (4),
.cycle 16 1 false (-2),
.cycle 13 3 false (0),
.cycle 16 1 false (-2),
.cycle 8 17 false (4),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 14 5 true (-1),
.cycle 14 2 true (-1)
])
theorem kid11_part359_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part359) = true := by rfl

def kid11_part335 : Audit := .split 13 (4,false) (byMove [(kid11_part336),(kid11_part337),(kid11_part338),(kid11_part339),(kid11_part340),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359)])

theorem kid11_part335_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part335) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part336),(kid11_part337),(kid11_part338),(kid11_part339),(kid11_part340),(kid11_part341),(kid11_part342),(kid11_part343),(kid11_part344),(kid11_part345),(kid11_part346),(kid11_part347),(kid11_part348),(kid11_part349),(kid11_part350),(kid11_part351),(kid11_part352),(kid11_part353),(kid11_part354),(kid11_part355),(kid11_part356),(kid11_part357),(kid11_part358),(kid11_part359)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part336_checked

  · exact kid11_part342_checked

  · exact kid11_part348_checked

  · exact kid11_part354_checked

  · exact kid11_part337_checked

  · exact kid11_part343_checked

  · exact kid11_part349_checked

  · exact kid11_part355_checked

  · exact kid11_part338_checked

  · exact kid11_part344_checked

  · exact kid11_part350_checked

  · exact kid11_part356_checked

  · exact kid11_part339_checked

  · exact kid11_part345_checked

  · exact kid11_part351_checked

  · exact kid11_part357_checked

  · exact kid11_part340_checked

  · exact kid11_part346_checked

  · exact kid11_part352_checked

  · exact kid11_part358_checked

  · exact kid11_part341_checked

  · exact kid11_part347_checked

  · exact kid11_part353_checked

  · exact kid11_part359_checked

def kid11_part360 : Audit := .cycle 13 1 false (-1)
theorem kid11_part360_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part360) = true := by rfl

def kid11_part361 : Audit := .cycle 0 13 true (0)
theorem kid11_part361_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part361) = true := by rfl

def kid11_part362 : Audit := .cycle 1 12 true (0)
theorem kid11_part362_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part362) = true := by rfl

def kid11_part363 : Audit := .cycle 19 1 false (3)
theorem kid11_part363_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part363) = true := by rfl

def kid11_part364 : Audit := .cycle 23 1 false (5)
theorem kid11_part364_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part364) = true := by rfl

def kid11_part365 : Audit := .split 13 (4,false) (byMove [
.cycle 22 1 false (4),
.cycle 15 1 false (1),
.split 14 (2,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.cycle 12 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 13 2 true (0),
.cycle 11 4 true (0)
]),
.cycle 0 15 true (0),
.split 14 (4,true) (byMove [
.cycle 0 15 false (4),
.cycle 22 1 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (4),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 13 2 true (0),
.cycle 11 4 true (0)
]),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 12 9 true (0),
.cycle 19 1 false (3),
.cycle 13 1 true (1),
.cycle 10 4 true (0),
.cycle 16 1 false (2),
.cycle 12 3 true (0),
.split 14 (2,true) (byMove [
.cycle 8 19 false (4),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 10 10 true (-2),
.cycle 15 1 false (-1),
.cycle 23 1 false (5),
.cycle 16 1 false (2),
.cycle 17 1 false (3),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 12 3 true (0),
.cycle 12 5 true (-1),
.last 19 (4,true),
.cycle 25 1 false (5),
.cycle 15 1 false (-1),
.cycle 20 1 false (2),
.cycle 15 1 false (-1),
.cycle 8 16 true (0),
.cycle 10 6 true (0),
.cycle 2 14 true (0),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 12 3 true (0)
]),
.cycle 23 1 false (5),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 23 1 false (5),
.cycle 16 1 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 16 1 false (2),
.cycle 12 3 true (0),
.cycle 12 5 true (-1),
.last 16 (2,true),
.cycle 25 1 false (5),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 8 16 true (0),
.cycle 10 6 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 13 3 true (0),
.cycle 12 3 true (0)
]),
.split 15 (4,true) (byMove [
.cycle 24 1 false (4),
.cycle 17 1 false (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 18 1 false (-2),
.cycle 12 4 true (0),
.cycle 0 16 true (0),
.cycle 8 16 true (0),
.cycle 12 11 true (0),
.cycle 21 1 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 10 6 true (0),
.cycle 18 1 false (2),
.cycle 12 5 true (0),
.last 16 (2,true),
.cycle 25 1 false (5),
.cycle 18 1 false (-2),
.cycle 14 2 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 8 20 true (0),
.cycle 13 3 true (0),
.cycle 11 5 true (0)
]),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 8 18 true (0),
.cycle 13 1 true (1),
.cycle 11 3 true (0)
])
theorem kid11_part365_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part365) = true := by rfl

def kid11_part366 : Audit := .cycle 11 2 true (0)
theorem kid11_part366_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part366) = true := by rfl

def kid11_part318 : Audit := .split 12 (5,true) (byMove [(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366)])

theorem kid11_part318_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (kid11_part318) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part319),(kid11_part320),(kid11_part321),(kid11_part322),(kid11_part323),(kid11_part324),(kid11_part325),(kid11_part326),(kid11_part327),(kid11_part328),(kid11_part329),(kid11_part330),(kid11_part331),(kid11_part332),(kid11_part333),(kid11_part334),(kid11_part335),(kid11_part360),(kid11_part361),(kid11_part362),(kid11_part363),(kid11_part364),(kid11_part365),(kid11_part366)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part319_checked

  · exact kid11_part325_checked

  · exact kid11_part331_checked

  · exact kid11_part361_checked

  · exact kid11_part320_checked

  · exact kid11_part326_checked

  · exact kid11_part332_checked

  · exact kid11_part362_checked

  · exact kid11_part321_checked

  · exact kid11_part327_checked

  · exact kid11_part333_checked

  · exact kid11_part363_checked

  · exact kid11_part322_checked

  · exact kid11_part328_checked

  · exact kid11_part334_checked

  · exact kid11_part364_checked

  · exact kid11_part323_checked

  · exact kid11_part329_checked

  · exact kid11_part335_checked

  · exact kid11_part365_checked

  · exact kid11_part324_checked

  · exact kid11_part330_checked

  · exact kid11_part360_checked

  · exact kid11_part366_checked

def kid11_part367 : Audit := .cycle 0 9 true (0)
theorem kid11_part367_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,0⟩)) (kid11_part367) = true := by rfl

def kid11_part368 : Audit := .cycle 1 8 true (1)
theorem kid11_part368_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,1⟩)) (kid11_part368) = true := by rfl

def kid11_part370 : Audit := .split 22 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 29 true (0),
.cycle 26 1 false (2),
.cycle 0 27 true (0),
.split 23 (4,true) (byMove [
.cycle 0 109 true (0),
.cycle 38 1 false (12),
.last 25 (4,false),
.cycle 0 35 true (0),
.last 25 (4,false),
.cycle 0 39 true (0),
.cycle 0 27 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 288, 4096, 4, 128, 256, 8, 2, 4096, 4, 4096],[2, 32, 4096, 1, 2, 256, 2, 32, 256, 1, 2, 256, 4096],5136⟩,
.cycle 0 65 true (0),
.cycle 41 1 false (9),
.last 24 (4,false),
.last 26 (4,false),
.last 28 (4,false),
.cycle 0 72 true (0),
.last 25 (4,false),
.cycle 29 1 false (3),
.last 25 (4,false),
.cycle 19 5 false (4),
.cycle 0 27 true (0),
.cycle 1 29 true (0),
.cycle 2 60 true (0),
.cycle 0 29 true (0),
.last 24 (4,false),
.last 26 (4,false)
]),
.cycle 0 109 true (0),
.cycle 6 17 true (0),
.cycle 0 25 true (0),
.cycle 0 59 true (0),
.cycle 3 54 true (0),
.split 23 (4,true) (byMove [
.last 27 (4,false),
.cycle 0 27 true (0),
.cycle 0 31 true (0),
.last 29 (4,false),
.last 24 (4,false),
.cycle 0 27 true (0),
.last 57 (4,false),
.cycle 7 17 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.last 29 (4,false),
.last 61 (4,false),
.cycle 0 29 true (0),
.last 24 (4,false),
.last 29 (4,false),
.cycle 0 66 true (0),
.last 38 (4,false),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 65 true (0)
]),
.cycle 23 13 true (4),
.cycle 0 48 true (0),
.cycle 0 35 true (0),
.cycle 41 1 false (9),
.cycle 0 27 true (0),
.split 23 (4,true) (byMove [
.cycle 20 8 true (2),
.last 27 (4,false),
.last 25 (4,false),
.cycle 26 17 true (4),
.last 25 (4,false),
.cycle 0 56 true (0),
.cycle 0 27 true (0),
.cycle 0 48 true (0),
.last 25 (4,false),
.cycle 0 48 true (0),
.last 27 (4,false),
.cycle 0 35 true (0),
.cycle 0 41 true (0),
.cycle 18 6 true (2),
.last 25 (4,false),
.cycle 37 1 false (9),
.last 25 (4,false),
.cycle 19 5 false (4),
.cycle 0 27 true (0),
.cycle 24 15 true (4),
.cycle 22 2 true (3),
.cycle 5 19 true (0),
.last 27 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 288, 4096, 4, 128, 256, 8, 2, 4096, 4, 4096],[2, 32, 4096, 1, 2048, 256, 2, 32, 256, 1, 2048, 256, 4096],5136⟩
]),
.cycle 19 8 true (2),
.cycle 0 66 true (0),
.cycle 0 25 true (0),
.cycle 2 23 true (0),
.cycle 0 53 true (0),
.split 23 (4,true) (byMove [
.last 27 (4,false),
.last 27 (4,false),
.last 25 (4,false),
.last 40 (4,false),
.last 27 (4,false),
.cycle 0 29 true (0),
.cycle 0 53 true (0),
.cycle 0 66 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.last 29 (4,false),
.cycle 22 2 true (4),
.cycle 5 19 true (0),
.last 27 (4,false),
.last 33 (4,false),
.cycle 0 66 true (0),
.last 38 (4,false),
.last 25 (4,false),
.cycle 0 25 true (0),
.last 25 (4,false),
.last 54 (4,false)
]),
.cycle 0 36 true (0)
])
theorem kid11_part370_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part370) = true := by rfl

def kid11_part371 : Audit := .cycle 44 32 true (4)
theorem kid11_part371_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part371) = true := by rfl

def kid11_part372 : Audit := .cycle 21 1 false (3)
theorem kid11_part372_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part372) = true := by rfl

def kid11_part373 : Audit := .cycle 20 1 false (2)
theorem kid11_part373_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part373) = true := by rfl

def kid11_part375 : Audit := .cycle 0 49 true (0)
theorem kid11_part375_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part375) = true := by rfl

def kid11_part376 : Audit := .cycle 57 1 false (9)
theorem kid11_part376_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part376) = true := by rfl

def kid11_part377 : Audit := .cycle 22 1 false (2)
theorem kid11_part377_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part377) = true := by rfl

def kid11_part378 : Audit := .cycle 21 1 false (1)
theorem kid11_part378_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part378) = true := by rfl

def kid11_part379 : Audit := .cycle 20 1 false (2)
theorem kid11_part379_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part379) = true := by rfl

def kid11_part380 : Audit := .cycle 23 1 false (3)
theorem kid11_part380_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part380) = true := by rfl

def kid11_part381 : Audit := .cycle 22 13 true (4)
theorem kid11_part381_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part381) = true := by rfl

def kid11_part382 : Audit := .split 22 (2,true) (byMove [
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 25 1 false (3),
.cycle 0 59 true (0),
.last 23 (4,true),
.cycle 0 109 true (0),
.cycle 6 17 true (0),
.cycle 50 15 true (8),
.cycle 69 1 false (17),
.cycle 0 89 true (0),
.last 23 (4,true),
.cycle 23 13 true (4),
.cycle 33 1 false (9),
.cycle 45 1 false (11),
.cycle 39 1 false (11),
.cycle 37 1 false (11),
.last 23 (4,true),
.cycle 19 4 true (2),
.cycle 0 97 true (0),
.cycle 1 53 true (0),
.cycle 2 23 true (0),
.cycle 23 64 true (4),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part382_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part382) = true := by rfl

def kid11_part383 : Audit := .cycle 27 1 false (9)
theorem kid11_part383_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part383) = true := by rfl

def kid11_part384 : Audit := .cycle 21 1 false (3)
theorem kid11_part384_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part384) = true := by rfl

def kid11_part385 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 0 99 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 true (5),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.cycle 25 1 true (5),
.last 23 (2,true),
.cycle 34 1 false (12),
.cycle 25 1 true (7),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.last 24 (2,true),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.cycle 21 2 true (3),
.last 24 (2,true),
.cycle 66 1 true (14),
.cycle 25 1 true (5),
.last 23 (2,true),
.cycle 53 1 true (11),
.cycle 25 1 true (7),
.last 26 (2,true)
])
theorem kid11_part385_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part385) = true := by rfl

def kid11_part386 : Audit := .split 22 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 99 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 32 1 false (8),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.cycle 28 1 false (8),
.cycle 26 1 false (8),
.cycle 34 1 false (12),
.last 23 (4,true),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.cycle 44 1 false (8),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.cycle 38 1 false (8),
.cycle 21 2 true (3),
.cycle 25 42 true (4),
.cycle 1 38 true (0),
.cycle 2 23 true (0),
.cycle 8 46 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part386_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part386) = true := by rfl

def kid11_part387 : Audit := .split 24 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 71 23 true (9),
.cycle 39 26 true (2),
.cycle 32 1 false (4),
.cycle 30 18 true (3),
.cycle 16 44 true (0),
.cycle 0 54 true (0),
.cycle 18 54 true (1),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 8, 8, 64, 16, 64],64⟩,
.cycle 16 40 true (0),
.last 25 (4,true),
.cycle 8 23 true (0),
.cycle 30 17 true (4),
.cycle 36 22 true (3),
.cycle 0 60 true (0),
.cycle 36 24 true (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 32, 4, 128, 256, 8, 2, 32, 4, 4096],[2, 32, 4, 1, 4096, 4, 2, 32, 4096, 1, 4096, 4096, 4096],4096⟩,
.cycle 23 2 true (3),
.cycle 0 90 true (0),
.cycle 1 54 true (0),
.cycle 2 25 true (0),
.cycle 0 116 true (0),
.last 25 (4,true),
.last 26 (4,true)
])
theorem kid11_part387_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part387) = true := by rfl

def kid11_part388 : Audit := .split 22 (2,true) (byMove [
.cycle 55 40 true (4),
.cycle 31 1 false (9),
.cycle 25 1 false (1),
.cycle 0 38 true (0),
.last 23 (4,true),
.cycle 19 4 false (3),
.cycle 0 35 true (0),
.cycle 28 32 true (4),
.cycle 0 54 true (0),
.cycle 57 1 false (9),
.last 26 (4,true),
.cycle 8 23 true (0),
.cycle 0 41 true (0),
.cycle 18 5 false (3),
.cycle 51 1 false (11),
.cycle 45 1 false (11),
.last 23 (4,true),
.cycle 19 4 false (3),
.cycle 0 50 true (0),
.cycle 1 41 true (0),
.cycle 2 49 true (0),
.cycle 4 27 true (0),
.cycle 18 9 false (3),
.last 26 (4,true)
])
theorem kid11_part388_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part388) = true := by rfl

def kid11_part389 : Audit := .split 27 (2,true) (byMove [
.cycle 0 35 true (0),
.cycle 29 15 true (3),
.cycle 29 1 false (3),
.cycle 28 1 false (2),
.cycle 0 38 true (0),
.cycle 29 15 true (3),
.cycle 0 31 true (0),
.cycle 40 1 false (12),
.cycle 0 31 true (0),
.cycle 28 15 true (4),
.last 28 (4,true),
.cycle 35 15 true (5),
.cycle 23 5 false (5),
.cycle 0 46 true (0),
.cycle 46 1 false (12),
.cycle 28 1 false (2),
.cycle 48 1 false (12),
.cycle 27 2 true (2),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 0 31 true (0),
.cycle 28 15 true (4),
.last 28 (4,true),
.last 29 (4,true)
])
theorem kid11_part389_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part389) = true := by rfl

def kid11_part390 : Audit := .cycle 21 1 false (1)
theorem kid11_part390_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part390) = true := by rfl

def kid11_part391 : Audit := .cycle 20 1 false (2)
theorem kid11_part391_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part391) = true := by rfl

def kid11_part392 : Audit := .split 22 (2,true) (byMove [
.cycle 0 55 true (0),
.cycle 65 1 false (9),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 20 3 false (2),
.cycle 25 1 false (3),
.cycle 0 35 true (0),
.cycle 56 17 true (7),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.last 26 (4,true),
.cycle 33 1 false (9),
.cycle 43 19 true (3),
.cycle 18 7 false (3),
.cycle 0 41 true (0),
.cycle 23 1 false (1),
.cycle 20 3 false (2),
.cycle 21 2 true (1),
.last 28 (4,true),
.last 29 (4,true),
.cycle 51 36 true (4),
.cycle 37 1 false (9),
.cycle 19 5 false (3),
.last 26 (4,true)
])
theorem kid11_part392_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part392) = true := by rfl

def kid11_part393 : Audit := .cycle 22 13 true (4)
theorem kid11_part393_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part393) = true := by rfl

def kid11_part394 : Audit := .split 22 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 29 true (0),
.cycle 26 1 false (2),
.cycle 1 27 true (0),
.last 23 (4,true),
.last 24 (4,true),
.cycle 6 17 true (0),
.cycle 1 25 true (0),
.cycle 1 59 true (0),
.cycle 3 54 true (0),
.last 23 (4,true),
.cycle 23 13 true (4),
.cycle 1 48 true (0),
.cycle 1 35 true (0),
.cycle 41 1 false (9),
.cycle 1 27 true (0),
.last 23 (4,true),
.last 24 (4,true),
.cycle 1 66 true (0),
.cycle 1 25 true (0),
.cycle 2 23 true (0),
.cycle 1 53 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part394_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part394) = true := by rfl

def kid11_part395 : Audit := .cycle 45 32 true (4)
theorem kid11_part395_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part395) = true := by rfl

def kid11_part396 : Audit := .cycle 33 1 false (9)
theorem kid11_part396_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part396) = true := by rfl

def kid11_part397 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.last 25 (2,true),
.last 23 (2,true),
.cycle 27 1 true (5),
.cycle 47 1 true (-1),
.cycle 27 1 false (3),
.cycle 6 17 true (0),
.cycle 25 1 true (5),
.last 23 (2,true),
.cycle 3 54 true (0),
.cycle 25 1 true (7),
.cycle 23 13 true (4),
.cycle 48 1 true (8),
.cycle 35 1 true (5),
.last 23 (2,true),
.cycle 27 1 true (5),
.cycle 23 3 false (3),
.last 26 (2,true),
.cycle 66 1 true (14),
.cycle 25 1 true (5),
.last 23 (2,true),
.cycle 53 1 true (11),
.cycle 25 1 true (7),
.last 26 (2,true)
])
theorem kid11_part397_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part397) = true := by rfl

def kid11_part398 : Audit := .split 22 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 292, 2048, 4, 128, 256, 8, 2, 2048, 4, 4096],[2, 32, 256, 1, 4096, 4, 2, 32, 256, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 60 true (0),
.cycle 41 1 false (9),
.cycle 56 1 false (14),
.cycle 29 10 true (5),
.cycle 0 65 true (0),
.cycle 41 10 true (7),
.cycle 23 10 true (5),
.cycle 9 16 true (0),
.cycle 0 59 true (0),
.last 23 (4,true),
.cycle 41 10 true (8),
.cycle 24 15 true (4),
.cycle 39 10 true (5),
.cycle 44 10 true (6),
.cycle 37 1 false (9),
.last 25 (4,true),
.cycle 21 2 true (3),
.cycle 63 10 true (13),
.cycle 23 10 true (5),
.cycle 2 23 true (0),
.cycle 49 10 true (9),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part398_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part398) = true := by rfl

def kid11_part374 : Audit := .split 20 (4,false) (byMove [(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398)])

theorem kid11_part374_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part374) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) 20 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part375),(kid11_part376),(kid11_part377),(kid11_part378),(kid11_part379),(kid11_part380),(kid11_part381),(kid11_part382),(kid11_part383),(kid11_part384),(kid11_part385),(kid11_part386),(kid11_part387),(kid11_part388),(kid11_part389),(kid11_part390),(kid11_part391),(kid11_part392),(kid11_part393),(kid11_part394),(kid11_part395),(kid11_part396),(kid11_part397),(kid11_part398)] mv))) = true

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

def kid11_part399 : Audit := .cycle 27 1 false (9)
theorem kid11_part399_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part399) = true := by rfl

def kid11_part400 : Audit := .cycle 0 23 true (0)
theorem kid11_part400_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part400) = true := by rfl

def kid11_part401 : Audit := .cycle 25 1 false (9)
theorem kid11_part401_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part401) = true := by rfl

def kid11_part402 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 89 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.split 21 (4,false) (byMove [
.cycle 0 60 true (0),
.cycle 41 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 24 1 false (4),
.cycle 0 36 true (0),
.last 24 (4,true),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.last 23 (4,true),
.cycle 30 1 false (8),
.cycle 30 14 true (4),
.last 24 (4,true),
.cycle 0 40 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 20 3 false (4),
.cycle 0 36 true (0),
.last 24 (4,true),
.cycle 0 89 true (0),
.cycle 28 1 false (8),
.last 23 (4,true),
.cycle 9 28 true (0)
]),
.cycle 34 1 false (12),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.cycle 24 1 false (8),
.cycle 32 1 false (12),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 0 25 true (0),
.cycle 32 1 false (12),
.cycle 25 1 false (9),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 24 1 false (8),
.last 35 (4,false),
.last 27 (4,false),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.last 22 (4,false),
.last 27 (4,false),
.cycle 0 60 true (0),
.last 34 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 32 1 false (10)
]),
.cycle 25 1 false (9),
.cycle 22 13 true (4),
.cycle 36 1 false (8),
.cycle 27 1 false (9),
.cycle 21 1 false (3),
.split 21 (4,false) (byMove [
.last 25 (4,true),
.cycle 28 20 true (2),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 29 1 false (9),
.cycle 20 2 true (3),
.cycle 27 1 false (9),
.last 22 (4,true),
.cycle 30 1 false (8),
.cycle 28 14 true (4),
.last 24 (4,true),
.cycle 28 1 false (8),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 20 3 false (4),
.cycle 25 15 true (3),
.cycle 22 13 true (4),
.last 23 (4,true),
.cycle 5 17 true (0),
.last 22 (4,true),
.cycle 9 28 true (0)
]),
.cycle 20 2 true (3),
.cycle 24 36 true (4),
.cycle 1 32 true (0),
.cycle 2 21 true (0),
.cycle 9 40 true (0),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.last 25 (4,false),
.last 23 (4,false),
.last 36 (4,false),
.last 23 (4,false),
.cycle 0 25 true (0),
.cycle 9 40 true (0),
.cycle 24 36 true (4),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 33 (4,false),
.cycle 26 1 false (8),
.last 25 (4,false),
.cycle 20 2 true (4),
.cycle 27 1 false (9),
.last 23 (4,false),
.last 27 (4,false),
.cycle 0 60 true (0),
.last 34 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 9 22 true (0)
]),
.cycle 24 24 true (4)
])
theorem kid11_part402_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part402) = true := by rfl

def kid11_part403 : Audit := .cycle 25 1 false (9)
theorem kid11_part403_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part403) = true := by rfl

def kid11_part405 : Audit := .split 23 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 16, 16777216, 4, 16777216],[2, 32, 256, 1, 256, 16, 8192, 131072, 256, 4096, 256, 65536, 524288, 8388608, 256, 262144, 256, 4194304, 2, 32, 256, 1, 256, 16, 16777216],23153680⟩,
.cycle 0 57 true (0),
.cycle 27 1 false (3),
.cycle 0 38 true (0),
.cycle 0 29 true (0),
.last 25 (4,false),
.last 53 (4,false),
.last 66 (4,false),
.cycle 0 35 true (0),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 25 (4,false),
.last 27 (4,false),
.cycle 0 27 true (0),
.last 31 (4,false),
.cycle 5 19 true (0),
.cycle 20 8 true (3),
.cycle 0 31 true (0),
.cycle 0 66 true (0),
.cycle 0 36 true (0),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.last 54 (4,false),
.last 25 (4,false)
])
theorem kid11_part405_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part405) = true := by rfl

def kid11_part406 : Audit := .cycle 0 89 true (0)
theorem kid11_part406_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part406) = true := by rfl

def kid11_part407 : Audit := .cycle 22 1 false (4)
theorem kid11_part407_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part407) = true := by rfl

def kid11_part408 : Audit := .cycle 21 1 false (3)
theorem kid11_part408_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part408) = true := by rfl

def kid11_part409 : Audit := .split 21 (4,false) (byMove [
.cycle 0 60 true (0),
.cycle 41 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 24 1 false (4),
.cycle 0 26 true (0),
.last 23 (2,true),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.cycle 27 1 true (5),
.last 23 (2,true),
.last 25 (2,true),
.last 23 (2,true),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 23 (2,true),
.cycle 0 26 true (0),
.last 23 (2,true),
.cycle 0 89 true (0),
.cycle 40 1 false (14),
.cycle 35 1 true (1),
.last 23 (2,true)
])
theorem kid11_part409_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part409) = true := by rfl

def kid11_part410 : Audit := .cycle 34 1 false (12)
theorem kid11_part410_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part410) = true := by rfl

def kid11_part411 : Audit := .cycle 25 1 false (9)
theorem kid11_part411_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part411) = true := by rfl

def kid11_part412 : Audit := .split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 33 1 false (11),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.cycle 23 1 false (7),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.cycle 33 1 false (13),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.cycle 23 1 true (7),
.cycle 26 1 false (10),
.cycle 46 1 false (16),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 24 1 false (6),
.cycle 23 1 false (7),
.last 25 (2,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 32 1 false (12),
.cycle 36 1 false (14),
.cycle 23 1 true (7),
.cycle 21 10 true (5)
])
theorem kid11_part412_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part412) = true := by rfl

def kid11_part413 : Audit := .split 21 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 260, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 16, 16777216, 4, 16777216],[2, 32, 256, 1, 4, 16, 8192, 131072, 256, 4096, 16384, 65536, 524288, 8388608, 256, 262144, 1048576, 4194304, 2, 32, 256, 1, 4, 16, 16777216],23153680⟩,
.cycle 0 25 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 0 25 true (0),
.cycle 32 1 false (12),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.cycle 0 23 true (0),
.cycle 24 1 false (8),
.last 23 (4,false),
.last 25 (4,false),
.cycle 28 1 false (8),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.last 22 (4,false),
.cycle 21 2 true (4),
.cycle 0 60 true (0),
.cycle 35 1 false (11),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.last 31 (4,false),
.last 23 (4,false)
])
theorem kid11_part413_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part413) = true := by rfl

def kid11_part414 : Audit := .cycle 32 1 false (12)
theorem kid11_part414_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part414) = true := by rfl

def kid11_part415 : Audit := .split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 33 1 false (11),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.cycle 23 1 false (7),
.cycle 26 1 false (8),
.cycle 0 24 true (0),
.cycle 33 1 false (13),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.cycle 23 1 true (7),
.cycle 26 1 false (10),
.cycle 22 14 true (6),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 24 1 false (6),
.cycle 23 1 false (7),
.last 25 (2,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 32 1 false (12),
.cycle 36 1 false (14),
.cycle 23 1 true (7),
.cycle 23 10 true (7)
])
theorem kid11_part415_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part415) = true := by rfl

def kid11_part416 : Audit := .cycle 25 1 false (9)
theorem kid11_part416_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part416) = true := by rfl

def kid11_part417 : Audit := .cycle 22 13 true (4)
theorem kid11_part417_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part417) = true := by rfl

def kid11_part418 : Audit := .split 22 (2,true) (byMove [
.cycle 39 1 false (11),
.cycle 0 29 true (0),
.cycle 25 1 false (3),
.last 27 (4,false),
.cycle 20 3 false (4),
.last 24 (4,false),
.cycle 6 17 true (0),
.last 25 (4,false),
.last 59 (4,false),
.cycle 0 89 true (0),
.last 29 (4,false),
.cycle 23 13 true (5),
.cycle 33 1 false (9),
.last 35 (4,false),
.last 29 (4,false),
.last 27 (4,false),
.cycle 20 3 false (4),
.cycle 19 4 true (3),
.last 66 (4,false),
.last 25 (4,false),
.cycle 2 23 true (0),
.last 53 (4,false),
.last 29 (4,false),
.last 36 (4,false)
])
theorem kid11_part418_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part418) = true := by rfl

def kid11_part419 : Audit := .cycle 27 1 false (9)
theorem kid11_part419_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part419) = true := by rfl

def kid11_part420 : Audit := .cycle 21 1 false (3)
theorem kid11_part420_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part420) = true := by rfl

def kid11_part421 : Audit := .split 21 (4,false) (byMove [
.last 24 (2,true),
.cycle 16 60 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.cycle 29 1 false (9),
.cycle 0 26 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 27 1 false (9),
.cycle 20 2 true (3),
.cycle 32 1 false (10),
.cycle 28 18 true (4),
.last 23 (2,true),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (3),
.last 23 (2,true),
.cycle 0 26 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 20 3 false (4),
.cycle 28 10 true (6)
])
theorem kid11_part421_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part421) = true := by rfl

def kid11_part422 : Audit := .split 22 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 16, 16777216, 4, 16777216],[2, 32, 256, 1, 256, 16, 8192, 131072, 256, 4096, 256, 65536, 524288, 8388608, 256, 262144, 256, 4194304, 2, 32, 256, 1, 256, 16, 16777216],23153680⟩,
.cycle 0 99 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.last 25 (4,false),
.cycle 26 1 false (8),
.cycle 34 1 false (12),
.last 29 (4,false),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.last 41 (4,false),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 21 2 true (3),
.last 66 (4,false),
.last 25 (4,false),
.cycle 2 23 true (0),
.last 53 (4,false),
.last 33 (4,false),
.last 36 (4,false)
])
theorem kid11_part422_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part422) = true := by rfl

def kid11_part423 : Audit := .split 60 (4,false) (byMove [
.cycle 0 61 true (0),
.cycle 0 87 true (0),
.cycle 0 71 true (0),
.cycle 69 1 false (15),
.cycle 0 65 true (0),
.cycle 23 38 true (4),
.cycle 0 61 true (0),
.cycle 17 68 true (1),
.cycle 9 52 true (0),
.cycle 25 36 true (4),
.cycle 60 1 true (16),
.cycle 43 18 true (8),
.cycle 0 74 true (0),
.last 62 (2,true),
.cycle 0 63 true (0),
.cycle 0 69 true (0),
.cycle 0 69 true (0),
.last 62 (2,true),
.cycle 0 61 true (0),
.cycle 1 60 true (0),
.cycle 31 52 true (5),
.cycle 53 36 true (9),
.cycle 60 1 true (16),
.cycle 57 10 true (13)
])
theorem kid11_part423_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part423) = true := by rfl

def kid11_part424 : Audit := .split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 1 47 true (0),
.cycle 34 1 false (8),
.cycle 31 1 false (9),
.cycle 1 26 true (0),
.cycle 1 34 true (0),
.cycle 0 24 true (0),
.cycle 18 29 true (2),
.cycle 1 46 true (0),
.cycle 1 32 true (0),
.cycle 23 1 true (7),
.cycle 8 16 true (0),
.cycle 1 36 true (0),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.cycle 1 29 true (0),
.last 25 (2,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 1 59 true (0),
.cycle 1 56 true (0),
.cycle 23 1 true (7),
.cycle 21 10 true (5)
])
theorem kid11_part424_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part424) = true := by rfl

def kid11_part425 : Audit := .split 21 (2,true) (byMove [
.cycle 35 1 false (11),
.cycle 34 1 false (10),
.cycle 24 1 false (4),
.cycle 44 1 false (14),
.cycle 0 25 true (0),
.last 23 (4,false),
.last 49 (4,false),
.last 60 (4,false),
.cycle 41 1 false (13),
.cycle 0 23 true (0),
.last 46 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.cycle 27 1 false (9),
.cycle 20 2 true (4),
.cycle 35 1 false (11),
.cycle 0 60 true (0),
.cycle 18 40 true (2),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 23 (4,false)
])
theorem kid11_part425_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part425) = true := by rfl

def kid11_part426 : Audit := .split 49 (4,false) (byMove [
.cycle 0 50 true (0),
.cycle 5 107 true (0),
.cycle 0 62 true (0),
.cycle 71 1 false (19),
.cycle 67 1 false (15),
.cycle 8 42 true (0),
.cycle 0 50 true (0),
.cycle 16 59 true (0),
.cycle 5 58 true (0),
.cycle 10 40 true (0),
.cycle 49 1 true (13),
.cycle 30 20 true (4),
.cycle 0 106 true (0),
.last 51 (2,true),
.cycle 0 52 true (0),
.cycle 0 60 true (0),
.cycle 5 89 true (0),
.last 51 (2,true),
.cycle 0 50 true (0),
.cycle 1 49 true (0),
.cycle 0 79 true (0),
.cycle 5 79 true (0),
.cycle 49 1 true (13),
.cycle 45 10 true (9)
])
theorem kid11_part426_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part426) = true := by rfl

def kid11_part427 : Audit := .split 23 (4,false) (byMove [
.cycle 20 26 true (4),
.cycle 20 34 true (4),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 22 2 true (6),
.cycle 8 28 true (0),
.cycle 0 24 true (0),
.cycle 20 25 true (4),
.cycle 20 26 true (4),
.cycle 3 21 true (0),
.cycle 23 1 true (7),
.cycle 22 12 true (6),
.cycle 21 16 true (5),
.last 28 (2,true),
.last 24 (2,true),
.cycle 20 29 true (4),
.cycle 21 3 true (5),
.cycle 22 3 true (6),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 20 30 true (4),
.cycle 23 1 true (7),
.cycle 23 10 true (7)
])
theorem kid11_part427_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part427) = true := by rfl

def kid11_part428 : Audit := .split 32 (4,false) (byMove [
.cycle 0 33 true (0),
.cycle 19 40 true (3),
.cycle 9 24 true (0),
.cycle 57 1 false (15),
.cycle 48 1 false (8),
.cycle 23 28 true (4),
.cycle 0 33 true (0),
.cycle 19 44 true (3),
.cycle 19 28 true (3),
.cycle 25 24 true (4),
.cycle 32 1 true (10),
.cycle 51 14 true (11),
.cycle 21 23 true (5),
.last 34 (2,true),
.cycle 0 35 true (0),
.cycle 11 22 true (0),
.cycle 19 22 true (3),
.last 34 (2,true),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 59 24 true (11),
.cycle 65 32 true (11),
.cycle 32 1 true (10),
.cycle 23 10 true (6)
])
theorem kid11_part428_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part428) = true := by rfl

def kid11_part404 : Audit := .split 20 (4,true) (byMove [(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418),(kid11_part419),(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428)])

theorem kid11_part404_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part404) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) 20 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part405),(kid11_part406),(kid11_part407),(kid11_part408),(kid11_part409),(kid11_part410),(kid11_part411),(kid11_part412),(kid11_part413),(kid11_part414),(kid11_part415),(kid11_part416),(kid11_part417),(kid11_part418),(kid11_part419),(kid11_part420),(kid11_part421),(kid11_part422),(kid11_part423),(kid11_part424),(kid11_part425),(kid11_part426),(kid11_part427),(kid11_part428)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part405_checked

  · exact kid11_part411_checked

  · exact kid11_part417_checked

  · exact kid11_part423_checked

  · exact kid11_part406_checked

  · exact kid11_part412_checked

  · exact kid11_part418_checked

  · exact kid11_part424_checked

  · exact kid11_part407_checked

  · exact kid11_part413_checked

  · exact kid11_part419_checked

  · exact kid11_part425_checked

  · exact kid11_part408_checked

  · exact kid11_part414_checked

  · exact kid11_part420_checked

  · exact kid11_part426_checked

  · exact kid11_part409_checked

  · exact kid11_part415_checked

  · exact kid11_part421_checked

  · exact kid11_part427_checked

  · exact kid11_part410_checked

  · exact kid11_part416_checked

  · exact kid11_part422_checked

  · exact kid11_part428_checked

def kid11_part429 : Audit := .cycle 25 1 false (9)
theorem kid11_part429_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part429) = true := by rfl

def kid11_part430 : Audit := .cycle 24 15 true (4)
theorem kid11_part430_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part430) = true := by rfl

def kid11_part431 : Audit := .split 21 (2,true) (byMove [
.cycle 41 1 false (11),
.cycle 0 109 true (0),
.cycle 24 1 false (2),
.cycle 24 15 true (4),
.split 22 (4,true) (byMove [
.cycle 0 55 true (0),
.cycle 65 1 false (9),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 25 1 false (3),
.cycle 24 15 true (4),
.cycle 41 1 false (11),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.last 23 (4,false),
.last 25 (4,false),
.last 27 (4,false),
.cycle 20 3 false (3),
.last 32 (4,false),
.cycle 23 1 false (1),
.last 23 (4,false),
.last 25 (4,false),
.cycle 24 15 true (4),
.cycle 1 31 true (0),
.cycle 51 36 true (4),
.cycle 37 1 false (9),
.last 23 (4,false),
.last 25 (4,false)
]),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 36 30 true (6),
.cycle 9 16 true (0),
.cycle 46 32 true (4),
.split 22 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 1 60 true (0),
.cycle 41 1 false (9),
.cycle 41 1 false (11),
.last 23 (4,false),
.cycle 0 65 true (0),
.last 46 (4,false),
.last 27 (4,false),
.cycle 9 16 true (0),
.cycle 0 59 true (0),
.last 25 (4,false),
.last 44 (4,false),
.cycle 24 15 true (4),
.last 31 (4,false),
.last 50 (4,false),
.cycle 37 1 false (9),
.last 23 (4,false),
.last 31 (4,false),
.last 68 (4,false),
.last 27 (4,false),
.last 50 (4,false),
.last 55 (4,false),
.last 25 (4,false),
.last 40 (4,false)
]),
.cycle 25 15 true (4),
.cycle 41 1 false (9),
.cycle 18 4 true (2),
.cycle 37 1 false (9),
.cycle 33 1 false (9),
.split 22 (4,true) (byMove [
.cycle 20 8 true (1),
.cycle 0 35 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 23 (4,false),
.cycle 0 35 true (0),
.cycle 33 1 false (9),
.cycle 41 1 false (9),
.last 24 (4,false),
.cycle 0 31 true (0),
.last 27 (4,false),
.cycle 19 4 true (2),
.cycle 17 12 true (1),
.cycle 20 3 false (3),
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.last 23 (4,false),
.last 25 (4,false),
.cycle 39 36 true (5),
.cycle 28 19 true (4),
.cycle 21 2 true (2),
.cycle 0 31 true (0),
.last 27 (4,false),
.cycle 18 6 true (2)
]),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.split 22 (4,true) (byMove [
.last 58 (4,false),
.cycle 7 20 true (0),
.last 24 (4,false),
.last 29 (4,false),
.last 25 (4,false),
.last 28 (4,false),
.cycle 6 17 true (0),
.last 27 (4,false),
.last 35 (4,false),
.cycle 3 54 true (0),
.last 25 (4,false),
.cycle 23 13 true (4),
.last 50 (4,false),
.last 37 (4,false),
.cycle 21 2 true (3),
.last 29 (4,false),
.last 25 (4,false),
.cycle 18 6 true (2),
.last 68 (4,false),
.last 27 (4,false),
.cycle 2 23 true (0),
.last 55 (4,false),
.last 25 (4,false),
.last 40 (4,false)
]),
.cycle 33 11 true (5)
])
theorem kid11_part431_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part431) = true := by rfl

def kid11_part432 : Audit := .cycle 0 27 true (0)
theorem kid11_part432_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part432) = true := by rfl

def kid11_part433 : Audit := .cycle 20 1 false (2)
theorem kid11_part433_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part433) = true := by rfl

def kid11_part435 : Audit := .split 23 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 77 25 true (9),
.cycle 27 1 false (1),
.cycle 30 17 true (4),
.last 24 (4,true),
.last 25 (4,true),
.cycle 0 31 true (0),
.cycle 40 36 true (5),
.cycle 9 18 true (0),
.cycle 3 49 true (0),
.last 24 (4,true),
.cycle 32 19 true (4),
.cycle 24 31 true (2),
.cycle 18 12 true (1),
.cycle 65 1 false (9),
.cycle 5 27 true (0),
.last 24 (4,true),
.last 25 (4,true),
.cycle 0 31 true (0),
.cycle 28 15 true (4),
.cycle 2 25 true (0),
.cycle 5 19 true (0),
.last 24 (4,true),
.last 25 (4,true)
])
theorem kid11_part435_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part435) = true := by rfl

def kid11_part436 : Audit := .cycle 0 31 true (0)
theorem kid11_part436_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part436) = true := by rfl

def kid11_part437 : Audit := .cycle 22 1 false (2)
theorem kid11_part437_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part437) = true := by rfl

def kid11_part438 : Audit := .cycle 21 1 false (1)
theorem kid11_part438_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part438) = true := by rfl

def kid11_part439 : Audit := .cycle 20 1 false (2)
theorem kid11_part439_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part439) = true := by rfl

def kid11_part440 : Audit := .cycle 0 31 true (0)
theorem kid11_part440_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part440) = true := by rfl

def kid11_part441 : Audit := .cycle 29 1 false (9)
theorem kid11_part441_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part441) = true := by rfl

def kid11_part442 : Audit := .cycle 33 1 false (9)
theorem kid11_part442_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part442) = true := by rfl

def kid11_part443 : Audit := .split 21 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 50 36 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 29 1 false (9),
.cycle 29 1 false (9),
.cycle 0 27 true (0),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 27 1 false (9),
.last 22 (4,true),
.cycle 33 1 false (9),
.cycle 28 19 true (4),
.cycle 18 6 true (2),
.cycle 0 31 true (0),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.cycle 21 2 true (2),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part443_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part443) = true := by rfl

def kid11_part444 : Audit := .cycle 0 27 true (0)
theorem kid11_part444_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part444) = true := by rfl

def kid11_part445 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 50 36 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 31 1 true (5),
.cycle 29 1 false (9),
.cycle 0 27 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 27 1 false (9),
.cycle 25 1 true (7),
.cycle 33 1 false (9),
.cycle 28 19 true (4),
.last 23 (2,true),
.cycle 0 31 true (0),
.cycle 22 1 false (2),
.cycle 20 2 true (2),
.last 23 (2,true),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 25 1 true (7),
.cycle 21 2 true (3)
])
theorem kid11_part445_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part445) = true := by rfl

def kid11_part446 : Audit := .cycle 19 2 true (2)
theorem kid11_part446_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part446) = true := by rfl

def kid11_part447 : Audit := .cycle 17 8 true (1)
theorem kid11_part447_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part447) = true := by rfl

def kid11_part448 : Audit := .split 22 (2,true) (byMove [
.cycle 45 1 false (11),
.cycle 62 44 true (4),
.cycle 25 1 false (1),
.cycle 18 10 true (1),
.last 23 (4,true),
.cycle 19 4 false (3),
.cycle 6 23 true (0),
.cycle 23 25 true (2),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 2, 8, 64],[8, 10, 8, 8, 64, 16, 64],64⟩,
.cycle 0 31 true (0),
.last 23 (4,true),
.cycle 18 7 false (3),
.cycle 17 6 true (1),
.cycle 18 5 false (3),
.cycle 57 1 false (9),
.cycle 49 1 false (9),
.last 23 (4,true),
.cycle 19 4 false (3),
.cycle 39 36 true (5),
.cycle 18 11 false (4),
.cycle 2 25 true (0),
.cycle 0 31 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part448_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part448) = true := by rfl

def kid11_part449 : Audit := .cycle 33 1 false (9)
theorem kid11_part449_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part449) = true := by rfl

def kid11_part450 : Audit := .cycle 21 1 false (1)
theorem kid11_part450_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part450) = true := by rfl

def kid11_part451 : Audit := .cycle 20 1 false (2)
theorem kid11_part451_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part451) = true := by rfl

def kid11_part452 : Audit := .split 22 (2,true) (byMove [
.far true 2 ⟨0,[0, 1, 0, 1],[512, 512, 512, 512, 2048, 512, 1536, 512, 512, 512, 2048, 512, 4096],[512, 512, 1, 2560, 4096, 1024, 512, 2048, 1, 512, 4096, 1024, 4096],4096⟩,
.cycle 0 35 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 20 3 false (2),
.cycle 0 35 true (0),
.cycle 33 1 false (9),
.cycle 41 1 false (9),
.cycle 28 1 false (8),
.cycle 0 31 true (0),
.last 23 (4,true),
.cycle 19 4 true (1),
.cycle 19 8 false (3),
.cycle 18 7 false (3),
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.cycle 20 3 false (2),
.cycle 21 2 true (1),
.cycle 39 36 true (5),
.cycle 19 7 false (4),
.cycle 2 25 true (0),
.cycle 0 31 true (0),
.last 23 (4,true),
.last 24 (4,true)
])
theorem kid11_part452_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part452) = true := by rfl

def kid11_part453 : Audit := .cycle 35 30 true (5)
theorem kid11_part453_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part453) = true := by rfl

def kid11_part454 : Audit := .cycle 24 15 true (4)
theorem kid11_part454_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part454) = true := by rfl

def kid11_part455 : Audit := .split 21 (2,true) (byMove [
.cycle 41 1 false (11),
.cycle 0 109 true (0),
.cycle 24 1 false (2),
.cycle 24 15 true (4),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 36 30 true (6),
.cycle 9 16 true (0),
.cycle 46 32 true (4),
.last 22 (4,true),
.cycle 25 15 true (4),
.cycle 41 1 false (9),
.cycle 18 4 true (2),
.cycle 37 1 false (9),
.cycle 33 1 false (9),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part455_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part455) = true := by rfl

def kid11_part456 : Audit := .cycle 0 27 true (0)
theorem kid11_part456_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part456) = true := by rfl

def kid11_part457 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.last 24 (2,true),
.last 22 (2,true),
.cycle 24 15 true (4),
.cycle 56 1 true (-2),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 36 30 true (6),
.last 22 (2,true),
.cycle 46 32 true (4),
.cycle 25 1 true (7),
.cycle 25 15 true (4),
.cycle 41 1 false (9),
.cycle 18 4 true (2),
.last 22 (2,true),
.cycle 33 1 false (9),
.cycle 20 3 false (3),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 25 1 true (7),
.cycle 21 2 true (3)
])
theorem kid11_part457_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part457) = true := by rfl

def kid11_part458 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 0 35 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.last 25 (2,true),
.cycle 0 35 true (0),
.cycle 33 1 false (9),
.cycle 41 1 false (9),
.last 23 (2,true),
.cycle 0 31 true (0),
.cycle 25 14 true (5),
.cycle 19 4 true (2),
.cycle 17 12 true (1),
.last 24 (2,true),
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.cycle 20 3 false (3),
.last 24 (2,true),
.cycle 39 36 true (5),
.cycle 28 19 true (4),
.last 23 (2,true),
.cycle 0 31 true (0),
.cycle 25 14 true (5),
.cycle 21 2 true (2)
])
theorem kid11_part458_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part458) = true := by rfl

def kid11_part434 : Audit := .split 20 (4,false) (byMove [(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449),(kid11_part450),(kid11_part451),(kid11_part452),(kid11_part453),(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458)])

theorem kid11_part434_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part434) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) 20 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part435),(kid11_part436),(kid11_part437),(kid11_part438),(kid11_part439),(kid11_part440),(kid11_part441),(kid11_part442),(kid11_part443),(kid11_part444),(kid11_part445),(kid11_part446),(kid11_part447),(kid11_part448),(kid11_part449),(kid11_part450),(kid11_part451),(kid11_part452),(kid11_part453),(kid11_part454),(kid11_part455),(kid11_part456),(kid11_part457),(kid11_part458)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part435_checked

  · exact kid11_part441_checked

  · exact kid11_part447_checked

  · exact kid11_part453_checked

  · exact kid11_part436_checked

  · exact kid11_part442_checked

  · exact kid11_part448_checked

  · exact kid11_part454_checked

  · exact kid11_part437_checked

  · exact kid11_part443_checked

  · exact kid11_part449_checked

  · exact kid11_part455_checked

  · exact kid11_part438_checked

  · exact kid11_part444_checked

  · exact kid11_part450_checked

  · exact kid11_part456_checked

  · exact kid11_part439_checked

  · exact kid11_part445_checked

  · exact kid11_part451_checked

  · exact kid11_part457_checked

  · exact kid11_part440_checked

  · exact kid11_part446_checked

  · exact kid11_part452_checked

  · exact kid11_part458_checked

def kid11_part459 : Audit := .split 21 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 50 36 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.cycle 0 55 true (0),
.cycle 65 1 false (9),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 24 15 true (4),
.last 25 (4,true),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.last 24 (4,true),
.cycle 34 1 false (8),
.cycle 30 20 true (3),
.last 25 (4,true),
.cycle 0 42 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 20 3 false (3),
.cycle 24 15 true (4),
.last 25 (4,true),
.cycle 51 36 true (4),
.cycle 37 1 false (9),
.last 24 (4,true),
.cycle 29 12 true (5)
]),
.cycle 29 1 false (9),
.cycle 0 27 true (0),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 27 1 false (9),
.split 22 (4,true) (byMove [
.cycle 0 27 true (0),
.cycle 0 99 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.last 23 (4,false),
.cycle 36 1 false (12),
.cycle 27 1 false (9),
.last 27 (4,false),
.cycle 26 1 false (8),
.cycle 34 1 false (12),
.last 25 (4,false),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.last 31 (4,false),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.last 23 (4,false),
.last 31 (4,false),
.last 68 (4,false),
.last 27 (4,false),
.last 50 (4,false),
.last 55 (4,false),
.last 25 (4,false),
.last 44 (4,false)
]),
.cycle 33 1 false (9),
.cycle 28 19 true (4),
.cycle 18 6 true (2),
.cycle 0 31 true (0),
.cycle 22 1 false (2),
.split 22 (4,false) (byMove [
.last 26 (4,true),
.cycle 0 35 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 0 35 true (0),
.cycle 33 1 false (9),
.cycle 41 1 false (9),
.cycle 21 2 true (2),
.cycle 0 31 true (0),
.last 23 (4,true),
.cycle 19 4 true (2),
.cycle 17 12 true (1),
.last 25 (4,true),
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 20 3 false (3),
.cycle 39 36 true (5),
.cycle 28 19 true (4),
.last 24 (4,true),
.cycle 0 31 true (0),
.last 23 (4,true),
.cycle 19 5 false (3)
]),
.cycle 20 2 true (2),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.split 22 (4,true) (byMove [
.last 58 (4,false),
.cycle 30 1 false (8),
.last 24 (4,false),
.last 29 (4,false),
.last 24 (4,false),
.last 26 (4,false),
.cycle 6 17 true (0),
.last 27 (4,false),
.last 35 (4,false),
.cycle 0 89 true (0),
.last 25 (4,false),
.cycle 23 13 true (4),
.cycle 33 1 false (9),
.last 37 (4,false),
.cycle 21 2 true (3),
.last 29 (4,false),
.last 24 (4,false),
.cycle 19 4 true (2),
.last 68 (4,false),
.last 27 (4,false),
.cycle 2 23 true (0),
.last 55 (4,false),
.last 25 (4,false),
.cycle 19 6 true (2)
]),
.cycle 19 4 true (2)
])
theorem kid11_part459_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part459) = true := by rfl

def kid11_part460 : Audit := .cycle 0 23 true (0)
theorem kid11_part460_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part460) = true := by rfl

def kid11_part461 : Audit := .cycle 20 11 true (4)
theorem kid11_part461_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part461) = true := by rfl

def kid11_part462 : Audit := .split 20 (2,true) (byMove [
.cycle 37 1 false (11),
.cycle 0 27 true (0),
.cycle 23 1 false (3),
.cycle 0 51 true (0),
.split 21 (4,true) (byMove [
.cycle 0 60 true (0),
.cycle 41 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (4),
.cycle 0 51 true (0),
.cycle 37 1 false (11),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.last 22 (4,false),
.last 24 (4,false),
.last 26 (4,false),
.cycle 20 3 false (4),
.cycle 0 57 true (0),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 24 (4,false),
.cycle 0 51 true (0),
.cycle 1 27 true (0),
.cycle 0 89 true (0),
.cycle 35 1 false (11),
.last 22 (4,false),
.last 24 (4,false)
]),
.cycle 0 89 true (0),
.cycle 6 15 true (0),
.cycle 44 13 true (8),
.cycle 61 1 false (17),
.cycle 0 79 true (0),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.cycle 0 25 true (0),
.cycle 37 1 false (11),
.last 27 (4,false),
.last 22 (4,false),
.cycle 0 25 true (0),
.last 51 (4,false),
.cycle 7 15 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 45 13 true (9),
.last 50 (4,false),
.last 27 (4,false),
.last 55 (4,false),
.cycle 35 1 false (11),
.last 22 (4,false),
.last 27 (4,false),
.cycle 0 60 true (0),
.last 34 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 2 21 true (0)
]),
.cycle 21 11 true (5),
.cycle 29 1 false (9),
.cycle 37 1 false (11),
.cycle 35 1 false (11),
.cycle 33 1 false (11),
.split 21 (4,true) (byMove [
.cycle 20 8 true (2),
.cycle 16 58 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.cycle 29 1 false (9),
.last 23 (4,false),
.cycle 27 1 false (9),
.last 25 (4,false),
.cycle 37 1 false (11),
.cycle 18 39 true (2),
.cycle 20 3 false (4),
.cycle 35 1 false (11),
.cycle 22 1 false (2),
.last 22 (4,false),
.last 24 (4,false),
.cycle 47 15 true (7),
.cycle 22 13 true (4),
.cycle 20 2 true (3),
.cycle 5 17 true (0),
.last 25 (4,false),
.cycle 2 27 true (0)
]),
.cycle 19 2 true (3),
.cycle 0 85 true (0),
.cycle 1 45 true (0),
.cycle 2 21 true (0),
.cycle 21 56 true (4),
.split 21 (4,true) (byMove [
.last 25 (4,false),
.last 25 (4,false),
.last 23 (4,false),
.last 36 (4,false),
.last 24 (4,false),
.cycle 0 25 true (0),
.last 76 (4,false),
.last 85 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.last 46 (4,false),
.cycle 47 15 true (7),
.last 25 (4,false),
.cycle 20 2 true (4),
.cycle 5 17 true (0),
.last 24 (4,false),
.last 27 (4,false),
.cycle 0 60 true (0),
.last 34 (4,false),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 2 21 true (0)
]),
.cycle 2 57 true (0)
])
theorem kid11_part462_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part462) = true := by rfl

def kid11_part463 : Audit := .cycle 5 15 true (0)
theorem kid11_part463_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part463) = true := by rfl

def kid11_part465 : Audit := .split 23 (2,true) (byMove [
.cycle 37 1 false (11),
.cycle 36 1 false (10),
.cycle 26 1 false (4),
.cycle 48 1 false (14),
.cycle 0 29 true (0),
.last 25 (4,false),
.last 53 (4,false),
.last 66 (4,false),
.cycle 45 1 false (13),
.cycle 0 25 true (0),
.cycle 0 25 true (0),
.last 25 (4,false),
.last 27 (4,false),
.cycle 37 1 false (11),
.cycle 31 1 false (9),
.cycle 29 1 false (9),
.cycle 20 8 true (3),
.cycle 41 1 false (11),
.cycle 0 66 true (0),
.cycle 18 46 true (2),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.last 54 (4,false),
.last 25 (4,false)
])
theorem kid11_part465_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part465) = true := by rfl

def kid11_part466 : Audit := .split 23 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 1048836, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 1024, 16777216, 4, 16777216],[2, 32, 256, 1, 32768, 1024, 8192, 131072, 256, 4096, 1048580, 1024, 524288, 8388608, 256, 262144, 32768, 1024, 2, 32, 256, 1, 32768, 1024, 16777216],23153680⟩,
.cycle 0 27 true (0),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.last 24 (4,false),
.cycle 0 27 true (0),
.cycle 34 1 false (12),
.cycle 27 1 false (9),
.cycle 26 1 false (8),
.cycle 0 25 true (0),
.cycle 34 1 false (10),
.last 25 (4,false),
.last 27 (4,false),
.cycle 32 1 false (8),
.cycle 36 1 false (12),
.cycle 24 1 false (4),
.last 24 (4,false),
.cycle 22 2 true (4),
.cycle 0 66 true (0),
.cycle 39 1 false (11),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.cycle 28 1 false (8),
.last 25 (4,false)
])
theorem kid11_part466_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part466) = true := by rfl

def kid11_part467 : Audit := .split 21 (2,true) (byMove [
.cycle 0 60 true (0),
.cycle 41 1 false (9),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 24 1 false (4),
.last 25 (4,false),
.last 66 (4,false),
.cycle 34 1 false (12),
.cycle 22 1 false (4),
.last 22 (4,false),
.last 25 (4,false),
.last 29 (4,false),
.last 26 (4,false),
.last 27 (4,false),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 2 true (2),
.last 25 (4,false),
.cycle 1 36 true (0),
.cycle 0 89 true (0),
.last 27 (4,false),
.last 22 (4,false),
.last 25 (4,false)
])
theorem kid11_part467_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part467) = true := by rfl

def kid11_part468 : Audit := .split 25 (4,false) (byMove [
.cycle 0 69 true (0),
.cycle 0 54 true (0),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 39 1 false (11),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 0 53 true (0),
.cycle 23 9 true (5),
.cycle 0 51 true (0),
.cycle 25 1 true (7),
.cycle 0 38 true (0),
.cycle 6 20 true (0),
.cycle 23 3 true (5),
.last 26 (2,true),
.cycle 18 35 true (2),
.last 31 (2,true),
.cycle 0 29 true (0),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 0 71 true (0),
.cycle 25 1 true (7),
.cycle 23 10 true (5)
])
theorem kid11_part468_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part468) = true := by rfl

def kid11_part469 : Audit := .split 22 (4,false) (byMove [
.cycle 0 35 true (0),
.last 31 (2,true),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.last 25 (2,true),
.cycle 0 99 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 29 1 true (5),
.cycle 36 1 false (12),
.cycle 16 44 true (0),
.last 24 (2,true),
.last 27 (2,true),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 24 (2,true),
.last 25 (2,true),
.cycle 1 60 true (0),
.cycle 41 1 false (9),
.last 27 (2,true),
.cycle 40 1 true (0),
.cycle 0 65 true (0)
])
theorem kid11_part469_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part469) = true := by rfl

def kid11_part470 : Audit := .split 22 (4,false) (byMove [
.last 25 (2,true),
.last 25 (2,true),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 26 1 false (4),
.cycle 21 2 true (3),
.cycle 6 17 true (0),
.cycle 24 28 true (6),
.last 23 (2,true),
.cycle 0 89 true (0),
.cycle 0 27 true (0),
.cycle 23 13 true (5),
.cycle 33 1 false (9),
.cycle 31 3 true (5),
.last 23 (2,true),
.cycle 39 1 false (13),
.cycle 31 1 false (9),
.cycle 19 4 true (3),
.cycle 0 67 true (0),
.cycle 1 25 true (0),
.last 23 (2,true),
.cycle 23 32 true (4),
.cycle 28 1 true (6),
.cycle 25 10 true (5)
])
theorem kid11_part470_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part470) = true := by rfl

def kid11_part471 : Audit := .cycle 6 15 true (0)
theorem kid11_part471_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part471) = true := by rfl

def kid11_part472 : Audit := .split 23 (4,false) (byMove [
.cycle 18 30 true (2),
.cycle 7 17 true (0),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 18 30 true (2),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 24 24 true (6),
.cycle 21 9 true (5),
.cycle 44 13 true (8),
.cycle 23 1 true (7),
.cycle 32 24 true (8),
.cycle 24 24 true (3),
.cycle 21 3 true (5),
.last 24 (2,true),
.cycle 50 24 true (8),
.cycle 25 24 true (3),
.cycle 24 24 true (6),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 49 13 true (11),
.cycle 23 1 true (7),
.cycle 21 10 true (5)
])
theorem kid11_part472_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part472) = true := by rfl

def kid11_part473 : Audit := .split 21 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 0, 1],[128, 256, 8, 256, 1073741824, 4, 128, 256, 32768, 34078722, 1073741824, 16384, 128, 256, 2097152, 536870944, 1073741824, 1048576, 128, 256, 134217728, 1024, 1073741824, 67108864, 128, 256, 8, 16384, 1073741824, 4, 1073741824],[2, 32, 256, 1, 4, 1024, 8192, 131072, 256, 4096, 16384, 1024, 524288, 8388608, 256, 262144, 1048576, 1024, 33554432, 536870912, 256, 16777216, 67108864, 1024, 2, 32, 256, 1, 4, 1024, 1073741824],1483951120⟩,
.cycle 0 25 true (0),
.last 29 (4,false),
.cycle 0 28 true (0),
.last 22 (4,false),
.cycle 0 25 true (0),
.last 59 (4,false),
.cycle 7 15 true (0),
.last 53 (4,false),
.cycle 0 23 true (0),
.last 35 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.last 35 (4,false),
.last 63 (4,false),
.last 27 (4,false),
.last 22 (4,false),
.cycle 21 2 true (4),
.cycle 0 60 true (0),
.last 42 (4,false),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.last 31 (4,false),
.last 23 (4,false)
])
theorem kid11_part473_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part473) = true := by rfl

def kid11_part474 : Audit := .cycle 0 79 true (0)
theorem kid11_part474_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part474) = true := by rfl

def kid11_part475 : Audit := .split 23 (4,false) (byMove [
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 12, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 43 1 false (11),
.cycle 0 33 true (0),
.cycle 28 1 false (4),
.cycle 58 2 true (12),
.cycle 0 24 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 9 15 true (0),
.cycle 61 1 false (17),
.cycle 23 1 true (7),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 22 14 true (6),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 39 1 false (11),
.cycle 32 1 false (8),
.last 25 (2,true),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 4, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 23 1 true (7),
.cycle 23 10 true (7)
])
theorem kid11_part475_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part475) = true := by rfl

def kid11_part476 : Audit := .cycle 21 11 true (5)
theorem kid11_part476_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part476) = true := by rfl

def kid11_part477 : Audit := .cycle 29 1 false (9)
theorem kid11_part477_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part477) = true := by rfl

def kid11_part478 : Audit := .split 29 (4,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.last 30 (2,true),
.cycle 0 31 true (0),
.last 32 (2,true),
.cycle 28 2 true (6),
.cycle 0 30 true (0),
.cycle 18 33 true (2),
.cycle 27 9 true (5),
.cycle 37 1 false (11),
.cycle 29 1 true (7),
.cycle 24 14 true (4),
.cycle 34 1 false (10),
.cycle 27 3 true (5),
.last 30 (2,true),
.cycle 41 1 false (13),
.last 32 (2,true),
.cycle 25 5 true (5),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 2 28 true (0),
.cycle 18 40 true (2),
.cycle 29 1 true (7),
.cycle 27 10 true (5)
])
theorem kid11_part478_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part478) = true := by rfl

def kid11_part479 : Audit := .split 21 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 1024, 16777216, 4, 16777216],[2, 32, 256, 1, 1, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 262144, 1024, 2, 32, 256, 1, 1, 1024, 16777216],23153680⟩,
.last 48 (4,false),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 29 1 false (9),
.last 25 (4,false),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 27 1 false (9),
.cycle 29 1 false (9),
.last 29 (4,false),
.last 35 (4,false),
.cycle 18 6 true (2),
.last 27 (4,false),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 21 2 true (2),
.last 25 (4,false),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.cycle 20 2 true (3),
.last 29 (4,false)
])
theorem kid11_part479_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part479) = true := by rfl

def kid11_part480 : Audit := .split 25 (4,false) (byMove [
.cycle 36 1 false (12),
.cycle 29 1 false (9),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 27 1 false (5),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.cycle 63 1 false (19),
.cycle 21 9 true (3),
.cycle 33 1 false (11),
.cycle 25 1 true (7),
.cycle 48 1 false (16),
.cycle 30 1 false (10),
.cycle 23 3 true (5),
.last 26 (2,true),
.cycle 37 1 false (13),
.cycle 27 1 false (5),
.cycle 39 1 false (13),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 61 1 false (17),
.cycle 25 1 true (7),
.cycle 21 10 true (3)
])
theorem kid11_part480_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part480) = true := by rfl

def kid11_part481 : Audit := .split 22 (4,false) (byMove [
.last 25 (2,true),
.cycle 16 102 true (0),
.cycle 24 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 28 2 true (6),
.cycle 33 1 false (9),
.cycle 18 41 true (2),
.last 23 (2,true),
.cycle 35 1 false (11),
.cycle 21 2 true (2),
.cycle 19 4 true (2),
.cycle 17 12 true (1),
.last 24 (2,true),
.cycle 37 1 false (9),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.last 24 (2,true),
.cycle 0 49 true (0),
.cycle 1 35 true (0),
.last 23 (2,true),
.cycle 5 57 true (0),
.cycle 20 3 false (4),
.cycle 20 5 false (4)
])
theorem kid11_part481_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part481) = true := by rfl

def kid11_part482 : Audit := .cycle 19 2 true (3)
theorem kid11_part482_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part482) = true := by rfl

def kid11_part483 : Audit := .split 60 (4,false) (byMove [
.cycle 31 54 true (5),
.cycle 7 54 true (0),
.last 61 (2,true),
.cycle 0 62 true (0),
.cycle 0 62 true (0),
.cycle 59 2 true (15),
.cycle 0 61 true (0),
.cycle 36 25 true (8),
.cycle 57 9 true (13),
.cycle 0 85 true (0),
.cycle 60 1 true (16),
.cycle 0 72 true (0),
.cycle 41 20 true (8),
.cycle 58 3 true (14),
.last 61 (2,true),
.cycle 17 70 true (1),
.cycle 34 27 true (8),
.cycle 0 63 true (0),
.cycle 0 61 true (0),
.cycle 1 60 true (0),
.cycle 2 59 true (0),
.cycle 0 90 true (0),
.cycle 60 1 true (16),
.cycle 57 10 true (13)
])
theorem kid11_part483_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part483) = true := by rfl

def kid11_part484 : Audit := .split 23 (4,false) (byMove [
.cycle 1 61 true (0),
.cycle 1 48 true (0),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 22 2 true (6),
.cycle 0 24 true (0),
.cycle 1 47 true (0),
.cycle 21 9 true (5),
.cycle 1 45 true (0),
.cycle 23 1 true (7),
.cycle 1 34 true (0),
.cycle 6 18 true (0),
.cycle 21 3 true (5),
.last 24 (2,true),
.cycle 18 31 true (2),
.cycle 1 36 true (0),
.cycle 1 25 true (0),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 1 63 true (0),
.cycle 23 1 true (7),
.cycle 21 10 true (5)
])
theorem kid11_part484_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part484) = true := by rfl

def kid11_part485 : Audit := .split 21 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 4, 128, 256, 32768, 524290, 16777216, 16384, 128, 256, 2097152, 32, 16777216, 1048576, 128, 256, 8, 1024, 16777216, 4, 16777216],[2, 32, 256, 1, 256, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 256, 1024, 2, 32, 256, 1, 256, 1024, 16777216],23153680⟩,
.cycle 0 53 true (0),
.cycle 25 1 false (3),
.cycle 2 34 true (0),
.cycle 0 25 true (0),
.last 23 (4,false),
.last 49 (4,false),
.last 60 (4,false),
.cycle 2 31 true (0),
.cycle 0 23 true (0),
.last 46 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.cycle 2 23 true (0),
.last 29 (4,false),
.cycle 5 17 true (0),
.cycle 20 2 true (4),
.cycle 2 25 true (0),
.cycle 0 60 true (0),
.cycle 2 32 true (0),
.cycle 2 21 true (0),
.cycle 0 23 true (0),
.cycle 2 21 true (0),
.last 23 (4,false)
])
theorem kid11_part485_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part485) = true := by rfl

def kid11_part486 : Audit := .split 49 (4,false) (byMove [
.cycle 0 81 true (0),
.cycle 5 60 true (0),
.last 50 (2,true),
.cycle 0 51 true (0),
.cycle 16 63 true (0),
.cycle 48 2 true (12),
.cycle 0 50 true (0),
.cycle 5 66 true (0),
.cycle 45 9 true (9),
.cycle 21 56 true (4),
.cycle 49 1 true (13),
.cycle 21 41 true (4),
.cycle 28 22 true (4),
.cycle 47 3 true (11),
.last 50 (2,true),
.cycle 16 61 true (0),
.cycle 0 52 true (0),
.cycle 21 32 true (4),
.cycle 0 50 true (0),
.cycle 1 49 true (0),
.cycle 2 48 true (0),
.cycle 21 30 true (4),
.cycle 49 1 true (13),
.cycle 45 10 true (9)
])
theorem kid11_part486_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part486) = true := by rfl

def kid11_part487 : Audit := .split 23 (4,false) (byMove [
.cycle 20 26 true (4),
.cycle 22 13 true (5),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 22 2 true (6),
.cycle 23 2 true (6),
.cycle 0 24 true (0),
.cycle 20 25 true (4),
.cycle 23 9 true (6),
.cycle 3 21 true (0),
.cycle 23 1 true (7),
.cycle 22 12 true (6),
.cycle 21 16 true (5),
.cycle 23 3 true (6),
.last 24 (2,true),
.cycle 20 29 true (4),
.cycle 21 3 true (5),
.cycle 22 3 true (6),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 20 30 true (4),
.cycle 23 1 true (7),
.cycle 23 10 true (7)
])
theorem kid11_part487_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part487) = true := by rfl

def kid11_part488 : Audit := .split 32 (4,false) (byMove [
.cycle 19 41 true (3),
.cycle 21 41 true (5),
.last 33 (2,true),
.cycle 0 34 true (0),
.cycle 22 11 true (6),
.cycle 31 2 true (9),
.cycle 0 33 true (0),
.cycle 31 25 true (9),
.cycle 24 9 true (6),
.cycle 3 57 true (0),
.cycle 32 1 true (10),
.cycle 21 21 true (5),
.cycle 19 31 true (3),
.cycle 30 3 true (8),
.last 33 (2,true),
.cycle 19 73 true (3),
.cycle 31 3 true (9),
.cycle 21 12 true (5),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 2 31 true (0),
.cycle 19 39 true (3),
.cycle 32 1 true (10),
.cycle 23 10 true (6)
])
theorem kid11_part488_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part488) = true := by rfl

def kid11_part464 : Audit := .split 20 (4,true) (byMove [(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475),(kid11_part476),(kid11_part477),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488)])

theorem kid11_part464_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part464) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) 20 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part465),(kid11_part466),(kid11_part467),(kid11_part468),(kid11_part469),(kid11_part470),(kid11_part471),(kid11_part472),(kid11_part473),(kid11_part474),(kid11_part475),(kid11_part476),(kid11_part477),(kid11_part478),(kid11_part479),(kid11_part480),(kid11_part481),(kid11_part482),(kid11_part483),(kid11_part484),(kid11_part485),(kid11_part486),(kid11_part487),(kid11_part488)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part465_checked

  · exact kid11_part471_checked

  · exact kid11_part477_checked

  · exact kid11_part483_checked

  · exact kid11_part466_checked

  · exact kid11_part472_checked

  · exact kid11_part478_checked

  · exact kid11_part484_checked

  · exact kid11_part467_checked

  · exact kid11_part473_checked

  · exact kid11_part479_checked

  · exact kid11_part485_checked

  · exact kid11_part468_checked

  · exact kid11_part474_checked

  · exact kid11_part480_checked

  · exact kid11_part486_checked

  · exact kid11_part469_checked

  · exact kid11_part475_checked

  · exact kid11_part481_checked

  · exact kid11_part487_checked

  · exact kid11_part470_checked

  · exact kid11_part476_checked

  · exact kid11_part482_checked

  · exact kid11_part488_checked

def kid11_part489 : Audit := .cycle 22 9 true (6)
theorem kid11_part489_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part489) = true := by rfl

def kid11_part369 : Audit := .split 19 (5,true) (byMove [(kid11_part370),(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part489)])

theorem kid11_part369_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (kid11_part369) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part370),(kid11_part371),(kid11_part372),(kid11_part373),(kid11_part374),(kid11_part399),(kid11_part400),(kid11_part401),(kid11_part402),(kid11_part403),(kid11_part404),(kid11_part429),(kid11_part430),(kid11_part431),(kid11_part432),(kid11_part433),(kid11_part434),(kid11_part459),(kid11_part460),(kid11_part461),(kid11_part462),(kid11_part463),(kid11_part464),(kid11_part489)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part370_checked

  · exact kid11_part400_checked

  · exact kid11_part430_checked

  · exact kid11_part460_checked

  · exact kid11_part371_checked

  · exact kid11_part401_checked

  · exact kid11_part431_checked

  · exact kid11_part461_checked

  · exact kid11_part372_checked

  · exact kid11_part402_checked

  · exact kid11_part432_checked

  · exact kid11_part462_checked

  · exact kid11_part373_checked

  · exact kid11_part403_checked

  · exact kid11_part433_checked

  · exact kid11_part463_checked

  · exact kid11_part374_checked

  · exact kid11_part404_checked

  · exact kid11_part434_checked

  · exact kid11_part464_checked

  · exact kid11_part399_checked

  · exact kid11_part429_checked

  · exact kid11_part459_checked

  · exact kid11_part489_checked

def kid11_part491 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 0 32 true (0),
.split 21 (4,true) (byMove [
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.last 23 (4,false),
.cycle 0 28 true (0),
.last 23 (4,false),
.cycle 0 32 true (0),
.cycle 0 32 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 8, 16, 8, 8, 1, 64],80⟩,
.cycle 0 24 true (0),
.cycle 0 28 true (0),
.last 22 (4,false),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 28 true (0),
.last 23 (4,false),
.cycle 27 1 false (3),
.last 23 (4,false),
.cycle 17 5 false (4),
.cycle 0 32 true (0),
.cycle 1 24 true (0),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 22 (4,false),
.cycle 0 24 true (0)
]),
.cycle 0 26 true (0),
.cycle 0 47 true (0),
.cycle 0 57 true (0),
.cycle 0 42 true (0),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.proven (BB6.Agent11Raw39B0RBPumps.M795.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M795.never m hm),
.last 22 (4,false),
.cycle 3 20 true (0),
.cycle 0 22 true (0),
.cycle 0 47 true (0),
.last 34 (4,false),
.cycle 0 29 true (0),
.last 22 (4,false),
.last 34 (4,false),
.cycle 0 32 true (0),
.last 24 (4,false),
.cycle 0 24 true (0),
.cycle 4 18 true (0),
.last 22 (4,false),
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.last 44 (4,false),
.cycle 5 44 true (0),
.last 22 (4,false),
.last 72 (4,false)
]),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 5 16 true (0),
.split 21 (4,true) (byMove [
.cycle 18 8 true (2),
.cycle 34 1 false (10),
.last 23 (4,false),
.cycle 0 26 true (0),
.last 23 (4,false),
.cycle 0 69 true (0),
.cycle 6 16 true (0),
.cycle 0 24 true (0),
.last 23 (4,false),
.cycle 0 57 true (0),
.last 24 (4,false),
.cycle 0 28 true (0),
.cycle 0 32 true (0),
.cycle 16 6 true (2),
.last 23 (4,false),
.cycle 0 26 true (0),
.last 23 (4,false),
.cycle 17 5 false (4),
.cycle 0 63 true (0),
.cycle 0 24 true (0),
.cycle 20 2 true (3),
.cycle 0 51 true (0),
.last 24 (4,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 8, 16, 8, 8, 1, 64],80⟩
]),
.cycle 17 8 true (2),
.cycle 0 57 true (0),
.cycle 0 30 true (0),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.split 21 (4,true) (byMove [
.last 48 (4,false),
.cycle 0 31 true (0),
.last 23 (4,false),
.cycle 0 23 true (0),
.last 25 (4,false),
.cycle 0 51 true (0),
.cycle 0 22 true (0),
.last 57 (4,false),
.cycle 0 30 true (0),
.cycle 3 19 true (0),
.last 22 (4,false),
.cycle 0 30 true (0),
.last 36 (4,false),
.cycle 0 24 true (0),
.cycle 20 2 true (4),
.cycle 0 51 true (0),
.last 25 (4,false),
.last 26 (4,false),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 3 20 true (0)
]),
.cycle 3 46 true (0)
])
theorem kid11_part491_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part491) = true := by rfl

def kid11_part492 : Audit := .cycle 0 51 true (0)
theorem kid11_part492_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part492) = true := by rfl

def kid11_part493 : Audit := .cycle 19 1 false (3)
theorem kid11_part493_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part493) = true := by rfl

def kid11_part494 : Audit := .cycle 18 1 false (2)
theorem kid11_part494_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part494) = true := by rfl

def kid11_part495 : Audit := .split 18 (4,false) (byMove [
.cycle 0 57 true (0),
.cycle 45 1 false (7),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 0 23 true (0),
.split 20 (2,true) (byMove [
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 23 1 false (3),
.cycle 41 1 false (11),
.last 21 (4,true),
.cycle 0 26 true (0),
.cycle 0 77 true (0),
.cycle 29 51 true (5),
.cycle 51 1 false (13),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 17 68 true (2),
.cycle 33 1 false (9),
.cycle 37 1 false (9),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 17 4 true (2),
.cycle 0 57 true (0),
.cycle 16 38 true (2),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 30 1 false (10),
.cycle 19 1 false (3),
.split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.cycle 22 1 false (4),
.cycle 30 1 false (10),
.cycle 23 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 22 1 true (4),
.cycle 24 1 true (4),
.last 22 (2,true),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 19 2 true (3),
.cycle 32 1 false (10),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 30 1 false (8)
]),
.cycle 30 1 false (10),
.cycle 14 35 true (0),
.split 20 (2,true) (byMove [
.cycle 0 63 true (0),
.cycle 23 1 false (3),
.cycle 23 1 false (1),
.cycle 0 40 true (0),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 0 30 true (0),
.cycle 36 28 true (6),
.cycle 14 35 true (0),
.cycle 45 1 false (7),
.last 24 (4,true),
.cycle 14 35 true (0),
.cycle 34 1 false (10),
.cycle 16 5 false (3),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 0 36 true (0),
.cycle 1 34 true (0),
.cycle 0 57 true (0),
.cycle 13 41 true (0),
.cycle 16 9 false (3),
.cycle 0 57 true (0)
]),
.split 25 (2,true) (byMove [
.cycle 0 63 true (0),
.cycle 0 29 true (0),
.cycle 27 1 false (3),
.cycle 26 1 false (2),
.cycle 0 42 true (0),
.cycle 27 1 false (3),
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.cycle 28 1 false (6),
.cycle 0 27 true (0),
.last 26 (4,true),
.cycle 0 30 true (0),
.cycle 21 5 false (5),
.cycle 0 46 true (0),
.cycle 37 1 false (9),
.cycle 26 1 false (2),
.cycle 32 1 false (6),
.cycle 37 1 false (9),
.cycle 0 56 true (0),
.cycle 0 38 true (0),
.cycle 2 25 true (0),
.cycle 0 27 true (0),
.last 26 (4,true),
.last 27 (4,true)
]),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 0 42 true (0),
.cycle 0 23 true (0),
.split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 24 true (0),
.cycle 24 1 false (2),
.cycle 1 32 true (0),
.last 21 (4,true),
.last 22 (4,true),
.cycle 1 47 true (0),
.cycle 1 57 true (0),
.cycle 1 42 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 1 22 true (0),
.cycle 1 24 true (0),
.cycle 1 28 true (0),
.cycle 1 28 true (0),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 0 51 true (0),
.cycle 36 1 false (10),
.split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.last 21 (2,true),
.cycle 32 1 true (6),
.cycle 32 1 true (0),
.cycle 24 1 false (2),
.cycle 47 1 true (9),
.cycle 57 1 true (11),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 22 1 true (4),
.cycle 24 1 true (4),
.cycle 28 1 true (4),
.last 21 (2,true),
.cycle 5 16 true (0),
.cycle 21 3 false (3),
.cycle 28 1 true (4),
.cycle 0 57 true (0),
.cycle 30 1 true (6),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 22 1 true (6),
.cycle 3 21 true (0)
]),
.cycle 0 51 true (0)
])
theorem kid11_part495_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part495) = true := by rfl

def kid11_part496 : Audit := .cycle 19 1 false (3)
theorem kid11_part496_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part496) = true := by rfl

def kid11_part497 : Audit := .cycle 21 1 false (7)
theorem kid11_part497_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part497) = true := by rfl

def kid11_part498 : Audit := .cycle 28 1 false (10)
theorem kid11_part498_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part498) = true := by rfl

def kid11_part499 : Audit := .split 18 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 8, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 29 1 false (7),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 31 1 false (9),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.last 21 (4,true),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.last 22 (4,true),
.cycle 33 1 false (9),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 33 1 false (9),
.cycle 0 57 true (0),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.last 21 (4,true),
.cycle 0 22 true (0)
]),
.cycle 20 1 false (4),
.cycle 28 1 false (10),
.cycle 21 1 false (7),
.cycle 21 1 false (7),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 28 1 false (8),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 21 1 false (5),
.cycle 0 20 true (0),
.cycle 28 1 false (10),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.last 20 (4,false),
.cycle 21 1 false (7),
.cycle 31 1 false (9),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 27 1 false (9),
.cycle 31 1 false (11),
.last 20 (4,false),
.cycle 27 1 false (9)
]),
.cycle 21 1 false (7),
.cycle 43 1 false (11),
.cycle 29 1 false (7),
.cycle 30 1 false (10),
.cycle 19 1 false (3),
.split 19 (4,false) (byMove [
.last 23 (4,true),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 23 1 false (7),
.cycle 18 2 true (3),
.cycle 30 1 false (10),
.last 20 (4,true),
.cycle 25 1 false (7),
.cycle 21 14 true (3),
.last 22 (4,true),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 25 1 false (7),
.cycle 9 49 true (0),
.cycle 43 1 false (11),
.last 21 (4,true),
.cycle 5 55 true (0),
.last 20 (4,true),
.cycle 17 28 true (3)
]),
.cycle 30 1 false (10),
.cycle 0 51 true (0),
.cycle 29 1 false (9),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 22 1 false (6),
.cycle 0 20 true (0),
.last 51 (4,false),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.last 20 (4,false),
.cycle 29 1 false (9),
.cycle 23 1 false (7),
.cycle 23 1 false (7),
.cycle 18 2 true (4),
.cycle 30 1 false (10),
.last 21 (4,false),
.last 22 (4,false),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (4),
.last 20 (4,false),
.cycle 3 18 true (0)
]),
.cycle 29 1 false (9)
])
theorem kid11_part499_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part499) = true := by rfl

def kid11_part500 : Audit := .cycle 28 1 false (10)
theorem kid11_part500_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part500) = true := by rfl

def kid11_part502 : Audit := .split 21 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 8, 128, 256, 32768, 524290, 16777216, 32768, 128, 256, 2097152, 32, 16777216, 2097152, 128, 256, 8, 16, 16777216, 8, 16777216],[2, 32, 256, 1, 256, 16, 8192, 131072, 256, 4096, 256, 65536, 524288, 8388608, 256, 262144, 256, 4194304, 2, 32, 256, 1, 256, 16, 16777216],23282704⟩,
.last 31 (4,false),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 32 1 false (8),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 0 55 true (0),
.last 30 (4,false),
.cycle 3 19 true (0),
.last 22 (4,false),
.last 30 (4,false),
.cycle 0 34 true (0),
.last 24 (4,false),
.cycle 29 1 false (7),
.last 51 (4,false),
.cycle 18 8 true (3),
.cycle 0 24 true (0),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 3 20 true (0)
])
theorem kid11_part502_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part502) = true := by rfl

def kid11_part503 : Audit := .cycle 0 22 true (0)
theorem kid11_part503_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part503) = true := by rfl

def kid11_part504 : Audit := .cycle 20 1 false (4)
theorem kid11_part504_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part504) = true := by rfl

def kid11_part505 : Audit := .cycle 19 1 false (3)
theorem kid11_part505_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part505) = true := by rfl

def kid11_part506 : Audit := .split 19 (4,false) (byMove [
.cycle 0 24 true (0),
.cycle 37 1 false (9),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 0 31 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 22 1 true (4),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.last 21 (2,true),
.cycle 0 35 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 0 35 true (0),
.cycle 0 31 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.cycle 24 1 true (2),
.cycle 0 22 true (0)
])
theorem kid11_part506_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part506) = true := by rfl

def kid11_part507 : Audit := .cycle 20 1 false (4)
theorem kid11_part507_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part507) = true := by rfl

def kid11_part508 : Audit := .cycle 28 1 false (10)
theorem kid11_part508_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part508) = true := by rfl

def kid11_part509 : Audit := .cycle 21 1 false (7)
theorem kid11_part509_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part509) = true := by rfl

def kid11_part510 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 28 1 false (8),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 21 1 false (5),
.cycle 0 20 true (0),
.cycle 28 1 false (10),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.last 20 (4,false),
.cycle 21 1 false (7),
.last 30 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 27 1 false (9),
.cycle 31 1 false (11),
.last 20 (4,false),
.cycle 27 1 false (9)
])
theorem kid11_part510_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part510) = true := by rfl

def kid11_part511 : Audit := .cycle 0 20 true (0)
theorem kid11_part511_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part511) = true := by rfl

def kid11_part512 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 22 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.cycle 22 1 false (8),
.cycle 20 11 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.cycle 28 1 false (10)
])
theorem kid11_part512_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part512) = true := by rfl

def kid11_part513 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 22 1 false (6),
.cycle 0 21 true (0),
.cycle 29 1 false (11),
.cycle 22 1 false (8),
.cycle 21 1 false (7),
.cycle 20 1 true (6),
.cycle 22 1 false (8),
.cycle 19 11 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (5),
.cycle 20 1 false (6),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (10),
.cycle 32 1 false (12),
.cycle 20 1 true (6),
.cycle 28 1 false (10)
])
theorem kid11_part513_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part513) = true := by rfl

def kid11_part514 : Audit := .split 22 (4,false) (byMove [
.cycle 0 23 true (0),
.cycle 16 68 true (2),
.cycle 33 1 false (7),
.cycle 29 1 false (7),
.cycle 36 1 false (6),
.cycle 33 1 false (7),
.cycle 0 23 true (0),
.cycle 16 80 true (2),
.cycle 9 15 true (0),
.cycle 43 1 false (11),
.cycle 22 1 true (6),
.cycle 8 15 true (0),
.cycle 20 11 true (4),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 30 1 false (6),
.cycle 16 11 true (2),
.cycle 0 25 true (0),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 16 27 true (2),
.cycle 16 37 true (2),
.cycle 22 1 true (6),
.cycle 16 27 true (2)
])
theorem kid11_part514_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part514) = true := by rfl

def kid11_part515 : Audit := .split 20 (2,true) (byMove [
.cycle 33 1 false (9),
.cycle 0 24 true (0),
.cycle 23 1 false (3),
.last 32 (4,false),
.cycle 18 3 false (4),
.last 22 (4,false),
.last 47 (4,false),
.last 57 (4,false),
.last 42 (4,false),
.cycle 0 22 true (0),
.last 24 (4,false),
.last 22 (4,false),
.last 24 (4,false),
.last 28 (4,false),
.cycle 27 1 false (7),
.cycle 25 1 false (7),
.cycle 18 3 false (4),
.cycle 17 4 true (3),
.cycle 0 57 true (0),
.last 30 (4,false),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 24 (4,false),
.last 22 (4,false)
])
theorem kid11_part515_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part515) = true := by rfl

def kid11_part516 : Audit := .cycle 30 1 false (10)
theorem kid11_part516_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part516) = true := by rfl

def kid11_part517 : Audit := .cycle 19 1 false (3)
theorem kid11_part517_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part517) = true := by rfl

def kid11_part518 : Audit := .split 19 (4,false) (byMove [
.last 22 (2,true),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 31 1 false (11),
.last 20 (2,true),
.cycle 30 1 false (10),
.cycle 18 2 true (3),
.cycle 26 1 false (8),
.cycle 26 11 true (4),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 25 1 false (7),
.cycle 0 58 true (0),
.cycle 1 22 true (0),
.last 20 (2,true),
.cycle 37 39 true (3),
.cycle 18 3 false (4),
.cycle 17 27 true (3)
])
theorem kid11_part518_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part518) = true := by rfl

def kid11_part519 : Audit := .cycle 30 1 false (10)
theorem kid11_part519_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part519) = true := by rfl

def kid11_part520 : Audit := .cycle 0 51 true (0)
theorem kid11_part520_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part520) = true := by rfl

def kid11_part521 : Audit := .split 28 (4,false) (byMove [
.cycle 0 29 true (0),
.cycle 37 1 false (11),
.cycle 30 1 false (8),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.cycle 30 1 false (8),
.cycle 0 29 true (0),
.cycle 37 1 false (13),
.cycle 30 1 false (10),
.cycle 29 1 false (9),
.cycle 28 1 true (8),
.cycle 30 1 false (10),
.cycle 19 11 true (4),
.last 30 (2,true),
.cycle 0 31 true (0),
.cycle 29 1 false (7),
.cycle 28 1 false (8),
.cycle 0 31 true (0),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 36 1 false (12),
.cycle 40 1 false (14),
.cycle 28 1 true (8),
.cycle 36 1 false (12)
])
theorem kid11_part521_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part521) = true := by rfl

def kid11_part522 : Audit := .split 19 (2,true) (byMove [
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.cycle 28 1 false (8),
.last 21 (4,false),
.cycle 0 20 true (0),
.cycle 58 1 false (16),
.last 28 (4,false),
.cycle 26 1 false (8),
.last 20 (4,false),
.last 28 (4,false),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 32 1 false (10),
.cycle 30 1 false (10),
.cycle 18 2 true (4),
.cycle 29 1 false (9),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (4),
.last 20 (4,false),
.cycle 3 18 true (0)
])
theorem kid11_part522_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part522) = true := by rfl

def kid11_part523 : Audit := .cycle 0 20 true (0)
theorem kid11_part523_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part523) = true := by rfl

def kid11_part524 : Audit := .split 20 (4,false) (byMove [
.cycle 18 23 true (4),
.cycle 39 1 false (11),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 30 1 false (8),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 18 26 true (4),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.cycle 18 26 true (4),
.cycle 37 1 false (11),
.last 25 (2,true),
.last 21 (2,true),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.cycle 3 19 true (0)
])
theorem kid11_part524_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part524) = true := by rfl

def kid11_part525 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (8),
.cycle 32 1 false (10),
.cycle 30 1 false (8),
.cycle 28 1 false (8),
.cycle 0 21 true (0),
.cycle 17 24 true (3),
.cycle 38 1 false (12),
.cycle 29 1 false (9),
.cycle 20 1 true (6),
.cycle 38 1 false (12),
.cycle 19 11 true (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 26 1 false (8),
.cycle 22 20 true (4),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 22 20 true (4),
.cycle 45 20 true (9),
.cycle 20 1 true (6),
.cycle 21 20 true (4)
])
theorem kid11_part525_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part525) = true := by rfl

def kid11_part501 : Audit := .split 18 (4,true) (byMove [(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525)])

theorem kid11_part501_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part501) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part502),(kid11_part503),(kid11_part504),(kid11_part505),(kid11_part506),(kid11_part507),(kid11_part508),(kid11_part509),(kid11_part510),(kid11_part511),(kid11_part512),(kid11_part513),(kid11_part514),(kid11_part515),(kid11_part516),(kid11_part517),(kid11_part518),(kid11_part519),(kid11_part520),(kid11_part521),(kid11_part522),(kid11_part523),(kid11_part524),(kid11_part525)] mv))) = true

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

def kid11_part526 : Audit := .cycle 21 1 false (7)
theorem kid11_part526_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part526) = true := by rfl

def kid11_part527 : Audit := .cycle 22 10 true (4)
theorem kid11_part527_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part527) = true := by rfl

def kid11_part528 : Audit := .split 19 (2,true) (byMove [
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 22 1 false (2),
.cycle 0 27 true (0),
.split 20 (4,true) (byMove [
.cycle 0 63 true (0),
.cycle 51 1 false (7),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 22 1 false (2),
.cycle 0 27 true (0),
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.last 21 (4,false),
.cycle 32 1 false (10),
.cycle 14 39 true (0),
.cycle 18 3 false (3),
.last 30 (4,false),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 0 50 true (0),
.cycle 0 27 true (0),
.cycle 1 26 true (0),
.cycle 0 57 true (0),
.cycle 40 1 false (10),
.last 21 (4,false),
.cycle 0 57 true (0)
]),
.cycle 17 3 false (3),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.cycle 9 14 true (0),
.cycle 0 51 true (0),
.split 20 (4,true) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.last 30 (4,false),
.last 26 (4,false),
.last 21 (4,false),
.last 30 (4,false),
.cycle 0 51 true (0),
.cycle 7 14 true (0),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 24 (4,false),
.last 26 (4,false),
.last 26 (4,false),
.cycle 0 57 true (0),
.last 28 (4,false),
.last 21 (4,false),
.cycle 0 57 true (0),
.cycle 0 57 true (0),
.last 32 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 26 (4,false)
]),
.cycle 23 10 true (4),
.cycle 33 1 false (7),
.cycle 16 4 true (2),
.cycle 40 1 false (10),
.cycle 36 1 false (10),
.split 20 (4,true) (byMove [
.cycle 18 8 true (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 22 1 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.last 22 (4,false),
.cycle 25 1 false (7),
.last 24 (4,false),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.cycle 18 3 false (3),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.last 21 (4,false),
.cycle 40 1 false (10),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.cycle 19 2 true (2),
.cycle 5 16 true (0),
.last 24 (4,false),
.cycle 16 6 true (2)
]),
.cycle 17 3 false (3),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 2 20 true (0),
.cycle 20 30 true (3),
.split 20 (4,true) (byMove [
.last 24 (4,false),
.cycle 0 24 true (0),
.last 22 (4,false),
.last 34 (4,false),
.last 23 (4,false),
.last 26 (4,false),
.last 49 (4,false),
.last 59 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 24 (4,false),
.last 26 (4,false),
.last 30 (4,false),
.cycle 19 2 true (3),
.cycle 5 16 true (0),
.last 23 (4,false),
.cycle 16 6 true (2),
.cycle 0 57 true (0),
.last 32 (4,false),
.last 22 (4,false),
.cycle 0 22 true (0),
.last 22 (4,false),
.last 26 (4,false)
]),
.cycle 3 28 true (0)
])
theorem kid11_part528_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part528) = true := by rfl

def kid11_part529 : Audit := .cycle 23 1 false (7)
theorem kid11_part529_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part529) = true := by rfl

def kid11_part530 : Audit := .cycle 18 1 false (2)
theorem kid11_part530_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part530) = true := by rfl

def kid11_part532 : Audit := .split 21 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 14 39 true (0),
.cycle 25 1 false (1),
.cycle 0 31 true (0),
.last 22 (4,true),
.last 23 (4,true),
.cycle 6 16 true (0),
.cycle 50 14 true (7),
.cycle 9 16 true (0),
.cycle 0 57 true (0),
.last 22 (4,true),
.cycle 30 12 true (4),
.cycle 22 22 true (2),
.cycle 16 12 true (1),
.cycle 51 1 false (7),
.cycle 14 41 true (0),
.last 22 (4,true),
.last 23 (4,true),
.cycle 0 67 true (0),
.cycle 1 27 true (0),
.cycle 2 22 true (0),
.cycle 22 34 true (3),
.last 22 (4,true),
.last 23 (4,true)
])
theorem kid11_part532_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part532) = true := by rfl

def kid11_part533 : Audit := .cycle 0 46 true (0)
theorem kid11_part533_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part533) = true := by rfl

def kid11_part534 : Audit := .cycle 20 1 false (2)
theorem kid11_part534_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part534) = true := by rfl

def kid11_part535 : Audit := .cycle 19 1 false (1)
theorem kid11_part535_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part535) = true := by rfl

def kid11_part536 : Audit := .cycle 18 1 false (2)
theorem kid11_part536_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part536) = true := by rfl

def kid11_part537 : Audit := .cycle 20 1 false (2)
theorem kid11_part537_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part537) = true := by rfl

def kid11_part538 : Audit := .cycle 32 1 false (10)
theorem kid11_part538_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part538) = true := by rfl

def kid11_part539 : Audit := .cycle 27 1 false (7)
theorem kid11_part539_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part539) = true := by rfl

def kid11_part540 : Audit := .split 19 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 32 1 false (10),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 32 1 false (10),
.cycle 23 1 false (7),
.cycle 30 1 false (10),
.last 20 (4,true),
.cycle 27 1 false (7),
.cycle 26 12 true (4),
.cycle 16 6 true (2),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 25 1 false (7),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 2 20 true (0),
.cycle 5 77 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part540_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part540) = true := by rfl

def kid11_part541 : Audit := .cycle 23 1 false (7)
theorem kid11_part541_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part541) = true := by rfl

def kid11_part542 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 26 1 true (4),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 32 1 false (10),
.last 20 (2,true),
.cycle 30 1 false (10),
.cycle 22 1 true (6),
.cycle 27 1 false (7),
.cycle 26 12 true (4),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 18 2 true (2),
.cycle 25 1 false (7),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.last 20 (2,true),
.cycle 5 77 true (0),
.cycle 22 1 true (6),
.cycle 19 2 true (3)
])
theorem kid11_part542_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part542) = true := by rfl

def kid11_part543 : Audit := .cycle 17 2 true (2)
theorem kid11_part543_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part543) = true := by rfl

def kid11_part544 : Audit := .cycle 15 8 true (1)
theorem kid11_part544_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part544) = true := by rfl

def kid11_part545 : Audit := .split 20 (2,true) (byMove [
.cycle 39 1 false (9),
.cycle 27 1 false (7),
.cycle 23 1 false (1),
.cycle 16 10 true (1),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 15 35 true (1),
.cycle 21 18 true (2),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 2, 8, 64],[8, 10, 8, 8, 64, 16, 64],64⟩,
.cycle 0 46 true (0),
.last 21 (4,true),
.cycle 16 7 false (3),
.cycle 15 6 true (1),
.cycle 16 5 false (3),
.cycle 45 1 false (7),
.cycle 39 1 false (7),
.last 21 (4,true),
.cycle 17 4 false (3),
.cycle 49 14 true (7),
.cycle 16 11 false (4),
.cycle 2 22 true (0),
.cycle 5 16 true (0),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid11_part545_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part545) = true := by rfl

def kid11_part546 : Audit := .cycle 36 1 false (10)
theorem kid11_part546_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part546) = true := by rfl

def kid11_part547 : Audit := .cycle 19 1 false (1)
theorem kid11_part547_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part547) = true := by rfl

def kid11_part548 : Audit := .cycle 18 1 false (2)
theorem kid11_part548_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part548) = true := by rfl

def kid11_part549 : Audit := .cycle 36 1 false (10)
theorem kid11_part549_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part549) = true := by rfl

def kid11_part550 : Audit := .cycle 43 12 true (7)
theorem kid11_part550_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part550) = true := by rfl

def kid11_part551 : Audit := .cycle 22 10 true (4)
theorem kid11_part551_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part551) = true := by rfl

def kid11_part552 : Audit := .split 19 (2,true) (byMove [
.cycle 35 1 false (9),
.cycle 32 1 false (10),
.cycle 22 1 false (2),
.cycle 0 27 true (0),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.cycle 9 14 true (0),
.cycle 0 51 true (0),
.last 20 (4,true),
.cycle 23 10 true (4),
.cycle 33 1 false (7),
.cycle 16 4 true (2),
.cycle 40 1 false (10),
.cycle 36 1 false (10),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 2 20 true (0),
.cycle 20 30 true (3),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part552_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part552) = true := by rfl

def kid11_part553 : Audit := .cycle 5 14 true (0)
theorem kid11_part553_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part553) = true := by rfl

def kid11_part554 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 32 1 false (10),
.last 20 (2,true),
.cycle 0 27 true (0),
.cycle 39 1 true (-1),
.cycle 17 3 false (3),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.last 20 (2,true),
.cycle 0 51 true (0),
.cycle 22 1 true (6),
.cycle 23 10 true (4),
.cycle 33 1 false (7),
.cycle 16 4 true (2),
.last 20 (2,true),
.cycle 36 1 false (10),
.cycle 18 3 false (3),
.cycle 17 3 false (3),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.last 20 (2,true),
.cycle 20 30 true (3),
.cycle 22 1 true (6),
.cycle 19 2 true (3)
])
theorem kid11_part554_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part554) = true := by rfl

def kid11_part555 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 0 52 true (0),
.cycle 22 1 false (2),
.cycle 36 1 false (10),
.cycle 33 1 false (7),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.last 22 (2,true),
.cycle 40 1 false (10),
.cycle 21 1 false (1),
.cycle 18 3 false (3),
.cycle 40 1 false (10),
.cycle 49 14 true (7),
.cycle 26 12 true (4),
.last 21 (2,true),
.cycle 5 16 true (0),
.cycle 3 23 true (0),
.cycle 19 2 true (2)
])
theorem kid11_part555_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part555) = true := by rfl

def kid11_part531 : Audit := .split 18 (4,false) (byMove [(kid11_part532),(kid11_part533),(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553),(kid11_part554),(kid11_part555)])

theorem kid11_part531_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part531) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) 18 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part532),(kid11_part533),(kid11_part534),(kid11_part535),(kid11_part536),(kid11_part537),(kid11_part538),(kid11_part539),(kid11_part540),(kid11_part541),(kid11_part542),(kid11_part543),(kid11_part544),(kid11_part545),(kid11_part546),(kid11_part547),(kid11_part548),(kid11_part549),(kid11_part550),(kid11_part551),(kid11_part552),(kid11_part553),(kid11_part554),(kid11_part555)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid11_part536_checked

  · exact kid11_part542_checked

  · exact kid11_part548_checked

  · exact kid11_part554_checked

  · exact kid11_part537_checked

  · exact kid11_part543_checked

  · exact kid11_part549_checked

  · exact kid11_part555_checked

def kid11_part556 : Audit := .cycle 23 1 false (7)
theorem kid11_part556_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part556) = true := by rfl

def kid11_part557 : Audit := .cycle 0 51 true (0)
theorem kid11_part557_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part557) = true := by rfl

def kid11_part558 : Audit := .cycle 1 19 true (0)
theorem kid11_part558_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part558) = true := by rfl

def kid11_part559 : Audit := .split 18 (2,true) (byMove [
.cycle 31 1 false (9),
.cycle 0 22 true (0),
.cycle 21 1 false (3),
.cycle 37 1 false (11),
.split 19 (4,true) (byMove [
.cycle 0 24 true (0),
.cycle 35 1 false (9),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (3),
.cycle 37 1 false (11),
.cycle 31 1 false (9),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.cycle 18 3 false (4),
.cycle 39 1 false (11),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 39 1 false (11),
.cycle 16 36 true (2),
.cycle 1 22 true (0),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.last 20 (4,false),
.cycle 0 22 true (0)
]),
.cycle 0 22 true (0),
.cycle 0 67 true (0),
.cycle 27 43 true (5),
.cycle 45 1 false (13),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.last 20 (4,false),
.cycle 27 1 false (7),
.cycle 0 20 true (0),
.last 67 (4,false),
.last 30 (4,false),
.cycle 34 1 false (10),
.last 20 (4,false),
.last 30 (4,false),
.cycle 16 36 true (2),
.last 22 (4,false),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.last 40 (4,false),
.cycle 5 40 true (0),
.last 20 (4,false),
.cycle 2 38 true (0)
]),
.cycle 17 54 true (3),
.cycle 29 1 false (9),
.cycle 31 1 false (9),
.cycle 25 1 false (7),
.cycle 23 1 false (7),
.split 19 (4,true) (byMove [
.cycle 18 8 true (2),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 29 1 false (9),
.last 21 (4,false),
.cycle 30 1 false (10),
.last 22 (4,false),
.cycle 31 1 false (9),
.cycle 16 32 true (2),
.cycle 18 3 false (4),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (7),
.cycle 28 49 true (4),
.cycle 16 64 true (2),
.cycle 18 2 true (3),
.cycle 0 75 true (0),
.last 22 (4,false),
.cycle 2 22 true (0)
]),
.cycle 17 2 true (3),
.cycle 0 51 true (0),
.cycle 16 32 true (2),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.last 44 (4,false),
.cycle 36 1 false (10),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 22 (4,false),
.cycle 2 19 true (0),
.cycle 0 20 true (0),
.last 51 (4,false),
.last 52 (4,false),
.cycle 3 17 true (0),
.last 20 (4,false),
.cycle 17 32 true (3),
.last 32 (4,false),
.last 44 (4,false),
.cycle 18 2 true (4),
.last 73 (4,false),
.last 22 (4,false),
.last 22 (4,false),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (4),
.last 20 (4,false),
.cycle 3 18 true (0)
]),
.cycle 2 18 true (0)
])
theorem kid11_part559_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part559) = true := by rfl

def kid11_part560 : Audit := .cycle 5 67 true (0)
theorem kid11_part560_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part560) = true := by rfl

def kid11_part562 : Audit := .split 21 (2,true) (byMove [
.cycle 31 1 false (9),
.cycle 24 1 false (6),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.cycle 0 23 true (0),
.last 23 (4,false),
.cycle 0 22 true (0),
.cycle 64 1 false (16),
.last 30 (4,false),
.cycle 28 1 false (8),
.last 22 (4,false),
.last 30 (4,false),
.cycle 25 1 false (7),
.last 24 (4,false),
.cycle 34 1 false (10),
.cycle 32 1 false (10),
.cycle 18 8 true (3),
.cycle 33 1 false (9),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 23 25 true (4),
.last 22 (4,false),
.cycle 3 20 true (0)
])
theorem kid11_part562_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part562) = true := by rfl

def kid11_part563 : Audit := .cycle 0 22 true (0)
theorem kid11_part563_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part563) = true := by rfl

def kid11_part564 : Audit := .split 19 (2,true) (byMove [
.cycle 0 24 true (0),
.last 28 (4,false),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (3),
.last 30 (4,false),
.cycle 64 1 false (16),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.last 24 (4,false),
.last 32 (4,false),
.cycle 20 1 false (2),
.last 20 (4,false),
.last 32 (4,false),
.last 30 (4,false),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.last 20 (4,false),
.cycle 0 22 true (0)
])
theorem kid11_part564_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part564) = true := by rfl

def kid11_part565 : Audit := .split 30 (4,false) (byMove [
.cycle 40 1 false (12),
.cycle 33 1 false (9),
.last 31 (2,true),
.cycle 0 32 true (0),
.cycle 32 1 false (6),
.cycle 29 2 true (7),
.cycle 0 31 true (0),
.cycle 28 24 true (6),
.cycle 23 9 true (4),
.cycle 37 1 false (11),
.cycle 30 1 true (8),
.cycle 22 9 true (4),
.cycle 34 1 false (10),
.cycle 28 3 true (6),
.last 31 (2,true),
.cycle 41 1 false (13),
.cycle 32 1 false (6),
.cycle 0 34 true (0),
.cycle 0 31 true (0),
.cycle 1 30 true (0),
.cycle 2 29 true (0),
.cycle 0 60 true (0),
.cycle 30 1 true (8),
.cycle 3 29 true (0)
])
theorem kid11_part565_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part565) = true := by rfl

def kid11_part566 : Audit := .split 20 (4,false) (byMove [
.cycle 12 59 true (0),
.cycle 0 30 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 24 1 true (4),
.cycle 22 1 false (4),
.cycle 48 1 false (8),
.last 22 (2,true),
.last 25 (2,true),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.last 25 (2,true),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 2 27 true (0),
.last 25 (2,true),
.cycle 27 1 true (1),
.cycle 3 27 true (0)
])
theorem kid11_part566_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part566) = true := by rfl

def kid11_part567 : Audit := .split 20 (4,false) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.last 21 (2,true),
.cycle 0 34 true (0),
.cycle 23 1 false (3),
.cycle 19 2 true (3),
.cycle 0 48 true (0),
.cycle 32 24 true (6),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 29 1 false (7),
.cycle 21 9 true (5),
.cycle 28 1 false (8),
.cycle 24 3 true (4),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 23 1 false (3),
.cycle 17 4 true (3),
.cycle 0 57 true (0),
.cycle 1 30 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 23 1 true (5),
.cycle 3 21 true (0)
])
theorem kid11_part567_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part567) = true := by rfl

def kid11_part568 : Audit := .split 43 (4,false) (byMove [
.cycle 15 52 true (1),
.cycle 6 51 true (0),
.last 44 (2,true),
.cycle 0 45 true (0),
.cycle 0 45 true (0),
.cycle 42 2 true (10),
.cycle 0 44 true (0),
.cycle 6 57 true (0),
.cycle 40 9 true (8),
.cycle 0 67 true (0),
.cycle 43 1 true (11),
.cycle 40 9 true (8),
.cycle 25 19 true (3),
.cycle 41 3 true (9),
.last 44 (2,true),
.cycle 6 67 true (0),
.cycle 6 67 true (0),
.cycle 0 46 true (0),
.cycle 0 44 true (0),
.cycle 1 43 true (0),
.cycle 2 42 true (0),
.cycle 19 27 true (3),
.cycle 43 1 true (11),
.cycle 3 42 true (0)
])
theorem kid11_part568_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part568) = true := by rfl

def kid11_part569 : Audit := .split 51 (4,false) (byMove [
.cycle 16 58 true (2),
.cycle 7 45 true (0),
.last 52 (2,true),
.cycle 0 53 true (0),
.cycle 16 58 true (2),
.cycle 50 2 true (12),
.cycle 0 52 true (0),
.cycle 30 22 true (6),
.cycle 49 9 true (11),
.cycle 27 43 true (5),
.cycle 51 1 true (13),
.cycle 49 9 true (11),
.cycle 35 17 true (6),
.cycle 49 3 true (11),
.last 52 (2,true),
.cycle 46 30 true (8),
.cycle 36 17 true (6),
.cycle 28 24 true (6),
.cycle 0 52 true (0),
.cycle 1 51 true (0),
.cycle 2 50 true (0),
.cycle 27 48 true (5),
.cycle 51 1 true (13),
.cycle 3 50 true (0)
])
theorem kid11_part569_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part569) = true := by rfl

def kid11_part570 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.last 20 (4,false),
.cycle 27 1 false (7),
.cycle 0 20 true (0),
.last 43 (4,false),
.last 38 (4,false),
.last 27 (4,false),
.last 20 (4,false),
.last 38 (4,false),
.last 30 (4,false),
.last 24 (4,false),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.last 20 (4,false),
.cycle 0 22 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 38 true (0),
.cycle 5 40 true (0),
.last 20 (4,false),
.last 40 (4,false)
])
theorem kid11_part570_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part570) = true := by rfl

def kid11_part571 : Audit := .cycle 0 20 true (0)
theorem kid11_part571_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part571) = true := by rfl

def kid11_part572 : Audit := .split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.last 30 (2,true),
.cycle 27 1 false (7),
.cycle 24 1 false (4),
.cycle 28 2 true (6),
.cycle 0 21 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 9 13 true (0),
.cycle 45 1 false (13),
.cycle 20 1 true (6),
.cycle 8 13 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 38 1 false (12),
.cycle 27 1 false (7),
.cycle 0 23 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 20 1 true (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 8, 64],[2, 32, 64, 1, 16, 16, 64],64⟩
])
theorem kid11_part572_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part572) = true := by rfl

def kid11_part573 : Audit := .split 20 (4,false) (byMove [
.cycle 17 25 true (3),
.cycle 43 1 false (11),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 43 1 false (11),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 19 30 true (5),
.cycle 19 9 true (5),
.cycle 17 54 true (3),
.cycle 20 1 true (6),
.cycle 19 9 true (5),
.cycle 6 15 true (0),
.cycle 19 3 true (5),
.last 21 (2,true),
.cycle 17 70 true (3),
.cycle 18 3 true (4),
.cycle 19 11 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.cycle 20 1 true (6),
.cycle 3 19 true (0)
])
theorem kid11_part573_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part573) = true := by rfl

def kid11_part574 : Audit := .split 22 (4,false) (byMove [
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 19 12 true (3),
.cycle 21 2 true (5),
.cycle 0 23 true (0),
.cycle 49 1 false (13),
.cycle 19 9 true (3),
.cycle 29 1 false (9),
.cycle 22 1 true (6),
.cycle 19 9 true (3),
.cycle 26 1 false (8),
.cycle 20 3 true (4),
.last 23 (2,true),
.cycle 33 1 false (11),
.cycle 20 5 true (4),
.cycle 28 1 false (8),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 15 31 true (1),
.cycle 22 1 true (6),
.cycle 3 21 true (0)
])
theorem kid11_part574_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part574) = true := by rfl

def kid11_part575 : Audit := .split 24 (4,false) (byMove [
.cycle 34 1 false (10),
.cycle 27 1 false (7),
.last 25 (2,true),
.cycle 0 26 true (0),
.last 27 (2,true),
.cycle 23 2 true (5),
.cycle 0 25 true (0),
.cycle 16 28 true (2),
.cycle 22 9 true (4),
.cycle 31 1 false (9),
.cycle 24 1 true (6),
.cycle 22 9 true (4),
.cycle 28 1 false (8),
.cycle 22 3 true (4),
.last 25 (2,true),
.cycle 35 1 false (11),
.last 27 (2,true),
.cycle 20 5 true (4),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 2 23 true (0),
.cycle 16 35 true (2),
.cycle 24 1 true (6),
.cycle 3 23 true (0)
])
theorem kid11_part575_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part575) = true := by rfl

def kid11_part576 : Audit := .split 19 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 8, 128, 256, 32768, 524290, 16777216, 32768, 128, 256, 2097152, 32, 16777216, 2097152, 128, 256, 8, 1024, 16777216, 8, 16777216],[2, 32, 256, 1, 1, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 262144, 1024, 2, 32, 256, 1, 1, 1024, 16777216],23282704⟩,
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.last 22 (4,false),
.cycle 23 1 false (7),
.cycle 30 1 false (10),
.cycle 32 1 false (10),
.last 24 (4,false),
.last 28 (4,false),
.cycle 16 6 true (2),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (7),
.last 57 (4,false),
.last 22 (4,false),
.cycle 2 20 true (0),
.last 47 (4,false),
.cycle 18 2 true (3),
.last 24 (4,false)
])
theorem kid11_part576_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part576) = true := by rfl

def kid11_part577 : Audit := .cycle 23 1 false (7)
theorem kid11_part577_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part577) = true := by rfl

def kid11_part578 : Audit := .split 20 (4,false) (byMove [
.last 23 (2,true),
.cycle 14 87 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 0 25 true (0),
.cycle 16 34 true (2),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 19 2 true (2),
.cycle 17 4 true (2),
.cycle 15 12 true (1),
.last 22 (2,true),
.last 27 (2,true),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 36 1 false (8),
.cycle 0 25 true (0),
.cycle 1 28 true (0),
.last 21 (2,true),
.cycle 5 16 true (0),
.cycle 18 3 false (4),
.cycle 18 5 false (4)
])
theorem kid11_part578_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part578) = true := by rfl

def kid11_part579 : Audit := .cycle 17 2 true (3)
theorem kid11_part579_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part579) = true := by rfl

def kid11_part580 : Audit := .cycle 0 51 true (0)
theorem kid11_part580_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part580) = true := by rfl

def kid11_part581 : Audit := .split 28 (4,false) (byMove [
.cycle 1 81 true (0),
.cycle 1 55 true (0),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 27 2 true (7),
.cycle 0 29 true (0),
.cycle 26 22 true (6),
.cycle 21 9 true (4),
.cycle 16 32 true (2),
.cycle 28 1 true (8),
.cycle 20 9 true (4),
.cycle 1 46 true (0),
.cycle 26 3 true (6),
.last 29 (2,true),
.cycle 1 59 true (0),
.cycle 18 11 true (4),
.cycle 1 30 true (0),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 1 54 true (0),
.cycle 28 1 true (8),
.cycle 3 27 true (0)
])
theorem kid11_part581_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part581) = true := by rfl

def kid11_part582 : Audit := .split 19 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 8, 128, 256, 32768, 524290, 16777216, 32768, 128, 256, 2097152, 32, 16777216, 2097152, 128, 256, 8, 1024, 16777216, 8, 16777216],[2, 32, 256, 1, 256, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 256, 1024, 2, 32, 256, 1, 256, 1024, 16777216],23282704⟩,
.last 29 (4,false),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.cycle 2 19 true (0),
.last 21 (4,false),
.cycle 0 20 true (0),
.cycle 2 49 true (0),
.last 28 (4,false),
.cycle 3 17 true (0),
.last 20 (4,false),
.last 28 (4,false),
.cycle 2 30 true (0),
.last 22 (4,false),
.cycle 27 1 false (7),
.last 47 (4,false),
.cycle 18 2 true (4),
.cycle 2 20 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 21 23 true (4),
.last 20 (4,false),
.cycle 3 18 true (0)
])
theorem kid11_part582_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part582) = true := by rfl

def kid11_part583 : Audit := .cycle 0 20 true (0)
theorem kid11_part583_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part583) = true := by rfl

def kid11_part584 : Audit := .split 20 (4,false) (byMove [
.cycle 18 23 true (4),
.cycle 18 26 true (3),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 19 2 true (5),
.cycle 20 2 true (5),
.cycle 0 21 true (0),
.cycle 18 22 true (4),
.cycle 20 9 true (5),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.cycle 20 9 true (5),
.cycle 19 13 true (4),
.cycle 20 3 true (5),
.last 21 (2,true),
.cycle 18 26 true (4),
.cycle 18 3 true (4),
.cycle 19 3 true (5),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 18 27 true (4),
.cycle 20 1 true (6),
.cycle 3 19 true (0)
])
theorem kid11_part584_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part584) = true := by rfl

def kid11_part585 : Audit := .split 20 (4,false) (byMove [
.cycle 3 41 true (0),
.cycle 3 44 true (0),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 3 20 true (0),
.cycle 19 2 true (5),
.cycle 0 21 true (0),
.cycle 3 40 true (0),
.cycle 19 9 true (5),
.cycle 3 18 true (0),
.cycle 20 1 true (6),
.cycle 19 9 true (5),
.cycle 3 31 true (0),
.cycle 19 3 true (5),
.last 21 (2,true),
.cycle 17 26 true (3),
.cycle 18 3 true (4),
.cycle 3 21 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 17 27 true (3),
.cycle 20 1 true (6),
.cycle 3 19 true (0)
])
theorem kid11_part585_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part585) = true := by rfl

def kid11_part561 : Audit := .split 18 (4,true) (byMove [(kid11_part562),(kid11_part563),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578),(kid11_part579),(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585)])

theorem kid11_part561_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part561) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) 18 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part562),(kid11_part563),(kid11_part564),(kid11_part565),(kid11_part566),(kid11_part567),(kid11_part568),(kid11_part569),(kid11_part570),(kid11_part571),(kid11_part572),(kid11_part573),(kid11_part574),(kid11_part575),(kid11_part576),(kid11_part577),(kid11_part578),(kid11_part579),(kid11_part580),(kid11_part581),(kid11_part582),(kid11_part583),(kid11_part584),(kid11_part585)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part562_checked

  · exact kid11_part568_checked

  · exact kid11_part574_checked

  · exact kid11_part580_checked

  · exact kid11_part563_checked

  · exact kid11_part569_checked

  · exact kid11_part575_checked

  · exact kid11_part581_checked

  · exact kid11_part564_checked

  · exact kid11_part570_checked

  · exact kid11_part576_checked

  · exact kid11_part582_checked

  · exact kid11_part565_checked

  · exact kid11_part571_checked

  · exact kid11_part577_checked

  · exact kid11_part583_checked

  · exact kid11_part566_checked

  · exact kid11_part572_checked

  · exact kid11_part578_checked

  · exact kid11_part584_checked

  · exact kid11_part567_checked

  · exact kid11_part573_checked

  · exact kid11_part579_checked

  · exact kid11_part585_checked

def kid11_part586 : Audit := .cycle 3 18 true (0)
theorem kid11_part586_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part586) = true := by rfl

def kid11_part490 : Audit := .split 17 (5,true) (byMove [(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500),(kid11_part501),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part530),(kid11_part531),(kid11_part556),(kid11_part557),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part586)])

theorem kid11_part490_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (kid11_part490) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,3⟩)) (5,true) (some mv)) (byMove [(kid11_part491),(kid11_part492),(kid11_part493),(kid11_part494),(kid11_part495),(kid11_part496),(kid11_part497),(kid11_part498),(kid11_part499),(kid11_part500),(kid11_part501),(kid11_part526),(kid11_part527),(kid11_part528),(kid11_part529),(kid11_part530),(kid11_part531),(kid11_part556),(kid11_part557),(kid11_part558),(kid11_part559),(kid11_part560),(kid11_part561),(kid11_part586)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part491_checked

  · exact kid11_part497_checked

  · exact kid11_part527_checked

  · exact kid11_part557_checked

  · exact kid11_part492_checked

  · exact kid11_part498_checked

  · exact kid11_part528_checked

  · exact kid11_part558_checked

  · exact kid11_part493_checked

  · exact kid11_part499_checked

  · exact kid11_part529_checked

  · exact kid11_part559_checked

  · exact kid11_part494_checked

  · exact kid11_part500_checked

  · exact kid11_part530_checked

  · exact kid11_part560_checked

  · exact kid11_part495_checked

  · exact kid11_part501_checked

  · exact kid11_part531_checked

  · exact kid11_part561_checked

  · exact kid11_part496_checked

  · exact kid11_part526_checked

  · exact kid11_part556_checked

  · exact kid11_part586_checked

def kid11_part588 : Audit := .cycle 0 10 true (0)
theorem kid11_part588_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part588) = true := by rfl

def kid11_part589 : Audit := .cycle 1 9 true (1)
theorem kid11_part589_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part589) = true := by rfl

def kid11_part591 : Audit := .split 22 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.last 25 (4,true),
.cycle 26 1 false (2),
.cycle 0 36 true (0),
.last 23 (4,true),
.cycle 0 28 true (0),
.cycle 0 51 true (0),
.cycle 0 63 true (0),
.cycle 0 44 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 0 24 true (0),
.cycle 0 26 true (0),
.cycle 0 30 true (0),
.cycle 0 30 true (0),
.cycle 5 18 true (0),
.last 23 (4,true),
.cycle 19 8 true (2),
.cycle 0 63 true (0),
.cycle 0 34 true (0),
.cycle 2 22 true (0),
.cycle 0 24 true (0),
.last 23 (4,true),
.cycle 2 52 true (0)
])
theorem kid11_part591_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part591) = true := by rfl

def kid11_part592 : Audit := .cycle 0 55 true (0)
theorem kid11_part592_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part592) = true := by rfl

def kid11_part593 : Audit := .cycle 21 1 false (3)
theorem kid11_part593_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part593) = true := by rfl

def kid11_part594 : Audit := .cycle 20 1 false (2)
theorem kid11_part594_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part594) = true := by rfl

def kid11_part595 : Audit := .cycle 22 1 false (2)
theorem kid11_part595_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part595) = true := by rfl

def kid11_part596 : Audit := .cycle 23 1 false (3)
theorem kid11_part596_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part596) = true := by rfl

def kid11_part597 : Audit := .cycle 25 1 false (7)
theorem kid11_part597_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part597) = true := by rfl

def kid11_part598 : Audit := .cycle 32 1 false (10)
theorem kid11_part598_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part598) = true := by rfl

def kid11_part599 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 46, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 24 1 false (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.cycle 23 1 false (7),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 23 1 false (7),
.cycle 47 1 false (11),
.cycle 31 1 false (7),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.last 22 (4,true),
.cycle 0 57 true (0),
.cycle 33 1 false (9),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 31 1 false (9)
])
theorem kid11_part599_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part599) = true := by rfl

def kid11_part600 : Audit := .cycle 32 1 false (10)
theorem kid11_part600_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part600) = true := by rfl

def kid11_part601 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 24 1 false (4),
.cycle 32 1 false (10),
.cycle 25 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 24 1 false (6),
.cycle 24 1 false (6),
.cycle 35 1 false (7),
.last 22 (2,true),
.cycle 34 1 false (10),
.cycle 21 1 false (3),
.cycle 23 1 false (3),
.cycle 20 2 true (3),
.cycle 0 57 true (0),
.cycle 34 1 false (8),
.last 21 (2,true),
.cycle 0 22 true (0),
.last 23 (2,true),
.cycle 32 1 false (8)
])
theorem kid11_part601_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part601) = true := by rfl

def kid11_part602 : Audit := .cycle 25 1 false (7)
theorem kid11_part602_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part602) = true := by rfl

def kid11_part603 : Audit := .cycle 24 12 true (4)
theorem kid11_part603_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part603) = true := by rfl

def kid11_part604 : Audit := .split 21 (2,true) (byMove [
.cycle 39 1 false (9),
.last 24 (4,true),
.cycle 24 1 false (2),
.cycle 0 29 true (0),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 6 16 true (0),
.cycle 48 14 true (8),
.cycle 10 14 true (0),
.cycle 0 55 true (0),
.last 22 (4,true),
.cycle 25 12 true (4),
.cycle 37 1 false (7),
.cycle 18 4 true (2),
.cycle 44 1 false (10),
.cycle 40 1 false (10),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.cycle 2 22 true (0),
.cycle 22 32 true (3),
.last 22 (4,true),
.cycle 2 32 true (0)
])
theorem kid11_part604_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part604) = true := by rfl

def kid11_part605 : Audit := .cycle 27 1 false (7)
theorem kid11_part605_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part605) = true := by rfl

def kid11_part606 : Audit := .cycle 20 1 false (2)
theorem kid11_part606_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part606) = true := by rfl

def kid11_part607 : Audit := .cycle 22 1 false (2)
theorem kid11_part607_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part607) = true := by rfl

def kid11_part608 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 0 61 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (3),
.cycle 27 1 false (7),
.cycle 36 1 false (10),
.last 22 (2,true),
.cycle 34 1 false (10),
.cycle 26 1 false (6),
.cycle 31 1 false (7),
.cycle 28 14 true (4),
.last 23 (2,true),
.cycle 29 1 false (7),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 20 2 true (2),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.last 22 (2,true),
.cycle 5 83 true (0),
.last 25 (2,true),
.cycle 19 4 true (2)
])
theorem kid11_part608_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part608) = true := by rfl

def kid11_part609 : Audit := .cycle 0 57 true (0)
theorem kid11_part609_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part609) = true := by rfl

def kid11_part610 : Audit := .cycle 1 21 true (0)
theorem kid11_part610_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part610) = true := by rfl

def kid11_part611 : Audit := .split 20 (2,true) (byMove [
.cycle 35 1 false (9),
.last 23 (4,true),
.cycle 23 1 false (3),
.cycle 43 1 false (11),
.last 21 (4,true),
.cycle 0 24 true (0),
.cycle 0 73 true (0),
.cycle 31 47 true (5),
.cycle 49 1 false (13),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 60 true (3),
.cycle 33 1 false (9),
.cycle 35 1 false (9),
.cycle 29 1 false (7),
.cycle 27 1 false (7),
.last 21 (4,true),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.cycle 18 36 true (2),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 2 20 true (0)
])
theorem kid11_part611_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part611) = true := by rfl

def kid11_part612 : Audit := .cycle 5 73 true (0)
theorem kid11_part612_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part612) = true := by rfl

def kid11_part613 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 34 1 false (8),
.last 21 (2,true),
.last 35 (2,true),
.cycle 24 1 false (2),
.last 23 (2,true),
.last 48 (2,true),
.last 58 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.last 32 (2,true),
.last 23 (2,true),
.last 25 (2,true),
.last 27 (2,true),
.last 21 (2,true),
.cycle 27 1 false (7),
.cycle 24 1 false (2),
.cycle 19 2 true (3),
.cycle 0 57 true (0),
.last 33 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.last 23 (2,true),
.last 23 (2,true)
])
theorem kid11_part613_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part613) = true := by rfl

def kid11_part614 : Audit := .cycle 2 22 true (0)
theorem kid11_part614_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part614) = true := by rfl

def kid11_part590 : Audit := .split 19 (5,true) (byMove [(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part602),(kid11_part603),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614)])

theorem kid11_part590_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part590) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some mv)) (byMove [(kid11_part591),(kid11_part592),(kid11_part593),(kid11_part594),(kid11_part595),(kid11_part596),(kid11_part597),(kid11_part598),(kid11_part599),(kid11_part600),(kid11_part601),(kid11_part602),(kid11_part603),(kid11_part604),(kid11_part605),(kid11_part606),(kid11_part607),(kid11_part608),(kid11_part609),(kid11_part610),(kid11_part611),(kid11_part612),(kid11_part613),(kid11_part614)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part591_checked

  · exact kid11_part597_checked

  · exact kid11_part603_checked

  · exact kid11_part609_checked

  · exact kid11_part592_checked

  · exact kid11_part598_checked

  · exact kid11_part604_checked

  · exact kid11_part610_checked

  · exact kid11_part593_checked

  · exact kid11_part599_checked

  · exact kid11_part605_checked

  · exact kid11_part611_checked

  · exact kid11_part594_checked

  · exact kid11_part600_checked

  · exact kid11_part606_checked

  · exact kid11_part612_checked

  · exact kid11_part595_checked

  · exact kid11_part601_checked

  · exact kid11_part607_checked

  · exact kid11_part613_checked

  · exact kid11_part596_checked

  · exact kid11_part602_checked

  · exact kid11_part608_checked

  · exact kid11_part614_checked

def kid11_part616 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 30, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 31 1 false (5),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 32 1 false (6),
.cycle 0 21 true (0),
.cycle 0 52 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.last 47 (4,true),
.cycle 3 20 true (0),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 29 1 false (5),
.cycle 0 49 true (0),
.last 21 (4,true),
.cycle 17 8 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 0 23 true (0),
.cycle 19 31 true (3)
])
theorem kid11_part616_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part616) = true := by rfl

def kid11_part617 : Audit := .cycle 0 21 true (0)
theorem kid11_part617_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part617) = true := by rfl

def kid11_part618 : Audit := .cycle 19 1 false (3)
theorem kid11_part618_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part618) = true := by rfl

def kid11_part619 : Audit := .cycle 18 1 false (2)
theorem kid11_part619_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part619) = true := by rfl

def kid11_part620 : Audit := .cycle 19 1 false (1)
theorem kid11_part620_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part620) = true := by rfl

def kid11_part621 : Audit := .cycle 20 1 false (2)
theorem kid11_part621_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part621) = true := by rfl

def kid11_part622 : Audit := .cycle 28 1 false (8)
theorem kid11_part622_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part622) = true := by rfl

def kid11_part623 : Audit := .cycle 21 1 false (5)
theorem kid11_part623_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part623) = true := by rfl

def kid11_part624 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 20 1 false (4),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.cycle 24 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.cycle 0 21 true (0),
.cycle 33 1 false (9)
])
theorem kid11_part624_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part624) = true := by rfl

def kid11_part625 : Audit := .cycle 0 19 true (0)
theorem kid11_part625_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part625) = true := by rfl

def kid11_part626 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 28 1 false (6),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.cycle 0 19 true (0),
.cycle 28 1 false (8),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 20 1 false (4),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 18 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 27 1 false (7),
.cycle 31 1 false (9),
.cycle 0 21 true (0),
.cycle 33 1 false (9)
])
theorem kid11_part626_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part626) = true := by rfl

def kid11_part627 : Audit := .cycle 21 1 false (5)
theorem kid11_part627_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part627) = true := by rfl

def kid11_part628 : Audit := .cycle 3 22 true (0)
theorem kid11_part628_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part628) = true := by rfl

def kid11_part629 : Audit := .split 19 (2,true) (byMove [
.cycle 33 1 false (7),
.last 22 (4,true),
.cycle 22 1 false (2),
.cycle 32 1 false (6),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 10 12 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 3 22 true (0),
.cycle 29 1 false (5),
.cycle 16 4 true (2),
.cycle 27 1 false (5),
.cycle 25 1 false (5),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 3 20 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 16 41 true (2)
])
theorem kid11_part629_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part629) = true := by rfl

def kid11_part630 : Audit := .cycle 30 1 false (8)
theorem kid11_part630_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part630) = true := by rfl

def kid11_part631 : Audit := .cycle 18 1 false (2)
theorem kid11_part631_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part631) = true := by rfl

def kid11_part632 : Audit := .cycle 19 1 false (1)
theorem kid11_part632_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part632) = true := by rfl

def kid11_part633 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 25 1 false (5),
.cycle 3 26 true (0),
.last 21 (2,true),
.cycle 32 1 false (8),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 0 54 true (0),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 0 23 true (0),
.cycle 17 4 true (2)
])
theorem kid11_part633_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part633) = true := by rfl

def kid11_part634 : Audit := .cycle 0 48 true (0)
theorem kid11_part634_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part634) = true := by rfl

def kid11_part635 : Audit := .cycle 28 1 false (6)
theorem kid11_part635_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part635) = true := by rfl

def kid11_part636 : Audit := .split 18 (2,true) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 28 1 false (6),
.cycle 0 19 true (0),
.cycle 56 1 false (12),
.cycle 35 1 false (9),
.cycle 26 1 false (6),
.cycle 32 1 false (8),
.cycle 28 1 false (6),
.cycle 23 1 false (5),
.cycle 29 1 false (7),
.cycle 32 1 false (8),
.cycle 30 1 false (8),
.last 19 (4,true),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 0 21 true (0),
.cycle 17 27 true (3)
])
theorem kid11_part636_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part636) = true := by rfl

def kid11_part637 : Audit := .cycle 0 19 true (0)
theorem kid11_part637_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part637) = true := by rfl

def kid11_part638 : Audit := .split 18 (4,true) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 false (1),
.cycle 0 22 true (0),
.cycle 0 19 true (0),
.cycle 0 50 true (0),
.cycle 0 29 true (0),
.cycle 26 1 false (6),
.cycle 32 1 false (8),
.cycle 28 1 false (6),
.cycle 23 1 false (5),
.cycle 0 23 true (0),
.last 19 (2,true),
.cycle 30 1 false (8),
.cycle 21 1 false (1),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 0 21 true (0),
.cycle 17 27 true (3)
])
theorem kid11_part638_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part638) = true := by rfl

def kid11_part639 : Audit := .cycle 17 27 true (3)
theorem kid11_part639_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part639) = true := by rfl

def kid11_part615 : Audit := .split 17 (5,true) (byMove [(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631),(kid11_part632),(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639)])

theorem kid11_part615_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part615) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (5,true) (some mv)) (byMove [(kid11_part616),(kid11_part617),(kid11_part618),(kid11_part619),(kid11_part620),(kid11_part621),(kid11_part622),(kid11_part623),(kid11_part624),(kid11_part625),(kid11_part626),(kid11_part627),(kid11_part628),(kid11_part629),(kid11_part630),(kid11_part631),(kid11_part632),(kid11_part633),(kid11_part634),(kid11_part635),(kid11_part636),(kid11_part637),(kid11_part638),(kid11_part639)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part616_checked

  · exact kid11_part622_checked

  · exact kid11_part628_checked

  · exact kid11_part634_checked

  · exact kid11_part617_checked

  · exact kid11_part623_checked

  · exact kid11_part629_checked

  · exact kid11_part635_checked

  · exact kid11_part618_checked

  · exact kid11_part624_checked

  · exact kid11_part630_checked

  · exact kid11_part636_checked

  · exact kid11_part619_checked

  · exact kid11_part625_checked

  · exact kid11_part631_checked

  · exact kid11_part637_checked

  · exact kid11_part620_checked

  · exact kid11_part626_checked

  · exact kid11_part632_checked

  · exact kid11_part638_checked

  · exact kid11_part621_checked

  · exact kid11_part627_checked

  · exact kid11_part633_checked

  · exact kid11_part639_checked

def kid11_part640 : Audit := .split 14 (4,true) (byMove [
.cycle 0 15 false (5),
.cycle 23 1 false (3),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 23 1 false (5),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (2),
.cycle 11 7 false (3),
.split 16 (2,true) (byMove [
.cycle 26 1 false (4),
.cycle 19 1 false (1),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 14 3 false (0),
.last 17 (5,true),
.cycle 0 17 true (-1),
.cycle 9 17 false (5),
.last 24 (5,true),
.cycle 23 1 false (3),
.cycle 12 5 false (2),
.cycle 11 7 false (3),
.cycle 20 1 false (2),
.last 18 (5,true),
.cycle 29 1 false (5),
.cycle 27 1 false (5),
.cycle 14 3 false (0),
.last 17 (5,true),
.last 33 (5,true),
.last 32 (5,true),
.cycle 2 15 false (5),
.cycle 9 21 false (6),
.last 20 (5,true),
.last 22 (5,true)
]),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 2 true (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 22 1 false (4),
.cycle 26 1 false (6),
.cycle 13 2 true (0),
.cycle 12 4 true (0)
])
theorem kid11_part640_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part640) = true := by rfl

def kid11_part641 : Audit := .cycle 8 2 true (4)
theorem kid11_part641_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part641) = true := by rfl

def kid11_part642 : Audit := .cycle 0 10 true (0)
theorem kid11_part642_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part642) = true := by rfl

def kid11_part643 : Audit := .cycle 1 9 true (1)
theorem kid11_part643_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part643) = true := by rfl

def kid11_part645 : Audit := .split 24 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.last 27 (4,true),
.cycle 28 1 false (2),
.cycle 0 33 true (0),
.last 25 (4,true),
.cycle 0 58 true (0),
.cycle 0 28 true (0),
.cycle 0 79 true (0),
.cycle 0 78 true (0),
.cycle 0 50 true (0),
.last 25 (4,true),
.cycle 0 30 true (0),
.cycle 0 34 true (0),
.cycle 0 42 true (0),
.cycle 0 42 true (0),
.cycle 0 71 true (0),
.last 25 (4,true),
.cycle 21 8 true (2),
.cycle 0 28 true (0),
.cycle 1 29 true (0),
.cycle 2 26 true (0),
.cycle 5 20 true (0),
.last 25 (4,true),
.cycle 62 14 true (12)
])
theorem kid11_part645_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part645) = true := by rfl

def kid11_part646 : Audit := .cycle 0 87 true (0)
theorem kid11_part646_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part646) = true := by rfl

def kid11_part647 : Audit := .cycle 23 1 false (3)
theorem kid11_part647_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part647) = true := by rfl

def kid11_part648 : Audit := .cycle 22 1 false (2)
theorem kid11_part648_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part648) = true := by rfl

def kid11_part649 : Audit := .cycle 30 1 false (8)
theorem kid11_part649_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part649) = true := by rfl

def kid11_part650 : Audit := .split 24 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 292, 4, 16, 128, 256, 8, 2, 4, 16, 4096],[2, 32, 256, 1, 4096, 4, 2, 32, 256, 1, 4096, 316, 4096],4096⟩,
.cycle 8 46 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 33 1 false (11),
.cycle 37 1 false (9),
.cycle 31 1 false (9),
.cycle 40 1 false (14),
.cycle 29 1 false (9),
.cycle 31 1 false (11),
.last 25 (4,true),
.cycle 33 1 false (9),
.cycle 26 34 true (4),
.cycle 53 1 false (9),
.cycle 33 1 false (9),
.cycle 25 1 false (3),
.cycle 23 2 true (3),
.last 26 (4,true),
.cycle 0 75 true (0),
.cycle 1 29 true (0),
.cycle 2 26 true (0),
.cycle 5 20 true (0),
.last 25 (4,true),
.cycle 42 1 false (14)
])
theorem kid11_part650_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part650) = true := by rfl

def kid11_part651 : Audit := .cycle 36 1 false (14)
theorem kid11_part651_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part651) = true := by rfl

def kid11_part652 : Audit := .cycle 36 1 false (14)
theorem kid11_part652_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part652) = true := by rfl

def kid11_part653 : Audit := .split 22 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 10 40 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 31 1 false (11),
.cycle 35 1 false (9),
.cycle 27 1 false (9),
.cycle 36 1 false (14),
.cycle 27 1 false (9),
.cycle 29 1 false (11),
.last 23 (4,true),
.cycle 27 1 false (9),
.cycle 24 28 true (4),
.cycle 43 1 false (9),
.cycle 29 1 false (9),
.cycle 23 1 false (3),
.cycle 22 2 true (3),
.last 24 (4,true),
.cycle 0 65 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 5 18 true (0),
.last 23 (4,true),
.cycle 10 24 true (0)
])
theorem kid11_part653_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part653) = true := by rfl

def kid11_part654 : Audit := .cycle 26 1 false (8)
theorem kid11_part654_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part654) = true := by rfl

def kid11_part655 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 29 21 true (3),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 31 1 false (11),
.last 25 (2,true),
.cycle 28 1 false (10),
.cycle 36 1 false (14),
.last 23 (2,true),
.cycle 29 1 false (11),
.cycle 28 1 false (10),
.cycle 28 1 false (10),
.cycle 24 15 true (4),
.last 24 (2,true),
.cycle 30 1 false (10),
.cycle 23 1 false (3),
.last 24 (2,true),
.cycle 22 2 true (3),
.cycle 26 16 true (4),
.cycle 1 25 true (0),
.last 23 (2,true),
.cycle 5 18 true (0),
.cycle 9 26 true (0),
.cycle 26 12 true (6)
])
theorem kid11_part655_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part655) = true := by rfl

def kid11_part656 : Audit := .cycle 29 1 false (11)
theorem kid11_part656_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part656) = true := by rfl

def kid11_part657 : Audit := .cycle 26 20 true (4)
theorem kid11_part657_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part657) = true := by rfl

def kid11_part658 : Audit := .split 23 (2,true) (byMove [
.cycle 47 1 false (13),
.last 26 (4,true),
.cycle 26 1 false (2),
.cycle 0 37 true (0),
.last 24 (4,true),
.cycle 21 3 false (3),
.cycle 0 65 true (0),
.cycle 56 20 true (10),
.cycle 10 18 true (0),
.cycle 0 87 true (0),
.last 24 (4,true),
.cycle 27 20 true (4),
.cycle 49 1 false (11),
.cycle 20 4 true (2),
.cycle 54 1 false (14),
.cycle 48 1 false (14),
.last 24 (4,true),
.cycle 21 3 false (3),
.cycle 0 81 true (0),
.cycle 1 31 true (0),
.cycle 2 26 true (0),
.cycle 31 33 true (6),
.last 24 (4,true),
.cycle 35 18 true (5)
])
theorem kid11_part658_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part658) = true := by rfl

def kid11_part659 : Audit := .cycle 40 1 false (14)
theorem kid11_part659_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part659) = true := by rfl

def kid11_part660 : Audit := .cycle 22 1 false (2)
theorem kid11_part660_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part660) = true := by rfl

def kid11_part661 : Audit := .split 23 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 288, 4, 16, 128, 256, 8, 2, 4, 16, 4096],[2, 32, 256, 1, 4096, 256, 2, 32, 256, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 99 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 34 1 false (8),
.cycle 39 1 false (9),
.cycle 40 1 false (14),
.cycle 42 1 false (14),
.cycle 29 1 false (9),
.cycle 30 1 false (8),
.last 24 (4,true),
.cycle 39 1 false (11),
.cycle 30 26 true (4),
.cycle 20 6 true (2),
.cycle 44 1 false (14),
.cycle 24 1 false (2),
.cycle 22 2 true (2),
.last 25 (4,true),
.cycle 0 81 true (0),
.cycle 1 31 true (0),
.cycle 2 26 true (0),
.cycle 0 74 true (0),
.last 24 (4,true),
.last 25 (4,true)
])
theorem kid11_part661_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part661) = true := by rfl

def kid11_part662 : Audit := .split 23 (4,true) (byMove [
.last 26 (2,true),
.cycle 0 99 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 34 1 false (8),
.last 26 (2,true),
.cycle 40 1 false (14),
.cycle 42 1 false (14),
.last 24 (2,true),
.cycle 30 1 false (8),
.cycle 30 1 false (10),
.cycle 39 1 false (11),
.cycle 30 26 true (4),
.last 25 (2,true),
.cycle 44 1 false (14),
.cycle 24 1 false (2),
.last 25 (2,true),
.cycle 22 2 true (2),
.cycle 0 81 true (0),
.cycle 1 31 true (0),
.last 24 (2,true),
.cycle 0 74 true (0),
.cycle 27 11 true (7),
.cycle 21 4 true (2)
])
theorem kid11_part662_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part662) = true := by rfl

def kid11_part663 : Audit := .cycle 0 69 true (0)
theorem kid11_part663_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part663) = true := by rfl

def kid11_part664 : Audit := .cycle 1 25 true (0)
theorem kid11_part664_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part664) = true := by rfl

def kid11_part665 : Audit := .split 22 (2,true) (byMove [
.cycle 43 1 false (13),
.last 25 (4,true),
.cycle 25 1 false (3),
.cycle 0 29 true (0),
.last 23 (4,true),
.cycle 0 121 true (0),
.cycle 6 48 true (0),
.cycle 64 28 true (14),
.cycle 79 1 false (21),
.cycle 0 109 true (0),
.last 23 (4,true),
.cycle 23 40 true (5),
.cycle 39 1 false (13),
.cycle 43 1 false (13),
.cycle 44 1 false (14),
.cycle 40 1 false (14),
.last 23 (4,true),
.cycle 21 2 true (3),
.cycle 0 81 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 5 18 true (0),
.last 23 (4,true),
.cycle 2 24 true (0)
])
theorem kid11_part665_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part665) = true := by rfl

def kid11_part666 : Audit := .cycle 0 64 true (0)
theorem kid11_part666_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part666) = true := by rfl

def kid11_part667 : Audit := .split 22 (4,true) (byMove [
.last 25 (2,true),
.cycle 88 9 true (14),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 26 1 false (4),
.last 25 (2,true),
.cycle 23 9 true (5),
.cycle 67 9 true (17),
.last 23 (2,true),
.cycle 42 9 true (8),
.cycle 9 17 true (0),
.cycle 25 9 true (7),
.cycle 27 9 true (5),
.cycle 32 9 true (6),
.last 23 (2,true),
.cycle 40 1 false (14),
.last 25 (2,true),
.cycle 21 2 true (3),
.cycle 23 9 true (5),
.cycle 1 25 true (0),
.last 23 (2,true),
.cycle 5 18 true (0),
.cycle 26 9 true (7),
.cycle 25 9 true (7)
])
theorem kid11_part667_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part667) = true := by rfl

def kid11_part668 : Audit := .cycle 24 12 true (6)
theorem kid11_part668_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part668) = true := by rfl

def kid11_part644 : Audit := .split 21 (5,true) (byMove [(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655),(kid11_part656),(kid11_part657),(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668)])

theorem kid11_part644_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part644) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) 21 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (5,true) (some mv)) (byMove [(kid11_part645),(kid11_part646),(kid11_part647),(kid11_part648),(kid11_part649),(kid11_part650),(kid11_part651),(kid11_part652),(kid11_part653),(kid11_part654),(kid11_part655),(kid11_part656),(kid11_part657),(kid11_part658),(kid11_part659),(kid11_part660),(kid11_part661),(kid11_part662),(kid11_part663),(kid11_part664),(kid11_part665),(kid11_part666),(kid11_part667),(kid11_part668)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part645_checked

  · exact kid11_part651_checked

  · exact kid11_part657_checked

  · exact kid11_part663_checked

  · exact kid11_part646_checked

  · exact kid11_part652_checked

  · exact kid11_part658_checked

  · exact kid11_part664_checked

  · exact kid11_part647_checked

  · exact kid11_part653_checked

  · exact kid11_part659_checked

  · exact kid11_part665_checked

  · exact kid11_part648_checked

  · exact kid11_part654_checked

  · exact kid11_part660_checked

  · exact kid11_part666_checked

  · exact kid11_part649_checked

  · exact kid11_part655_checked

  · exact kid11_part661_checked

  · exact kid11_part667_checked

  · exact kid11_part650_checked

  · exact kid11_part656_checked

  · exact kid11_part662_checked

  · exact kid11_part668_checked

def kid11_part670 : Audit := .split 22 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.last 25 (4,true),
.cycle 26 1 false (2),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 0 109 true (0),
.cycle 6 17 true (0),
.cycle 0 25 true (0),
.cycle 0 59 true (0),
.cycle 3 54 true (0),
.last 23 (4,true),
.cycle 23 13 true (4),
.cycle 0 48 true (0),
.cycle 0 35 true (0),
.cycle 41 1 false (9),
.cycle 0 27 true (0),
.last 23 (4,true),
.cycle 19 8 true (2),
.cycle 0 66 true (0),
.cycle 0 25 true (0),
.cycle 2 23 true (0),
.cycle 0 53 true (0),
.last 23 (4,true),
.cycle 0 36 true (0)
])
theorem kid11_part670_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part670) = true := by rfl

def kid11_part671 : Audit := .cycle 44 32 true (4)
theorem kid11_part671_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part671) = true := by rfl

def kid11_part672 : Audit := .cycle 21 1 false (3)
theorem kid11_part672_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part672) = true := by rfl

def kid11_part673 : Audit := .cycle 20 1 false (2)
theorem kid11_part673_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part673) = true := by rfl

def kid11_part674 : Audit := .cycle 21 1 false (3)
theorem kid11_part674_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part674) = true := by rfl

def kid11_part675 : Audit := .cycle 27 1 false (9)
theorem kid11_part675_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part675) = true := by rfl

def kid11_part676 : Audit := .cycle 0 23 true (0)
theorem kid11_part676_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part676) = true := by rfl

def kid11_part677 : Audit := .cycle 25 1 false (9)
theorem kid11_part677_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part677) = true := by rfl

def kid11_part678 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 89 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 22 1 false (4),
.cycle 34 1 false (12),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.cycle 24 1 false (8),
.cycle 32 1 false (12),
.last 21 (4,true),
.cycle 25 1 false (9),
.cycle 22 13 true (4),
.cycle 36 1 false (8),
.cycle 27 1 false (9),
.cycle 21 1 false (3),
.cycle 27 1 false (9),
.last 22 (4,true),
.cycle 25 36 true (4),
.cycle 1 32 true (0),
.cycle 2 21 true (0),
.cycle 10 40 true (0),
.last 21 (4,true),
.cycle 25 24 true (4)
])
theorem kid11_part678_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part678) = true := by rfl

def kid11_part679 : Audit := .cycle 25 1 false (9)
theorem kid11_part679_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part679) = true := by rfl

def kid11_part680 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 89 true (0),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 22 1 false (4),
.cycle 34 1 false (12),
.cycle 25 1 false (9),
.cycle 24 1 false (8),
.last 21 (2,true),
.cycle 32 1 false (12),
.cycle 24 1 false (8),
.cycle 25 1 false (9),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 27 1 false (9),
.cycle 21 1 false (3),
.cycle 27 1 false (9),
.cycle 20 2 true (3),
.cycle 24 36 true (4),
.cycle 1 32 true (0),
.last 21 (2,true),
.cycle 9 40 true (0),
.cycle 3 21 true (0),
.cycle 24 24 true (4)
])
theorem kid11_part680_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part680) = true := by rfl

def kid11_part681 : Audit := .cycle 25 1 false (9)
theorem kid11_part681_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part681) = true := by rfl

def kid11_part682 : Audit := .cycle 24 15 true (4)
theorem kid11_part682_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part682) = true := by rfl

def kid11_part683 : Audit := .split 21 (2,true) (byMove [
.cycle 41 1 false (11),
.last 24 (4,true),
.cycle 24 1 false (2),
.cycle 24 15 true (4),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 36 30 true (6),
.cycle 10 16 true (0),
.cycle 46 32 true (4),
.last 22 (4,true),
.cycle 25 15 true (4),
.cycle 41 1 false (9),
.cycle 18 4 true (2),
.cycle 37 1 false (9),
.cycle 33 1 false (9),
.last 22 (4,true),
.cycle 19 3 false (3),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.cycle 2 23 true (0),
.cycle 5 17 true (0),
.last 22 (4,true),
.cycle 33 11 true (5)
])
theorem kid11_part683_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part683) = true := by rfl

def kid11_part684 : Audit := .cycle 0 27 true (0)
theorem kid11_part684_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part684) = true := by rfl

def kid11_part685 : Audit := .cycle 20 1 false (2)
theorem kid11_part685_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part685) = true := by rfl

def kid11_part686 : Audit := .cycle 0 27 true (0)
theorem kid11_part686_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part686) = true := by rfl

def kid11_part687 : Audit := .split 21 (4,true) (byMove [
.last 24 (2,true),
.cycle 50 36 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 29 1 false (9),
.cycle 0 27 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 27 1 false (9),
.cycle 26 1 false (8),
.cycle 33 1 false (9),
.cycle 28 19 true (4),
.last 23 (2,true),
.cycle 0 31 true (0),
.cycle 22 1 false (2),
.cycle 0 31 true (0),
.cycle 20 2 true (2),
.cycle 0 27 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 3 23 true (0),
.cycle 19 4 true (2)
])
theorem kid11_part687_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part687) = true := by rfl

def kid11_part688 : Audit := .cycle 0 23 true (0)
theorem kid11_part688_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part688) = true := by rfl

def kid11_part689 : Audit := .cycle 20 11 true (4)
theorem kid11_part689_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part689) = true := by rfl

def kid11_part690 : Audit := .split 20 (2,true) (byMove [
.cycle 37 1 false (11),
.last 23 (4,true),
.cycle 23 1 false (3),
.cycle 0 51 true (0),
.last 21 (4,true),
.cycle 0 89 true (0),
.cycle 6 15 true (0),
.cycle 44 13 true (8),
.cycle 61 1 false (17),
.cycle 0 79 true (0),
.last 21 (4,true),
.cycle 21 11 true (5),
.cycle 29 1 false (9),
.cycle 37 1 false (11),
.cycle 35 1 false (11),
.cycle 33 1 false (11),
.last 21 (4,true),
.cycle 19 2 true (3),
.cycle 0 85 true (0),
.cycle 1 45 true (0),
.cycle 2 21 true (0),
.cycle 21 56 true (4),
.last 21 (4,true),
.cycle 2 57 true (0)
])
theorem kid11_part690_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part690) = true := by rfl

def kid11_part691 : Audit := .cycle 5 15 true (0)
theorem kid11_part691_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part691) = true := by rfl

def kid11_part692 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 0 27 true (0),
.last 21 (2,true),
.cycle 0 51 true (0),
.cycle 23 1 false (3),
.cycle 0 89 true (0),
.cycle 6 15 true (0),
.cycle 44 13 true (8),
.last 21 (2,true),
.cycle 0 79 true (0),
.cycle 61 1 false (17),
.cycle 21 11 true (5),
.cycle 29 1 false (9),
.cycle 37 1 false (11),
.last 21 (2,true),
.cycle 33 1 false (11),
.cycle 35 1 false (11),
.cycle 19 2 true (3),
.cycle 0 85 true (0),
.cycle 1 45 true (0),
.last 21 (2,true),
.cycle 21 56 true (4),
.cycle 3 21 true (0),
.cycle 3 57 true (0)
])
theorem kid11_part692_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part692) = true := by rfl

def kid11_part693 : Audit := .cycle 22 9 true (6)
theorem kid11_part693_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part693) = true := by rfl

def kid11_part669 : Audit := .split 19 (5,true) (byMove [(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685),(kid11_part686),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part690),(kid11_part691),(kid11_part692),(kid11_part693)])

theorem kid11_part669_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part669) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) 19 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (5,true) (some mv)) (byMove [(kid11_part670),(kid11_part671),(kid11_part672),(kid11_part673),(kid11_part674),(kid11_part675),(kid11_part676),(kid11_part677),(kid11_part678),(kid11_part679),(kid11_part680),(kid11_part681),(kid11_part682),(kid11_part683),(kid11_part684),(kid11_part685),(kid11_part686),(kid11_part687),(kid11_part688),(kid11_part689),(kid11_part690),(kid11_part691),(kid11_part692),(kid11_part693)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part670_checked

  · exact kid11_part676_checked

  · exact kid11_part682_checked

  · exact kid11_part688_checked

  · exact kid11_part671_checked

  · exact kid11_part677_checked

  · exact kid11_part683_checked

  · exact kid11_part689_checked

  · exact kid11_part672_checked

  · exact kid11_part678_checked

  · exact kid11_part684_checked

  · exact kid11_part690_checked

  · exact kid11_part673_checked

  · exact kid11_part679_checked

  · exact kid11_part685_checked

  · exact kid11_part691_checked

  · exact kid11_part674_checked

  · exact kid11_part680_checked

  · exact kid11_part686_checked

  · exact kid11_part692_checked

  · exact kid11_part675_checked

  · exact kid11_part681_checked

  · exact kid11_part687_checked

  · exact kid11_part693_checked

def kid11_part694 : Audit := .cycle 9 1 true (5)
theorem kid11_part694_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part694) = true := by rfl

def kid11_part695 : Audit := .cycle 8 2 true (4)
theorem kid11_part695_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part695) = true := by rfl

def kid11_part696 : Audit := .cycle 7 4 true (3)
theorem kid11_part696_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part696) = true := by rfl

def kid11_part698 : Audit := .cycle 1 12 true (1)
theorem kid11_part698_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part698) = true := by rfl

def kid11_part699 : Audit := .cycle 7 5 true (3)
theorem kid11_part699_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part699) = true := by rfl

def kid11_part700 : Audit := .split 21 (5,true) (byMove [
.cycle 28 1 false (2),
.cycle 0 25 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 27 1 false (1),
.cycle 28 1 false (2),
.cycle 36 1 false (8),
.cycle 29 1 false (5),
.cycle 24 1 false (4),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 29 1 false (5),
.cycle 2 30 true (0),
.cycle 26 1 false (2),
.cycle 38 1 false (8),
.cycle 22 1 false (2),
.cycle 27 1 false (1),
.last 23 (4,true),
.cycle 0 60 true (0),
.cycle 40 1 false (6),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 31 1 false (3)
])
theorem kid11_part700_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part700) = true := by rfl

def kid11_part701 : Audit := .cycle 0 13 true (0)
theorem kid11_part701_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part701) = true := by rfl

def kid11_part702 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.last 19 (5,true),
.last 28 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 7 7 true (3),
.last 23 (5,true),
.cycle 0 15 true (0),
.last 19 (5,true),
.last 19 (5,true),
.cycle 12 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 8 5 true (4)
])
theorem kid11_part702_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part702) = true := by rfl

def kid11_part703 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 19 4 false (1),
.cycle 28 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 46 1 false (12),
.cycle 36 1 false (10),
.cycle 9 4 true (4),
.cycle 8 5 true (4),
.cycle 7 7 true (3),
.cycle 23 3 false (1),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.cycle 19 4 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.cycle 8 5 true (4)
])
theorem kid11_part703_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part703) = true := by rfl

def kid11_part704 : Audit := .cycle 0 12 true (0)
theorem kid11_part704_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part704) = true := by rfl

def kid11_part705 : Audit := .cycle 1 11 true (1)
theorem kid11_part705_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part705) = true := by rfl

def kid11_part706 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 9 11 true (4),
.cycle 8 12 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 41 1 false (11),
.cycle 0 37 true (0),
.cycle 9 11 true (4),
.cycle 8 12 true (4),
.cycle 7 14 true (3),
.cycle 10 10 true (4),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 16, 128, 256, 8, 2, 4, 16, 4096],[2, 32, 4, 1, 4096, 4, 2, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 18 3 true (6),
.cycle 8 12 true (4)
])
theorem kid11_part706_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part706) = true := by rfl

def kid11_part707 : Audit := .cycle 3 9 true (1)
theorem kid11_part707_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part707) = true := by rfl

def kid11_part708 : Audit := .cycle 9 3 true (4)
theorem kid11_part708_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part708) = true := by rfl

def kid11_part709 : Audit := .cycle 8 4 true (4)
theorem kid11_part709_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part709) = true := by rfl

def kid11_part710 : Audit := .cycle 6 6 true (2)
theorem kid11_part710_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part710) = true := by rfl

def kid11_part711 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 30 5 false (1),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 47 1 false (9),
.cycle 33 1 false (9),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 7 8 true (3),
.cycle 10 4 true (4),
.cycle 0 16 true (0),
.cycle 22 1 false (2),
.cycle 30 5 false (1),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 3 true (4),
.cycle 8 6 true (4)
])
theorem kid11_part711_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part711) = true := by rfl

def kid11_part712 : Audit := .cycle 1 15 true (1)
theorem kid11_part712_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part712) = true := by rfl

def kid11_part713 : Audit := .cycle 1 13 true (1)
theorem kid11_part713_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part713) = true := by rfl

def kid11_part714 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (3),
.cycle 0 16 true (0),
.last 21 (5,true),
.last 19 (5,true),
.last 19 (5,true),
.last 28 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 31 (5,true),
.cycle 0 14 true (0),
.cycle 9 5 true (4),
.last 13 (5,true),
.last 15 (5,true),
.last 23 (5,true),
.cycle 1 15 true (1),
.last 19 (5,true),
.last 19 (5,true),
.cycle 12 2 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part714_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part714) = true := by rfl

def kid11_part715 : Audit := .split 12 (5,true) (byMove [
.cycle 10 8 true (3),
.cycle 0 16 true (0),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 19 4 false (1),
.cycle 28 5 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4),
.cycle 7 10 true (3),
.cycle 23 3 false (1),
.cycle 1 15 true (1),
.cycle 20 1 false (2),
.cycle 19 4 false (1),
.last 14 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 11 2 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (4)
])
theorem kid11_part715_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part715) = true := by rfl

def kid11_part716 : Audit := .cycle 0 12 true (0)
theorem kid11_part716_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part716) = true := by rfl

def kid11_part717 : Audit := .cycle 1 11 true (1)
theorem kid11_part717_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part717) = true := by rfl

def kid11_part718 : Audit := .cycle 2 10 true (1)
theorem kid11_part718_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part718) = true := by rfl

def kid11_part719 : Audit := .cycle 1 14 true (1)
theorem kid11_part719_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part719) = true := by rfl

def kid11_part720 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 42 9 false (2),
.cycle 8 7 true (4),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 45 (4,true),
.cycle 0 39 true (0),
.cycle 9 6 true (4),
.cycle 8 7 true (4),
.cycle 7 9 true (3),
.cycle 10 5 true (4),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 21 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 12 3 true (5),
.cycle 8 7 true (4)
])
theorem kid11_part720_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part720) = true := by rfl

def kid11_part721 : Audit := .cycle 8 4 true (4)
theorem kid11_part721_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part721) = true := by rfl

def kid11_part697 : Audit := .split 11 (2,true) (byMove [(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709),(kid11_part710),(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714),(kid11_part715),(kid11_part716),(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721)])

theorem kid11_part697_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part697) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part698),(kid11_part699),(kid11_part700),(kid11_part701),(kid11_part702),(kid11_part703),(kid11_part704),(kid11_part705),(kid11_part706),(kid11_part707),(kid11_part708),(kid11_part709),(kid11_part710),(kid11_part711),(kid11_part712),(kid11_part713),(kid11_part714),(kid11_part715),(kid11_part716),(kid11_part717),(kid11_part718),(kid11_part719),(kid11_part720),(kid11_part721)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part698_checked

  · exact kid11_part704_checked

  · exact kid11_part710_checked

  · exact kid11_part716_checked

  · exact kid11_part699_checked

  · exact kid11_part705_checked

  · exact kid11_part711_checked

  · exact kid11_part717_checked

  · exact kid11_part700_checked

  · exact kid11_part706_checked

  · exact kid11_part712_checked

  · exact kid11_part718_checked

  · exact kid11_part701_checked

  · exact kid11_part707_checked

  · exact kid11_part713_checked

  · exact kid11_part719_checked

  · exact kid11_part702_checked

  · exact kid11_part708_checked

  · exact kid11_part714_checked

  · exact kid11_part720_checked

  · exact kid11_part703_checked

  · exact kid11_part709_checked

  · exact kid11_part715_checked

  · exact kid11_part721_checked

def kid11_part722 : Audit := .cycle 0 12 true (0)
theorem kid11_part722_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part722) = true := by rfl

def kid11_part724 : Audit := .split 20 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.last 23 (4,true),
.cycle 24 1 false (2),
.cycle 0 32 true (0),
.last 21 (4,true),
.cycle 0 26 true (0),
.cycle 0 47 true (0),
.cycle 0 57 true (0),
.cycle 0 42 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 0 22 true (0),
.cycle 0 24 true (0),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 5 16 true (0),
.last 21 (4,true),
.cycle 17 8 true (2),
.cycle 0 57 true (0),
.cycle 0 30 true (0),
.cycle 2 20 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 4 46 true (0)
])
theorem kid11_part724_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part724) = true := by rfl

def kid11_part725 : Audit := .cycle 0 51 true (0)
theorem kid11_part725_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part725) = true := by rfl

def kid11_part726 : Audit := .cycle 19 1 false (3)
theorem kid11_part726_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part726) = true := by rfl

def kid11_part727 : Audit := .cycle 18 1 false (2)
theorem kid11_part727_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part727) = true := by rfl

def kid11_part728 : Audit := .cycle 19 1 false (1)
theorem kid11_part728_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part728) = true := by rfl

def kid11_part729 : Audit := .cycle 20 1 false (2)
theorem kid11_part729_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part729) = true := by rfl

def kid11_part730 : Audit := .cycle 22 1 false (6)
theorem kid11_part730_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part730) = true := by rfl

def kid11_part731 : Audit := .cycle 29 1 false (9)
theorem kid11_part731_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part731) = true := by rfl

def kid11_part732 : Audit := .split 18 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 38, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.cycle 21 1 false (7),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 21 1 false (7),
.cycle 43 1 false (11),
.cycle 29 1 false (7),
.cycle 31 1 false (9),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,true),
.cycle 0 51 true (0),
.cycle 29 1 false (9),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 29 1 false (9)
])
theorem kid11_part732_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part732) = true := by rfl

def kid11_part733 : Audit := .cycle 29 1 false (9)
theorem kid11_part733_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part733) = true := by rfl

def kid11_part734 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.cycle 29 1 false (9),
.cycle 22 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 false (5),
.cycle 21 1 false (5),
.cycle 30 1 false (6),
.last 20 (2,true),
.cycle 31 1 false (9),
.cycle 19 1 false (3),
.cycle 20 1 false (2),
.cycle 18 2 true (3),
.cycle 0 51 true (0),
.cycle 29 1 false (7),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 26 true (4),
.cycle 27 1 false (7)
])
theorem kid11_part734_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part734) = true := by rfl

def kid11_part735 : Audit := .cycle 22 1 false (6)
theorem kid11_part735_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part735) = true := by rfl

def kid11_part736 : Audit := .cycle 22 10 true (4)
theorem kid11_part736_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part736) = true := by rfl

def kid11_part737 : Audit := .split 19 (2,true) (byMove [
.cycle 36 1 false (8),
.last 22 (4,true),
.cycle 22 1 false (2),
.cycle 0 27 true (0),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 6 14 true (0),
.cycle 44 12 true (8),
.cycle 10 14 true (0),
.cycle 0 51 true (0),
.last 20 (4,true),
.cycle 23 10 true (4),
.cycle 34 1 false (6),
.cycle 16 4 true (2),
.cycle 41 1 false (9),
.cycle 37 1 false (9),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.cycle 2 20 true (0),
.cycle 20 30 true (3),
.last 20 (4,true),
.cycle 4 28 true (0)
])
theorem kid11_part737_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part737) = true := by rfl

def kid11_part738 : Audit := .cycle 24 1 false (6)
theorem kid11_part738_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part738) = true := by rfl

def kid11_part739 : Audit := .cycle 18 1 false (2)
theorem kid11_part739_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part739) = true := by rfl

def kid11_part740 : Audit := .cycle 19 1 false (1)
theorem kid11_part740_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part740) = true := by rfl

def kid11_part741 : Audit := .split 19 (4,true) (byMove [
.last 22 (2,true),
.cycle 0 57 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 22 1 false (2),
.cycle 24 1 false (6),
.cycle 33 1 false (9),
.last 20 (2,true),
.cycle 31 1 false (9),
.cycle 23 1 false (5),
.cycle 28 1 false (6),
.cycle 26 12 true (4),
.last 21 (2,true),
.cycle 26 1 false (6),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 18 2 true (2),
.cycle 0 59 true (0),
.cycle 1 23 true (0),
.last 20 (2,true),
.cycle 5 77 true (0),
.cycle 19 28 true (3),
.cycle 17 4 true (2)
])
theorem kid11_part741_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part741) = true := by rfl

def kid11_part742 : Audit := .cycle 0 51 true (0)
theorem kid11_part742_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part742) = true := by rfl

def kid11_part743 : Audit := .cycle 1 19 true (0)
theorem kid11_part743_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part743) = true := by rfl

def kid11_part744 : Audit := .split 18 (2,true) (byMove [
.cycle 32 1 false (8),
.last 21 (4,true),
.cycle 21 1 false (3),
.cycle 38 1 false (10),
.last 19 (4,true),
.cycle 0 22 true (0),
.cycle 0 67 true (0),
.cycle 27 43 true (5),
.cycle 46 1 false (12),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 17 54 true (3),
.cycle 30 1 false (8),
.cycle 32 1 false (8),
.cycle 26 1 false (6),
.cycle 24 1 false (6),
.last 19 (4,true),
.cycle 17 2 true (3),
.cycle 0 51 true (0),
.cycle 16 32 true (2),
.cycle 2 18 true (0),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 2 18 true (0)
])
theorem kid11_part744_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part744) = true := by rfl

def kid11_part745 : Audit := .cycle 5 67 true (0)
theorem kid11_part745_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part745) = true := by rfl

def kid11_part746 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 31 1 false (7),
.last 19 (2,true),
.cycle 42 1 false (12),
.cycle 21 1 false (1),
.cycle 26 1 false (6),
.cycle 6 67 true (0),
.cycle 46 30 true (8),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 39 1 false (11),
.cycle 17 70 true (3),
.cycle 34 1 false (10),
.cycle 36 1 false (10),
.last 19 (2,true),
.cycle 24 1 false (6),
.cycle 21 1 false (1),
.cycle 17 2 true (3),
.cycle 0 51 true (0),
.cycle 1 59 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 26 true (4),
.cycle 17 26 true (3)
])
theorem kid11_part746_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part746) = true := by rfl

def kid11_part747 : Audit := .cycle 4 18 true (0)
theorem kid11_part747_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part747) = true := by rfl

def kid11_part723 : Audit := .split 17 (5,true) (byMove [(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734),(kid11_part735),(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747)])

theorem kid11_part723_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part723) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some mv)) (byMove [(kid11_part724),(kid11_part725),(kid11_part726),(kid11_part727),(kid11_part728),(kid11_part729),(kid11_part730),(kid11_part731),(kid11_part732),(kid11_part733),(kid11_part734),(kid11_part735),(kid11_part736),(kid11_part737),(kid11_part738),(kid11_part739),(kid11_part740),(kid11_part741),(kid11_part742),(kid11_part743),(kid11_part744),(kid11_part745),(kid11_part746),(kid11_part747)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part724_checked

  · exact kid11_part730_checked

  · exact kid11_part736_checked

  · exact kid11_part742_checked

  · exact kid11_part725_checked

  · exact kid11_part731_checked

  · exact kid11_part737_checked

  · exact kid11_part743_checked

  · exact kid11_part726_checked

  · exact kid11_part732_checked

  · exact kid11_part738_checked

  · exact kid11_part744_checked

  · exact kid11_part727_checked

  · exact kid11_part733_checked

  · exact kid11_part739_checked

  · exact kid11_part745_checked

  · exact kid11_part728_checked

  · exact kid11_part734_checked

  · exact kid11_part740_checked

  · exact kid11_part746_checked

  · exact kid11_part729_checked

  · exact kid11_part735_checked

  · exact kid11_part741_checked

  · exact kid11_part747_checked

def kid11_part749 : Audit := .split 17 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 16, 128, 256, 32768, 2, 256, 65536, 128, 256, 8, 32, 256, 16, 262144],[2, 32, 256, 1, 256, 262144, 8192, 131072, 256, 4096, 256, 262144, 2, 32, 256, 1, 256, 262144, 262144],278540⟩,
.cycle 20 15 true (1),
.cycle 21 1 false (-1),
.last 21 (5,true),
.last 25 (5,true),
.last 18 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 33 (5,true),
.last 21 (5,true),
.cycle 16 33 true (0),
.last 18 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 24 (5,true),
.last 21 (5,true),
.cycle 14 8 true (-1),
.last 18 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.cycle 16 20 true (0),
.last 21 (5,true),
.cycle 22 5 true (3),
.last 18 (5,true)
])
theorem kid11_part749_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part749) = true := by rfl

def kid11_part750 : Audit := .split 20 (5,true) (byMove [
.last 23 (2,true),
.cycle 0 24 true (-1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 10 11 false (4),
.cycle 8 13 false (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 59, 16, 64],[2, 32, 64, 1, 24, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 59, 16, 64],[2, 32, 64, 1, 24, 2, 64],64⟩,
.last 21 (2,true),
.cycle 0 22 true (-1),
.cycle 0 70 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 59, 16, 64],[2, 32, 64, 1, 24, 32, 64],64⟩,
.cycle 19 49 true (3),
.last 22 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 35, 35, 16, 128, 256, 8, 2, 9, 16, 4096],[2, 32, 4096, 1, 8, 1, 2, 32, 4096, 1, 16, 4096, 4096],4096⟩,
.cycle 29 1 false (1),
.cycle 10 11 false (4),
.cycle 0 26 true (-1),
.cycle 50 24 true (7),
.cycle 1 47 true (-1),
.last 21 (2,true),
.cycle 0 22 true (-1),
.cycle 0 45 true (-2),
.cycle 0 32 true (-1)
])
theorem kid11_part750_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part750) = true := by rfl

def kid11_part751 : Audit := .cycle 16 1 false (0)
theorem kid11_part751_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part751) = true := by rfl

def kid11_part752 : Audit := .cycle 15 1 false (-1)
theorem kid11_part752_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part752) = true := by rfl

def kid11_part753 : Audit := .cycle 15 1 false (-1)
theorem kid11_part753_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part753) = true := by rfl

def kid11_part754 : Audit := .cycle 16 1 false (0)
theorem kid11_part754_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part754) = true := by rfl

def kid11_part755 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 51 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (3),
.cycle 21 1 false (7),
.cycle 28 1 false (10),
.last 18 (2,true),
.cycle 28 1 false (10),
.cycle 28 1 false (10),
.cycle 21 1 false (7),
.cycle 22 10 true (4),
.last 19 (2,true),
.cycle 23 1 false (7),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 23 1 false (7),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 5 67 true (0),
.cycle 6 67 true (0),
.cycle 6 18 true (0)
])
theorem kid11_part755_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part755) = true := by rfl

def kid11_part756 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 38 29 true (2),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 18 1 false (2),
.cycle 0 20 true (0),
.cycle 21 1 false (7),
.last 17 (2,true),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 21 1 false (7),
.cycle 21 12 true (3),
.last 18 (2,true),
.cycle 0 24 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (1),
.cycle 25 1 false (7),
.cycle 0 20 true (0),
.cycle 17 8 true (3),
.last 17 (2,true),
.cycle 5 12 true (0),
.cycle 22 21 true (2),
.cycle 19 6 true (5)
])
theorem kid11_part756_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part756) = true := by rfl

def kid11_part757 : Audit := .split 15 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 16, 128, 256, 32768, 2, 256, 65536, 128, 256, 8, 32, 256, 16, 262144],[2, 32, 256, 1, 4, 262144, 8192, 131072, 256, 4096, 16384, 262144, 2, 32, 256, 1, 4, 262144, 262144],278540⟩,
.last 21 (5,true),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.last 18 (5,true),
.last 17 (5,true),
.cycle 21 1 false (7),
.last 19 (5,true),
.cycle 20 1 false (6),
.last 16 (5,true),
.last 18 (5,true),
.last 19 (5,true),
.last 20 (5,true),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 31 1 false (7),
.last 18 (5,true),
.last 17 (5,true),
.cycle 2 18 true (0),
.last 19 (5,true),
.cycle 18 3 true (4),
.last 16 (5,true)
])
theorem kid11_part757_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part757) = true := by rfl

def kid11_part758 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 20 1 false (4),
.cycle 28 1 false (10),
.cycle 21 1 false (7),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 20 1 false (6),
.cycle 21 1 false (7),
.cycle 17 28 true (3),
.last 20 (2,true),
.cycle 30 1 false (10),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 0 22 true (0),
.cycle 0 51 true (0),
.cycle 29 1 false (9),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 26 1 false (8),
.cycle 18 31 true (4)
])
theorem kid11_part758_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part758) = true := by rfl

def kid11_part759 : Audit := .cycle 20 1 false (6)
theorem kid11_part759_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part759) = true := by rfl

def kid11_part760 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 69 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 17 1 false (1),
.cycle 28 1 false (10),
.cycle 28 1 false (10),
.last 16 (2,true),
.cycle 20 1 false (6),
.cycle 20 1 false (6),
.cycle 21 1 false (7),
.cycle 21 14 true (2),
.last 17 (2,true),
.cycle 32 1 false (10),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.cycle 31 1 false (7),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 16 (2,true),
.cycle 0 52 true (0),
.cycle 18 3 true (4),
.cycle 18 6 true (4)
])
theorem kid11_part760_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part760) = true := by rfl

def kid11_part761 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 75 true (-1),
.cycle 26 1 false (2),
.last 22 (2,true),
.cycle 13 5 false (1),
.cycle 12 7 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 35, 35, 16, 64],[2, 32, 64, 1, 32, 1, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 18 (2,true),
.cycle 37 1 false (7),
.cycle 18 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 22 16 true (2),
.last 19 (2,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 35, 35, 16, 128, 256, 8, 2, 1, 16, 4096],[2, 32, 4096, 1, 32, 1, 2, 32, 4096, 1, 32, 4096, 4096],4096⟩,
.cycle 23 1 false (1),
.cycle 13 5 false (1),
.cycle 26 22 true (2),
.cycle 16 57 true (0),
.cycle 1 21 true (-1),
.last 18 (2,true),
.cycle 0 56 true (-1),
.cycle 24 5 true (4),
.cycle 20 8 true (4)
])
theorem kid11_part761_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part761) = true := by rfl

def kid11_part762 : Audit := .split 16 (2,true) (byMove [
.cycle 41 1 false (9),
.cycle 44 1 false (6),
.cycle 19 1 false (-1),
.last 20 (5,true),
.cycle 14 3 false (0),
.last 17 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.last 34 (5,true),
.last 20 (5,true),
.last 36 (5,true),
.last 17 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.last 22 (5,true),
.last 20 (5,true),
.cycle 14 3 false (0),
.last 17 (5,true),
.last 19 (5,true),
.last 18 (5,true),
.last 36 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 17 (5,true)
])
theorem kid11_part762_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part762) = true := by rfl

def kid11_part763 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 55 true (-1),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (3),
.cycle 23 1 false (7),
.cycle 30 1 false (10),
.last 20 (2,true),
.cycle 30 1 false (10),
.cycle 32 1 false (10),
.cycle 23 1 false (7),
.last 33 (2,true),
.last 21 (2,true),
.cycle 25 1 false (7),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 27 1 false (7),
.last 72 (2,true),
.cycle 1 21 true (-1),
.last 20 (2,true),
.cycle 5 73 true (-1),
.last 21 (2,true),
.last 26 (2,true)
])
theorem kid11_part763_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part763) = true := by rfl

def kid11_part764 : Audit := .cycle 15 1 false (-1)
theorem kid11_part764_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part764) = true := by rfl

def kid11_part765 : Audit := .cycle 15 1 false (-1)
theorem kid11_part765_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part765) = true := by rfl

def kid11_part766 : Audit := .cycle 14 2 true (-1)
theorem kid11_part766_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part766) = true := by rfl

def kid11_part767 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 51 true (0),
.cycle 27 1 false (3),
.cycle 0 69 true (0),
.cycle 0 69 true (0),
.cycle 11 8 true (0),
.cycle 0 69 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 1, 2, 64],64⟩,
.last 18 (2,true),
.cycle 0 75 true (0),
.cycle 0 51 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 1, 32, 64],64⟩,
.cycle 22 10 true (4),
.last 19 (2,true),
.cycle 0 83 true (0),
.cycle 24 1 false (2),
.cycle 12 6 true (0),
.cycle 0 59 true (0),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 5 67 true (0),
.cycle 0 51 true (0),
.cycle 18 16 true (4)
])
theorem kid11_part767_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part767) = true := by rfl

def kid11_part768 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 38 29 true (2),
.cycle 25 1 false (3),
.last 21 (2,true),
.cycle 1 38 true (0),
.cycle 12 6 true (0),
.cycle 0 20 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 2, 2, 64],64⟩,
.last 17 (2,true),
.cycle 0 36 true (0),
.cycle 1 26 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 21 12 true (3),
.last 18 (2,true),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 13 4 true (0),
.cycle 18 10 true (2),
.cycle 0 20 true (0),
.cycle 17 8 true (3),
.last 17 (2,true),
.cycle 5 12 true (0),
.cycle 1 30 true (0),
.cycle 19 6 true (5)
])
theorem kid11_part768_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part768) = true := by rfl

def kid11_part769 : Audit := .split 15 (2,true) (byMove [
.cycle 37 1 false (9),
.cycle 26 1 false (6),
.cycle 18 1 false (0),
.last 19 (5,true),
.last 21 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 31 (5,true),
.last 19 (5,true),
.cycle 22 20 true (4),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 21 (5,true),
.last 19 (5,true),
.cycle 14 2 true (0),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.cycle 2 18 true (0),
.last 19 (5,true),
.cycle 18 3 true (4),
.last 16 (5,true)
])
theorem kid11_part769_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part769) = true := by rfl

def kid11_part770 : Audit := .split 18 (5,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 26 1 false (2),
.cycle 0 78 true (0),
.cycle 10 10 true (0),
.cycle 0 49 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 64, 1, 8, 2, 64],64⟩,
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 54 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 16, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 5 24 true (0),
.last 20 (2,true),
.cycle 0 57 true (0),
.cycle 26 1 false (2),
.cycle 11 8 true (0),
.cycle 0 22 true (0),
.cycle 0 51 true (0),
.cycle 5 20 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 23 true (4),
.cycle 18 29 true (4)
])
theorem kid11_part770_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part770) = true := by rfl

def kid11_part771 : Audit := .cycle 18 3 true (4)
theorem kid11_part771_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part771) = true := by rfl

def kid11_part772 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 26 1 false (6),
.last 16 (2,true),
.last 24 (2,true),
.cycle 24 8 true (4),
.cycle 18 1 false (0),
.cycle 0 49 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 16, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 16 (2,true),
.cycle 34 1 false (8),
.cycle 20 6 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 16, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 23 14 true (3),
.last 19 (2,true),
.last 16 (2,true),
.cycle 20 1 false (2),
.cycle 14 2 true (0),
.cycle 14 4 true (-1),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 16 (2,true),
.cycle 0 52 true (0),
.cycle 18 3 true (4),
.cycle 18 6 true (4)
])
theorem kid11_part772_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part772) = true := by rfl

def kid11_part748 : Audit := .split 14 (4,true) (byMove [(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759),(kid11_part760),(kid11_part761),(kid11_part762),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767),(kid11_part768),(kid11_part769),(kid11_part770),(kid11_part771),(kid11_part772)])

theorem kid11_part748_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part748) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 14 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part749),(kid11_part750),(kid11_part751),(kid11_part752),(kid11_part753),(kid11_part754),(kid11_part755),(kid11_part756),(kid11_part757),(kid11_part758),(kid11_part759),(kid11_part760),(kid11_part761),(kid11_part762),(kid11_part763),(kid11_part764),(kid11_part765),(kid11_part766),(kid11_part767),(kid11_part768),(kid11_part769),(kid11_part770),(kid11_part771),(kid11_part772)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part749_checked

  · exact kid11_part755_checked

  · exact kid11_part761_checked

  · exact kid11_part767_checked

  · exact kid11_part750_checked

  · exact kid11_part756_checked

  · exact kid11_part762_checked

  · exact kid11_part768_checked

  · exact kid11_part751_checked

  · exact kid11_part757_checked

  · exact kid11_part763_checked

  · exact kid11_part769_checked

  · exact kid11_part752_checked

  · exact kid11_part758_checked

  · exact kid11_part764_checked

  · exact kid11_part770_checked

  · exact kid11_part753_checked

  · exact kid11_part759_checked

  · exact kid11_part765_checked

  · exact kid11_part771_checked

  · exact kid11_part754_checked

  · exact kid11_part760_checked

  · exact kid11_part766_checked

  · exact kid11_part772_checked

def kid11_part774 : Audit := .cycle 0 12 true (0)
theorem kid11_part774_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part774) = true := by rfl

def kid11_part775 : Audit := .cycle 1 11 true (1)
theorem kid11_part775_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part775) = true := by rfl

def kid11_part776 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 0 59 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 26 1 false (2),
.cycle 27 1 false (3),
.cycle 29 1 false (7),
.cycle 36 1 false (10),
.last 22 (2,true),
.cycle 36 1 false (10),
.cycle 24 1 false (4),
.cycle 29 1 false (7),
.cycle 26 14 true (4),
.last 23 (2,true),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.cycle 26 1 false (2),
.cycle 25 1 false (3),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 22 (2,true),
.cycle 5 79 true (0),
.last 23 (2,true),
.cycle 2 26 true (0)
])
theorem kid11_part776_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part776) = true := by rfl

def kid11_part777 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 21 1 false (3),
.cycle 25 1 false (5),
.cycle 3 26 true (0),
.last 21 (2,true),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 0 22 true (0),
.cycle 19 31 true (3)
])
theorem kid11_part777_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part777) = true := by rfl

def kid11_part778 : Audit := .split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 0 26 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 23 3 false (-1),
.cycle 24 3 false (0),
.cycle 32 3 false (6),
.cycle 25 3 false (3),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 23 3 false (1),
.cycle 25 3 false (3),
.cycle 15 28 true (-1),
.last 24 (2,true),
.cycle 34 3 false (6),
.cycle 23 1 false (-1),
.cycle 23 3 false (-1),
.cycle 23 3 false (0),
.cycle 9 26 true (0),
.cycle 15 10 true (0),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 24 3 false (0),
.cycle 18 7 true (0)
])
theorem kid11_part778_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part778) = true := by rfl

def kid11_part779 : Audit := .cycle 8 4 true (4)
theorem kid11_part779_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part779) = true := by rfl

def kid11_part780 : Audit := .cycle 0 12 true (0)
theorem kid11_part780_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part780) = true := by rfl

def kid11_part781 : Audit := .cycle 1 11 true (1)
theorem kid11_part781_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part781) = true := by rfl

def kid11_part782 : Audit := .split 23 (5,true) (byMove [
.last 26 (2,true),
.cycle 0 93 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 36 1 false (8),
.last 28 (2,true),
.cycle 40 1 false (14),
.cycle 40 1 false (14),
.last 24 (2,true),
.cycle 28 1 false (8),
.last 25 (2,true),
.cycle 33 1 false (11),
.cycle 28 22 true (4),
.last 25 (2,true),
.cycle 44 1 false (14),
.cycle 24 1 false (2),
.last 27 (2,true),
.last 26 (2,true),
.cycle 0 75 true (0),
.cycle 1 27 true (0),
.last 24 (2,true),
.cycle 0 68 true (0),
.last 25 (2,true),
.cycle 26 14 true (6)
])
theorem kid11_part782_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part782) = true := by rfl

def kid11_part783 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 48 34 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 25 1 false (3),
.cycle 33 1 false (9),
.cycle 0 25 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 29 1 false (9),
.cycle 36 1 false (12),
.cycle 29 1 false (9),
.cycle 26 17 true (4),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 0 33 true (0),
.cycle 31 1 false (9),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.cycle 0 85 true (0),
.cycle 24 11 true (6)
])
theorem kid11_part783_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part783) = true := by rfl

def kid11_part784 : Audit := .cycle 9 3 true (4)
theorem kid11_part784_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part784) = true := by rfl

def kid11_part785 : Audit := .cycle 8 4 true (4)
theorem kid11_part785_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part785) = true := by rfl

def kid11_part786 : Audit := .cycle 7 6 true (3)
theorem kid11_part786_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part786) = true := by rfl

def kid11_part787 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 23 (5,true),
.cycle 0 15 true (0),
.last 25 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 25 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.last 15 (5,true),
.cycle 8 6 true (4)
])
theorem kid11_part787_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part787) = true := by rfl

def kid11_part788 : Audit := .cycle 0 14 true (0)
theorem kid11_part788_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part788) = true := by rfl

def kid11_part789 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 24 1 false (2),
.cycle 26 1 false (6),
.cycle 33 1 false (9),
.last 20 (2,true),
.cycle 33 1 false (9),
.cycle 21 1 false (3),
.cycle 26 1 false (6),
.cycle 24 12 true (4),
.last 21 (2,true),
.cycle 28 1 false (6),
.cycle 20 1 false (2),
.cycle 23 1 false (1),
.cycle 22 1 false (2),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 5 73 true (0),
.cycle 28 1 false (6),
.cycle 4 22 true (0)
])
theorem kid11_part789_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part789) = true := by rfl

def kid11_part790 : Audit := .split 22 (5,true) (byMove [
.last 25 (2,true),
.cycle 0 32 true (-1),
.cycle 24 1 false (0),
.cycle 23 1 false (-1),
.cycle 23 3 false (-1),
.cycle 24 3 false (0),
.cycle 29 3 false (7),
.cycle 29 3 false (7),
.last 23 (2,true),
.cycle 0 28 true (0),
.cycle 23 3 false (1),
.cycle 29 3 false (7),
.cycle 30 20 true (2),
.last 24 (2,true),
.cycle 33 3 false (7),
.cycle 23 1 false (-1),
.cycle 23 3 false (-1),
.cycle 23 3 false (0),
.cycle 0 75 true (0),
.cycle 24 12 true (2),
.last 23 (2,true),
.cycle 0 28 true (0),
.cycle 24 3 false (0),
.cycle 25 8 true (3)
])
theorem kid11_part790_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part790) = true := by rfl

def kid11_part791 : Audit := .cycle 10 2 true (4)
theorem kid11_part791_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part791) = true := by rfl

def kid11_part792 : Audit := .cycle 0 12 true (0)
theorem kid11_part792_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part792) = true := by rfl

def kid11_part793 : Audit := .cycle 1 11 true (1)
theorem kid11_part793_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part793) = true := by rfl

def kid11_part794 : Audit := .cycle 2 10 true (1)
theorem kid11_part794_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part794) = true := by rfl

def kid11_part795 : Audit := .cycle 1 14 true (1)
theorem kid11_part795_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part795) = true := by rfl

def kid11_part796 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 29 5 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4),
.cycle 7 11 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 22 1 false (2),
.cycle 16 5 true (4),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 3 true (5),
.cycle 8 7 true (4)
])
theorem kid11_part796_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part796) = true := by rfl

def kid11_part797 : Audit := .cycle 8 4 true (4)
theorem kid11_part797_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part797) = true := by rfl

def kid11_part773 : Audit := .split 11 (4,true) (byMove [(kid11_part774),(kid11_part775),(kid11_part776),(kid11_part777),(kid11_part778),(kid11_part779),(kid11_part780),(kid11_part781),(kid11_part782),(kid11_part783),(kid11_part784),(kid11_part785),(kid11_part786),(kid11_part787),(kid11_part788),(kid11_part789),(kid11_part790),(kid11_part791),(kid11_part792),(kid11_part793),(kid11_part794),(kid11_part795),(kid11_part796),(kid11_part797)])

theorem kid11_part773_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part773) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (4,true) (some mv)) (byMove [(kid11_part774),(kid11_part775),(kid11_part776),(kid11_part777),(kid11_part778),(kid11_part779),(kid11_part780),(kid11_part781),(kid11_part782),(kid11_part783),(kid11_part784),(kid11_part785),(kid11_part786),(kid11_part787),(kid11_part788),(kid11_part789),(kid11_part790),(kid11_part791),(kid11_part792),(kid11_part793),(kid11_part794),(kid11_part795),(kid11_part796),(kid11_part797)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part774_checked

  · exact kid11_part780_checked

  · exact kid11_part786_checked

  · exact kid11_part792_checked

  · exact kid11_part775_checked

  · exact kid11_part781_checked

  · exact kid11_part787_checked

  · exact kid11_part793_checked

  · exact kid11_part776_checked

  · exact kid11_part782_checked

  · exact kid11_part788_checked

  · exact kid11_part794_checked

  · exact kid11_part777_checked

  · exact kid11_part783_checked

  · exact kid11_part789_checked

  · exact kid11_part795_checked

  · exact kid11_part778_checked

  · exact kid11_part784_checked

  · exact kid11_part790_checked

  · exact kid11_part796_checked

  · exact kid11_part779_checked

  · exact kid11_part785_checked

  · exact kid11_part791_checked

  · exact kid11_part797_checked

def kid11_part798 : Audit := .cycle 0 10 true (0)
theorem kid11_part798_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part798) = true := by rfl

def kid11_part799 : Audit := .cycle 1 9 true (1)
theorem kid11_part799_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part799) = true := by rfl

def kid11_part800 : Audit := .cycle 2 8 true (1)
theorem kid11_part800_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part800) = true := by rfl

def kid11_part801 : Audit := .cycle 1 12 true (1)
theorem kid11_part801_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part801) = true := by rfl

def kid11_part802 : Audit := .cycle 9 1 true (5)
theorem kid11_part802_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part802) = true := by rfl

def kid11_part803 : Audit := .cycle 8 2 true (4)
theorem kid11_part803_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part803) = true := by rfl

def kid11_part587 : Audit := .split 9 (4,false) (byMove [(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part615),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part669),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part722),(kid11_part723),(kid11_part748),(kid11_part773),(kid11_part798),(kid11_part799),(kid11_part800),(kid11_part801),(kid11_part802),(kid11_part803)])

theorem kid11_part587_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (kid11_part587) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part588),(kid11_part589),(kid11_part590),(kid11_part615),(kid11_part640),(kid11_part641),(kid11_part642),(kid11_part643),(kid11_part644),(kid11_part669),(kid11_part694),(kid11_part695),(kid11_part696),(kid11_part697),(kid11_part722),(kid11_part723),(kid11_part748),(kid11_part773),(kid11_part798),(kid11_part799),(kid11_part800),(kid11_part801),(kid11_part802),(kid11_part803)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part588_checked

  · exact kid11_part642_checked

  · exact kid11_part696_checked

  · exact kid11_part798_checked

  · exact kid11_part589_checked

  · exact kid11_part643_checked

  · exact kid11_part697_checked

  · exact kid11_part799_checked

  · exact kid11_part590_checked

  · exact kid11_part644_checked

  · exact kid11_part722_checked

  · exact kid11_part800_checked

  · exact kid11_part615_checked

  · exact kid11_part669_checked

  · exact kid11_part723_checked

  · exact kid11_part801_checked

  · exact kid11_part640_checked

  · exact kid11_part694_checked

  · exact kid11_part748_checked

  · exact kid11_part802_checked

  · exact kid11_part641_checked

  · exact kid11_part695_checked

  · exact kid11_part773_checked

  · exact kid11_part803_checked

def kid11_part804 : Audit := .cycle 8 1 true (4)
theorem kid11_part804_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨false,true,5⟩)) (kid11_part804) = true := by rfl

def kid11_part805 : Audit := .cycle 7 3 true (3)
theorem kid11_part805_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,0⟩)) (kid11_part805) = true := by rfl

def kid11_part807 : Audit := .cycle 1 11 true (1)
theorem kid11_part807_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part807) = true := by rfl

def kid11_part808 : Audit := .cycle 7 4 true (3)
theorem kid11_part808_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part808) = true := by rfl

def kid11_part809 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 32 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 33 1 false (3),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 0 21 true (0),
.cycle 33 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 true (2),
.cycle 26 1 false (2),
.cycle 29 1 false (1),
.cycle 25 1 false (1),
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 32 1 false (4),
.cycle 36 1 false (6),
.cycle 20 1 true (2),
.cycle 18 4 true (2)
]),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.split 20 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 33 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.cycle 26 1 false (2),
.cycle 0 21 true (0),
.cycle 33 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 true (4),
.cycle 26 1 false (4),
.cycle 29 1 false (3),
.cycle 25 1 false (3),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (4),
.cycle 26 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 32 1 false (6),
.cycle 36 1 false (8),
.cycle 20 1 true (4),
.cycle 18 4 true (2)
]),
.cycle 25 1 false (3),
.cycle 28 1 false (2),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.split 20 (4,false) (byMove [
.cycle 27 1 false (1),
.cycle 0 24 true (0),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 34 1 false (6),
.cycle 27 1 false (3),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 2 true (2),
.cycle 17 8 true (1),
.cycle 25 1 false (1),
.cycle 36 1 false (6),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 26 1 false (0),
.cycle 60 1 false (6),
.cycle 28 1 false (2),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 22 (4,true)
]),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.split 20 (4,false) (byMove [
.cycle 34 1 false (6),
.cycle 27 1 false (3),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 19 2 true (3),
.cycle 0 21 true (0),
.last 41 (4,true),
.cycle 12 9 true (0),
.cycle 31 1 false (5),
.cycle 20 1 true (4),
.cycle 27 1 false (3),
.cycle 28 1 false (4),
.cycle 18 3 true (2),
.cycle 23 1 false (3),
.cycle 35 1 false (7),
.last 21 (4,true),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.last 45 (4,true),
.cycle 20 1 true (4),
.cycle 18 4 true (2)
]),
.cycle 18 3 true (2)
])
theorem kid11_part809_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part809) = true := by rfl

def kid11_part810 : Audit := .cycle 0 12 true (0)
theorem kid11_part810_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part810) = true := by rfl

def kid11_part812 : Audit := .cycle 0 12 true (0)
theorem kid11_part812_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part812) = true := by rfl

def kid11_part813 : Audit := .cycle 1 11 true (1)
theorem kid11_part813_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part813) = true := by rfl

def kid11_part814 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 32 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.last 20 (4,false),
.cycle 25 1 false (3),
.last 27 (4,false),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.last 20 (4,false),
.cycle 18 3 true (2)
])
theorem kid11_part814_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part814) = true := by rfl

def kid11_part815 : Audit := .cycle 21 1 false (1)
theorem kid11_part815_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part815) = true := by rfl

def kid11_part816 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 12 1 true (2),
.cycle 22 5 false (0),
.cycle 19 8 false (1),
.cycle 16 4 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.last 15 (5,true)
])
theorem kid11_part816_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part816) = true := by rfl

def kid11_part817 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (4),
.cycle 24 4 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 24 4 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 17 4 false (1),
.cycle 12 7 false (2),
.cycle 17 4 false (0),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 4 false (3),
.cycle 27 4 false (5),
.last 17 (4,false),
.cycle 16 3 true (0)
])
theorem kid11_part817_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part817) = true := by rfl

def kid11_part818 : Audit := .cycle 0 12 true (0)
theorem kid11_part818_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part818) = true := by rfl

def kid11_part819 : Audit := .cycle 1 11 true (1)
theorem kid11_part819_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part819) = true := by rfl

def kid11_part820 : Audit := .split 21 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 0 59 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 27 1 false (3),
.cycle 29 1 false (7),
.cycle 36 1 false (10),
.last 23 (4,false),
.cycle 36 1 false (10),
.last 24 (4,false),
.cycle 29 1 false (7),
.cycle 26 14 true (4),
.cycle 40 1 false (10),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.last 22 (4,false),
.cycle 35 1 false (7),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.cycle 0 26 true (0),
.cycle 5 79 true (0),
.last 24 (4,false),
.cycle 23 3 true (5)
])
theorem kid11_part820_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part820) = true := by rfl

def kid11_part821 : Audit := .split 19 (5,true) (byMove [
.cycle 33 1 false (5),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 21 1 false (5),
.cycle 25 1 false (5),
.cycle 3 26 true (0),
.cycle 23 1 false (3),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 24 1 false (2),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.cycle 30 1 false (6),
.cycle 20 3 true (4)
])
theorem kid11_part821_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part821) = true := by rfl

def kid11_part822 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 17 1 false (1),
.last 25 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (5),
.last 25 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 15 (5,true)
])
theorem kid11_part822_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part822) = true := by rfl

def kid11_part823 : Audit := .cycle 8 4 true (3)
theorem kid11_part823_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part823) = true := by rfl

def kid11_part824 : Audit := .cycle 6 12 true (2)
theorem kid11_part824_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part824) = true := by rfl

def kid11_part825 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 28 3 false (3),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 21 3 false (0),
.cycle 0 20 true (0),
.cycle 28 3 false (5),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 21 3 false (2),
.cycle 15 8 true (0),
.cycle 20 3 false (1),
.cycle 0 22 true (0),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 21 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 27 3 false (4),
.cycle 31 3 false (6),
.last 20 (4,false),
.cycle 18 3 true (0)
])
theorem kid11_part825_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part825) = true := by rfl

def kid11_part826 : Audit := .cycle 0 14 true (0)
theorem kid11_part826_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part826) = true := by rfl

def kid11_part827 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 29 1 false (3),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 29 1 false (5),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.last 18 (4,false),
.cycle 22 1 false (2),
.cycle 37 1 false (5),
.cycle 21 1 false (1),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 22 1 false (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 28 1 false (4),
.cycle 32 1 false (6),
.last 18 (4,false),
.cycle 16 3 true (2)
])
theorem kid11_part827_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part827) = true := by rfl

def kid11_part828 : Audit := .split 12 (4,false) (byMove [
.cycle 17 6 false (1),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 11 2 true (2),
.last 13 (5,true),
.last 15 (5,true),
.cycle 16 4 false (0),
.cycle 1 15 true (1),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.cycle 17 3 false (1),
.last 13 (5,true)
])
theorem kid11_part828_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part828) = true := by rfl

def kid11_part829 : Audit := .split 16 (5,true) (byMove [
.cycle 13 5 false (2),
.cycle 0 30 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 18 4 false (3),
.cycle 18 4 false (2),
.last 18 (4,false),
.cycle 0 26 true (0),
.cycle 17 4 false (1),
.cycle 18 4 false (2),
.cycle 12 20 true (-1),
.cycle 17 4 false (0),
.cycle 20 4 false (3),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 16 26 true (0),
.cycle 12 6 true (0),
.cycle 17 4 false (1),
.cycle 0 26 true (0),
.cycle 15 2 true (0),
.cycle 21 3 true (3)
])
theorem kid11_part829_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part829) = true := by rfl

def kid11_part830 : Audit := .cycle 0 12 true (0)
theorem kid11_part830_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part830) = true := by rfl

def kid11_part831 : Audit := .cycle 1 11 true (1)
theorem kid11_part831_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part831) = true := by rfl

def kid11_part832 : Audit := .cycle 2 10 true (1)
theorem kid11_part832_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part832) = true := by rfl

def kid11_part833 : Audit := .cycle 1 14 true (1)
theorem kid11_part833_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part833) = true := by rfl

def kid11_part834 : Audit := .split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 29 1 false (1),
.cycle 0 14 true (0),
.cycle 11 2 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 33 (5,true),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.last 15 (5,true)
])
theorem kid11_part834_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part834) = true := by rfl

def kid11_part835 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 15 (4,false),
.cycle 29 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 27 (4,false),
.cycle 40 1 false (10),
.last 15 (4,false),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 22 1 false (2),
.last 15 (4,false),
.cycle 29 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 12 3 true (3)
])
theorem kid11_part835_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part835) = true := by rfl

def kid11_part811 : Audit := .split 11 (4,true) (byMove [(kid11_part812),(kid11_part813),(kid11_part814),(kid11_part815),(kid11_part816),(kid11_part817),(kid11_part818),(kid11_part819),(kid11_part820),(kid11_part821),(kid11_part822),(kid11_part823),(kid11_part824),(kid11_part825),(kid11_part826),(kid11_part827),(kid11_part828),(kid11_part829),(kid11_part830),(kid11_part831),(kid11_part832),(kid11_part833),(kid11_part834),(kid11_part835)])

theorem kid11_part811_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part811) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part812),(kid11_part813),(kid11_part814),(kid11_part815),(kid11_part816),(kid11_part817),(kid11_part818),(kid11_part819),(kid11_part820),(kid11_part821),(kid11_part822),(kid11_part823),(kid11_part824),(kid11_part825),(kid11_part826),(kid11_part827),(kid11_part828),(kid11_part829),(kid11_part830),(kid11_part831),(kid11_part832),(kid11_part833),(kid11_part834),(kid11_part835)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part812_checked

  · exact kid11_part818_checked

  · exact kid11_part824_checked

  · exact kid11_part830_checked

  · exact kid11_part813_checked

  · exact kid11_part819_checked

  · exact kid11_part825_checked

  · exact kid11_part831_checked

  · exact kid11_part814_checked

  · exact kid11_part820_checked

  · exact kid11_part826_checked

  · exact kid11_part832_checked

  · exact kid11_part815_checked

  · exact kid11_part821_checked

  · exact kid11_part827_checked

  · exact kid11_part833_checked

  · exact kid11_part816_checked

  · exact kid11_part822_checked

  · exact kid11_part828_checked

  · exact kid11_part834_checked

  · exact kid11_part817_checked

  · exact kid11_part823_checked

  · exact kid11_part829_checked

  · exact kid11_part835_checked

def kid11_part836 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 28 1 false (2),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 25 true (0),
.cycle 21 1 false (3),
.cycle 12 1 true (2),
.last 22 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (2),
.cycle 11 4 true (2)
]),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 28 1 false (4),
.cycle 0 21 true (0),
.split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 22 (4,true),
.cycle 21 1 false (3),
.last 16 (4,true),
.cycle 25 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (4,true),
.last 22 (4,true),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.last 20 (4,true),
.last 16 (4,true),
.last 26 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3)
]),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 18 1 false (2),
.split 12 (4,false) (byMove [
.last 17 (4,true),
.cycle 0 16 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (0),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (2),
.last 18 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (2),
.cycle 11 8 true (1),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 19 1 false (1),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 1 13 true (1),
.last 18 (4,true),
.last 18 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.split 12 (4,false) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 11 9 true (3),
.cycle 3 10 true (1),
.cycle 12 1 true (4),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 11 3 true (3),
.cycle 19 6 false (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 1 true (4),
.cycle 11 4 true (3)
]),
.cycle 11 3 true (3)
])
theorem kid11_part836_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part836) = true := by rfl

def kid11_part837 : Audit := .cycle 0 11 true (0)
theorem kid11_part837_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part837) = true := by rfl

def kid11_part838 : Audit := .cycle 1 10 true (1)
theorem kid11_part838_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part838) = true := by rfl

def kid11_part839 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.last 24 (4,true),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 40 1 false (8),
.cycle 31 1 false (3),
.cycle 19 1 true (5),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 29 1 false (1),
.last 24 (4,true),
.cycle 0 40 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (5),
.cycle 17 4 true (5)
]),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 38 1 false (10),
.cycle 34 1 false (8),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (4,true),
.last 30 (4,true),
.last 26 (4,true),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 34 (4,true),
.last 32 (4,true),
.cycle 19 1 true (7),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.last 30 (4,true),
.last 26 (4,true),
.last 33 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 17 4 true (5)
]),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 28 1 false (2),
.split 19 (4,false) (byMove [
.cycle 9 12 true (3),
.cycle 0 23 true (0),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.last 24 (4,true),
.cycle 0 25 true (0),
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 42 1 false (10),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 18 2 true (5),
.cycle 16 8 true (4),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 2, 2, 64],[0, 2, 8, 0, 64, 16, 64],64⟩,
.cycle 1 22 true (1),
.cycle 29 1 false (1),
.last 24 (4,true),
.far true 2 ⟨0,[0, 1, 0, 1],[1024, 2048, 512, 512, 2048, 128, 1024, 0, 128, 512, 2048, 128, 4096],[128, 0, 512, 2048, 4096, 1024, 128, 2048, 512, 0, 4096, 1024, 4096],4096⟩,
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
]),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.split 19 (4,false) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 34 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 18 2 true (6),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 11 9 true (3),
.cycle 3 17 true (1),
.cycle 19 1 true (7),
.cycle 8 12 true (3),
.cycle 6 14 true (2),
.cycle 17 3 true (5),
.last 36 (4,true),
.cycle 1 21 true (1),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 19 1 true (7),
.cycle 17 4 true (5)
]),
.cycle 17 3 true (5)
])
theorem kid11_part839_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part839) = true := by rfl

def kid11_part840 : Audit := .cycle 3 8 true (1)
theorem kid11_part840_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part840) = true := by rfl

def kid11_part842 : Audit := .cycle 0 12 true (0)
theorem kid11_part842_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part842) = true := by rfl

def kid11_part843 : Audit := .cycle 1 11 true (1)
theorem kid11_part843_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part843) = true := by rfl

def kid11_part844 : Audit := .cycle 2 10 true (1)
theorem kid11_part844_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part844) = true := by rfl

def kid11_part845 : Audit := .cycle 1 14 true (1)
theorem kid11_part845_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part845) = true := by rfl

def kid11_part846 : Audit := .split 13 (4,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 19 1 false (1),
.cycle 8 6 true (3),
.cycle 6 16 true (2),
.last 25 (5,true),
.cycle 0 16 true (0),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 2 true (3),
.last 16 (5,true)
])
theorem kid11_part846_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part846) = true := by rfl

def kid11_part847 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 24 8 false (0),
.cycle 29 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 27 (4,true),
.cycle 40 1 false (10),
.cycle 8 8 true (3),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 22 1 false (2),
.cycle 24 8 false (0),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 2 true (4),
.cycle 12 3 true (3)
])
theorem kid11_part847_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part847) = true := by rfl

def kid11_part848 : Audit := .cycle 0 12 true (0)
theorem kid11_part848_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part848) = true := by rfl

def kid11_part849 : Audit := .cycle 1 11 true (1)
theorem kid11_part849_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part849) = true := by rfl

def kid11_part850 : Audit := .split 20 (5,true) (byMove [
.cycle 9 13 true (3),
.cycle 0 24 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 24 true (0),
.last 43 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.last 39 (4,true),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 8 14 true (3),
.cycle 7 18 true (3),
.last 23 (4,true),
.cycle 1 23 true (1),
.cycle 30 1 false (2),
.last 23 (4,true),
.last 24 (4,true),
.cycle 1 21 true (1),
.cycle 7 14 true (3),
.cycle 10 11 true (3),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 21 3 true (7)
])
theorem kid11_part850_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part850) = true := by rfl

def kid11_part851 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 31 1 false (3),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 33 (4,true),
.cycle 34 1 false (8),
.last 32 (4,true),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 9 10 true (3),
.cycle 0 21 true (0),
.cycle 28 1 false (2),
.cycle 0 21 true (0),
.last 22 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 3 17 true (1),
.cycle 17 3 true (5)
])
theorem kid11_part851_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part851) = true := by rfl

def kid11_part852 : Audit := .cycle 11 1 true (5)
theorem kid11_part852_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part852) = true := by rfl

def kid11_part853 : Audit := .cycle 8 4 true (3)
theorem kid11_part853_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part853) = true := by rfl

def kid11_part854 : Audit := .cycle 7 6 true (3)
theorem kid11_part854_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part854) = true := by rfl

def kid11_part855 : Audit := .cycle 9 3 true (3)
theorem kid11_part855_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part855) = true := by rfl

def kid11_part856 : Audit := .cycle 0 14 true (0)
theorem kid11_part856_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part856) = true := by rfl

def kid11_part857 : Audit := .cycle 4 8 true (1)
theorem kid11_part857_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part857) = true := by rfl

def kid11_part858 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.last 21 (5,true),
.cycle 31 1 false (3),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.last 27 (5,true),
.cycle 1 15 true (1),
.cycle 29 1 false (7),
.last 14 (5,true),
.last 16 (5,true),
.last 26 (5,true),
.cycle 5 10 true (1),
.last 19 (5,true),
.cycle 17 1 false (-1),
.last 20 (5,true),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 2 14 true (1),
.cycle 1 15 true (1),
.cycle 14 3 true (4),
.last 14 (5,true)
])
theorem kid11_part858_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part858) = true := by rfl

def kid11_part859 : Audit := .split 14 (5,true) (byMove [
.cycle 9 7 true (3),
.cycle 0 18 true (0),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 19 (4,true),
.cycle 29 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 20 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 8 8 true (3),
.cycle 7 12 true (3),
.last 17 (4,true),
.cycle 1 17 true (1),
.cycle 22 1 false (2),
.last 19 (4,true),
.last 18 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (3),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 15 3 true (5)
])
theorem kid11_part859_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part859) = true := by rfl

def kid11_part860 : Audit := .cycle 0 12 true (0)
theorem kid11_part860_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part860) = true := by rfl

def kid11_part861 : Audit := .cycle 1 11 true (1)
theorem kid11_part861_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part861) = true := by rfl

def kid11_part862 : Audit := .cycle 2 10 true (1)
theorem kid11_part862_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part862) = true := by rfl

def kid11_part863 : Audit := .cycle 1 14 true (1)
theorem kid11_part863_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part863) = true := by rfl

def kid11_part864 : Audit := .cycle 11 1 true (5)
theorem kid11_part864_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part864) = true := by rfl

def kid11_part865 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 35 1 false (3),
.cycle 3 12 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 26 (4,true),
.cycle 0 24 true (0),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 30 1 false (2),
.last 17 (4,true),
.last 18 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid11_part865_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part865) = true := by rfl

def kid11_part841 : Audit := .split 11 (4,false) (byMove [(kid11_part842),(kid11_part843),(kid11_part844),(kid11_part845),(kid11_part846),(kid11_part847),(kid11_part848),(kid11_part849),(kid11_part850),(kid11_part851),(kid11_part852),(kid11_part853),(kid11_part854),(kid11_part855),(kid11_part856),(kid11_part857),(kid11_part858),(kid11_part859),(kid11_part860),(kid11_part861),(kid11_part862),(kid11_part863),(kid11_part864),(kid11_part865)])

theorem kid11_part841_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part841) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part842),(kid11_part843),(kid11_part844),(kid11_part845),(kid11_part846),(kid11_part847),(kid11_part848),(kid11_part849),(kid11_part850),(kid11_part851),(kid11_part852),(kid11_part853),(kid11_part854),(kid11_part855),(kid11_part856),(kid11_part857),(kid11_part858),(kid11_part859),(kid11_part860),(kid11_part861),(kid11_part862),(kid11_part863),(kid11_part864),(kid11_part865)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part842_checked

  · exact kid11_part848_checked

  · exact kid11_part854_checked

  · exact kid11_part860_checked

  · exact kid11_part843_checked

  · exact kid11_part849_checked

  · exact kid11_part855_checked

  · exact kid11_part861_checked

  · exact kid11_part844_checked

  · exact kid11_part850_checked

  · exact kid11_part856_checked

  · exact kid11_part862_checked

  · exact kid11_part845_checked

  · exact kid11_part851_checked

  · exact kid11_part857_checked

  · exact kid11_part863_checked

  · exact kid11_part846_checked

  · exact kid11_part852_checked

  · exact kid11_part858_checked

  · exact kid11_part864_checked

  · exact kid11_part847_checked

  · exact kid11_part853_checked

  · exact kid11_part859_checked

  · exact kid11_part865_checked

def kid11_part866 : Audit := .cycle 8 3 true (3)
theorem kid11_part866_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part866) = true := by rfl

def kid11_part867 : Audit := .cycle 6 5 true (2)
theorem kid11_part867_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part867) = true := by rfl

def kid11_part868 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 20 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 42 1 false (10),
.cycle 23 1 false (3),
.cycle 13 1 true (3),
.cycle 8 6 true (3),
.cycle 6 16 true (2),
.cycle 24 5 false (1),
.cycle 0 16 true (0),
.cycle 21 1 false (1),
.last 16 (4,true),
.cycle 20 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (3),
.cycle 11 4 true (3)
]),
.cycle 24 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 40 1 false (8),
.cycle 36 1 false (10),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 24 (4,true),
.last 22 (4,true),
.last 18 (4,true),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 26 (4,true),
.last 24 (4,true),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.last 22 (4,true),
.last 18 (4,true),
.last 19 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 4 true (3)
]),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.split 13 (4,false) (byMove [
.cycle 9 12 true (2),
.cycle 0 17 true (0),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.last 16 (4,true),
.cycle 20 6 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (3),
.cycle 11 8 true (2),
.cycle 24 5 false (1),
.cycle 1 16 true (1),
.cycle 21 1 false (1),
.last 16 (4,true),
.cycle 20 6 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 15 (4,true)
]),
.cycle 24 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 9 6 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 12 2 true (4),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 9 true (3),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.cycle 11 3 true (3),
.last 19 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.cycle 11 4 true (3)
]),
.cycle 11 3 true (3)
])
theorem kid11_part868_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part868) = true := by rfl

def kid11_part869 : Audit := .cycle 1 14 true (1)
theorem kid11_part869_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part869) = true := by rfl

def kid11_part870 : Audit := .cycle 1 12 true (1)
theorem kid11_part870_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part870) = true := by rfl

def kid11_part872 : Audit := .cycle 9 8 true (2)
theorem kid11_part872_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part872) = true := by rfl

def kid11_part873 : Audit := .cycle 0 15 true (0)
theorem kid11_part873_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part873) = true := by rfl

def kid11_part874 : Audit := .split 19 (5,true) (byMove [
.last 25 (4,false),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 33 1 false (7),
.cycle 26 1 false (4),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 26 1 false (4),
.cycle 32 1 false (2),
.cycle 24 1 false (2),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.last 20 (4,false),
.cycle 25 1 false (1),
.cycle 0 54 true (0),
.last 26 (4,false),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.last 22 (4,false),
.cycle 20 3 true (4)
])
theorem kid11_part874_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part874) = true := by rfl

def kid11_part875 : Audit := .cycle 21 1 false (1)
theorem kid11_part875_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part875) = true := by rfl

def kid11_part876 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (0),
.last 20 (5,true),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 16 6 true (2),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 15 1 true (3),
.cycle 22 5 false (0),
.cycle 19 8 false (1),
.cycle 16 4 false (0),
.cycle 18 8 true (1),
.cycle 22 1 false (0),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 0 26 true (0),
.cycle 0 21 true (0),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 17 1 true (1),
.last 15 (5,true)
])
theorem kid11_part876_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part876) = true := by rfl

def kid11_part877 : Audit := .split 16 (5,true) (byMove [
.cycle 0 32 true (-1),
.cycle 40 4 false (6),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 0 27 true (0),
.cycle 17 4 false (2),
.cycle 0 28 true (0),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 17 4 false (1),
.cycle 12 7 false (2),
.cycle 17 4 false (0),
.cycle 0 33 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 0 27 true (0),
.cycle 13 4 true (0),
.cycle 0 28 true (0),
.cycle 21 4 false (3),
.last 17 (4,false),
.cycle 24 3 true (4)
])
theorem kid11_part877_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part877) = true := by rfl

def kid11_part878 : Audit := .cycle 1 12 true (1)
theorem kid11_part878_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part878) = true := by rfl

def kid11_part879 : Audit := .cycle 7 5 true (3)
theorem kid11_part879_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part879) = true := by rfl

def kid11_part880 : Audit := .split 13 (4,false) (byMove [
.cycle 9 12 true (2),
.cycle 0 17 true (0),
.last 21 (5,true),
.cycle 25 1 false (1),
.cycle 18 1 false (2),
.last 20 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 25 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 25 (5,true),
.cycle 1 16 true (1),
.last 19 (5,true),
.cycle 18 1 false (0),
.last 20 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.last 22 (5,true),
.last 14 (5,true)
])
theorem kid11_part880_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part880) = true := by rfl

def kid11_part881 : Audit := .cycle 0 13 true (0)
theorem kid11_part881_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part881) = true := by rfl

def kid11_part882 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 19 1 false (1),
.cycle 8 6 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 25 (5,true),
.last 23 (5,true),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.last 21 (5,true),
.cycle 24 1 false (6),
.cycle 11 7 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
])
theorem kid11_part882_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part882) = true := by rfl

def kid11_part883 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.last 13 (4,false),
.cycle 25 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 25 (4,false),
.cycle 36 1 false (10),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.last 13 (4,false),
.cycle 25 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 3 true (4)
])
theorem kid11_part883_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part883) = true := by rfl

def kid11_part884 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 23 10 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,false),
.cycle 49 1 false (9),
.last 15 (4,false),
.cycle 8 7 true (2),
.cycle 13 9 true (3),
.cycle 9 12 true (2),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 15 (4,false),
.cycle 23 10 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 15 (4,false),
.cycle 13 3 true (3)
])
theorem kid11_part884_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part884) = true := by rfl

def kid11_part885 : Audit := .split 19 (5,true) (byMove [
.cycle 15 6 true (0),
.cycle 46 38 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 21 3 false (0),
.cycle 0 23 true (0),
.cycle 24 3 false (5),
.last 21 (4,false),
.cycle 24 3 false (5),
.cycle 20 3 false (2),
.cycle 24 3 false (5),
.cycle 24 11 true (2),
.cycle 20 3 false (1),
.cycle 0 27 true (0),
.cycle 20 1 false (0),
.last 20 (4,false),
.cycle 21 3 false (0),
.cycle 0 23 true (0),
.cycle 20 7 true (2),
.cycle 20 3 false (2),
.cycle 5 15 true (0),
.last 29 (4,false),
.cycle 22 3 true (4)
])
theorem kid11_part885_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part885) = true := by rfl

def kid11_part886 : Audit := .cycle 1 14 true (1)
theorem kid11_part886_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part886) = true := by rfl

def kid11_part887 : Audit := .split 17 (5,true) (byMove [
.cycle 29 1 false (3),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 22 1 false (0),
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.last 19 (4,false),
.cycle 0 19 true (0),
.cycle 19 1 false (3),
.cycle 23 1 false (3),
.cycle 5 22 true (0),
.cycle 21 1 false (1),
.cycle 32 1 false (6),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 22 1 false (0),
.cycle 0 48 true (0),
.cycle 30 1 false (4),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 32 1 false (6),
.cycle 18 3 true (4)
])
theorem kid11_part887_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part887) = true := by rfl

def kid11_part888 : Audit := .split 12 (4,false) (byMove [
.cycle 17 6 false (1),
.cycle 1 16 true (1),
.last 19 (5,true),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 12 2 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.last 13 (5,true),
.last 15 (5,true),
.cycle 16 4 false (0),
.cycle 5 9 true (1),
.last 17 (5,true),
.cycle 15 1 false (-1),
.last 15 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 18 3 false (0),
.cycle 1 14 true (1),
.cycle 17 3 false (1),
.last 13 (5,true)
])
theorem kid11_part888_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part888) = true := by rfl

def kid11_part889 : Audit := .split 16 (5,true) (byMove [
.cycle 13 5 false (2),
.cycle 23 32 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 28 4 false (8),
.cycle 28 4 false (8),
.last 18 (4,false),
.cycle 21 1 false (5),
.cycle 17 4 false (1),
.cycle 21 4 false (5),
.cycle 24 13 true (2),
.cycle 17 4 false (0),
.cycle 32 4 false (8),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 4 false (-1),
.cycle 16 22 true (0),
.cycle 1 20 true (0),
.cycle 17 4 false (1),
.cycle 16 37 true (0),
.cycle 15 2 true (0),
.cycle 20 3 true (4)
])
theorem kid11_part889_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part889) = true := by rfl

def kid11_part890 : Audit := .cycle 1 12 true (1)
theorem kid11_part890_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part890) = true := by rfl

def kid11_part891 : Audit := .cycle 7 5 true (3)
theorem kid11_part891_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part891) = true := by rfl

def kid11_part892 : Audit := .cycle 10 2 true (3)
theorem kid11_part892_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part892) = true := by rfl

def kid11_part893 : Audit := .cycle 0 13 true (0)
theorem kid11_part893_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part893) = true := by rfl

def kid11_part894 : Audit := .split 13 (4,false) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 12 2 true (4),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 13 1 true (5),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 11 5 true (3),
.cycle 1 15 true (1),
.cycle 11 3 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
])
theorem kid11_part894_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part894) = true := by rfl

def kid11_part895 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (4,false),
.cycle 0 14 true (0),
.last 17 (4,false),
.cycle 19 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 35 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 14 (4,false),
.cycle 1 14 true (1),
.cycle 11 2 true (3),
.cycle 19 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.cycle 12 3 true (4)
])
theorem kid11_part895_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part895) = true := by rfl

def kid11_part871 : Audit := .split 11 (4,true) (byMove [(kid11_part872),(kid11_part873),(kid11_part874),(kid11_part875),(kid11_part876),(kid11_part877),(kid11_part878),(kid11_part879),(kid11_part880),(kid11_part881),(kid11_part882),(kid11_part883),(kid11_part884),(kid11_part885),(kid11_part886),(kid11_part887),(kid11_part888),(kid11_part889),(kid11_part890),(kid11_part891),(kid11_part892),(kid11_part893),(kid11_part894),(kid11_part895)])

theorem kid11_part871_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part871) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) 11 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part872),(kid11_part873),(kid11_part874),(kid11_part875),(kid11_part876),(kid11_part877),(kid11_part878),(kid11_part879),(kid11_part880),(kid11_part881),(kid11_part882),(kid11_part883),(kid11_part884),(kid11_part885),(kid11_part886),(kid11_part887),(kid11_part888),(kid11_part889),(kid11_part890),(kid11_part891),(kid11_part892),(kid11_part893),(kid11_part894),(kid11_part895)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part872_checked

  · exact kid11_part878_checked

  · exact kid11_part884_checked

  · exact kid11_part890_checked

  · exact kid11_part873_checked

  · exact kid11_part879_checked

  · exact kid11_part885_checked

  · exact kid11_part891_checked

  · exact kid11_part874_checked

  · exact kid11_part880_checked

  · exact kid11_part886_checked

  · exact kid11_part892_checked

  · exact kid11_part875_checked

  · exact kid11_part881_checked

  · exact kid11_part887_checked

  · exact kid11_part893_checked

  · exact kid11_part876_checked

  · exact kid11_part882_checked

  · exact kid11_part888_checked

  · exact kid11_part894_checked

  · exact kid11_part877_checked

  · exact kid11_part883_checked

  · exact kid11_part889_checked

  · exact kid11_part895_checked

def kid11_part896 : Audit := .split 11 (5,true) (byMove [
.cycle 9 8 true (2),
.cycle 0 15 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.split 12 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 21 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 14 (4,true),
.cycle 15 5 false (1),
.last 19 (4,true),
.cycle 9 4 true (2),
.cycle 0 15 true (0),
.cycle 21 1 false (3),
.last 14 (4,true),
.last 22 (4,true),
.last 19 (4,true),
.last 16 (4,true),
.last 21 (4,true),
.cycle 22 1 false (0),
.last 14 (4,true),
.cycle 15 5 false (1),
.last 19 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 14 (4,true),
.cycle 11 4 true (2)
]),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 25 5 false (2),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 24 1 false (4),
.last 20 (4,false),
.last 13 (4,false),
.last 26 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 6 true (3),
.cycle 0 24 true (0),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 9 4 true (3),
.cycle 0 15 true (0),
.cycle 21 1 false (3),
.last 13 (4,false),
.cycle 25 5 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 8 5 true (3),
.cycle 13 9 true (3),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.cycle 18 1 false (2),
.split 12 (4,false) (byMove [
.last 17 (4,true),
.cycle 1 16 true (1),
.cycle 22 1 false (2),
.cycle 20 1 false (0),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 6 7 true (2),
.cycle 7 9 true (2),
.last 18 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 11 2 true (2),
.cycle 11 8 true (1),
.last 16 (4,true),
.cycle 5 9 true (1),
.cycle 19 1 false (1),
.last 14 (4,true),
.cycle 15 5 false (1),
.cycle 6 7 true (2),
.last 21 (4,true),
.last 18 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 14 (4,true)
]),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 19 6 false (1),
.cycle 0 14 true (0),
.last 14 (4,false),
.last 14 (4,false),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (4,false),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 15 (4,false),
.cycle 19 6 false (1),
.cycle 1 14 true (1),
.last 14 (4,false),
.cycle 11 2 true (3),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 13 (4,false),
.last 16 (4,false)
]),
.cycle 12 3 true (4)
])
theorem kid11_part896_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part896) = true := by rfl

def kid11_part897 : Audit := .cycle 0 11 true (0)
theorem kid11_part897_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part897) = true := by rfl

def kid11_part898 : Audit := .cycle 1 10 true (1)
theorem kid11_part898_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part898) = true := by rfl

def kid11_part899 : Audit := .cycle 2 9 true (1)
theorem kid11_part899_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part899) = true := by rfl

def kid11_part900 : Audit := .cycle 1 13 true (1)
theorem kid11_part900_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part900) = true := by rfl

def kid11_part902 : Audit := .cycle 1 12 true (1)
theorem kid11_part902_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part902) = true := by rfl

def kid11_part903 : Audit := .cycle 7 5 true (3)
theorem kid11_part903_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part903) = true := by rfl

def kid11_part904 : Audit := .cycle 10 2 true (4)
theorem kid11_part904_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part904) = true := by rfl

def kid11_part905 : Audit := .cycle 0 13 true (0)
theorem kid11_part905_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part905) = true := by rfl

def kid11_part906 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 21 1 false (1),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 1 14 true (1),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.last 15 (5,true)
])
theorem kid11_part906_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part906) = true := by rfl

def kid11_part907 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 25 1 false (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 19 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 35 (4,true),
.cycle 3 10 true (1),
.cycle 8 10 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 9 6 true (3),
.last 14 (4,true),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 11 2 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part907_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part907) = true := by rfl

def kid11_part908 : Audit := .cycle 0 12 true (0)
theorem kid11_part908_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part908) = true := by rfl

def kid11_part909 : Audit := .cycle 1 11 true (1)
theorem kid11_part909_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part909) = true := by rfl

def kid11_part910 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 41 1 false (3),
.cycle 36 1 false (2),
.cycle 1 34 true (1),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 32 (4,true),
.cycle 1 30 true (1),
.last 33 (4,true),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 9 11 true (3),
.cycle 0 22 true (0),
.cycle 36 1 false (2),
.cycle 10 11 true (4),
.last 23 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.cycle 18 3 true (6)
])
theorem kid11_part910_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part910) = true := by rfl

def kid11_part911 : Audit := .cycle 3 9 true (1)
theorem kid11_part911_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part911) = true := by rfl

def kid11_part912 : Audit := .cycle 11 1 true (5)
theorem kid11_part912_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part912) = true := by rfl

def kid11_part913 : Audit := .cycle 8 4 true (3)
theorem kid11_part913_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part913) = true := by rfl

def kid11_part914 : Audit := .cycle 6 6 true (2)
theorem kid11_part914_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part914) = true := by rfl

def kid11_part915 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 32 9 false (2),
.cycle 33 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 43 (4,true),
.cycle 36 1 false (8),
.cycle 9 6 true (3),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 20 (4,true),
.last 20 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.cycle 12 3 true (4)
])
theorem kid11_part915_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part915) = true := by rfl

def kid11_part916 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 10 4 true (4),
.cycle 0 15 true (0),
.cycle 0 19 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 17 true (0),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 12 2 true (4),
.cycle 1 15 true (1),
.last 21 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 11 3 true (4),
.last 16 (5,true)
])
theorem kid11_part916_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part916) = true := by rfl

def kid11_part917 : Audit := .cycle 1 13 true (1)
theorem kid11_part917_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part917) = true := by rfl

def kid11_part918 : Audit := .split 12 (4,true) (byMove [
.cycle 9 5 true (3),
.cycle 7 11 true (3),
.last 23 (5,true),
.cycle 7 8 true (3),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 36 1 false (8),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 12 2 true (3),
.cycle 5 8 true (1),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 11 3 true (4),
.last 13 (5,true)
])
theorem kid11_part918_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part918) = true := by rfl

def kid11_part919 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 true (3),
.last 17 (4,true),
.cycle 25 1 false (3),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 19 6 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 6 true (3),
.cycle 7 10 true (3),
.last 17 (4,true),
.last 14 (4,true),
.cycle 5 8 true (1),
.last 13 (4,true),
.last 17 (4,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 13 3 true (5)
])
theorem kid11_part919_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part919) = true := by rfl

def kid11_part920 : Audit := .cycle 0 12 true (0)
theorem kid11_part920_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part920) = true := by rfl

def kid11_part921 : Audit := .cycle 1 11 true (1)
theorem kid11_part921_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part921) = true := by rfl

def kid11_part922 : Audit := .cycle 2 10 true (1)
theorem kid11_part922_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part922) = true := by rfl

def kid11_part923 : Audit := .cycle 1 14 true (1)
theorem kid11_part923_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part923) = true := by rfl

def kid11_part924 : Audit := .cycle 11 1 true (5)
theorem kid11_part924_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part924) = true := by rfl

def kid11_part925 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 41 13 false (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 14 true (4),
.cycle 1 32 true (1),
.cycle 11 4 true (5),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 17 (4,true),
.last 24 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 11 4 true (5),
.cycle 12 3 true (5)
])
theorem kid11_part925_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part925) = true := by rfl

def kid11_part901 : Audit := .split 11 (4,false) (byMove [(kid11_part902),(kid11_part903),(kid11_part904),(kid11_part905),(kid11_part906),(kid11_part907),(kid11_part908),(kid11_part909),(kid11_part910),(kid11_part911),(kid11_part912),(kid11_part913),(kid11_part914),(kid11_part915),(kid11_part916),(kid11_part917),(kid11_part918),(kid11_part919),(kid11_part920),(kid11_part921),(kid11_part922),(kid11_part923),(kid11_part924),(kid11_part925)])

theorem kid11_part901_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part901) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part902),(kid11_part903),(kid11_part904),(kid11_part905),(kid11_part906),(kid11_part907),(kid11_part908),(kid11_part909),(kid11_part910),(kid11_part911),(kid11_part912),(kid11_part913),(kid11_part914),(kid11_part915),(kid11_part916),(kid11_part917),(kid11_part918),(kid11_part919),(kid11_part920),(kid11_part921),(kid11_part922),(kid11_part923),(kid11_part924),(kid11_part925)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part902_checked

  · exact kid11_part908_checked

  · exact kid11_part914_checked

  · exact kid11_part920_checked

  · exact kid11_part903_checked

  · exact kid11_part909_checked

  · exact kid11_part915_checked

  · exact kid11_part921_checked

  · exact kid11_part904_checked

  · exact kid11_part910_checked

  · exact kid11_part916_checked

  · exact kid11_part922_checked

  · exact kid11_part905_checked

  · exact kid11_part911_checked

  · exact kid11_part917_checked

  · exact kid11_part923_checked

  · exact kid11_part906_checked

  · exact kid11_part912_checked

  · exact kid11_part918_checked

  · exact kid11_part924_checked

  · exact kid11_part907_checked

  · exact kid11_part913_checked

  · exact kid11_part919_checked

  · exact kid11_part925_checked

def kid11_part926 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 30 1 false (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 19 9 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 44 1 false (8),
.cycle 3 12 true (1),
.cycle 14 1 true (4),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 33 9 false (2),
.last 17 (4,true),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 25 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (4),
.cycle 11 4 true (4)
]),
.cycle 32 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 91 24 true (13),
.cycle 36 1 false (8),
.split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 36 (4,true),
.cycle 3 12 true (1),
.last 17 (4,true),
.cycle 8 7 true (3),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.last 25 (4,true),
.last 23 (4,true),
.cycle 14 1 true (6),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 9 6 true (3),
.cycle 0 17 true (0),
.last 32 (4,true),
.last 17 (4,true),
.last 23 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 11 4 true (4)
]),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 9 5 true (3),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.split 14 (4,false) (byMove [
.cycle 9 7 true (3),
.last 20 (4,true),
.cycle 30 1 false (2),
.cycle 7 10 true (3),
.last 15 (4,true),
.cycle 19 9 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 13 2 true (4),
.cycle 12 8 true (3),
.last 21 (4,true),
.last 17 (4,true),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 25 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
]),
.cycle 25 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.split 14 (4,false) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 10 5 true (4),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 13 2 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 12 9 true (4),
.cycle 3 12 true (1),
.cycle 14 1 true (6),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 12 3 true (4),
.cycle 13 3 true (5),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 14 1 true (6),
.cycle 11 4 true (4)
]),
.cycle 11 3 true (4)
])
theorem kid11_part926_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part926) = true := by rfl

def kid11_part806 : Audit := .split 10 (2,true) (byMove [(kid11_part807),(kid11_part808),(kid11_part809),(kid11_part810),(kid11_part811),(kid11_part836),(kid11_part837),(kid11_part838),(kid11_part839),(kid11_part840),(kid11_part841),(kid11_part866),(kid11_part867),(kid11_part868),(kid11_part869),(kid11_part870),(kid11_part871),(kid11_part896),(kid11_part897),(kid11_part898),(kid11_part899),(kid11_part900),(kid11_part901),(kid11_part926)])

theorem kid11_part806_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (kid11_part806) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part807),(kid11_part808),(kid11_part809),(kid11_part810),(kid11_part811),(kid11_part836),(kid11_part837),(kid11_part838),(kid11_part839),(kid11_part840),(kid11_part841),(kid11_part866),(kid11_part867),(kid11_part868),(kid11_part869),(kid11_part870),(kid11_part871),(kid11_part896),(kid11_part897),(kid11_part898),(kid11_part899),(kid11_part900),(kid11_part901),(kid11_part926)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part807_checked

  · exact kid11_part837_checked

  · exact kid11_part867_checked

  · exact kid11_part897_checked

  · exact kid11_part808_checked

  · exact kid11_part838_checked

  · exact kid11_part868_checked

  · exact kid11_part898_checked

  · exact kid11_part809_checked

  · exact kid11_part839_checked

  · exact kid11_part869_checked

  · exact kid11_part899_checked

  · exact kid11_part810_checked

  · exact kid11_part840_checked

  · exact kid11_part870_checked

  · exact kid11_part900_checked

  · exact kid11_part811_checked

  · exact kid11_part841_checked

  · exact kid11_part871_checked

  · exact kid11_part901_checked

  · exact kid11_part836_checked

  · exact kid11_part866_checked

  · exact kid11_part896_checked

  · exact kid11_part926_checked

def kid11_part927 : Audit := .cycle 0 11 true (0)
theorem kid11_part927_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,2⟩)) (kid11_part927) = true := by rfl

def kid11_part929 : Audit := .split 18 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 38, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.split 19 (4,true) (byMove [
.cycle 29 1 false (5),
.cycle 22 1 false (2),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 8, 16, 8, 8, 1, 64],80⟩,
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.last 20 (4,false),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 0 22 true (0),
.last 21 (4,false),
.cycle 30 1 false (6),
.last 21 (4,false),
.cycle 15 5 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 0 49 true (0),
.last 20 (4,false),
.cycle 0 49 true (0)
]),
.cycle 29 1 false (5),
.cycle 0 19 true (0),
.cycle 0 46 true (0),
.cycle 0 27 true (0),
.cycle 3 16 true (0),
.split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.last 43 (4,true),
.last 21 (4,true),
.last 43 (4,true),
.cycle 0 20 true (0),
.last 40 (4,true),
.cycle 9 13 true (0),
.cycle 0 27 true (0),
.cycle 19 1 true (5),
.cycle 0 27 true (0),
.cycle 4 19 true (0),
.cycle 17 3 true (3),
.cycle 0 22 true (0),
.cycle 4 16 true (0),
.last 21 (4,true),
.cycle 5 16 true (0),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.last 38 (4,true),
.last 44 (4,true),
.cycle 19 1 true (5),
.last 44 (4,true)
]),
.cycle 4 16 true (0),
.cycle 0 28 true (0),
.cycle 0 21 true (0),
.cycle 26 1 false (4),
.cycle 0 45 true (0),
.split 19 (4,true) (byMove [
.cycle 16 8 true (2),
.cycle 22 1 false (2),
.last 21 (4,false),
.cycle 29 1 false (5),
.last 21 (4,false),
.cycle 0 25 true (0),
.cycle 0 45 true (0),
.cycle 0 28 true (0),
.last 21 (4,false),
.cycle 0 21 true (0),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 0 23 true (0),
.cycle 14 6 true (2),
.last 21 (4,false),
.cycle 24 1 false (4),
.last 21 (4,false),
.cycle 15 5 false (4),
.cycle 0 50 true (0),
.cycle 4 18 true (0),
.cycle 18 2 true (3),
.cycle 0 21 true (0),
.last 21 (4,false),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 64, 8, 64],[8, 8, 16, 8, 8, 1, 64],80⟩
]),
.cycle 15 8 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.split 19 (4,false) (byMove [
.last 40 (4,true),
.cycle 4 18 true (0),
.cycle 18 2 true (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 41 (4,true),
.cycle 0 20 true (0),
.last 39 (4,true),
.cycle 0 28 true (0),
.cycle 3 17 true (0),
.cycle 19 1 true (5),
.cycle 4 17 true (0),
.cycle 0 29 true (0),
.cycle 0 22 true (0),
.last 21 (4,true),
.last 42 (4,true),
.last 20 (4,true),
.cycle 17 5 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.last 43 (4,true),
.cycle 19 1 true (5),
.last 43 (4,true)
]),
.cycle 17 27 true (3)
])
theorem kid11_part929_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part929) = true := by rfl

def kid11_part930 : Audit := .cycle 0 19 true (0)
theorem kid11_part930_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part930) = true := by rfl

def kid11_part931 : Audit := .cycle 17 1 false (3)
theorem kid11_part931_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part931) = true := by rfl

def kid11_part932 : Audit := .cycle 16 1 false (2)
theorem kid11_part932_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part932) = true := by rfl

def kid11_part933 : Audit := .split 16 (4,false) (byMove [
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 18 1 false (0),
.cycle 25 1 false (5),
.split 18 (2,true) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 29 1 false (5),
.cycle 0 19 true (0),
.cycle 55 1 false (11),
.cycle 36 1 false (8),
.cycle 25 1 false (5),
.last 40 (4,true),
.cycle 25 1 false (5),
.cycle 22 1 false (4),
.cycle 30 1 false (6),
.cycle 31 1 false (7),
.cycle 29 1 false (7),
.last 19 (4,true),
.cycle 15 4 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.last 39 (4,true),
.last 43 (4,true)
]),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 27 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 19 1 true (3),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 27 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 19 1 true (5),
.cycle 20 1 false (4),
.cycle 27 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 17 2 true (3),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 26 1 false (6),
.cycle 30 1 false (8),
.cycle 19 1 true (5),
.cycle 30 1 false (8)
]),
.cycle 18 1 false (2),
.cycle 34 1 false (4),
.split 18 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 0 24 true (0),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 0 47 true (0),
.cycle 19 32 true (3),
.cycle 0 21 true (0),
.cycle 34 1 false (4),
.last 22 (4,true),
.cycle 34 1 false (4),
.cycle 22 1 false (2),
.cycle 14 5 false (3),
.cycle 37 1 false (7),
.cycle 33 1 false (7),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 4 18 true (0),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 4 15 true (0),
.cycle 14 9 false (3),
.cycle 5 15 true (0)
]),
.cycle 27 1 false (5),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 18 1 false (0),
.cycle 4 16 true (0),
.split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 26 1 false (4),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 46 true (0),
.cycle 1 27 true (0),
.cycle 3 16 true (0),
.cycle 1 19 true (0),
.cycle 4 16 true (0),
.cycle 1 28 true (0),
.cycle 1 21 true (0),
.cycle 26 1 false (4),
.cycle 1 45 true (0),
.last 19 (4,true),
.last 20 (4,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 1 19 true (0),
.last 43 (4,true)
]),
.cycle 0 19 true (0),
.cycle 22 1 false (4),
.split 18 (4,true) (byMove [
.last 41 (2,true),
.cycle 26 1 false (4),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 true (1),
.cycle 22 1 false (0),
.cycle 0 19 true (0),
.cycle 46 1 true (8),
.cycle 27 1 true (5),
.cycle 3 16 true (0),
.cycle 19 1 true (5),
.cycle 4 16 true (0),
.cycle 28 1 true (4),
.cycle 21 1 true (3),
.last 19 (2,true),
.cycle 45 1 true (7),
.cycle 19 3 false (3),
.cycle 22 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 19 1 true (5),
.cycle 5 40 true (0)
]),
.cycle 22 1 false (4)
])
theorem kid11_part933_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part933) = true := by rfl

def kid11_part934 : Audit := .cycle 17 1 false (1)
theorem kid11_part934_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part934) = true := by rfl

def kid11_part935 : Audit := .cycle 25 1 false (7)
theorem kid11_part935_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part935) = true := by rfl

def kid11_part936 : Audit := .cycle 18 1 false (4)
theorem kid11_part936_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part936) = true := by rfl

def kid11_part937 : Audit := .split 16 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 25 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 true (3),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.last 20 (4,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 17 1 true (3),
.cycle 29 1 false (7)
]),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 25 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.cycle 26 1 false (8),
.cycle 19 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 true (5),
.cycle 19 1 false (5),
.cycle 26 1 false (6),
.cycle 16 3 true (4),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (7),
.cycle 29 1 false (9),
.cycle 17 1 true (5),
.cycle 29 1 false (9)
]),
.cycle 18 1 false (4),
.cycle 25 1 false (5),
.cycle 22 1 false (6),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.split 17 (4,false) (byMove [
.last 21 (4,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.cycle 16 2 true (3),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 20 1 false (6),
.cycle 9 14 true (0),
.last 20 (4,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 47 1 false (11),
.cycle 25 1 false (5),
.last 19 (4,true),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 28 1 false (8)
]),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 24 1 false (6),
.cycle 28 1 false (8),
.split 17 (4,false) (byMove [
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.cycle 16 2 true (4),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 20 1 false (6),
.cycle 0 18 true (0),
.last 35 (4,true),
.cycle 27 1 false (9),
.cycle 24 1 false (6),
.cycle 17 1 true (5),
.cycle 24 1 false (6),
.cycle 21 1 false (5),
.cycle 21 1 false (7),
.last 19 (4,true),
.cycle 28 1 false (8),
.last 18 (4,true),
.cycle 15 3 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.last 39 (4,true),
.cycle 17 1 true (5),
.last 39 (4,true)
]),
.cycle 28 1 false (8)
])
theorem kid11_part937_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part937) = true := by rfl

def kid11_part938 : Audit := .cycle 0 17 true (0)
theorem kid11_part938_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part938) = true := by rfl

def kid11_part939 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 25 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 true (3),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 17 1 true (3),
.cycle 29 1 false (7)
]),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 25 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.cycle 26 1 false (8),
.cycle 19 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 true (5),
.cycle 19 1 false (5),
.cycle 26 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (7),
.cycle 29 1 false (9),
.cycle 17 1 true (5),
.cycle 29 1 false (9)
]),
.cycle 18 1 false (4),
.cycle 25 1 false (5),
.split 18 (2,true) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.cycle 16 3 false (4),
.last 20 (4,false),
.cycle 0 19 true (0),
.last 46 (4,false),
.last 27 (4,false),
.cycle 25 1 false (5),
.last 19 (4,false),
.cycle 25 1 false (5),
.cycle 22 1 false (4),
.last 21 (4,false),
.cycle 31 1 false (7),
.cycle 29 1 false (7),
.cycle 16 3 false (4),
.cycle 15 4 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.last 19 (4,false),
.cycle 15 27 true (3)
]),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.split 17 (4,false) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (3),
.cycle 21 1 false (5),
.cycle 14 27 true (2),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 17 1 false (3),
.cycle 19 1 false (1),
.cycle 0 47 true (0),
.cycle 25 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 3 false (4),
.cycle 15 34 true (3)
]),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 24 1 false (6),
.cycle 28 1 false (8),
.split 17 (4,false) (byMove [
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 21 1 false (3),
.cycle 0 18 true (0),
.cycle 16 19 true (4),
.cycle 28 1 false (10),
.cycle 24 1 false (6),
.cycle 17 1 true (5),
.cycle 24 1 false (6),
.cycle 21 1 false (5),
.last 22 (2,true),
.last 18 (2,true),
.cycle 28 1 false (8),
.cycle 16 3 true (4),
.cycle 15 3 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 16 24 true (4),
.cycle 17 1 true (5),
.cycle 16 24 true (4)
]),
.cycle 28 1 false (8)
])
theorem kid11_part939_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part939) = true := by rfl

def kid11_part940 : Audit := .cycle 18 1 false (4)
theorem kid11_part940_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part940) = true := by rfl

def kid11_part941 : Audit := .cycle 4 18 true (0)
theorem kid11_part941_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part941) = true := by rfl

def kid11_part942 : Audit := .split 17 (2,true) (byMove [
.cycle 30 1 false (6),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 27 1 false (5),
.split 18 (4,true) (byMove [
.cycle 0 23 true (0),
.cycle 38 1 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 27 1 false (5),
.cycle 30 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.last 19 (4,false),
.cycle 20 1 false (2),
.cycle 38 1 false (4),
.cycle 16 3 false (3),
.cycle 29 1 false (5),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 4 18 true (0),
.cycle 1 21 true (0),
.cycle 0 21 true (0),
.cycle 24 1 false (4),
.last 19 (4,false),
.cycle 24 1 false (4)
]),
.cycle 15 3 false (3),
.cycle 0 43 true (0),
.cycle 24 22 true (4),
.cycle 9 12 true (0),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.last 19 (4,false),
.cycle 30 1 false (6),
.cycle 0 19 true (0),
.last 43 (4,false),
.cycle 9 12 true (0),
.last 28 (4,false),
.last 19 (4,false),
.last 28 (4,false),
.cycle 4 18 true (0),
.last 21 (4,false),
.cycle 0 21 true (0),
.cycle 24 1 false (4),
.last 19 (4,false),
.cycle 24 1 false (4),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.last 38 (4,false),
.cycle 5 38 true (0),
.last 19 (4,false),
.last 54 (4,false)
]),
.cycle 4 18 true (0),
.cycle 26 1 false (4),
.cycle 14 4 true (2),
.cycle 24 1 false (4),
.cycle 22 1 false (4),
.split 18 (4,true) (byMove [
.cycle 16 8 true (1),
.cycle 12 34 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 22 1 false (4),
.cycle 26 1 false (4),
.last 20 (4,false),
.cycle 29 1 false (7),
.last 21 (4,false),
.cycle 15 4 true (2),
.cycle 13 12 true (1),
.cycle 16 3 false (3),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.last 19 (4,false),
.cycle 20 1 false (0),
.cycle 25 26 true (3),
.cycle 4 22 true (0),
.cycle 17 2 true (2),
.cycle 0 49 true (0),
.last 21 (4,false),
.cycle 14 6 true (2)
]),
.cycle 15 3 false (3),
.cycle 0 48 true (0),
.cycle 4 16 true (0),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.split 18 (4,true) (byMove [
.last 42 (4,false),
.cycle 26 1 false (4),
.last 20 (4,false),
.cycle 0 20 true (0),
.last 21 (4,false),
.last 24 (4,false),
.cycle 0 19 true (0),
.last 48 (4,false),
.last 29 (4,false),
.cycle 3 16 true (0),
.last 19 (4,false),
.cycle 4 16 true (0),
.last 30 (4,false),
.last 23 (4,false),
.cycle 17 2 true (3),
.last 47 (4,false),
.last 21 (4,false),
.cycle 14 6 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.last 19 (4,false),
.cycle 14 29 true (2)
]),
.cycle 14 37 true (2)
])
theorem kid11_part942_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part942) = true := by rfl

def kid11_part943 : Audit := .cycle 27 1 false (7)
theorem kid11_part943_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part943) = true := by rfl

def kid11_part944 : Audit := .cycle 16 1 false (2)
theorem kid11_part944_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part944) = true := by rfl

def kid11_part946 : Audit := .split 19 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 1, 8, 64, 16, 64],64⟩,
.cycle 38 1 false (4),
.cycle 23 1 false (1),
.cycle 0 50 true (0),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 49 true (0),
.cycle 26 26 true (3),
.cycle 9 14 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 1, 8, 64],[8, 9, 9, 8, 64, 16, 64],64⟩,
.cycle 20 13 true (2),
.cycle 14 12 true (1),
.cycle 38 1 false (4),
.cycle 5 15 true (0),
.last 20 (4,true),
.last 21 (4,true),
.cycle 0 54 true (0),
.cycle 4 18 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 21 (4,true)
])
theorem kid11_part946_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part946) = true := by rfl

def kid11_part947 : Audit := .cycle 12 30 true (0)
theorem kid11_part947_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part947) = true := by rfl

def kid11_part948 : Audit := .cycle 18 1 false (2)
theorem kid11_part948_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part948) = true := by rfl

def kid11_part949 : Audit := .cycle 17 1 false (1)
theorem kid11_part949_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part949) = true := by rfl

def kid11_part950 : Audit := .cycle 16 1 false (2)
theorem kid11_part950_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part950) = true := by rfl

def kid11_part951 : Audit := .cycle 18 1 false (0)
theorem kid11_part951_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part951) = true := by rfl

def kid11_part952 : Audit := .cycle 20 1 false (4)
theorem kid11_part952_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part952) = true := by rfl

def kid11_part953 : Audit := .cycle 22 1 false (4)
theorem kid11_part953_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part953) = true := by rfl

def kid11_part954 : Audit := .split 17 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 64, 16, 64],64⟩,
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.cycle 20 1 false (6),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.cycle 14 6 true (2),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 0 48 true (0),
.cycle 25 1 false (5),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 19 (4,true)
])
theorem kid11_part954_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part954) = true := by rfl

def kid11_part955 : Audit := .cycle 27 1 false (7)
theorem kid11_part955_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part955) = true := by rfl

def kid11_part956 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 21 1 true (3),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 true (5),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 16 2 true (2),
.cycle 19 1 false (1),
.cycle 0 48 true (0),
.cycle 25 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 true (5),
.cycle 17 2 true (3)
])
theorem kid11_part956_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part956) = true := by rfl

def kid11_part957 : Audit := .cycle 15 2 true (2)
theorem kid11_part957_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part957) = true := by rfl

def kid11_part958 : Audit := .cycle 13 8 true (1)
theorem kid11_part958_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part958) = true := by rfl

def kid11_part959 : Audit := .split 18 (2,true) (byMove [
.cycle 34 1 false (6),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 14 10 true (1),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 6 13 true (0),
.cycle 19 11 true (2),
.far true 1 ⟨0,[0, 0],[10, 8, 8, 8, 2, 8, 64],[8, 10, 8, 8, 64, 16, 64],64⟩,
.cycle 12 30 true (0),
.last 19 (4,true),
.cycle 14 7 false (3),
.cycle 13 6 true (1),
.cycle 14 5 false (3),
.cycle 34 1 false (4),
.cycle 30 1 false (4),
.last 19 (4,true),
.cycle 15 4 false (3),
.cycle 25 26 true (3),
.cycle 14 11 false (4),
.cycle 2 19 true (0),
.cycle 0 49 true (0),
.last 19 (4,true),
.last 20 (4,true)
])
theorem kid11_part959_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part959) = true := by rfl

def kid11_part960 : Audit := .cycle 22 1 false (4)
theorem kid11_part960_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part960) = true := by rfl

def kid11_part961 : Audit := .cycle 17 1 false (1)
theorem kid11_part961_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part961) = true := by rfl

def kid11_part962 : Audit := .cycle 16 1 false (2)
theorem kid11_part962_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part962) = true := by rfl

def kid11_part963 : Audit := .cycle 18 1 false (0)
theorem kid11_part963_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part963) = true := by rfl

def kid11_part964 : Audit := .cycle 23 22 true (3)
theorem kid11_part964_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part964) = true := by rfl

def kid11_part965 : Audit := .cycle 4 18 true (0)
theorem kid11_part965_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part965) = true := by rfl

def kid11_part966 : Audit := .split 17 (2,true) (byMove [
.cycle 30 1 false (6),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 27 1 false (5),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 43 true (0),
.cycle 24 22 true (4),
.cycle 9 12 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 4 18 true (0),
.cycle 26 1 false (4),
.cycle 14 4 true (2),
.cycle 24 1 false (4),
.cycle 22 1 false (4),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 48 true (0),
.cycle 4 16 true (0),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 19 (4,true)
])
theorem kid11_part966_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part966) = true := by rfl

def kid11_part967 : Audit := .cycle 0 43 true (0)
theorem kid11_part967_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part967) = true := by rfl

def kid11_part968 : Audit := .split 17 (4,true) (byMove [
.last 20 (2,true),
.cycle 20 1 false (2),
.last 18 (2,true),
.cycle 27 1 false (5),
.cycle 26 1 true (0),
.cycle 15 3 false (3),
.cycle 0 43 true (0),
.cycle 24 22 true (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 true (5),
.cycle 4 18 true (0),
.cycle 26 1 false (4),
.cycle 14 4 true (2),
.last 18 (2,true),
.cycle 22 1 false (4),
.cycle 16 3 false (3),
.cycle 15 3 false (3),
.cycle 0 48 true (0),
.cycle 4 16 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 true (5),
.cycle 17 2 true (3)
])
theorem kid11_part968_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part968) = true := by rfl

def kid11_part969 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 12 34 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 34 1 false (4),
.cycle 20 1 false (0),
.cycle 22 1 false (4),
.cycle 26 1 false (4),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 33 1 false (9),
.cycle 15 4 true (2),
.cycle 13 12 true (1),
.last 20 (2,true),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 16 3 false (3),
.cycle 20 1 false (0),
.cycle 25 26 true (3),
.cycle 4 22 true (0),
.last 19 (2,true),
.cycle 0 49 true (0),
.cycle 18 28 true (2),
.cycle 17 2 true (2)
])
theorem kid11_part969_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part969) = true := by rfl

def kid11_part945 : Audit := .split 16 (4,false) (byMove [(kid11_part946),(kid11_part947),(kid11_part948),(kid11_part949),(kid11_part950),(kid11_part951),(kid11_part952),(kid11_part953),(kid11_part954),(kid11_part955),(kid11_part956),(kid11_part957),(kid11_part958),(kid11_part959),(kid11_part960),(kid11_part961),(kid11_part962),(kid11_part963),(kid11_part964),(kid11_part965),(kid11_part966),(kid11_part967),(kid11_part968),(kid11_part969)])

theorem kid11_part945_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part945) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) 16 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part946),(kid11_part947),(kid11_part948),(kid11_part949),(kid11_part950),(kid11_part951),(kid11_part952),(kid11_part953),(kid11_part954),(kid11_part955),(kid11_part956),(kid11_part957),(kid11_part958),(kid11_part959),(kid11_part960),(kid11_part961),(kid11_part962),(kid11_part963),(kid11_part964),(kid11_part965),(kid11_part966),(kid11_part967),(kid11_part968),(kid11_part969)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part946_checked

  · exact kid11_part952_checked

  · exact kid11_part958_checked

  · exact kid11_part964_checked

  · exact kid11_part947_checked

  · exact kid11_part953_checked

  · exact kid11_part959_checked

  · exact kid11_part965_checked

  · exact kid11_part948_checked

  · exact kid11_part954_checked

  · exact kid11_part960_checked

  · exact kid11_part966_checked

  · exact kid11_part949_checked

  · exact kid11_part955_checked

  · exact kid11_part961_checked

  · exact kid11_part967_checked

  · exact kid11_part950_checked

  · exact kid11_part956_checked

  · exact kid11_part962_checked

  · exact kid11_part968_checked

  · exact kid11_part951_checked

  · exact kid11_part957_checked

  · exact kid11_part963_checked

  · exact kid11_part969_checked

def kid11_part970 : Audit := .cycle 17 1 false (1)
theorem kid11_part970_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part970) = true := by rfl

def kid11_part971 : Audit := .cycle 0 42 true (0)
theorem kid11_part971_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part971) = true := by rfl

def kid11_part972 : Audit := .cycle 23 1 false (5)
theorem kid11_part972_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part972) = true := by rfl

def kid11_part973 : Audit := .split 16 (2,true) (byMove [
.cycle 26 1 false (6),
.cycle 19 1 false (3),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.split 17 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.last 18 (4,false),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.cycle 16 3 false (4),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.last 18 (4,false),
.cycle 29 1 false (7)
]),
.cycle 25 1 false (5),
.cycle 0 17 true (0),
.cycle 49 1 false (11),
.cycle 32 1 false (8),
.cycle 23 1 false (5),
.split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.last 19 (4,true),
.cycle 29 1 false (7),
.cycle 0 18 true (0),
.last 36 (4,true),
.cycle 9 11 true (0),
.cycle 32 1 false (8),
.cycle 17 1 true (5),
.cycle 32 1 false (8),
.cycle 4 17 true (0),
.cycle 16 3 true (4),
.cycle 0 20 true (0),
.cycle 23 1 false (5),
.last 19 (4,true),
.cycle 23 1 false (5),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.last 34 (4,true),
.last 40 (4,true),
.cycle 17 1 true (5),
.last 40 (4,true)
]),
.cycle 23 1 false (5),
.cycle 20 1 false (4),
.cycle 26 1 false (6),
.cycle 29 1 false (7),
.cycle 27 1 false (7),
.split 17 (4,true) (byMove [
.cycle 16 8 true (2),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 19 (4,false),
.cycle 0 19 true (0),
.last 19 (4,false),
.cycle 26 1 false (6),
.cycle 14 25 true (2),
.cycle 16 3 false (4),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 53 1 false (11),
.cycle 25 1 false (5),
.cycle 16 2 true (3),
.cycle 0 19 true (0),
.last 19 (4,false),
.cycle 2 17 true (0)
]),
.cycle 15 2 true (3),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (3),
.split 17 (4,false) (byMove [
.last 36 (4,true),
.cycle 25 1 false (5),
.cycle 16 2 true (4),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 2 17 true (0),
.cycle 0 18 true (0),
.last 35 (4,true),
.last 44 (4,true),
.cycle 3 15 true (0),
.cycle 17 1 true (5),
.cycle 4 15 true (0),
.cycle 34 1 false (8),
.last 36 (4,true),
.last 19 (4,true),
.last 38 (4,true),
.last 18 (4,true),
.cycle 15 3 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.last 39 (4,true),
.cycle 17 1 true (5),
.last 39 (4,true)
]),
.cycle 15 23 true (3)
])
theorem kid11_part973_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part973) = true := by rfl

def kid11_part974 : Audit := .cycle 0 17 true (0)
theorem kid11_part974_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part974) = true := by rfl

def kid11_part976 : Audit := .cycle 26 1 false (6)
theorem kid11_part976_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part976) = true := by rfl

def kid11_part977 : Audit := .cycle 19 1 false (3)
theorem kid11_part977_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part977) = true := by rfl

def kid11_part978 : Audit := .split 17 (2,true) (byMove [
.cycle 0 18 true (0),
.cycle 26 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 26 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.last 18 (4,false),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.last 22 (4,false),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.last 18 (4,false),
.cycle 29 1 false (7)
])
theorem kid11_part978_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part978) = true := by rfl

def kid11_part979 : Audit := .cycle 0 18 true (0)
theorem kid11_part979_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part979) = true := by rfl

def kid11_part980 : Audit := .split 18 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 27 1 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 20 1 false (0),
.cycle 0 19 true (0),
.cycle 27 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 true (2),
.cycle 20 1 false (2),
.cycle 27 1 false (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 20 1 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 26 1 false (4),
.cycle 30 1 false (6),
.cycle 18 1 true (2),
.cycle 30 1 false (6)
])
theorem kid11_part980_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part980) = true := by rfl

def kid11_part981 : Audit := .split 18 (4,false) (byMove [
.cycle 28 1 false (6),
.cycle 21 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 1 false (1),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 17 28 true (3),
.cycle 17 9 true (3),
.cycle 25 1 false (5),
.cycle 18 1 true (4),
.cycle 25 1 false (5),
.cycle 22 1 false (4),
.cycle 17 3 true (3),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 21 1 false (1),
.cycle 15 4 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 18 1 true (4),
.cycle 15 27 true (3)
])
theorem kid11_part981_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part981) = true := by rfl

def kid11_part982 : Audit := .cycle 0 17 true (0)
theorem kid11_part982_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part982) = true := by rfl

def kid11_part983 : Audit := .split 42 (4,false) (byMove [
.cycle 52 1 false (12),
.cycle 45 1 false (9),
.last 43 (2,true),
.cycle 0 44 true (0),
.cycle 52 1 false (12),
.cycle 41 2 true (9),
.cycle 0 43 true (0),
.cycle 17 26 true (3),
.cycle 36 9 true (6),
.cycle 49 1 false (11),
.cycle 42 1 true (10),
.cycle 49 1 false (11),
.cycle 46 1 false (10),
.cycle 40 3 true (8),
.last 43 (2,true),
.cycle 53 1 false (13),
.cycle 46 1 false (10),
.cycle 15 28 true (3),
.cycle 0 43 true (0),
.cycle 1 42 true (0),
.cycle 2 41 true (0),
.cycle 40 24 true (8),
.cycle 42 1 true (10),
.cycle 40 24 true (8)
])
theorem kid11_part983_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part983) = true := by rfl

def kid11_part984 : Audit := .split 25 (4,false) (byMove [
.cycle 35 1 false (9),
.cycle 28 1 false (6),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 28 1 false (8),
.cycle 24 2 true (6),
.cycle 0 26 true (0),
.last 43 (2,true),
.cycle 17 9 true (3),
.cycle 32 1 false (8),
.cycle 25 1 true (7),
.cycle 32 1 false (8),
.cycle 29 1 false (7),
.cycle 23 3 true (5),
.last 26 (2,true),
.cycle 36 1 false (10),
.last 27 (2,true),
.cycle 15 11 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.last 47 (2,true),
.cycle 25 1 true (7),
.last 47 (2,true)
])
theorem kid11_part984_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part984) = true := by rfl

def kid11_part985 : Audit := .cycle 23 1 false (5)
theorem kid11_part985_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part985) = true := by rfl

def kid11_part986 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 20 1 false (4),
.cycle 29 1 false (7),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 50, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 9 11 true (0),
.cycle 32 1 false (8),
.cycle 17 1 true (5),
.cycle 32 1 false (8),
.cycle 4 17 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 23 1 false (5),
.cycle 22 1 false (6),
.cycle 23 1 false (5),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 50, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 50, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 17 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 50, 64],[2, 32, 64, 1, 16, 16, 64],64⟩
])
theorem kid11_part986_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part986) = true := by rfl

def kid11_part987 : Audit := .cycle 23 1 false (5)
theorem kid11_part987_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part987) = true := by rfl

def kid11_part988 : Audit := .cycle 20 1 false (4)
theorem kid11_part988_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part988) = true := by rfl

def kid11_part989 : Audit := .split 19 (4,false) (byMove [
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 22 (2,true),
.cycle 18 2 true (4),
.cycle 0 20 true (0),
.cycle 14 23 true (2),
.cycle 17 9 true (3),
.cycle 26 1 false (6),
.cycle 19 1 true (5),
.cycle 26 1 false (6),
.cycle 23 1 false (5),
.cycle 17 3 true (3),
.last 20 (2,true),
.cycle 30 1 false (8),
.last 22 (2,true),
.cycle 15 5 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 2 18 true (0),
.cycle 14 30 true (2),
.cycle 19 1 true (5),
.cycle 14 30 true (2)
])
theorem kid11_part989_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part989) = true := by rfl

def kid11_part990 : Audit := .split 17 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 256, 16777216, 256, 128, 256, 32768, 524290, 16777216, 524290, 128, 256, 2097152, 32, 16777216, 32, 128, 256, 8, 1024, 16777216, 1024, 16777216],[2, 32, 256, 1, 1, 1024, 8192, 131072, 256, 4096, 256, 1024, 524288, 8388608, 256, 262144, 262144, 1024, 2, 32, 256, 1, 1, 1024, 16777216],31540240⟩,
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.cycle 20 1 false (6),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.last 19 (4,false),
.last 21 (4,false),
.cycle 14 6 true (2),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.last 18 (4,false),
.cycle 19 1 false (1),
.last 46 (4,false),
.cycle 25 1 false (5),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.cycle 16 2 true (3),
.last 19 (4,false)
])
theorem kid11_part990_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part990) = true := by rfl

def kid11_part991 : Audit := .cycle 27 1 false (7)
theorem kid11_part991_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part991) = true := by rfl

def kid11_part992 : Audit := .split 18 (4,false) (byMove [
.last 21 (2,true),
.cycle 12 34 true (0),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 20 1 false (0),
.cycle 22 1 false (4),
.cycle 14 27 true (2),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 17 2 true (2),
.cycle 15 4 true (2),
.cycle 13 12 true (1),
.last 20 (2,true),
.cycle 24 1 false (4),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 20 1 false (0),
.cycle 0 29 true (0),
.cycle 1 21 true (0),
.last 19 (2,true),
.cycle 19 28 true (2),
.cycle 16 3 false (4),
.cycle 16 5 false (4)
])
theorem kid11_part992_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part992) = true := by rfl

def kid11_part993 : Audit := .cycle 15 2 true (3)
theorem kid11_part993_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part993) = true := by rfl

def kid11_part994 : Audit := .cycle 0 17 true (0)
theorem kid11_part994_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part994) = true := by rfl

def kid11_part995 : Audit := .cycle 1 16 true (0)
theorem kid11_part995_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part995) = true := by rfl

def kid11_part996 : Audit := .cycle 2 15 true (0)
theorem kid11_part996_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part996) = true := by rfl

def kid11_part997 : Audit := .cycle 18 20 true (3)
theorem kid11_part997_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part997) = true := by rfl

def kid11_part998 : Audit := .split 17 (4,false) (byMove [
.cycle 16 20 true (3),
.cycle 25 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 17 2 true (4),
.cycle 0 18 true (0),
.cycle 16 19 true (4),
.cycle 17 9 true (4),
.cycle 3 15 true (0),
.cycle 17 1 true (5),
.cycle 4 15 true (0),
.cycle 31 1 false (7),
.cycle 17 3 true (4),
.last 18 (2,true),
.cycle 16 23 true (3),
.cycle 16 3 true (4),
.cycle 15 3 true (3),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 16 24 true (4),
.cycle 17 1 true (5),
.cycle 16 24 true (4)
])
theorem kid11_part998_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part998) = true := by rfl

def kid11_part999 : Audit := .cycle 15 23 true (3)
theorem kid11_part999_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part999) = true := by rfl

def kid11_part975 : Audit := .split 16 (4,true) (byMove [(kid11_part976),(kid11_part977),(kid11_part978),(kid11_part979),(kid11_part980),(kid11_part981),(kid11_part982),(kid11_part983),(kid11_part984),(kid11_part985),(kid11_part986),(kid11_part987),(kid11_part988),(kid11_part989),(kid11_part990),(kid11_part991),(kid11_part992),(kid11_part993),(kid11_part994),(kid11_part995),(kid11_part996),(kid11_part997),(kid11_part998),(kid11_part999)])

theorem kid11_part975_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part975) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) 16 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part976),(kid11_part977),(kid11_part978),(kid11_part979),(kid11_part980),(kid11_part981),(kid11_part982),(kid11_part983),(kid11_part984),(kid11_part985),(kid11_part986),(kid11_part987),(kid11_part988),(kid11_part989),(kid11_part990),(kid11_part991),(kid11_part992),(kid11_part993),(kid11_part994),(kid11_part995),(kid11_part996),(kid11_part997),(kid11_part998),(kid11_part999)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part976_checked

  · exact kid11_part982_checked

  · exact kid11_part988_checked

  · exact kid11_part994_checked

  · exact kid11_part977_checked

  · exact kid11_part983_checked

  · exact kid11_part989_checked

  · exact kid11_part995_checked

  · exact kid11_part978_checked

  · exact kid11_part984_checked

  · exact kid11_part990_checked

  · exact kid11_part996_checked

  · exact kid11_part979_checked

  · exact kid11_part985_checked

  · exact kid11_part991_checked

  · exact kid11_part997_checked

  · exact kid11_part980_checked

  · exact kid11_part986_checked

  · exact kid11_part992_checked

  · exact kid11_part998_checked

  · exact kid11_part981_checked

  · exact kid11_part987_checked

  · exact kid11_part993_checked

  · exact kid11_part999_checked

def kid11_part1000 : Audit := .cycle 15 23 true (3)
theorem kid11_part1000_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1000) = true := by rfl

def kid11_part928 : Audit := .split 15 (5,true) (byMove [(kid11_part929),(kid11_part930),(kid11_part931),(kid11_part932),(kid11_part933),(kid11_part934),(kid11_part935),(kid11_part936),(kid11_part937),(kid11_part938),(kid11_part939),(kid11_part940),(kid11_part941),(kid11_part942),(kid11_part943),(kid11_part944),(kid11_part945),(kid11_part970),(kid11_part971),(kid11_part972),(kid11_part973),(kid11_part974),(kid11_part975),(kid11_part1000)])

theorem kid11_part928_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (kid11_part928) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,3⟩)) (5,true) (some mv)) (byMove [(kid11_part929),(kid11_part930),(kid11_part931),(kid11_part932),(kid11_part933),(kid11_part934),(kid11_part935),(kid11_part936),(kid11_part937),(kid11_part938),(kid11_part939),(kid11_part940),(kid11_part941),(kid11_part942),(kid11_part943),(kid11_part944),(kid11_part945),(kid11_part970),(kid11_part971),(kid11_part972),(kid11_part973),(kid11_part974),(kid11_part975),(kid11_part1000)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part929_checked

  · exact kid11_part935_checked

  · exact kid11_part941_checked

  · exact kid11_part971_checked

  · exact kid11_part930_checked

  · exact kid11_part936_checked

  · exact kid11_part942_checked

  · exact kid11_part972_checked

  · exact kid11_part931_checked

  · exact kid11_part937_checked

  · exact kid11_part943_checked

  · exact kid11_part973_checked

  · exact kid11_part932_checked

  · exact kid11_part938_checked

  · exact kid11_part944_checked

  · exact kid11_part974_checked

  · exact kid11_part933_checked

  · exact kid11_part939_checked

  · exact kid11_part945_checked

  · exact kid11_part975_checked

  · exact kid11_part934_checked

  · exact kid11_part940_checked

  · exact kid11_part970_checked

  · exact kid11_part1000_checked

def kid11_part1003 : Audit := .cycle 1 13 true (1)
theorem kid11_part1003_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1003) = true := by rfl

def kid11_part1004 : Audit := .cycle 7 12 true (2)
theorem kid11_part1004_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1004) = true := by rfl

def kid11_part1005 : Audit := .cycle 29 1 false (1)
theorem kid11_part1005_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1005) = true := by rfl

def kid11_part1006 : Audit := .cycle 0 14 true (0)
theorem kid11_part1006_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1006) = true := by rfl

def kid11_part1007 : Audit := .split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.cycle 0 32 true (0),
.cycle 0 15 true (0),
.cycle 0 32 true (0),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 8 12 true (2),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 0 20 true (0),
.cycle 1 15 true (1),
.cycle 19 6 false (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 16 (5,true)
])
theorem kid11_part1007_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1007) = true := by rfl

def kid11_part1008 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 34 7 false (3),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 95 1 false (9),
.cycle 3 11 true (1),
.cycle 0 15 true (0),
.cycle 8 12 true (2),
.cycle 6 8 true (2),
.cycle 23 3 false (1),
.last 16 (4,true),
.cycle 1 15 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 1 15 true (1),
.last 15 (4,true)
])
theorem kid11_part1008_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1008) = true := by rfl

def kid11_part1009 : Audit := .cycle 0 13 true (0)
theorem kid11_part1009_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1009) = true := by rfl

def kid11_part1010 : Audit := .cycle 1 12 true (1)
theorem kid11_part1010_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1010) = true := by rfl

def kid11_part1011 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 41 1 false (3),
.cycle 36 1 false (2),
.cycle 0 22 true (0),
.cycle 8 13 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 58 1 false (12),
.cycle 1 31 true (1),
.cycle 0 22 true (0),
.cycle 8 13 true (2),
.cycle 11 15 true (3),
.cycle 11 10 true (3),
.cycle 0 23 true (0),
.cycle 36 1 false (2),
.cycle 9 12 true (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 256, 16384, 128, 256, 32768, 2, 256, 262144, 128, 256, 8, 32, 256, 16384, 262144],[2, 32, 4, 1, 262144, 4, 8192, 131072, 16384, 4096, 262144, 262148, 2, 32, 4, 1, 262144, 262144, 262144],264192⟩,
.cycle 0 21 true (0),
.cycle 1 20 true (1),
.cycle 2 19 true (1),
.cycle 1 23 true (1),
.cycle 1 22 true (1),
.last 22 (4,true)
])
theorem kid11_part1011_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1011) = true := by rfl

def kid11_part1012 : Audit := .cycle 3 10 true (1)
theorem kid11_part1012_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1012) = true := by rfl

def kid11_part1013 : Audit := .cycle 0 14 true (0)
theorem kid11_part1013_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1013) = true := by rfl

def kid11_part1014 : Audit := .cycle 11 5 true (3)
theorem kid11_part1014_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1014) = true := by rfl

def kid11_part1015 : Audit := .cycle 6 7 true (2)
theorem kid11_part1015_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1015) = true := by rfl

def kid11_part1016 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 68 1 false (10),
.cycle 49 1 false (9),
.cycle 0 16 true (0),
.cycle 8 7 true (2),
.cycle 11 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.cycle 9 12 true (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 1 16 true (1),
.last 16 (4,true)
])
theorem kid11_part1016_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1016) = true := by rfl

def kid11_part1017 : Audit := .cycle 5 11 true (1)
theorem kid11_part1017_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1017) = true := by rfl

def kid11_part1018 : Audit := .cycle 1 14 true (1)
theorem kid11_part1018_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1018) = true := by rfl

def kid11_part1019 : Audit := .split 13 (4,true) (byMove [
.cycle 10 8 true (2),
.last 65 (5,true),
.cycle 21 1 false (1),
.last 29 (5,true),
.last 24 (5,true),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 9 12 true (2),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 24 (5,true),
.cycle 5 9 true (1),
.cycle 19 6 false (1),
.last 14 (5,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.cycle 1 16 true (1),
.last 14 (5,true)
])
theorem kid11_part1019_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1019) = true := by rfl

def kid11_part1020 : Audit := .split 13 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 66 58 true (0),
.last 16 (4,true),
.cycle 30 1 false (2),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 7 true (2),
.cycle 15 11 true (3),
.cycle 23 3 false (1),
.last 16 (4,true),
.cycle 5 9 true (1),
.last 14 (4,true),
.last 16 (4,true),
.cycle 1 14 true (1),
.cycle 11 7 true (3),
.cycle 12 2 true (3),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid11_part1020_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1020) = true := by rfl

def kid11_part1021 : Audit := .cycle 0 13 true (0)
theorem kid11_part1021_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1021) = true := by rfl

def kid11_part1022 : Audit := .cycle 1 12 true (1)
theorem kid11_part1022_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1022) = true := by rfl

def kid11_part1023 : Audit := .cycle 2 11 true (1)
theorem kid11_part1023_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1023) = true := by rfl

def kid11_part1024 : Audit := .cycle 1 15 true (1)
theorem kid11_part1024_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1024) = true := by rfl

def kid11_part1025 : Audit := .cycle 1 14 true (1)
theorem kid11_part1025_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1025) = true := by rfl

def kid11_part1026 : Audit := .split 14 (4,true) (byMove [
.cycle 11 5 true (3),
.last 21 (5,true),
.last 27 (5,true),
.cycle 11 10 true (3),
.last 31 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 16 (5,true),
.cycle 5 10 true (1),
.last 21 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.cycle 12 3 true (4),
.cycle 0 16 true (0),
.cycle 1 17 true (1),
.last 15 (5,true)
])
theorem kid11_part1026_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1026) = true := by rfl

def kid11_part1002 : Audit := .split 12 (2,true) (byMove [(kid11_part1003),(kid11_part1004),(kid11_part1005),(kid11_part1006),(kid11_part1007),(kid11_part1008),(kid11_part1009),(kid11_part1010),(kid11_part1011),(kid11_part1012),(kid11_part1013),(kid11_part1014),(kid11_part1015),(kid11_part1016),(kid11_part1017),(kid11_part1018),(kid11_part1019),(kid11_part1020),(kid11_part1021),(kid11_part1022),(kid11_part1023),(kid11_part1024),(kid11_part1025),(kid11_part1026)])

theorem kid11_part1002_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1002) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid11_part1003),(kid11_part1004),(kid11_part1005),(kid11_part1006),(kid11_part1007),(kid11_part1008),(kid11_part1009),(kid11_part1010),(kid11_part1011),(kid11_part1012),(kid11_part1013),(kid11_part1014),(kid11_part1015),(kid11_part1016),(kid11_part1017),(kid11_part1018),(kid11_part1019),(kid11_part1020),(kid11_part1021),(kid11_part1022),(kid11_part1023),(kid11_part1024),(kid11_part1025),(kid11_part1026)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1003_checked

  · exact kid11_part1009_checked

  · exact kid11_part1015_checked

  · exact kid11_part1021_checked

  · exact kid11_part1004_checked

  · exact kid11_part1010_checked

  · exact kid11_part1016_checked

  · exact kid11_part1022_checked

  · exact kid11_part1005_checked

  · exact kid11_part1011_checked

  · exact kid11_part1017_checked

  · exact kid11_part1023_checked

  · exact kid11_part1006_checked

  · exact kid11_part1012_checked

  · exact kid11_part1018_checked

  · exact kid11_part1024_checked

  · exact kid11_part1007_checked

  · exact kid11_part1013_checked

  · exact kid11_part1019_checked

  · exact kid11_part1025_checked

  · exact kid11_part1008_checked

  · exact kid11_part1014_checked

  · exact kid11_part1020_checked

  · exact kid11_part1026_checked

def kid11_part1027 : Audit := .cycle 0 13 true (0)
theorem kid11_part1027_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1027) = true := by rfl

def kid11_part1029 : Audit := .split 20 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 4, 16, 64],[9, 13, 1, 9, 64, 1, 64],64⟩,
.cycle 0 33 true (0),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.last 21 (4,true),
.cycle 33 1 false (5),
.cycle 0 21 true (0),
.cycle 0 52 true (0),
.cycle 0 29 true (0),
.cycle 3 18 true (0),
.cycle 2 20 true (0),
.cycle 30 1 false (2),
.cycle 0 32 true (0),
.cycle 0 23 true (0),
.cycle 30 1 false (4),
.cycle 0 49 true (0),
.last 21 (4,true),
.cycle 17 8 true (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 2 19 true (0),
.cycle 22 24 true (3),
.cycle 20 2 true (4),
.last 22 (4,true)
])
theorem kid11_part1029_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1029) = true := by rfl

def kid11_part1030 : Audit := .cycle 0 21 true (0)
theorem kid11_part1030_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1030) = true := by rfl

def kid11_part1031 : Audit := .cycle 19 1 false (3)
theorem kid11_part1031_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1031) = true := by rfl

def kid11_part1032 : Audit := .cycle 18 1 false (2)
theorem kid11_part1032_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1032) = true := by rfl

def kid11_part1033 : Audit := .cycle 20 1 false (2)
theorem kid11_part1033_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1033) = true := by rfl

def kid11_part1034 : Audit := .cycle 21 1 false (1)
theorem kid11_part1034_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1034) = true := by rfl

def kid11_part1035 : Audit := .cycle 29 1 false (7)
theorem kid11_part1035_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1035) = true := by rfl

def kid11_part1036 : Audit := .cycle 22 1 false (4)
theorem kid11_part1036_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1036) = true := by rfl

def kid11_part1037 : Audit := .split 18 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 29 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 21 1 false (5),
.cycle 22 1 false (4),
.cycle 18 5 false (5),
.cycle 24 1 false (6),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 18 2 true (4),
.last 20 (4,true)
])
theorem kid11_part1037_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1037) = true := by rfl

def kid11_part1038 : Audit := .cycle 0 19 true (0)
theorem kid11_part1038_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1038) = true := by rfl

def kid11_part1039 : Audit := .split 18 (4,true) (byMove [
.cycle 0 19 true (0),
.cycle 29 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 29 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 false (5),
.cycle 21 1 false (5),
.cycle 22 1 false (4),
.last 23 (2,true),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.last 20 (2,true),
.cycle 32 1 false (6)
])
theorem kid11_part1039_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1039) = true := by rfl

def kid11_part1040 : Audit := .cycle 22 1 false (4)
theorem kid11_part1040_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1040) = true := by rfl

def kid11_part1041 : Audit := .split 25 (2,true) (byMove [
.cycle 0 30 true (0),
.cycle 30 1 false (2),
.cycle 28 1 false (2),
.cycle 0 31 true (0),
.last 26 (4,true),
.cycle 35 1 false (-1),
.cycle 21 5 true (3),
.cycle 16 31 true (2),
.cycle 0 28 true (0),
.cycle 37 1 false (5),
.cycle 41 1 false (5),
.cycle 32 1 false (2),
.cycle 31 1 false (3),
.cycle 25 9 false (4),
.cycle 46 1 false (8),
.cycle 42 1 false (8),
.last 26 (4,true),
.cycle 17 9 false (5),
.cycle 21 5 true (3),
.cycle 1 27 true (0),
.cycle 0 28 true (0),
.cycle 4 22 true (0),
.cycle 24 2 true (3),
.last 27 (4,true)
])
theorem kid11_part1041_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1041) = true := by rfl

def kid11_part1042 : Audit := .split 19 (2,true) (byMove [
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 26 1 false (2),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 47 true (0),
.cycle 28 24 true (4),
.cycle 11 12 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 32 1 false (2),
.cycle 30 1 false (4),
.cycle 16 4 true (2),
.cycle 28 1 false (4),
.cycle 26 1 false (4),
.last 20 (4,true),
.cycle 17 3 false (3),
.cycle 0 54 true (0),
.cycle 1 25 true (0),
.cycle 2 19 true (0),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 26 (4,true)
])
theorem kid11_part1042_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1042) = true := by rfl

def kid11_part1043 : Audit := .cycle 31 1 false (7)
theorem kid11_part1043_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1043) = true := by rfl

def kid11_part1044 : Audit := .cycle 18 1 false (2)
theorem kid11_part1044_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1044) = true := by rfl

def kid11_part1045 : Audit := .cycle 20 1 false (2)
theorem kid11_part1045_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1045) = true := by rfl

def kid11_part1046 : Audit := .cycle 21 1 false (1)
theorem kid11_part1046_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1046) = true := by rfl

def kid11_part1047 : Audit := .cycle 0 48 true (0)
theorem kid11_part1047_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1047) = true := by rfl

def kid11_part1048 : Audit := .split 21 (2,true) (byMove [
.cycle 0 26 true (0),
.cycle 1 29 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 18 5 true (3),
.cycle 1 43 true (0),
.cycle 0 24 true (0),
.cycle 22 1 false (4),
.cycle 24 1 false (4),
.cycle 25 1 false (3),
.cycle 18 5 false (5),
.cycle 1 29 true (0),
.cycle 18 7 true (2),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 18 5 true (3),
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.cycle 29 1 false (5),
.cycle 20 2 true (3),
.last 23 (4,true)
])
theorem kid11_part1048_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1048) = true := by rfl

def kid11_part1049 : Audit := .split 18 (2,true) (byMove [
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 29 1 false (5),
.cycle 0 19 true (0),
.cycle 57 1 false (11),
.cycle 36 1 false (8),
.cycle 27 1 false (5),
.cycle 29 1 false (5),
.cycle 25 1 false (3),
.cycle 24 1 false (4),
.cycle 30 1 false (6),
.cycle 33 1 false (7),
.cycle 31 1 false (7),
.last 19 (4,true),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.cycle 18 2 true (4),
.last 20 (4,true)
])
theorem kid11_part1049_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1049) = true := by rfl

def kid11_part1050 : Audit := .cycle 0 19 true (0)
theorem kid11_part1050_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1050) = true := by rfl

def kid11_part1051 : Audit := .split 18 (4,true) (byMove [
.cycle 30 1 false (6),
.cycle 23 1 false (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 22 1 false (2),
.last 21 (2,true),
.cycle 0 19 true (0),
.last 49 (2,true),
.last 28 (2,true),
.cycle 27 1 false (5),
.cycle 29 1 false (5),
.last 21 (2,true),
.cycle 24 1 false (4),
.last 22 (2,true),
.last 19 (2,true),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.cycle 17 2 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.last 20 (2,true),
.last 23 (2,true)
])
theorem kid11_part1051_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1051) = true := by rfl

def kid11_part1052 : Audit := .split 20 (4,true) (byMove [
.last 23 (2,true),
.cycle 25 1 false (3),
.last 21 (2,true),
.last 26 (2,true),
.cycle 24 1 false (2),
.cycle 27 1 false (1),
.cycle 17 25 true (3),
.cycle 37 1 false (7),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 36 1 false (8),
.cycle 18 3 true (4),
.cycle 22 5 true (4),
.cycle 16 5 true (2),
.last 21 (2,true),
.cycle 27 1 false (5),
.cycle 24 1 false (2),
.cycle 17 5 true (3),
.cycle 17 23 true (3),
.last 24 (2,true),
.last 21 (2,true),
.cycle 0 22 true (0),
.last 23 (2,true),
.cycle 18 3 true (4)
])
theorem kid11_part1052_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1052) = true := by rfl

def kid11_part1028 : Audit := .split 17 (5,true) (byMove [(kid11_part1029),(kid11_part1030),(kid11_part1031),(kid11_part1032),(kid11_part1033),(kid11_part1034),(kid11_part1035),(kid11_part1036),(kid11_part1037),(kid11_part1038),(kid11_part1039),(kid11_part1040),(kid11_part1041),(kid11_part1042),(kid11_part1043),(kid11_part1044),(kid11_part1045),(kid11_part1046),(kid11_part1047),(kid11_part1048),(kid11_part1049),(kid11_part1050),(kid11_part1051),(kid11_part1052)])

theorem kid11_part1028_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1028) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) 17 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (5,true) (some mv)) (byMove [(kid11_part1029),(kid11_part1030),(kid11_part1031),(kid11_part1032),(kid11_part1033),(kid11_part1034),(kid11_part1035),(kid11_part1036),(kid11_part1037),(kid11_part1038),(kid11_part1039),(kid11_part1040),(kid11_part1041),(kid11_part1042),(kid11_part1043),(kid11_part1044),(kid11_part1045),(kid11_part1046),(kid11_part1047),(kid11_part1048),(kid11_part1049),(kid11_part1050),(kid11_part1051),(kid11_part1052)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1029_checked

  · exact kid11_part1035_checked

  · exact kid11_part1041_checked

  · exact kid11_part1047_checked

  · exact kid11_part1030_checked

  · exact kid11_part1036_checked

  · exact kid11_part1042_checked

  · exact kid11_part1048_checked

  · exact kid11_part1031_checked

  · exact kid11_part1037_checked

  · exact kid11_part1043_checked

  · exact kid11_part1049_checked

  · exact kid11_part1032_checked

  · exact kid11_part1038_checked

  · exact kid11_part1044_checked

  · exact kid11_part1050_checked

  · exact kid11_part1033_checked

  · exact kid11_part1039_checked

  · exact kid11_part1045_checked

  · exact kid11_part1051_checked

  · exact kid11_part1034_checked

  · exact kid11_part1040_checked

  · exact kid11_part1046_checked

  · exact kid11_part1052_checked

def kid11_part1053 : Audit := .cycle 17 1 false (1)
theorem kid11_part1053_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1053) = true := by rfl

def kid11_part1054 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 false (4),
.cycle 21 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 17 true (0),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.cycle 29 1 false (5),
.cycle 22 1 false (4),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 29 1 false (7),
.cycle 22 1 false (6),
.cycle 21 1 false (5),
.cycle 21 1 false (5),
.cycle 22 1 false (4),
.last 27 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (3),
.cycle 22 1 false (2),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 28 1 false (6),
.cycle 32 1 false (8),
.cycle 31 1 false (7),
.cycle 25 1 false (5)
]),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 11 5 false (1),
.split 14 (2,true) (byMove [
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 24 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 0 19 true (-1),
.last 22 (5,true),
.last 22 (5,true),
.cycle 21 1 false (1),
.cycle 10 5 false (2),
.cycle 11 5 false (1),
.cycle 18 1 false (0),
.last 16 (5,true),
.last 26 (5,true),
.last 24 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.cycle 0 19 true (-1),
.last 22 (5,true),
.cycle 2 13 false (4),
.cycle 0 21 true (-1),
.last 18 (5,true),
.last 18 (5,true)
]),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 17 true (0),
.split 20 (5,true) (byMove [
.cycle 0 21 true (0),
.proven (BB6.Agent11Raw39B0RBCounter861.M861.table) (fun m hm => BB6.Agent11Raw39B0RBCounter861.M861.never m hm),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 1 24 true (0),
.cycle 0 28 true (0),
.cycle 0 21 true (0),
.proven (BB6.Agent11Raw39B0RBCounter862.M862.table) (fun m hm => BB6.Agent11Raw39B0RBCounter862.M862.never m hm),
.last 32 (2,true),
.cycle 40 1 false (8),
.cycle 1 26 true (0),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 32, 32, 32, 128, 256, 32768, 524290, 256, 131072, 128, 256, 2097152, 32, 32768, 16777216, 128, 256, 8, 32, 32, 262144, 16777216],[2, 32, 16777216, 1, 128, 32, 8192, 131072, 16777216, 4096, 128, 131072, 524288, 8388608, 16777216, 262144, 128, 8388608, 2, 32, 16777216, 1, 128, 32, 16777216],16910336⟩,
.last 27 (2,true),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 28 1 false (2),
.cycle 9 12 true (0),
.cycle 0 75 true (0),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.proven (BB6.Agent11Raw39B0RBCounter864.M864.table) (fun m hm => BB6.Agent11Raw39B0RBCounter864.M864.never m hm),
.proven (BB6.Agent11Raw39B0RBCounter865.M865.table) (fun m hm => BB6.Agent11Raw39B0RBCounter865.M865.never m hm),
.cycle 1 22 true (0),
.last 28 (2,true)
]),
.cycle 20 1 false (2),
.cycle 0 19 true (0),
.cycle 11 2 true (0),
.split 15 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 0 21 true (0),
.cycle 12 4 true (0),
.cycle 18 1 false (-2),
.last 18 (2,true),
.cycle 0 19 true (0),
.last 24 (2,true),
.cycle 22 1 false (2),
.cycle 10 6 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 19 1 false (1),
.last 19 (2,true),
.last 16 (2,true),
.cycle 0 21 true (0),
.cycle 14 2 true (0),
.cycle 18 1 false (-2),
.last 18 (2,true),
.cycle 0 19 true (0),
.far false 6 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 5, 1, 3, 4],[128, 256, 8, 0, 0, 0, 128, 256, 32768, 524290, 256, 256, 33554432, 67108864, 2097152, 536870944, 32768, 68719476736, 33554432, 67108864, 134217728, 68786585856, 536870944, 262144, 128, 256, 8589934592, 70900514816, 256, 256, 33554432, 67108864, 2097152, 103087603712, 32768, 68719476736, 68719476736],[2, 32, 68719476736, 1, 2048, 256, 8192, 131072, 68719476736, 4096, 2048, 256, 524288, 8388608, 68719476736, 262144, 536870912, 67108864, 33554432, 536870912, 68719476736, 16777216, 536870912, 67108864, 2147483648, 34359738368, 68719476736, 1073741824, 2048, 256, 524288, 8388608, 68719476736, 262144, 536870912, 67108864, 68719476736],118316753408⟩,
.last 20 (2,true),
.cycle 26 5 true (4),
.cycle 22 3 true (4)
])
])
theorem kid11_part1054_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1054) = true := by rfl

def kid11_part1055 : Audit := .split 12 (5,true) (byMove [
.cycle 0 26 true (-1),
.cycle 36 2 false (6),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 21 true (0),
.split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 16 2 false (2),
.cycle 17 1 false (1),
.cycle 0 20 true (0),
.last 15 (4,true),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.last 29 (4,true),
.cycle 0 17 true (0),
.cycle 28 2 false (8),
.last 17 (4,true),
.cycle 42 5 true (6),
.cycle 17 2 false (3),
.cycle 28 2 false (8),
.cycle 32 2 false (8),
.cycle 28 2 false (8),
.last 15 (4,true),
.cycle 17 2 false (3),
.cycle 0 22 true (0),
.cycle 1 16 true (0),
.cycle 0 17 true (0),
.cycle 4 11 true (0),
.last 33 (4,true),
.last 16 (4,true)
]),
.cycle 0 22 true (0),
.cycle 13 1 false (1),
.cycle 13 2 false (1),
.cycle 13 2 false (1),
.cycle 10 5 false (2),
.split 14 (2,true) (byMove [
.cycle 0 30 true (-1),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 0 24 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 27 true (-1),
.last 31 (4,true),
.cycle 0 26 true (-1),
.cycle 36 2 false (6),
.last 17 (4,true),
.cycle 10 5 false (2),
.cycle 17 2 false (1),
.cycle 12 4 true (-1),
.cycle 38 2 false (8),
.cycle 32 2 false (8),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 12 31 true (-1),
.cycle 12 20 true (-1),
.cycle 0 26 true (-1),
.cycle 4 11 false (4),
.cycle 12 6 true (-1),
.last 16 (4,true)
]),
.cycle 0 27 true (-1),
.cycle 13 1 false (-1),
.cycle 13 2 false (-1),
.cycle 13 2 false (-1),
.cycle 0 21 true (0),
.split 14 (2,true) (byMove [
.cycle 0 19 true (0),
.cycle 10 6 true (0),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.last 15 (4,true),
.cycle 0 19 true (0),
.cycle 0 22 true (0),
.last 29 (4,true),
.cycle 0 17 true (0),
.cycle 1 20 true (0),
.last 17 (4,true),
.cycle 1 20 true (0),
.last 20 (4,true),
.cycle 1 20 true (0),
.cycle 21 2 false (3),
.far false 5 ⟨0,[0, 1, 2, 3, 1, 1, 0, 4, 4, 4],[128, 256, 8, 131200, 1712990626, 1644832930, 524288, 1048576, 32768, 532610, 1048576, 1073741824, 128, 256, 512, 133152, 1073741824, 128, 33554432, 67108864, 8, 128, 67108864, 1073741824, 33554432, 67108864, 134217728, 570556578, 1712990626, 1644832930, 1073741824],[2, 32, 131200, 1, 1073741824, 128, 8192, 131072, 532610, 4096, 1073741824, 524288, 128, 2048, 133152, 64, 1073741824, 128, 2, 32, 128, 1, 1073741824, 33554432, 33554432, 536870912, 570556578, 16777216, 1073741824, 33554432, 1073741824],2144201586⟩,
.last 15 (4,true),
.cycle 1 24 true (0),
.cycle 0 22 true (0),
.cycle 1 16 true (0),
.cycle 0 17 true (0),
.cycle 4 11 true (0),
.cycle 1 20 true (0),
.last 16 (4,true)
]),
.cycle 0 22 true (0),
.cycle 17 2 false (3),
.cycle 11 2 true (0),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.cycle 17 2 false (3),
.cycle 24 2 false (6),
.last 15 (2,true),
.last 18 (2,true),
.cycle 17 2 false (3),
.cycle 20 3 true (4),
.cycle 28 5 true (4),
.last 16 (2,true),
.cycle 19 2 false (3),
.cycle 15 1 false (-1),
.cycle 15 2 false (-1),
.cycle 15 2 false (-1),
.last 23 (2,true),
.cycle 16 10 true (2),
.last 15 (2,true),
.last 18 (2,true),
.cycle 21 5 true (3),
.cycle 20 3 true (4)
])
])
theorem kid11_part1055_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1055) = true := by rfl

def kid11_part1056 : Audit := .cycle 1 10 true (1)
theorem kid11_part1056_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1056) = true := by rfl

def kid11_part1057 : Audit := .cycle 7 3 true (3)
theorem kid11_part1057_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1057) = true := by rfl

def kid11_part1059 : Audit := .cycle 0 11 true (0)
theorem kid11_part1059_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1059) = true := by rfl

def kid11_part1060 : Audit := .cycle 1 10 true (1)
theorem kid11_part1060_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1060) = true := by rfl

def kid11_part1061 : Audit := .split 19 (5,true) (byMove [
.cycle 26 1 false (2),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 0 23 true (0),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.cycle 24 1 false (2),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 24 1 false (2),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 22 (4,true)
])
theorem kid11_part1061_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1061) = true := by rfl

def kid11_part1062 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 28 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (4),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 28 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 20 1 false (6),
.cycle 21 1 false (3),
.cycle 36 1 false (6),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 11 9 true (0),
.last 19 (4,true)
])
theorem kid11_part1062_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1062) = true := by rfl

def kid11_part1063 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 0 59 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 38 1 false (10),
.cycle 27 1 false (3),
.cycle 29 1 false (7),
.cycle 36 1 false (10),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.last 22 (4,true),
.cycle 29 1 false (7),
.cycle 26 14 true (4),
.last 24 (4,true),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.cycle 40 1 false (10),
.cycle 35 1 false (7),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 23 (4,true),
.cycle 5 79 true (0),
.last 22 (4,true),
.last 25 (4,true)
])
theorem kid11_part1063_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1063) = true := by rfl

def kid11_part1064 : Audit := .split 18 (4,true) (byMove [
.last 22 (5,true),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 22 true (-1),
.cycle 19 3 false (-1),
.cycle 27 3 false (5),
.cycle 20 3 false (2),
.cycle 19 3 false (1),
.cycle 0 20 true (0),
.cycle 22 1 false (4),
.last 19 (5,true),
.last 21 (5,true),
.last 21 (5,true),
.cycle 29 3 false (5),
.cycle 19 1 false (-1),
.cycle 19 3 false (0),
.cycle 19 3 false (-1),
.cycle 8 22 true (0),
.cycle 14 6 true (0),
.last 20 (5,true),
.cycle 0 20 true (0),
.last 28 (5,true),
.last 19 (5,true)
])
theorem kid11_part1064_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1064) = true := by rfl

def kid11_part1065 : Audit := .cycle 0 11 true (0)
theorem kid11_part1065_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1065) = true := by rfl

def kid11_part1066 : Audit := .cycle 1 10 true (1)
theorem kid11_part1066_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1066) = true := by rfl

def kid11_part1067 : Audit := .split 21 (5,true) (byMove [
.cycle 0 61 true (0),
.cycle 48 34 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 31 1 false (9),
.cycle 33 1 false (9),
.cycle 0 25 true (0),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 29 1 false (9),
.last 22 (4,true),
.cycle 29 1 false (9),
.cycle 26 17 true (4),
.cycle 10 16 true (0),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 28 1 false (8),
.cycle 30 1 false (8),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.cycle 65 1 false (17),
.cycle 5 17 true (0),
.last 22 (4,true),
.last 26 (4,true)
])
theorem kid11_part1067_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1067) = true := by rfl

def kid11_part1068 : Audit := .split 19 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 34 1 false (10),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.cycle 0 22 true (0),
.cycle 32 1 false (10),
.last 20 (4,true),
.cycle 25 1 false (7),
.cycle 24 12 true (4),
.cycle 0 55 true (0),
.cycle 27 1 false (7),
.cycle 20 1 false (2),
.cycle 34 1 false (10),
.cycle 29 1 false (7),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 5 73 true (0),
.last 20 (4,true),
.last 23 (4,true)
])
theorem kid11_part1068_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1068) = true := by rfl

def kid11_part1069 : Audit := .split 23 (5,true) (byMove [
.last 27 (4,true),
.cycle 0 93 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.last 29 (4,true),
.cycle 40 1 false (14),
.cycle 40 1 false (14),
.last 25 (4,true),
.cycle 28 1 false (8),
.last 24 (4,true),
.cycle 33 1 false (11),
.cycle 28 22 true (4),
.last 26 (4,true),
.cycle 44 1 false (14),
.cycle 24 1 false (2),
.last 26 (4,true),
.last 27 (4,true),
.cycle 0 75 true (0),
.cycle 1 27 true (0),
.last 25 (4,true),
.cycle 0 68 true (0),
.last 24 (4,true),
.last 29 (4,true)
])
theorem kid11_part1069_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1069) = true := by rfl

def kid11_part1070 : Audit := .cycle 8 3 true (3)
theorem kid11_part1070_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1070) = true := by rfl

def kid11_part1071 : Audit := .cycle 7 5 true (3)
theorem kid11_part1071_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1071) = true := by rfl

def kid11_part1072 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 46 1 false (10),
.last 30 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 42 1 false (8),
.cycle 40 1 false (10),
.last 28 (4,true),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 22 1 false (2),
.cycle 9 6 true (3),
.last 30 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 9 true (3),
.last 16 (4,true)
])
theorem kid11_part1072_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1072) = true := by rfl

def kid11_part1073 : Audit := .cycle 0 13 true (0)
theorem kid11_part1073_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1073) = true := by rfl

def kid11_part1074 : Audit := .split 17 (5,true) (byMove [
.cycle 0 49 true (0),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 0 21 true (0),
.cycle 21 1 false (1),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 19 1 false (3),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.cycle 26 1 false (4),
.cycle 31 1 false (7),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 48 true (0),
.cycle 29 1 false (5),
.cycle 31 1 false (7),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 20 (4,true)
])
theorem kid11_part1074_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1074) = true := by rfl

def kid11_part1075 : Audit := .cycle 9 2 true (3)
theorem kid11_part1075_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1075) = true := by rfl

def kid11_part1076 : Audit := .split 18 (4,true) (byMove [
.last 22 (5,true),
.last 24 (5,true),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.last 24 (5,true),
.cycle 19 3 false (-1),
.last 21 (5,true),
.last 20 (5,true),
.cycle 19 3 false (1),
.last 22 (5,true),
.cycle 25 1 false (7),
.last 19 (5,true),
.last 21 (5,true),
.last 21 (5,true),
.last 23 (5,true),
.cycle 19 1 false (-1),
.cycle 19 3 false (0),
.cycle 19 3 false (-1),
.last 21 (5,true),
.last 20 (5,true),
.last 20 (5,true),
.last 22 (5,true),
.last 31 (5,true),
.last 19 (5,true)
])
theorem kid11_part1076_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1076) = true := by rfl

def kid11_part1077 : Audit := .cycle 0 11 true (0)
theorem kid11_part1077_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1077) = true := by rfl

def kid11_part1078 : Audit := .cycle 1 10 true (1)
theorem kid11_part1078_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1078) = true := by rfl

def kid11_part1079 : Audit := .cycle 2 9 true (1)
theorem kid11_part1079_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1079) = true := by rfl

def kid11_part1080 : Audit := .cycle 1 13 true (1)
theorem kid11_part1080_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1080) = true := by rfl

def kid11_part1081 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 43 true (0),
.cycle 8 12 true (3),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.last 35 (4,true),
.cycle 0 37 true (0),
.last 36 (4,true),
.cycle 8 12 true (3),
.cycle 7 14 true (3),
.cycle 10 11 true (4),
.cycle 0 22 true (0),
.cycle 30 1 false (2),
.cycle 9 11 true (3),
.last 23 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 11 9 true (4),
.last 21 (4,true)
])
theorem kid11_part1081_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1081) = true := by rfl

def kid11_part1082 : Audit := .split 12 (4,true) (byMove [
.cycle 14 5 true (4),
.cycle 0 16 true (0),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 16 true (0),
.cycle 23 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 27 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 19 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.last 22 (5,true),
.last 13 (5,true)
])
theorem kid11_part1082_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1082) = true := by rfl

def kid11_part1058 : Audit := .split 10 (2,true) (byMove [(kid11_part1059),(kid11_part1060),(kid11_part1061),(kid11_part1062),(kid11_part1063),(kid11_part1064),(kid11_part1065),(kid11_part1066),(kid11_part1067),(kid11_part1068),(kid11_part1069),(kid11_part1070),(kid11_part1071),(kid11_part1072),(kid11_part1073),(kid11_part1074),(kid11_part1075),(kid11_part1076),(kid11_part1077),(kid11_part1078),(kid11_part1079),(kid11_part1080),(kid11_part1081),(kid11_part1082)])

theorem kid11_part1058_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1058) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part1059),(kid11_part1060),(kid11_part1061),(kid11_part1062),(kid11_part1063),(kid11_part1064),(kid11_part1065),(kid11_part1066),(kid11_part1067),(kid11_part1068),(kid11_part1069),(kid11_part1070),(kid11_part1071),(kid11_part1072),(kid11_part1073),(kid11_part1074),(kid11_part1075),(kid11_part1076),(kid11_part1077),(kid11_part1078),(kid11_part1079),(kid11_part1080),(kid11_part1081),(kid11_part1082)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1059_checked

  · exact kid11_part1065_checked

  · exact kid11_part1071_checked

  · exact kid11_part1077_checked

  · exact kid11_part1060_checked

  · exact kid11_part1066_checked

  · exact kid11_part1072_checked

  · exact kid11_part1078_checked

  · exact kid11_part1061_checked

  · exact kid11_part1067_checked

  · exact kid11_part1073_checked

  · exact kid11_part1079_checked

  · exact kid11_part1062_checked

  · exact kid11_part1068_checked

  · exact kid11_part1074_checked

  · exact kid11_part1080_checked

  · exact kid11_part1063_checked

  · exact kid11_part1069_checked

  · exact kid11_part1075_checked

  · exact kid11_part1081_checked

  · exact kid11_part1064_checked

  · exact kid11_part1070_checked

  · exact kid11_part1076_checked

  · exact kid11_part1082_checked

def kid11_part1083 : Audit := .cycle 0 11 true (0)
theorem kid11_part1083_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1083) = true := by rfl

def kid11_part1085 : Audit := .cycle 0 11 true (0)
theorem kid11_part1085_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1085) = true := by rfl

def kid11_part1086 : Audit := .cycle 1 10 true (1)
theorem kid11_part1086_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1086) = true := by rfl

def kid11_part1087 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 24 1 false (4),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.last 21 (2,true),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 24 1 false (2),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 21 (2,true),
.last 23 (2,true)
])
theorem kid11_part1087_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1087) = true := by rfl

def kid11_part1088 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 28 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 true (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 28 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 18 1 true (4),
.cycle 21 1 false (3),
.cycle 36 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 18 1 true (4),
.cycle 20 1 false (2)
])
theorem kid11_part1088_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1088) = true := by rfl

def kid11_part1089 : Audit := .cycle 11 1 true (3)
theorem kid11_part1089_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1089) = true := by rfl

def kid11_part1090 : Audit := .cycle 18 3 false (0)
theorem kid11_part1090_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1090) = true := by rfl

def kid11_part1091 : Audit := .cycle 0 11 true (0)
theorem kid11_part1091_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1091) = true := by rfl

def kid11_part1092 : Audit := .cycle 1 10 true (1)
theorem kid11_part1092_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1092) = true := by rfl

def kid11_part1093 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 48 34 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.last 25 (2,true),
.cycle 33 1 false (9),
.cycle 0 25 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 29 1 false (9),
.last 23 (2,true),
.cycle 29 1 false (9),
.cycle 26 17 true (4),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.last 24 (2,true),
.last 25 (2,true),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.last 23 (2,true),
.last 27 (2,true)
])
theorem kid11_part1093_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1093) = true := by rfl

def kid11_part1094 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 0 24 true (0),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.last 20 (2,true),
.cycle 32 1 false (10),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.cycle 24 12 true (4),
.last 21 (2,true),
.cycle 27 1 false (7),
.cycle 20 1 false (2),
.cycle 34 1 false (10),
.cycle 29 1 false (7),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 5 73 true (0),
.cycle 0 22 true (0),
.cycle 0 25 true (0)
])
theorem kid11_part1094_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1094) = true := by rfl

def kid11_part1095 : Audit := .cycle 11 1 true (5)
theorem kid11_part1095_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1095) = true := by rfl

def kid11_part1096 : Audit := .cycle 8 3 true (3)
theorem kid11_part1096_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1096) = true := by rfl

def kid11_part1097 : Audit := .cycle 7 5 true (3)
theorem kid11_part1097_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1097) = true := by rfl

def kid11_part1098 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (5,true),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 13 1 true (5),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.last 16 (5,true)
])
theorem kid11_part1098_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1098) = true := by rfl

def kid11_part1099 : Audit := .cycle 0 13 true (0)
theorem kid11_part1099_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1099) = true := by rfl

def kid11_part1100 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 false (3),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.last 19 (2,true),
.cycle 31 1 false (7),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 48 true (0),
.cycle 29 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 31 1 false (7),
.cycle 27 1 false (5)
])
theorem kid11_part1100_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1100) = true := by rfl

def kid11_part1101 : Audit := .cycle 9 2 true (3)
theorem kid11_part1101_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1101) = true := by rfl

def kid11_part1102 : Audit := .cycle 18 3 false (0)
theorem kid11_part1102_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1102) = true := by rfl

def kid11_part1103 : Audit := .cycle 0 11 true (0)
theorem kid11_part1103_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1103) = true := by rfl

def kid11_part1104 : Audit := .cycle 1 10 true (1)
theorem kid11_part1104_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1104) = true := by rfl

def kid11_part1105 : Audit := .cycle 2 9 true (1)
theorem kid11_part1105_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1105) = true := by rfl

def kid11_part1106 : Audit := .cycle 1 13 true (1)
theorem kid11_part1106_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1106) = true := by rfl

def kid11_part1107 : Audit := .cycle 11 1 true (5)
theorem kid11_part1107_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1107) = true := by rfl

def kid11_part1108 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 29 7 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 36 (2,true),
.cycle 3 11 true (1),
.cycle 14 1 true (6),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 26 5 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 1 true (6),
.cycle 11 3 true (4)
])
theorem kid11_part1108_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1108) = true := by rfl

def kid11_part1084 : Audit := .split 10 (4,true) (byMove [(kid11_part1085),(kid11_part1086),(kid11_part1087),(kid11_part1088),(kid11_part1089),(kid11_part1090),(kid11_part1091),(kid11_part1092),(kid11_part1093),(kid11_part1094),(kid11_part1095),(kid11_part1096),(kid11_part1097),(kid11_part1098),(kid11_part1099),(kid11_part1100),(kid11_part1101),(kid11_part1102),(kid11_part1103),(kid11_part1104),(kid11_part1105),(kid11_part1106),(kid11_part1107),(kid11_part1108)])

theorem kid11_part1084_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1084) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1085),(kid11_part1086),(kid11_part1087),(kid11_part1088),(kid11_part1089),(kid11_part1090),(kid11_part1091),(kid11_part1092),(kid11_part1093),(kid11_part1094),(kid11_part1095),(kid11_part1096),(kid11_part1097),(kid11_part1098),(kid11_part1099),(kid11_part1100),(kid11_part1101),(kid11_part1102),(kid11_part1103),(kid11_part1104),(kid11_part1105),(kid11_part1106),(kid11_part1107),(kid11_part1108)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1085_checked

  · exact kid11_part1091_checked

  · exact kid11_part1097_checked

  · exact kid11_part1103_checked

  · exact kid11_part1086_checked

  · exact kid11_part1092_checked

  · exact kid11_part1098_checked

  · exact kid11_part1104_checked

  · exact kid11_part1087_checked

  · exact kid11_part1093_checked

  · exact kid11_part1099_checked

  · exact kid11_part1105_checked

  · exact kid11_part1088_checked

  · exact kid11_part1094_checked

  · exact kid11_part1100_checked

  · exact kid11_part1106_checked

  · exact kid11_part1089_checked

  · exact kid11_part1095_checked

  · exact kid11_part1101_checked

  · exact kid11_part1107_checked

  · exact kid11_part1090_checked

  · exact kid11_part1096_checked

  · exact kid11_part1102_checked

  · exact kid11_part1108_checked

def kid11_part1109 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (3),
.cycle 18 1 false (2),
.cycle 8 4 true (3),
.split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 3 false (0),
.cycle 19 3 false (-1),
.cycle 27 3 false (5),
.cycle 20 3 false (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 21 3 false (3),
.cycle 19 3 false (1),
.cycle 16 5 false (2),
.last 20 (2,true),
.cycle 29 3 false (5),
.cycle 19 1 false (-1),
.cycle 19 3 false (0),
.cycle 19 3 false (-1),
.cycle 8 22 true (0),
.cycle 14 6 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 14 7 true (0),
.cycle 20 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 8, 64],64⟩,
.cycle 0 95 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 38 1 false (8),
.cycle 40 1 false (12),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 26 1 false (8),
.cycle 36 1 false (12),
.last 23 (4,true),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.cycle 38 1 false (8),
.cycle 31 1 false (9),
.cycle 23 1 false (3),
.cycle 32 1 false (8),
.cycle 21 4 true (2),
.cycle 27 38 true (4),
.cycle 1 34 true (0),
.cycle 2 23 true (0),
.cycle 10 42 true (0),
.last 23 (4,true),
.last 26 (4,true)
]),
.cycle 32 1 false (10),
.cycle 8 4 true (3),
.cycle 8 3 true (3),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 26 1 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 8 6 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 8 6 true (3),
.last 14 (4,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (2),
.cycle 9 2 true (3),
.split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 8 17 false (4),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 3 false (0),
.cycle 19 3 false (-1),
.cycle 21 3 false (3),
.cycle 20 3 false (2),
.last 19 (2,true),
.cycle 22 3 false (4),
.cycle 24 3 false (6),
.cycle 19 3 false (1),
.cycle 16 5 false (2),
.last 20 (2,true),
.cycle 23 3 false (3),
.cycle 19 1 false (-1),
.cycle 19 3 false (0),
.cycle 19 3 false (-1),
.cycle 13 8 true (0),
.cycle 16 4 true (0),
.last 19 (2,true),
.cycle 10 12 true (0),
.cycle 20 8 true (2),
.cycle 20 3 false (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 8 4 true (3),
.split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.last 26 (2,true),
.cycle 22 1 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 23 5 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 7 true (3),
.cycle 10 3 true (4),
.cycle 10 5 true (3),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 5 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 15 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 8 7 true (3),
.cycle 10 3 true (4)
])
])
theorem kid11_part1109_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1109) = true := by rfl

def kid11_part1110 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 30 1 false (0),
.last 19 (2,true),
.cycle 18 15 false (2),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 8 16 true (2),
.cycle 20 8 false (2),
.cycle 25 5 false (1),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 27 1 false (-1),
.cycle 20 6 false (1),
.cycle 15 7 false (1),
.cycle 1 15 true (1),
.cycle 34 13 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 11 true (2),
.cycle 16 9 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.split 22 (2,true) (byMove [
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 36 1 false (4),
.cycle 33 1 false (3),
.cycle 90 1 false (10),
.cycle 8 15 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 42 1 false (10),
.cycle 53 1 false (11),
.last 47 (4,true),
.cycle 8 15 true (2),
.cycle 10 43 true (0),
.cycle 66 1 false (10),
.cycle 0 25 true (0),
.cycle 33 1 false (3),
.cycle 9 14 true (2),
.cycle 19 12 true (3),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 1 25 true (1),
.cycle 6 18 true (2),
.last 24 (4,true)
]),
.cycle 45 1 false (9),
.cycle 11 8 true (3),
.cycle 8 5 true (2),
.cycle 11 7 true (3),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 16 true (2),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (3),
.cycle 3 12 true (1),
.cycle 11 10 true (3),
.cycle 11 7 true (3),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 5 13 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 25 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 6 10 true (2),
.last 16 (4,true)
]),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 9 8 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 1 18 true (1),
.cycle 30 1 false (0),
.last 19 (2,true),
.cycle 18 15 false (2),
.cycle 15 7 false (1),
.cycle 6 9 true (2),
.cycle 29 9 false (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 14 18 true (2),
.cycle 20 8 false (2),
.cycle 25 5 false (1),
.last 16 (2,true),
.cycle 5 11 true (1),
.cycle 27 1 false (-1),
.cycle 20 6 false (1),
.cycle 15 7 false (1),
.cycle 6 9 true (2),
.cycle 11 4 true (2),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 6 12 true (2),
.cycle 16 9 false (2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 6 8 true (2),
.split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 18 true (0),
.last 39 (2,true),
.last 19 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 15 9 false (3),
.cycle 1 15 true (1),
.cycle 7 8 true (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 11 11 true (3),
.cycle 12 3 true (4),
.cycle 10 5 true (2),
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 5 30 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 27 5 true (3),
.cycle 1 15 true (1),
.cycle 11 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 6 11 true (2),
.cycle 12 3 true (4)
])
])
theorem kid11_part1110_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1110) = true := by rfl

def kid11_part1112 : Audit := .cycle 1 15 true (1)
theorem kid11_part1112_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1112) = true := by rfl

def kid11_part1113 : Audit := .split 21 (5,true) (byMove [
.cycle 15 8 true (0),
.cycle 52 46 true (0),
.cycle 23 1 false (1),
.cycle 22 1 false (0),
.cycle 22 5 false (0),
.cycle 22 5 false (0),
.cycle 0 25 true (0),
.cycle 24 5 false (5),
.cycle 0 123 true (0),
.cycle 24 5 false (5),
.last 22 (4,true),
.cycle 25 5 false (5),
.cycle 26 9 true (2),
.cycle 22 5 false (1),
.cycle 0 29 true (0),
.cycle 22 1 false (0),
.cycle 22 5 false (0),
.cycle 22 5 false (0),
.cycle 0 25 true (0),
.cycle 22 5 true (2),
.cycle 22 5 false (2),
.cycle 5 17 true (0),
.last 22 (4,true),
.last 26 (4,true)
])
theorem kid11_part1113_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1113) = true := by rfl

def kid11_part1114 : Audit := .cycle 25 1 false (1)
theorem kid11_part1114_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1114) = true := by rfl

def kid11_part1115 : Audit := .split 18 (5,true) (byMove [
.cycle 0 23 true (0),
.cycle 0 22 true (0),
.cycle 29 1 false (3),
.cycle 26 1 false (2),
.cycle 0 27 true (0),
.cycle 30 11 false (2),
.cycle 1 19 true (1),
.cycle 7 12 true (2),
.cycle 29 1 false (3),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 8 12 true (2),
.cycle 13 9 true (3),
.cycle 10 9 true (2),
.cycle 1 21 true (1),
.cycle 26 1 false (2),
.cycle 16 10 true (2),
.last 28 (4,true),
.cycle 1 19 true (1),
.cycle 14 5 true (3),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.last 19 (4,true),
.last 21 (4,true)
])
theorem kid11_part1115_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1115) = true := by rfl

def kid11_part1116 : Audit := .split 12 (4,true) (byMove [
.cycle 0 17 true (0),
.last 20 (5,true),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.last 15 (5,true),
.cycle 14 5 false (0),
.last 18 (5,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 9 4 true (2),
.last 21 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 20 (5,true),
.cycle 22 1 false (0),
.last 15 (5,true),
.cycle 14 5 false (0),
.last 18 (5,true),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.last 15 (5,true)
])
theorem kid11_part1116_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1116) = true := by rfl

def kid11_part1117 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 1 20 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 1 19 true (1),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 0 21 true (0),
.cycle 9 4 true (2),
.cycle 24 5 false (5),
.cycle 20 9 true (2),
.cycle 17 3 false (1),
.cycle 1 23 true (1),
.cycle 22 1 false (0),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 1 19 true (1),
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 16 (4,true),
.last 14 (4,true)
])
theorem kid11_part1117_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1117) = true := by rfl

def kid11_part1118 : Audit := .cycle 1 12 true (1)
theorem kid11_part1118_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1118) = true := by rfl

def kid11_part1119 : Audit := .cycle 7 5 true (2)
theorem kid11_part1119_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1119) = true := by rfl

def kid11_part1120 : Audit := .split 21 (5,true) (byMove [
.cycle 0 33 true (0),
.cycle 0 25 true (0),
.cycle 33 1 false (3),
.cycle 30 1 false (2),
.cycle 0 27 true (0),
.cycle 0 29 true (0),
.cycle 1 22 true (1),
.cycle 7 15 true (2),
.cycle 42 1 false (10),
.cycle 0 23 true (0),
.last 22 (4,true),
.cycle 8 15 true (2),
.cycle 20 9 true (4),
.cycle 10 12 true (2),
.cycle 1 24 true (1),
.cycle 30 1 false (2),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 2, 16, 64],[0, 2, 8, 0, 64, 16, 64],64⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 4, 16384, 1048576, 128, 256, 32768, 524290, 16777220, 16777216, 128, 256, 2097152, 32, 16384, 16777220, 128, 256, 8, 4, 16384, 1048576, 16777216],[2, 32, 4, 1, 16777216, 4, 8192, 131072, 16384, 4096, 16777216, 16777220, 524288, 8388608, 1048576, 262144, 16777216, 16777216, 2, 32, 4, 1, 16777216, 16777220, 16777216],16911360⟩,
.cycle 1 22 true (1),
.cycle 20 5 true (4),
.cycle 2 29 true (1),
.cycle 0 23 true (0),
.last 22 (4,true),
.last 24 (4,true)
])
theorem kid11_part1120_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1120) = true := by rfl

def kid11_part1121 : Audit := .cycle 0 13 true (0)
theorem kid11_part1121_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1121) = true := by rfl

def kid11_part1122 : Audit := .split 12 (4,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.cycle 14 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 13 3 true (4),
.cycle 8 5 true (2),
.last 18 (5,true),
.cycle 13 3 true (3),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.last 15 (5,true),
.cycle 14 7 false (2),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 15 (5,true)
])
theorem kid11_part1122_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1122) = true := by rfl

def kid11_part1123 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 23 7 false (1),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 8 15 true (2),
.cycle 45 1 false (9),
.last 20 (4,true),
.cycle 8 5 true (2),
.cycle 12 9 true (3),
.cycle 10 9 true (2),
.cycle 0 15 true (0),
.cycle 4 9 true (1),
.cycle 22 7 false (2),
.last 14 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.last 14 (4,true)
])
theorem kid11_part1123_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1123) = true := by rfl

def kid11_part1124 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 6 12 true (2),
.cycle 24 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 28 7 true (4),
.cycle 40 1 false (10),
.cycle 6 12 true (2),
.cycle 8 7 true (2),
.cycle 13 9 true (3),
.cycle 6 11 true (2),
.cycle 0 17 true (0),
.cycle 22 1 false (2),
.cycle 9 6 true (2),
.cycle 24 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 13 3 true (3),
.last 16 (4,true)
])
theorem kid11_part1124_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1124) = true := by rfl

def kid11_part1125 : Audit := .split 13 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.cycle 25 1 false (1),
.cycle 20 5 false (1),
.cycle 16 6 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (2),
.cycle 46 1 false (8),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 8 7 true (2),
.cycle 12 9 true (2),
.cycle 10 4 true (2),
.cycle 1 16 true (1),
.cycle 20 1 false (2),
.cycle 20 5 false (1),
.cycle 16 6 false (1),
.cycle 1 14 true (1),
.cycle 12 5 true (2),
.cycle 2 15 true (1),
.cycle 0 15 true (0),
.last 14 (4,true),
.last 16 (4,true)
])
theorem kid11_part1125_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1125) = true := by rfl

def kid11_part1126 : Audit := .cycle 5 9 true (1)
theorem kid11_part1126_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1126) = true := by rfl

def kid11_part1127 : Audit := .cycle 5 7 true (1)
theorem kid11_part1127_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1127) = true := by rfl

def kid11_part1128 : Audit := .split 12 (4,true) (byMove [
.cycle 10 8 true (1),
.cycle 1 16 true (1),
.last 19 (5,true),
.cycle 19 1 false (1),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 21 (5,true),
.cycle 1 14 true (1),
.cycle 13 5 true (3),
.last 13 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.cycle 5 9 true (1),
.last 17 (5,true),
.last 15 (5,true),
.cycle 14 5 false (0),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 13 (5,true)
])
theorem kid11_part1128_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1128) = true := by rfl

def kid11_part1129 : Audit := .split 12 (5,true) (byMove [
.cycle 10 8 true (1),
.cycle 1 16 true (1),
.cycle 21 1 false (3),
.cycle 19 1 false (1),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 17 6 false (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 8 7 true (2),
.cycle 14 9 true (2),
.cycle 17 3 false (1),
.cycle 5 9 true (1),
.cycle 18 1 false (2),
.cycle 15 4 false (1),
.last 14 (4,true),
.cycle 6 7 true (2),
.cycle 1 14 true (1),
.cycle 11 2 true (2),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true)
])
theorem kid11_part1129_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1129) = true := by rfl

def kid11_part1130 : Audit := .cycle 1 12 true (1)
theorem kid11_part1130_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1130) = true := by rfl

def kid11_part1131 : Audit := .split 16 (5,true) (byMove [
.cycle 1 19 true (1),
.cycle 0 20 true (0),
.cycle 35 1 false (3),
.cycle 1 21 true (1),
.cycle 0 26 true (0),
.last 18 (4,true),
.cycle 1 17 true (1),
.cycle 7 10 true (2),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 8 10 true (2),
.cycle 12 9 true (3),
.cycle 10 7 true (2),
.cycle 1 19 true (1),
.cycle 30 1 false (2),
.cycle 26 11 false (3),
.last 18 (4,true),
.cycle 1 17 true (1),
.cycle 12 5 true (3),
.cycle 1 17 true (1),
.cycle 0 18 true (0),
.last 17 (4,true),
.last 19 (4,true)
])
theorem kid11_part1131_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1131) = true := by rfl

def kid11_part1132 : Audit := .cycle 2 11 true (1)
theorem kid11_part1132_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1132) = true := by rfl

def kid11_part1133 : Audit := .cycle 0 13 true (0)
theorem kid11_part1133_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1133) = true := by rfl

def kid11_part1134 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.last 17 (5,true),
.last 16 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.last 18 (5,true),
.last 16 (5,true),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 15 (5,true)
])
theorem kid11_part1134_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1134) = true := by rfl

def kid11_part1135 : Audit := .split 12 (5,true) (byMove [
.cycle 1 13 true (1),
.cycle 0 21 true (0),
.last 15 (4,true),
.cycle 0 14 true (0),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 36 (4,true),
.cycle 3 10 true (1),
.last 17 (4,true),
.cycle 8 10 true (2),
.cycle 6 7 true (2),
.last 18 (4,true),
.cycle 11 2 true (3),
.cycle 1 14 true (1),
.last 13 (4,true),
.last 16 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 12 3 true (4),
.last 14 (4,true)
])
theorem kid11_part1135_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1135) = true := by rfl

def kid11_part1111 : Audit := .split 11 (2,true) (byMove [(kid11_part1112),(kid11_part1113),(kid11_part1114),(kid11_part1115),(kid11_part1116),(kid11_part1117),(kid11_part1118),(kid11_part1119),(kid11_part1120),(kid11_part1121),(kid11_part1122),(kid11_part1123),(kid11_part1124),(kid11_part1125),(kid11_part1126),(kid11_part1127),(kid11_part1128),(kid11_part1129),(kid11_part1130),(kid11_part1131),(kid11_part1132),(kid11_part1133),(kid11_part1134),(kid11_part1135)])

theorem kid11_part1111_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1111) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid11_part1112),(kid11_part1113),(kid11_part1114),(kid11_part1115),(kid11_part1116),(kid11_part1117),(kid11_part1118),(kid11_part1119),(kid11_part1120),(kid11_part1121),(kid11_part1122),(kid11_part1123),(kid11_part1124),(kid11_part1125),(kid11_part1126),(kid11_part1127),(kid11_part1128),(kid11_part1129),(kid11_part1130),(kid11_part1131),(kid11_part1132),(kid11_part1133),(kid11_part1134),(kid11_part1135)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1112_checked

  · exact kid11_part1118_checked

  · exact kid11_part1124_checked

  · exact kid11_part1130_checked

  · exact kid11_part1113_checked

  · exact kid11_part1119_checked

  · exact kid11_part1125_checked

  · exact kid11_part1131_checked

  · exact kid11_part1114_checked

  · exact kid11_part1120_checked

  · exact kid11_part1126_checked

  · exact kid11_part1132_checked

  · exact kid11_part1115_checked

  · exact kid11_part1121_checked

  · exact kid11_part1127_checked

  · exact kid11_part1133_checked

  · exact kid11_part1116_checked

  · exact kid11_part1122_checked

  · exact kid11_part1128_checked

  · exact kid11_part1134_checked

  · exact kid11_part1117_checked

  · exact kid11_part1123_checked

  · exact kid11_part1129_checked

  · exact kid11_part1135_checked

def kid11_part1136 : Audit := .cycle 1 12 true (1)
theorem kid11_part1136_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1136) = true := by rfl

def kid11_part1138 : Audit := .split 18 (2,true) (byMove [
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 16, 64],[8, 8, 1, 8, 64, 1, 64],64⟩,
.cycle 27 1 false (3),
.cycle 22 1 false (2),
.cycle 0 20 true (0),
.last 19 (4,true),
.cycle 30 1 false (4),
.cycle 0 19 true (0),
.cycle 0 46 true (0),
.cycle 0 27 true (0),
.cycle 3 16 true (0),
.cycle 4 16 true (0),
.cycle 5 16 true (0),
.cycle 0 28 true (0),
.cycle 0 21 true (0),
.cycle 27 1 false (3),
.cycle 0 45 true (0),
.last 19 (4,true),
.cycle 15 8 true (2),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 20 22 true (3),
.last 42 (4,true),
.last 20 (4,true)
])
theorem kid11_part1138_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1138) = true := by rfl

def kid11_part1139 : Audit := .cycle 0 19 true (0)
theorem kid11_part1139_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1139) = true := by rfl

def kid11_part1140 : Audit := .cycle 17 1 false (3)
theorem kid11_part1140_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1140) = true := by rfl

def kid11_part1141 : Audit := .cycle 16 1 false (2)
theorem kid11_part1141_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1141) = true := by rfl

def kid11_part1142 : Audit := .cycle 17 1 false (1)
theorem kid11_part1142_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1142) = true := by rfl

def kid11_part1143 : Audit := .cycle 18 1 false (0)
theorem kid11_part1143_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1143) = true := by rfl

def kid11_part1144 : Audit := .cycle 26 1 false (6)
theorem kid11_part1144_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1144) = true := by rfl

def kid11_part1145 : Audit := .cycle 19 1 false (3)
theorem kid11_part1145_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1145) = true := by rfl

def kid11_part1146 : Audit := .split 16 (2,true) (byMove [
.cycle 0 17 true (0),
.cycle 26 1 false (4),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 26 1 false (6),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.cycle 22 1 false (6),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 29 1 false (7),
.last 18 (4,true)
])
theorem kid11_part1146_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1146) = true := by rfl

def kid11_part1147 : Audit := .cycle 0 17 true (0)
theorem kid11_part1147_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1147) = true := by rfl

def kid11_part1148 : Audit := .split 16 (4,true) (byMove [
.cycle 0 17 true (0),
.cycle 26 1 false (4),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 26 1 false (6),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 19 1 false (3),
.cycle 26 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 25 1 false (5),
.cycle 29 1 false (7),
.cycle 29 1 false (7),
.cycle 27 1 false (5)
])
theorem kid11_part1148_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1148) = true := by rfl

def kid11_part1149 : Audit := .cycle 19 1 false (3)
theorem kid11_part1149_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1149) = true := by rfl

def kid11_part1150 : Audit := .cycle 5 18 true (0)
theorem kid11_part1150_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1150) = true := by rfl

def kid11_part1151 : Audit := .split 17 (2,true) (byMove [
.cycle 31 1 false (5),
.cycle 21 1 false (1),
.cycle 20 1 false (2),
.cycle 28 1 false (4),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 43 true (0),
.cycle 24 22 true (4),
.cycle 10 12 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 5 18 true (0),
.cycle 27 1 false (3),
.cycle 14 4 true (2),
.cycle 25 1 false (3),
.cycle 23 1 false (3),
.last 18 (4,true),
.cycle 15 3 false (3),
.cycle 0 48 true (0),
.cycle 5 16 true (0),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.last 18 (4,true),
.last 24 (4,true)
])
theorem kid11_part1151_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1151) = true := by rfl

def kid11_part1152 : Audit := .cycle 28 1 false (6)
theorem kid11_part1152_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1152) = true := by rfl

def kid11_part1153 : Audit := .cycle 16 1 false (2)
theorem kid11_part1153_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1153) = true := by rfl

def kid11_part1154 : Audit := .cycle 17 1 false (1)
theorem kid11_part1154_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1154) = true := by rfl

def kid11_part1155 : Audit := .cycle 18 1 false (0)
theorem kid11_part1155_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1155) = true := by rfl

def kid11_part1156 : Audit := .cycle 0 42 true (0)
theorem kid11_part1156_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1156) = true := by rfl

def kid11_part1157 : Audit := .cycle 24 1 false (4)
theorem kid11_part1157_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1157) = true := by rfl

def kid11_part1158 : Audit := .split 16 (2,true) (byMove [
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 19 1 false (3),
.cycle 0 18 true (0),
.last 17 (4,true),
.cycle 26 1 false (4),
.cycle 0 17 true (0),
.cycle 50 1 false (10),
.cycle 33 1 false (7),
.cycle 24 1 false (4),
.cycle 24 1 false (4),
.cycle 24 1 false (4),
.cycle 21 1 false (3),
.cycle 27 1 false (5),
.cycle 30 1 false (6),
.cycle 28 1 false (6),
.last 17 (4,true),
.cycle 15 2 true (3),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (3),
.last 38 (4,true),
.last 18 (4,true)
])
theorem kid11_part1158_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1158) = true := by rfl

def kid11_part1159 : Audit := .cycle 0 17 true (0)
theorem kid11_part1159_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1159) = true := by rfl

def kid11_part1160 : Audit := .split 16 (4,true) (byMove [
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 19 1 false (1),
.cycle 30 1 false (6),
.cycle 0 17 true (0),
.cycle 54 1 false (12),
.cycle 37 1 false (9),
.cycle 24 1 false (4),
.cycle 24 1 false (4),
.cycle 24 1 false (4),
.cycle 21 1 false (3),
.cycle 31 1 false (7),
.last 17 (2,true),
.cycle 28 1 false (6),
.cycle 19 1 false (1),
.cycle 15 2 true (3),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 18 20 true (3),
.cycle 16 23 true (3),
.cycle 15 26 true (3)
])
theorem kid11_part1160_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1160) = true := by rfl

def kid11_part1161 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 22 1 false (2),
.last 19 (2,true),
.cycle 29 1 false (5),
.cycle 21 1 false (1),
.cycle 24 1 false (0),
.cycle 15 23 true (3),
.cycle 32 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 31 1 false (7),
.cycle 16 3 true (4),
.cycle 20 5 true (4),
.cycle 14 5 true (2),
.last 19 (2,true),
.cycle 24 1 false (4),
.cycle 21 1 false (1),
.cycle 15 5 true (3),
.cycle 15 21 true (3),
.cycle 5 17 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 15 26 true (3),
.cycle 16 3 true (4)
])
theorem kid11_part1161_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1161) = true := by rfl

def kid11_part1137 : Audit := .split 15 (5,true) (byMove [(kid11_part1138),(kid11_part1139),(kid11_part1140),(kid11_part1141),(kid11_part1142),(kid11_part1143),(kid11_part1144),(kid11_part1145),(kid11_part1146),(kid11_part1147),(kid11_part1148),(kid11_part1149),(kid11_part1150),(kid11_part1151),(kid11_part1152),(kid11_part1153),(kid11_part1154),(kid11_part1155),(kid11_part1156),(kid11_part1157),(kid11_part1158),(kid11_part1159),(kid11_part1160),(kid11_part1161)])

theorem kid11_part1137_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1137) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) 15 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (5,true) (some mv)) (byMove [(kid11_part1138),(kid11_part1139),(kid11_part1140),(kid11_part1141),(kid11_part1142),(kid11_part1143),(kid11_part1144),(kid11_part1145),(kid11_part1146),(kid11_part1147),(kid11_part1148),(kid11_part1149),(kid11_part1150),(kid11_part1151),(kid11_part1152),(kid11_part1153),(kid11_part1154),(kid11_part1155),(kid11_part1156),(kid11_part1157),(kid11_part1158),(kid11_part1159),(kid11_part1160),(kid11_part1161)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1138_checked

  · exact kid11_part1144_checked

  · exact kid11_part1150_checked

  · exact kid11_part1156_checked

  · exact kid11_part1139_checked

  · exact kid11_part1145_checked

  · exact kid11_part1151_checked

  · exact kid11_part1157_checked

  · exact kid11_part1140_checked

  · exact kid11_part1146_checked

  · exact kid11_part1152_checked

  · exact kid11_part1158_checked

  · exact kid11_part1141_checked

  · exact kid11_part1147_checked

  · exact kid11_part1153_checked

  · exact kid11_part1159_checked

  · exact kid11_part1142_checked

  · exact kid11_part1148_checked

  · exact kid11_part1154_checked

  · exact kid11_part1160_checked

  · exact kid11_part1143_checked

  · exact kid11_part1149_checked

  · exact kid11_part1155_checked

  · exact kid11_part1161_checked

def kid11_part1163 : Audit := .split 15 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 256, 128, 256, 32768, 2, 256, 256, 128, 256, 8, 32, 256, 256, 262144],[2, 32, 256, 1, 256, 262144, 8192, 131072, 256, 4096, 256, 262144, 2, 32, 256, 1, 256, 262144, 262144],278540⟩,
.cycle 11 7 false (1),
.cycle 19 1 false (-1),
.last 19 (5,true),
.last 39 (5,true),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 29 (5,true),
.last 31 (5,true),
.cycle 14 21 true (0),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 22 (5,true),
.last 19 (5,true),
.cycle 12 8 true (-1),
.last 16 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.cycle 14 17 true (0),
.cycle 14 11 true (0),
.cycle 42 5 true (5),
.last 16 (5,true)
])
theorem kid11_part1163_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1163) = true := by rfl

def kid11_part1164 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (-1),
.cycle 0 60 true (-2),
.cycle 30 1 false (2),
.cycle 27 1 false (1),
.cycle 9 11 false (4),
.cycle 8 11 false (4),
.cycle 0 19 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 35, 64],[2, 32, 64, 1, 43, 2, 64],64⟩,
.last 31 (2,true),
.cycle 33 1 false (5),
.cycle 0 36 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 35, 64],[2, 32, 64, 1, 43, 32, 64],64⟩,
.cycle 117 1 false (-1),
.last 20 (2,true),
.cycle 0 21 true (-1),
.cycle 27 1 false (1),
.cycle 9 11 false (4),
.cycle 8 11 false (4),
.cycle 77 20 true (11),
.cycle 1 18 true (-1),
.last 40 (2,true),
.cycle 46 22 true (4),
.cycle 0 24 true (-1),
.cycle 0 24 true (-1)
])
theorem kid11_part1164_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1164) = true := by rfl

def kid11_part1165 : Audit := .cycle 14 1 false (0)
theorem kid11_part1165_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1165) = true := by rfl

def kid11_part1166 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1166_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1166) = true := by rfl

def kid11_part1167 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1167_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1167) = true := by rfl

def kid11_part1168 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1168_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1168) = true := by rfl

def kid11_part1169 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 25 1 false (7),
.cycle 18 1 false (4),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 18 1 false (4),
.cycle 6 18 true (0),
.last 17 (2,true),
.cycle 27 1 false (7),
.cycle 16 1 false (2),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 0 42 true (0),
.cycle 23 1 false (5),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 15 23 true (3)
])
theorem kid11_part1169_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1169) = true := by rfl

def kid11_part1170 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 45 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 18 1 false (4),
.cycle 25 1 false (7),
.last 15 (2,true),
.cycle 25 1 false (7),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 19 7 true (3),
.last 16 (2,true),
.cycle 20 1 false (4),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 42 true (0),
.cycle 1 16 true (0),
.last 15 (2,true),
.cycle 5 58 true (0),
.cycle 30 14 true (4),
.cycle 15 10 true (3)
])
theorem kid11_part1170_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1170) = true := by rfl

def kid11_part1171 : Audit := .split 13 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 256, 256, 128, 256, 32768, 2, 256, 256, 128, 256, 8, 32, 256, 256, 262144],[2, 32, 256, 1, 4, 262144, 8192, 131072, 256, 4096, 16384, 262144, 2, 32, 256, 1, 4, 262144, 262144],278540⟩,
.last 31 (5,true),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 18 1 false (6),
.cycle 18 1 false (4),
.cycle 18 1 false (6),
.last 14 (5,true),
.last 16 (5,true),
.last 17 (5,true),
.last 18 (5,true),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.last 24 (5,true),
.last 14 (5,true)
])
theorem kid11_part1171_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1171) = true := by rfl

def kid11_part1172 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 25 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 25 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 32 1 false (8),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (3),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 24 1 false (6),
.cycle 28 1 false (8),
.cycle 0 20 true (0),
.cycle 0 20 true (0)
])
theorem kid11_part1172_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1172) = true := by rfl

def kid11_part1173 : Audit := .cycle 17 1 false (5)
theorem kid11_part1173_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1173) = true := by rfl

def kid11_part1174 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 32 26 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 18 1 false (4),
.last 14 (2,true),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 19 9 true (2),
.last 15 (2,true),
.cycle 0 21 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.cycle 15 5 true (3),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 14 5 true (2),
.cycle 16 3 true (4)
])
theorem kid11_part1174_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1174) = true := by rfl

def kid11_part1175 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 36 28 true (-1),
.cycle 24 1 false (2),
.last 20 (2,true),
.cycle 11 5 false (1),
.cycle 12 5 false (1),
.cycle 0 19 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 16 (2,true),
.cycle 0 34 true (-2),
.cycle 16 9 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 20 11 true (2),
.last 17 (2,true),
.cycle 0 23 true (-1),
.cycle 21 1 false (1),
.cycle 11 5 false (1),
.cycle 12 5 false (1),
.cycle 14 19 true (0),
.cycle 16 7 true (2),
.last 16 (2,true),
.cycle 5 11 true (-1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 48, 48, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 22 5 true (4)
])
theorem kid11_part1175_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1175) = true := by rfl

def kid11_part1176 : Audit := .split 14 (2,true) (byMove [
.cycle 36 1 false (6),
.cycle 17 1 false (-1),
.cycle 17 1 false (-1),
.last 18 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 30 (5,true),
.last 18 (5,true),
.last 31 (5,true),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 20 (5,true),
.last 18 (5,true),
.cycle 12 3 false (0),
.last 15 (5,true),
.last 17 (5,true),
.last 16 (5,true),
.last 31 (5,true),
.last 18 (5,true),
.last 17 (5,true),
.last 15 (5,true)
])
theorem kid11_part1176_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1176) = true := by rfl

def kid11_part1177 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (-1),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.cycle 27 1 false (7),
.cycle 20 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 0 21 true (-1),
.cycle 20 1 false (4),
.last 26 (2,true),
.last 19 (2,true),
.cycle 29 1 false (7),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.last 61 (2,true),
.cycle 27 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (-1),
.last 19 (2,true),
.last 21 (2,true)
])
theorem kid11_part1177_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1177) = true := by rfl

def kid11_part1178 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1178_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1178) = true := by rfl

def kid11_part1179 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1179_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1179) = true := by rfl

def kid11_part1180 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1180_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1180) = true := by rfl

def kid11_part1181 : Audit := .split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 10 12 true (0),
.cycle 10 12 true (0),
.cycle 0 60 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 1, 2, 64],64⟩,
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 1, 32, 64],64⟩,
.cycle 17 14 true (3),
.last 17 (2,true),
.cycle 0 72 true (0),
.cycle 22 1 false (2),
.cycle 10 6 true (0),
.cycle 11 6 true (0),
.cycle 0 42 true (0),
.cycle 1 28 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 17 true (0),
.cycle 15 21 true (3)
])
theorem kid11_part1181_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1181) = true := by rfl

def kid11_part1182 : Audit := .split 14 (5,true) (byMove [
.last 17 (2,true),
.cycle 0 45 true (0),
.cycle 23 1 false (3),
.last 19 (2,true),
.cycle 11 8 true (0),
.cycle 11 8 true (0),
.cycle 0 28 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 2, 2, 64],64⟩,
.last 15 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 43, 43, 43, 64],[2, 32, 64, 1, 2, 8, 64],64⟩,
.cycle 1 28 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 2, 32, 64],64⟩,
.cycle 19 7 true (3),
.last 16 (2,true),
.cycle 0 34 true (0),
.cycle 20 1 false (2),
.cycle 11 4 true (0),
.cycle 12 4 true (0),
.cycle 0 42 true (0),
.cycle 1 16 true (0),
.last 15 (2,true),
.cycle 5 58 true (0),
.cycle 15 8 true (3),
.cycle 16 8 true (4)
])
theorem kid11_part1182_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1182) = true := by rfl

def kid11_part1183 : Audit := .split 13 (2,true) (byMove [
.cycle 32 1 false (6),
.cycle 16 1 false (0),
.cycle 16 1 false (0),
.last 17 (5,true),
.last 31 (5,true),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 27 (5,true),
.last 27 (5,true),
.cycle 14 22 true (2),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.last 19 (5,true),
.last 17 (5,true),
.cycle 12 2 true (0),
.last 14 (5,true),
.last 16 (5,true),
.last 15 (5,true),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.cycle 2 15 true (0),
.last 14 (5,true)
])
theorem kid11_part1183_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1183) = true := by rfl

def kid11_part1184 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 true (0),
.cycle 0 76 true (0),
.cycle 27 1 false (3),
.cycle 24 1 false (2),
.cycle 5 16 true (0),
.cycle 5 16 true (0),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 35, 64],[2, 32, 64, 1, 8, 2, 64],64⟩,
.last 28 (2,true),
.cycle 36 1 false (8),
.cycle 22 31 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 35, 35, 64],[2, 32, 64, 1, 8, 32, 64],64⟩,
.cycle 15 31 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 24 1 false (2),
.cycle 9 8 true (0),
.cycle 10 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 35 (2,true),
.cycle 0 46 true (0),
.cycle 0 20 true (0),
.cycle 0 20 true (0)
])
theorem kid11_part1184_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1184) = true := by rfl

def kid11_part1185 : Audit := .cycle 15 3 true (3)
theorem kid11_part1185_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1185) = true := by rfl

def kid11_part1186 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 16 1 false (0),
.last 14 (2,true),
.last 22 (2,true),
.cycle 12 4 true (0),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 34, 34, 64],[2, 32, 64, 1, 32, 2, 64],64⟩,
.last 14 (2,true),
.cycle 42 1 false (6),
.cycle 14 8 true (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 21 9 true (3),
.last 17 (2,true),
.last 14 (2,true),
.cycle 18 1 false (2),
.cycle 12 2 true (0),
.cycle 16 1 false (-2),
.cycle 0 17 true (0),
.cycle 15 5 true (3),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 18 3 true (4),
.cycle 16 3 true (4)
])
theorem kid11_part1186_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1186) = true := by rfl

def kid11_part1162 : Audit := .split 12 (4,true) (byMove [(kid11_part1163),(kid11_part1164),(kid11_part1165),(kid11_part1166),(kid11_part1167),(kid11_part1168),(kid11_part1169),(kid11_part1170),(kid11_part1171),(kid11_part1172),(kid11_part1173),(kid11_part1174),(kid11_part1175),(kid11_part1176),(kid11_part1177),(kid11_part1178),(kid11_part1179),(kid11_part1180),(kid11_part1181),(kid11_part1182),(kid11_part1183),(kid11_part1184),(kid11_part1185),(kid11_part1186)])

theorem kid11_part1162_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1162) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) 12 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1163),(kid11_part1164),(kid11_part1165),(kid11_part1166),(kid11_part1167),(kid11_part1168),(kid11_part1169),(kid11_part1170),(kid11_part1171),(kid11_part1172),(kid11_part1173),(kid11_part1174),(kid11_part1175),(kid11_part1176),(kid11_part1177),(kid11_part1178),(kid11_part1179),(kid11_part1180),(kid11_part1181),(kid11_part1182),(kid11_part1183),(kid11_part1184),(kid11_part1185),(kid11_part1186)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1163_checked

  · exact kid11_part1169_checked

  · exact kid11_part1175_checked

  · exact kid11_part1181_checked

  · exact kid11_part1164_checked

  · exact kid11_part1170_checked

  · exact kid11_part1176_checked

  · exact kid11_part1182_checked

  · exact kid11_part1165_checked

  · exact kid11_part1171_checked

  · exact kid11_part1177_checked

  · exact kid11_part1183_checked

  · exact kid11_part1166_checked

  · exact kid11_part1172_checked

  · exact kid11_part1178_checked

  · exact kid11_part1184_checked

  · exact kid11_part1167_checked

  · exact kid11_part1173_checked

  · exact kid11_part1179_checked

  · exact kid11_part1185_checked

  · exact kid11_part1168_checked

  · exact kid11_part1174_checked

  · exact kid11_part1180_checked

  · exact kid11_part1186_checked

def kid11_part1188 : Audit := .split 15 (2,true) (byMove [
.proven (BB6.Agent11Raw39B0RBPumps.M893.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M893.never m hm),
.cycle 10 7 false (2),
.cycle 19 1 false (-1),
.cycle 0 24 true (-1),
.last 16 (4,true),
.last 28 (4,true),
.cycle 0 19 true (-1),
.last 33 (4,true),
.cycle 0 69 true (-1),
.last 24 (4,true),
.last 16 (4,true),
.cycle 14 21 true (0),
.cycle 0 25 true (-1),
.cycle 14 33 true (0),
.cycle 0 33 true (-2),
.cycle 0 53 true (-1),
.last 16 (4,true),
.cycle 12 8 true (-1),
.cycle 0 19 true (-1),
.cycle 14 20 true (0),
.cycle 14 17 true (0),
.cycle 14 11 true (0),
.last 16 (4,true),
.last 34 (4,true)
])
theorem kid11_part1188_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1188) = true := by rfl

def kid11_part1189 : Audit := .split 33 (4,true) (byMove [
.last 36 (2,true),
.cycle 0 60 true (-2),
.cycle 35 1 false (-1),
.cycle 34 1 false (-2),
.cycle 34 2 false (-2),
.cycle 34 2 false (-2),
.cycle 12 24 true (-1),
.cycle 0 45 true (-1),
.last 34 (2,true),
.cycle 0 56 true (-1),
.cycle 41 2 false (7),
.cycle 19 26 true (-1),
.cycle 19 28 true (-2),
.last 35 (2,true),
.cycle 12 26 true (-2),
.cycle 34 1 false (-2),
.cycle 34 2 false (-2),
.cycle 34 2 false (-2),
.cycle 12 24 true (-1),
.cycle 0 45 true (-1),
.last 34 (2,true),
.cycle 0 56 true (-1),
.cycle 56 2 false (0),
.cycle 36 2 false (0)
])
theorem kid11_part1189_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1189) = true := by rfl

def kid11_part1190 : Audit := .cycle 14 1 false (0)
theorem kid11_part1190_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1190) = true := by rfl

def kid11_part1191 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1191_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1191) = true := by rfl

def kid11_part1192 : Audit := .cycle 13 2 false (-1)
theorem kid11_part1192_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1192) = true := by rfl

def kid11_part1193 : Audit := .cycle 13 2 false (-1)
theorem kid11_part1193_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1193) = true := by rfl

def kid11_part1194 : Audit := .cycle 24 2 false (8)
theorem kid11_part1194_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1194) = true := by rfl

def kid11_part1195 : Audit := .cycle 24 2 false (8)
theorem kid11_part1195_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1195) = true := by rfl

def kid11_part1196 : Audit := .split 13 (2,true) (byMove [
.last 38 (4,true),
.last 24 (4,true),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 18 1 false (6),
.cycle 24 2 false (8),
.cycle 18 1 false (6),
.cycle 17 2 false (5),
.last 14 (4,true),
.cycle 18 1 false (6),
.cycle 16 19 true (2),
.cycle 34 1 false (6),
.cycle 20 1 false (6),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.last 41 (4,true),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.last 14 (4,true),
.cycle 12 24 true (0)
])
theorem kid11_part1196_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1196) = true := by rfl

def kid11_part1197 : Audit := .cycle 17 1 false (5)
theorem kid11_part1197_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1197) = true := by rfl

def kid11_part1198 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 48 26 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 17 2 false (5),
.cycle 24 2 false (8),
.last 14 (2,true),
.cycle 17 2 false (5),
.cycle 17 2 false (5),
.cycle 17 2 false (5),
.cycle 16 18 true (2),
.last 15 (2,true),
.cycle 19 2 false (5),
.cycle 14 1 false (0),
.cycle 14 2 false (0),
.cycle 14 2 false (0),
.cycle 0 26 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 16 3 true (4),
.cycle 15 8 true (3)
])
theorem kid11_part1198_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1198) = true := by rfl

def kid11_part1199 : Audit := .cycle 17 2 false (5)
theorem kid11_part1199_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1199) = true := by rfl

def kid11_part1200 : Audit := .cycle 20 11 true (2)
theorem kid11_part1200_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1200) = true := by rfl

def kid11_part1201 : Audit := .split 14 (2,true) (byMove [
.cycle 35 2 false (7),
.cycle 16 2 false (0),
.cycle 17 1 false (-1),
.cycle 0 28 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 47 true (-1),
.last 35 (4,true),
.cycle 12 18 true (-1),
.last 33 (4,true),
.last 15 (4,true),
.cycle 18 13 true (1),
.cycle 37 2 false (5),
.cycle 12 4 true (-1),
.cycle 42 2 false (8),
.cycle 36 2 false (8),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 33 (4,true),
.cycle 12 24 true (-1),
.cycle 12 19 true (-1),
.cycle 37 26 true (2),
.last 15 (4,true),
.last 36 (4,true)
])
theorem kid11_part1201_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1201) = true := by rfl

def kid11_part1202 : Audit := .cycle 28 2 false (8)
theorem kid11_part1202_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1202) = true := by rfl

def kid11_part1203 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1203_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1203) = true := by rfl

def kid11_part1204 : Audit := .cycle 13 2 false (-1)
theorem kid11_part1204_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1204) = true := by rfl

def kid11_part1205 : Audit := .cycle 13 2 false (-1)
theorem kid11_part1205_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1205) = true := by rfl

def kid11_part1206 : Audit := .split 29 (4,true) (byMove [
.last 32 (2,true),
.cycle 13 20 true (1),
.cycle 0 58 true (0),
.cycle 35 2 false (3),
.cycle 33 2 false (-1),
.cycle 39 2 false (-1),
.cycle 0 42 true (0),
.cycle 0 35 true (0),
.last 30 (2,true),
.cycle 13 18 true (1),
.cycle 0 54 true (0),
.cycle 12 18 true (0),
.cycle 12 20 true (0),
.last 31 (2,true),
.cycle 0 46 true (0),
.cycle 0 54 true (0),
.cycle 33 2 false (-1),
.cycle 0 54 true (0),
.cycle 0 42 true (0),
.cycle 0 35 true (0),
.last 30 (2,true),
.cycle 13 18 true (1),
.cycle 15 21 true (3),
.cycle 12 18 true (0)
])
theorem kid11_part1206_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1206) = true := by rfl

def kid11_part1207 : Audit := .cycle 1 16 true (0)
theorem kid11_part1207_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1207) = true := by rfl

def kid11_part1208 : Audit := .split 13 (2,true) (byMove [
.cycle 31 2 false (7),
.cycle 15 2 false (1),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.last 14 (4,true),
.last 24 (4,true),
.last 30 (4,true),
.last 29 (4,true),
.cycle 67 2 false (15),
.last 22 (4,true),
.last 14 (4,true),
.last 28 (4,true),
.cycle 27 2 false (7),
.cycle 31 2 false (7),
.cycle 32 2 false (8),
.cycle 28 2 false (8),
.last 14 (4,true),
.cycle 12 2 true (0),
.last 48 (4,true),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.last 14 (4,true),
.cycle 2 15 true (0)
])
theorem kid11_part1208_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1208) = true := by rfl

def kid11_part1209 : Audit := .split 36 (4,true) (byMove [
.last 39 (2,true),
.cycle 0 48 true (-1),
.cycle 38 1 false (0),
.cycle 37 1 false (-1),
.cycle 37 2 false (-1),
.cycle 37 2 false (-1),
.cycle 39 20 true (3),
.cycle 5 38 true (0),
.last 37 (2,true),
.cycle 0 46 true (0),
.cycle 46 2 false (10),
.cycle 12 29 true (0),
.cycle 12 31 true (-1),
.last 38 (2,true),
.cycle 41 20 true (3),
.cycle 37 1 false (-1),
.cycle 37 2 false (-1),
.cycle 37 2 false (-1),
.cycle 39 20 true (3),
.cycle 5 38 true (0),
.last 37 (2,true),
.cycle 0 46 true (0),
.cycle 0 49 true (0),
.cycle 12 29 true (0)
])
theorem kid11_part1209_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1209) = true := by rfl

def kid11_part1210 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 15 2 false (1),
.last 14 (2,true),
.cycle 0 20 true (0),
.cycle 15 2 false (-1),
.cycle 11 4 true (0),
.cycle 0 20 true (0),
.cycle 15 21 true (3),
.last 14 (2,true),
.cycle 33 2 false (7),
.cycle 41 2 false (7),
.cycle 14 8 true (2),
.cycle 26 2 false (6),
.cycle 21 5 true (3),
.last 14 (2,true),
.cycle 28 2 false (8),
.cycle 15 2 false (-1),
.cycle 12 2 true (0),
.cycle 0 20 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 5 9 true (0),
.cycle 16 3 true (4),
.cycle 15 6 true (3)
])
theorem kid11_part1210_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1210) = true := by rfl

def kid11_part1211 : Audit := .split 18 (4,true) (byMove [
.last 21 (2,true),
.cycle 13 9 true (1),
.last 19 (2,true),
.cycle 14 10 true (2),
.cycle 23 2 false (-1),
.cycle 31 2 false (-1),
.cycle 12 23 true (0),
.cycle 15 10 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 13 10 true (1),
.cycle 16 3 true (4),
.cycle 20 5 true (4),
.cycle 15 5 true (3),
.last 19 (2,true),
.cycle 5 14 true (0),
.cycle 23 2 false (-1),
.cycle 14 5 true (2),
.cycle 14 21 true (2),
.cycle 14 8 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 15 6 true (3),
.cycle 16 3 true (4)
])
theorem kid11_part1211_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1211) = true := by rfl

def kid11_part1187 : Audit := .split 12 (5,true) (byMove [(kid11_part1188),(kid11_part1189),(kid11_part1190),(kid11_part1191),(kid11_part1192),(kid11_part1193),(kid11_part1194),(kid11_part1195),(kid11_part1196),(kid11_part1197),(kid11_part1198),(kid11_part1199),(kid11_part1200),(kid11_part1201),(kid11_part1202),(kid11_part1203),(kid11_part1204),(kid11_part1205),(kid11_part1206),(kid11_part1207),(kid11_part1208),(kid11_part1209),(kid11_part1210),(kid11_part1211)])

theorem kid11_part1187_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1187) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part1188),(kid11_part1189),(kid11_part1190),(kid11_part1191),(kid11_part1192),(kid11_part1193),(kid11_part1194),(kid11_part1195),(kid11_part1196),(kid11_part1197),(kid11_part1198),(kid11_part1199),(kid11_part1200),(kid11_part1201),(kid11_part1202),(kid11_part1203),(kid11_part1204),(kid11_part1205),(kid11_part1206),(kid11_part1207),(kid11_part1208),(kid11_part1209),(kid11_part1210),(kid11_part1211)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1188_checked

  · exact kid11_part1194_checked

  · exact kid11_part1200_checked

  · exact kid11_part1206_checked

  · exact kid11_part1189_checked

  · exact kid11_part1195_checked

  · exact kid11_part1201_checked

  · exact kid11_part1207_checked

  · exact kid11_part1190_checked

  · exact kid11_part1196_checked

  · exact kid11_part1202_checked

  · exact kid11_part1208_checked

  · exact kid11_part1191_checked

  · exact kid11_part1197_checked

  · exact kid11_part1203_checked

  · exact kid11_part1209_checked

  · exact kid11_part1192_checked

  · exact kid11_part1198_checked

  · exact kid11_part1204_checked

  · exact kid11_part1210_checked

  · exact kid11_part1193_checked

  · exact kid11_part1199_checked

  · exact kid11_part1205_checked

  · exact kid11_part1211_checked

def kid11_part1212 : Audit := .cycle 1 10 true (1)
theorem kid11_part1212_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1212) = true := by rfl

def kid11_part1213 : Audit := .cycle 7 3 true (3)
theorem kid11_part1213_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1213) = true := by rfl

def kid11_part1215 : Audit := .cycle 1 11 true (1)
theorem kid11_part1215_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1215) = true := by rfl

def kid11_part1216 : Audit := .cycle 7 4 true (3)
theorem kid11_part1216_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1216) = true := by rfl

def kid11_part1217 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 32 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 32 1 false (4),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 32 1 false (6),
.cycle 25 1 false (3),
.cycle 28 1 false (2),
.cycle 24 1 false (2),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.cycle 2 19 true (0),
.last 21 (4,true)
])
theorem kid11_part1217_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1217) = true := by rfl

def kid11_part1218 : Audit := .cycle 0 12 true (0)
theorem kid11_part1218_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1218) = true := by rfl

def kid11_part1219 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 2 11 true (1),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 2 11 true (1),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.last 19 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 18 3 false (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 14 (5,true)
])
theorem kid11_part1219_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1219) = true := by rfl

def kid11_part1220 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.cycle 2 11 true (1),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 28 1 false (4),
.cycle 0 21 true (0),
.cycle 2 11 true (1),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.cycle 19 3 false (1),
.cycle 0 14 true (0),
.cycle 18 1 false (2),
.last 18 (4,true),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 2 11 true (1),
.last 13 (4,true)
])
theorem kid11_part1220_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1220) = true := by rfl

def kid11_part1221 : Audit := .cycle 0 11 true (0)
theorem kid11_part1221_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1221) = true := by rfl

def kid11_part1222 : Audit := .cycle 1 10 true (1)
theorem kid11_part1222_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1222) = true := by rfl

def kid11_part1223 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 2 18 true (1),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 38 1 false (10),
.cycle 34 1 false (8),
.cycle 2 18 true (1),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.cycle 10 10 true (3),
.cycle 0 21 true (0),
.cycle 28 1 false (2),
.cycle 9 10 true (3),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 256, 16384, 128, 256, 32768, 2, 256, 262144, 128, 256, 8, 32, 256, 16384, 262144],[2, 32, 4, 1, 262144, 4, 8192, 131072, 16384, 4096, 262144, 262148, 2, 32, 4, 1, 262144, 262144, 262144],264192⟩,
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 2 18 true (1),
.last 20 (4,true)
])
theorem kid11_part1223_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1223) = true := by rfl

def kid11_part1224 : Audit := .cycle 3 8 true (1)
theorem kid11_part1224_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1224) = true := by rfl

def kid11_part1225 : Audit := .cycle 2 10 true (1)
theorem kid11_part1225_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1225) = true := by rfl

def kid11_part1226 : Audit := .cycle 8 3 true (3)
theorem kid11_part1226_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1226) = true := by rfl

def kid11_part1227 : Audit := .cycle 6 5 true (2)
theorem kid11_part1227_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1227) = true := by rfl

def kid11_part1228 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 2 12 true (1),
.last 24 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 40 1 false (8),
.cycle 36 1 false (10),
.cycle 2 12 true (1),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.cycle 10 4 true (3),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.cycle 9 4 true (3),
.last 24 (4,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 2 12 true (1),
.last 14 (4,true)
])
theorem kid11_part1228_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1228) = true := by rfl

def kid11_part1229 : Audit := .cycle 1 14 true (1)
theorem kid11_part1229_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1229) = true := by rfl

def kid11_part1230 : Audit := .cycle 1 12 true (1)
theorem kid11_part1230_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1230) = true := by rfl

def kid11_part1231 : Audit := .split 11 (4,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.last 16 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (3),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.last 12 (5,true),
.last 14 (5,true),
.last 19 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.cycle 18 3 false (0),
.last 16 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.cycle 2 12 true (1),
.last 12 (5,true)
])
theorem kid11_part1231_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1231) = true := by rfl

def kid11_part1232 : Audit := .split 11 (5,true) (byMove [
.cycle 10 8 true (2),
.cycle 0 15 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 24 (4,true),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 8 5 true (3),
.cycle 13 9 true (3),
.cycle 19 3 false (1),
.cycle 1 14 true (1),
.cycle 18 1 false (2),
.last 18 (4,true),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 10 2 true (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.last 14 (4,true)
])
theorem kid11_part1232_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1232) = true := by rfl

def kid11_part1233 : Audit := .cycle 0 11 true (0)
theorem kid11_part1233_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1233) = true := by rfl

def kid11_part1234 : Audit := .cycle 1 10 true (1)
theorem kid11_part1234_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1234) = true := by rfl

def kid11_part1235 : Audit := .cycle 2 9 true (1)
theorem kid11_part1235_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1235) = true := by rfl

def kid11_part1236 : Audit := .cycle 1 13 true (1)
theorem kid11_part1236_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1236) = true := by rfl

def kid11_part1237 : Audit := .cycle 2 10 true (1)
theorem kid11_part1237_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1237) = true := by rfl

def kid11_part1238 : Audit := .split 12 (4,true) (byMove [
.cycle 10 5 true (3),
.last 17 (5,true),
.last 23 (5,true),
.cycle 7 8 true (3),
.last 21 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 13 true (1),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 14 (5,true),
.cycle 5 8 true (1),
.last 16 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 3 true (4),
.cycle 0 14 true (0),
.cycle 2 13 true (1),
.last 13 (5,true)
])
theorem kid11_part1238_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1238) = true := by rfl

def kid11_part1214 : Audit := .split 10 (2,true) (byMove [(kid11_part1215),(kid11_part1216),(kid11_part1217),(kid11_part1218),(kid11_part1219),(kid11_part1220),(kid11_part1221),(kid11_part1222),(kid11_part1223),(kid11_part1224),(kid11_part1225),(kid11_part1226),(kid11_part1227),(kid11_part1228),(kid11_part1229),(kid11_part1230),(kid11_part1231),(kid11_part1232),(kid11_part1233),(kid11_part1234),(kid11_part1235),(kid11_part1236),(kid11_part1237),(kid11_part1238)])

theorem kid11_part1214_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1214) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid11_part1215),(kid11_part1216),(kid11_part1217),(kid11_part1218),(kid11_part1219),(kid11_part1220),(kid11_part1221),(kid11_part1222),(kid11_part1223),(kid11_part1224),(kid11_part1225),(kid11_part1226),(kid11_part1227),(kid11_part1228),(kid11_part1229),(kid11_part1230),(kid11_part1231),(kid11_part1232),(kid11_part1233),(kid11_part1234),(kid11_part1235),(kid11_part1236),(kid11_part1237),(kid11_part1238)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1215_checked

  · exact kid11_part1221_checked

  · exact kid11_part1227_checked

  · exact kid11_part1233_checked

  · exact kid11_part1216_checked

  · exact kid11_part1222_checked

  · exact kid11_part1228_checked

  · exact kid11_part1234_checked

  · exact kid11_part1217_checked

  · exact kid11_part1223_checked

  · exact kid11_part1229_checked

  · exact kid11_part1235_checked

  · exact kid11_part1218_checked

  · exact kid11_part1224_checked

  · exact kid11_part1230_checked

  · exact kid11_part1236_checked

  · exact kid11_part1219_checked

  · exact kid11_part1225_checked

  · exact kid11_part1231_checked

  · exact kid11_part1237_checked

  · exact kid11_part1220_checked

  · exact kid11_part1226_checked

  · exact kid11_part1232_checked

  · exact kid11_part1238_checked

def kid11_part1239 : Audit := .cycle 0 11 true (0)
theorem kid11_part1239_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1239) = true := by rfl

def kid11_part1241 : Audit := .cycle 1 11 true (1)
theorem kid11_part1241_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1241) = true := by rfl

def kid11_part1242 : Audit := .cycle 7 4 true (3)
theorem kid11_part1242_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1242) = true := by rfl

def kid11_part1243 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 12 1 true (4),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.last 15 (5,true),
.cycle 0 14 true (0),
.last 17 (5,true),
.cycle 20 1 false (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.last 21 (5,true)
])
theorem kid11_part1243_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1243) = true := by rfl

def kid11_part1244 : Audit := .cycle 0 12 true (0)
theorem kid11_part1244_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1244) = true := by rfl

def kid11_part1245 : Audit := .cycle 12 1 true (2)
theorem kid11_part1245_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1245) = true := by rfl

def kid11_part1246 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 22 (2,true),
.cycle 0 21 true (0),
.cycle 12 1 true (4),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 1 false (2),
.cycle 20 3 false (-1),
.cycle 16 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 12 1 true (4),
.cycle 19 6 false (1)
])
theorem kid11_part1246_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1246) = true := by rfl

def kid11_part1247 : Audit := .cycle 0 11 true (0)
theorem kid11_part1247_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1247) = true := by rfl

def kid11_part1248 : Audit := .cycle 1 10 true (1)
theorem kid11_part1248_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1248) = true := by rfl

def kid11_part1249 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 19 1 true (5),
.cycle 8 11 true (3),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.last 32 (2,true),
.cycle 34 1 false (8),
.cycle 19 1 true (7),
.cycle 8 11 true (3),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 28 1 false (2),
.cycle 9 10 true (3),
.last 22 (2,true),
.cycle 0 19 true (0),
.cycle 1 18 true (1),
.cycle 2 17 true (1),
.cycle 1 21 true (1),
.cycle 19 1 true (7),
.last 21 (2,true)
])
theorem kid11_part1249_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1249) = true := by rfl

def kid11_part1250 : Audit := .cycle 3 8 true (1)
theorem kid11_part1250_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1250) = true := by rfl

def kid11_part1251 : Audit := .cycle 11 1 true (5)
theorem kid11_part1251_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1251) = true := by rfl

def kid11_part1252 : Audit := .cycle 8 3 true (3)
theorem kid11_part1252_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1252) = true := by rfl

def kid11_part1253 : Audit := .cycle 6 5 true (2)
theorem kid11_part1253_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1253) = true := by rfl

def kid11_part1254 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 13 1 true (3),
.last 26 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 24 (2,true),
.cycle 36 1 false (10),
.cycle 13 1 true (5),
.cycle 8 5 true (3),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 20 1 false (2),
.cycle 9 4 true (3),
.last 26 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 13 1 true (5),
.last 16 (2,true)
])
theorem kid11_part1254_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1254) = true := by rfl

def kid11_part1255 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 13 9 true (1),
.last 16 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 23 (5,true),
.cycle 0 13 true (0),
.cycle 0 15 true (0),
.last 12 (5,true),
.last 14 (5,true),
.last 15 (5,true),
.cycle 1 14 true (1),
.last 17 (5,true),
.last 23 (5,true),
.last 16 (5,true),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.last 12 (5,true)
])
theorem kid11_part1255_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1255) = true := by rfl

def kid11_part1256 : Audit := .cycle 1 12 true (1)
theorem kid11_part1256_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1256) = true := by rfl

def kid11_part1257 : Audit := .cycle 17 3 false (1)
theorem kid11_part1257_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1257) = true := by rfl

def kid11_part1258 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.cycle 18 9 false (0),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 24 5 false (0),
.cycle 8 5 true (3),
.cycle 13 9 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 1 false (2),
.cycle 20 3 false (-1),
.cycle 16 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 10 2 true (3),
.cycle 11 5 true (3)
])
theorem kid11_part1258_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1258) = true := by rfl

def kid11_part1259 : Audit := .cycle 0 11 true (0)
theorem kid11_part1259_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1259) = true := by rfl

def kid11_part1260 : Audit := .cycle 1 10 true (1)
theorem kid11_part1260_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1260) = true := by rfl

def kid11_part1261 : Audit := .cycle 2 9 true (1)
theorem kid11_part1261_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1261) = true := by rfl

def kid11_part1262 : Audit := .cycle 1 13 true (1)
theorem kid11_part1262_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1262) = true := by rfl

def kid11_part1263 : Audit := .cycle 11 1 true (5)
theorem kid11_part1263_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1263) = true := by rfl

def kid11_part1264 : Audit := .split 13 (5,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (4),
.cycle 22 8 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 33 (2,true),
.cycle 3 11 true (1),
.cycle 14 1 true (6),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 17 (2,true),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (4),
.cycle 20 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 14 1 true (6),
.cycle 11 3 true (4)
])
theorem kid11_part1264_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1264) = true := by rfl

def kid11_part1240 : Audit := .split 10 (4,true) (byMove [(kid11_part1241),(kid11_part1242),(kid11_part1243),(kid11_part1244),(kid11_part1245),(kid11_part1246),(kid11_part1247),(kid11_part1248),(kid11_part1249),(kid11_part1250),(kid11_part1251),(kid11_part1252),(kid11_part1253),(kid11_part1254),(kid11_part1255),(kid11_part1256),(kid11_part1257),(kid11_part1258),(kid11_part1259),(kid11_part1260),(kid11_part1261),(kid11_part1262),(kid11_part1263),(kid11_part1264)])

theorem kid11_part1240_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1240) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1241),(kid11_part1242),(kid11_part1243),(kid11_part1244),(kid11_part1245),(kid11_part1246),(kid11_part1247),(kid11_part1248),(kid11_part1249),(kid11_part1250),(kid11_part1251),(kid11_part1252),(kid11_part1253),(kid11_part1254),(kid11_part1255),(kid11_part1256),(kid11_part1257),(kid11_part1258),(kid11_part1259),(kid11_part1260),(kid11_part1261),(kid11_part1262),(kid11_part1263),(kid11_part1264)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1241_checked

  · exact kid11_part1247_checked

  · exact kid11_part1253_checked

  · exact kid11_part1259_checked

  · exact kid11_part1242_checked

  · exact kid11_part1248_checked

  · exact kid11_part1254_checked

  · exact kid11_part1260_checked

  · exact kid11_part1243_checked

  · exact kid11_part1249_checked

  · exact kid11_part1255_checked

  · exact kid11_part1261_checked

  · exact kid11_part1244_checked

  · exact kid11_part1250_checked

  · exact kid11_part1256_checked

  · exact kid11_part1262_checked

  · exact kid11_part1245_checked

  · exact kid11_part1251_checked

  · exact kid11_part1257_checked

  · exact kid11_part1263_checked

  · exact kid11_part1246_checked

  · exact kid11_part1252_checked

  · exact kid11_part1258_checked

  · exact kid11_part1264_checked

def kid11_part1266 : Audit := .cycle 1 11 true (1)
theorem kid11_part1266_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1266) = true := by rfl

def kid11_part1267 : Audit := .cycle 7 4 true (3)
theorem kid11_part1267_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1267) = true := by rfl

def kid11_part1268 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 21 1 false (3),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.last 14 (4,true),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.cycle 25 1 false (3),
.cycle 0 14 true (0),
.cycle 19 1 false (3),
.last 18 (4,true),
.cycle 18 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.last 14 (4,true),
.last 13 (4,true)
])
theorem kid11_part1268_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1268) = true := by rfl

def kid11_part1269 : Audit := .cycle 0 12 true (0)
theorem kid11_part1269_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1269) = true := by rfl

def kid11_part1270 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 19 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 36 1 false (8),
.cycle 11 4 true (3),
.cycle 8 4 true (3),
.cycle 6 12 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 19 4 false (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 11 4 true (3),
.cycle 10 4 true (3)
])
theorem kid11_part1270_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1270) = true := by rfl

def kid11_part1271 : Audit := .cycle 15 4 false (1)
theorem kid11_part1271_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1271) = true := by rfl

def kid11_part1272 : Audit := .cycle 0 11 true (0)
theorem kid11_part1272_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1272) = true := by rfl

def kid11_part1273 : Audit := .cycle 1 10 true (1)
theorem kid11_part1273_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1273) = true := by rfl

def kid11_part1274 : Audit := .split 32 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 292, 2048, 4, 128, 256, 8, 2, 2048, 4096, 4096],[2, 32, 256, 1, 4096, 4, 2, 32, 256, 1, 4096, 4, 4096],7184⟩,
.cycle 47 81 true (3),
.cycle 34 1 false (4),
.cycle 33 1 false (3),
.last 35 (4,true),
.cycle 15 22 true (0),
.cycle 0 37 true (0),
.cycle 49 1 false (13),
.cycle 38 1 false (10),
.cycle 38 1 false (10),
.last 33 (4,true),
.cycle 49 1 false (13),
.cycle 34 29 true (4),
.cycle 58 1 false (10),
.cycle 0 41 true (0),
.cycle 33 1 false (3),
.cycle 37 28 true (5),
.last 38 (4,true),
.cycle 0 37 true (0),
.cycle 1 71 true (0),
.cycle 2 35 true (0),
.cycle 0 91 true (0),
.last 33 (4,true),
.last 38 (4,true)
])
theorem kid11_part1274_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1274) = true := by rfl

def kid11_part1275 : Audit := .cycle 3 8 true (1)
theorem kid11_part1275_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1275) = true := by rfl

def kid11_part1276 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 38 1 false (4),
.last 18 (2,true),
.cycle 24 3 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4),
.cycle 10 6 true (4),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 33 1 false (3),
.cycle 9 8 true (3),
.cycle 23 6 false (1),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4)
])
theorem kid11_part1276_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1276) = true := by rfl

def kid11_part1277 : Audit := .cycle 8 3 true (3)
theorem kid11_part1277_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1277) = true := by rfl

def kid11_part1278 : Audit := .cycle 6 5 true (2)
theorem kid11_part1278_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1278) = true := by rfl

def kid11_part1279 : Audit := .split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 28 1 false (2),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 23 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 11 10 true (3),
.cycle 3 12 true (1),
.last 17 (4,true),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 11 4 true (3),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 23 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.last 17 (4,true),
.last 16 (4,true)
])
theorem kid11_part1279_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1279) = true := by rfl

def kid11_part1280 : Audit := .split 11 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 0 15 true (0),
.cycle 35 1 false (7),
.cycle 21 1 false (1),
.last 14 (4,true),
.cycle 0 33 true (-1),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 0 31 true (0),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 0 15 true (0),
.cycle 0 17 true (0),
.cycle 1 18 true (1),
.cycle 1 14 true (1),
.cycle 32 1 false (6),
.last 18 (4,true),
.cycle 32 4 false (8),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 10 2 true (3)
])
theorem kid11_part1280_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1280) = true := by rfl

def kid11_part1281 : Audit := .cycle 1 12 true (1)
theorem kid11_part1281_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1281) = true := by rfl

def kid11_part1282 : Audit := .split 11 (4,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 4 true (3),
.cycle 9 4 true (3),
.cycle 9 12 true (2),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 21 1 false (1),
.cycle 18 3 false (0),
.cycle 17 4 false (0),
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 11 4 true (3),
.cycle 10 2 true (3)
])
theorem kid11_part1282_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1282) = true := by rfl

def kid11_part1283 : Audit := .cycle 15 4 false (1)
theorem kid11_part1283_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1283) = true := by rfl

def kid11_part1284 : Audit := .cycle 0 11 true (0)
theorem kid11_part1284_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1284) = true := by rfl

def kid11_part1285 : Audit := .cycle 1 10 true (1)
theorem kid11_part1285_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1285) = true := by rfl

def kid11_part1286 : Audit := .cycle 2 9 true (1)
theorem kid11_part1286_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1286) = true := by rfl

def kid11_part1287 : Audit := .cycle 1 13 true (1)
theorem kid11_part1287_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1287) = true := by rfl

def kid11_part1288 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 7 12 true (3),
.last 14 (2,true),
.cycle 7 9 true (3),
.cycle 22 3 false (0),
.cycle 9 6 true (3),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4),
.cycle 10 6 true (4),
.cycle 10 8 true (4),
.last 14 (2,true),
.cycle 5 9 true (1),
.cycle 24 5 false (2),
.cycle 13 2 true (4),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 11 4 true (5),
.cycle 10 4 true (4)
])
theorem kid11_part1288_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1288) = true := by rfl

def kid11_part1289 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 10 7 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 20 3 false (0),
.cycle 21 8 false (2),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 4 true (4),
.cycle 10 3 true (4),
.cycle 14 5 true (4),
.cycle 10 5 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 32, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 10 5 true (3),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 4 true (4),
.cycle 10 3 true (4)
])
theorem kid11_part1289_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1289) = true := by rfl

def kid11_part1265 : Audit := .split 10 (5,true) (byMove [(kid11_part1266),(kid11_part1267),(kid11_part1268),(kid11_part1269),(kid11_part1270),(kid11_part1271),(kid11_part1272),(kid11_part1273),(kid11_part1274),(kid11_part1275),(kid11_part1276),(kid11_part1277),(kid11_part1278),(kid11_part1279),(kid11_part1280),(kid11_part1281),(kid11_part1282),(kid11_part1283),(kid11_part1284),(kid11_part1285),(kid11_part1286),(kid11_part1287),(kid11_part1288),(kid11_part1289)])

theorem kid11_part1265_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1265) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (5,true) (some mv)) (byMove [(kid11_part1266),(kid11_part1267),(kid11_part1268),(kid11_part1269),(kid11_part1270),(kid11_part1271),(kid11_part1272),(kid11_part1273),(kid11_part1274),(kid11_part1275),(kid11_part1276),(kid11_part1277),(kid11_part1278),(kid11_part1279),(kid11_part1280),(kid11_part1281),(kid11_part1282),(kid11_part1283),(kid11_part1284),(kid11_part1285),(kid11_part1286),(kid11_part1287),(kid11_part1288),(kid11_part1289)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1266_checked

  · exact kid11_part1272_checked

  · exact kid11_part1278_checked

  · exact kid11_part1284_checked

  · exact kid11_part1267_checked

  · exact kid11_part1273_checked

  · exact kid11_part1279_checked

  · exact kid11_part1285_checked

  · exact kid11_part1268_checked

  · exact kid11_part1274_checked

  · exact kid11_part1280_checked

  · exact kid11_part1286_checked

  · exact kid11_part1269_checked

  · exact kid11_part1275_checked

  · exact kid11_part1281_checked

  · exact kid11_part1287_checked

  · exact kid11_part1270_checked

  · exact kid11_part1276_checked

  · exact kid11_part1282_checked

  · exact kid11_part1288_checked

  · exact kid11_part1271_checked

  · exact kid11_part1277_checked

  · exact kid11_part1283_checked

  · exact kid11_part1289_checked

def kid11_part1001 : Audit := .split 9 (4,false) (byMove [(kid11_part1002),(kid11_part1027),(kid11_part1028),(kid11_part1053),(kid11_part1054),(kid11_part1055),(kid11_part1056),(kid11_part1057),(kid11_part1058),(kid11_part1083),(kid11_part1084),(kid11_part1109),(kid11_part1110),(kid11_part1111),(kid11_part1136),(kid11_part1137),(kid11_part1162),(kid11_part1187),(kid11_part1212),(kid11_part1213),(kid11_part1214),(kid11_part1239),(kid11_part1240),(kid11_part1265)])

theorem kid11_part1001_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (kid11_part1001) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1002),(kid11_part1027),(kid11_part1028),(kid11_part1053),(kid11_part1054),(kid11_part1055),(kid11_part1056),(kid11_part1057),(kid11_part1058),(kid11_part1083),(kid11_part1084),(kid11_part1109),(kid11_part1110),(kid11_part1111),(kid11_part1136),(kid11_part1137),(kid11_part1162),(kid11_part1187),(kid11_part1212),(kid11_part1213),(kid11_part1214),(kid11_part1239),(kid11_part1240),(kid11_part1265)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1002_checked

  · exact kid11_part1056_checked

  · exact kid11_part1110_checked

  · exact kid11_part1212_checked

  · exact kid11_part1027_checked

  · exact kid11_part1057_checked

  · exact kid11_part1111_checked

  · exact kid11_part1213_checked

  · exact kid11_part1028_checked

  · exact kid11_part1058_checked

  · exact kid11_part1136_checked

  · exact kid11_part1214_checked

  · exact kid11_part1053_checked

  · exact kid11_part1083_checked

  · exact kid11_part1137_checked

  · exact kid11_part1239_checked

  · exact kid11_part1054_checked

  · exact kid11_part1084_checked

  · exact kid11_part1162_checked

  · exact kid11_part1240_checked

  · exact kid11_part1055_checked

  · exact kid11_part1109_checked

  · exact kid11_part1187_checked

  · exact kid11_part1265_checked

def kid11_part1291 : Audit := .split 15 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 10 7 false (2),
.cycle 19 1 false (-1),
.cycle 0 24 true (-1),
.split 16 (4,true) (byMove [
.cycle 0 40 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 0 33 true (-1),
.last 18 (4,false),
.cycle 0 41 true (-2),
.cycle 0 24 true (-1),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 33, 1, 64],80⟩,
.cycle 0 49 true (-2),
.cycle 0 33 true (-1),
.last 17 (4,false),
.cycle 10 7 false (2),
.cycle 19 1 false (1),
.cycle 32 3 false (1),
.last 18 (4,false),
.cycle 22 1 false (0),
.last 18 (4,false),
.cycle 12 5 false (1),
.cycle 14 24 true (0),
.cycle 14 25 true (0),
.cycle 0 36 true (-1),
.cycle 0 61 true (-1),
.last 17 (4,false),
.cycle 11 12 true (-1)
]),
.cycle 0 40 true (-1),
.cycle 0 19 true (-1),
.cycle 0 52 true (-1),
.cycle 0 69 true (-1),
.cycle 0 32 true (-1),
.split 16 (4,true) (byMove [
.cycle 14 21 true (0),
.last 49 (4,false),
.last 27 (4,false),
.proven (BB6.Agent11Raw39B0RBPumps.M900.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M900.never m hm),
.last 17 (4,false),
.last 22 (4,false),
.cycle 0 32 true (-1),
.cycle 0 19 true (-1),
.last 35 (4,false),
.cycle 0 54 true (-1),
.last 19 (4,false),
.last 21 (4,false),
.last 23 (4,false),
.last 25 (4,false),
.cycle 0 36 true (-1),
.last 25 (4,false),
.last 17 (4,false),
.cycle 11 12 true (-1),
.cycle 0 48 true (-1),
.cycle 14 19 true (0),
.last 38 (4,false),
.cycle 0 41 true (-1),
.last 19 (4,false),
.last 21 (4,false)
]),
.cycle 14 21 true (0),
.cycle 0 25 true (-1),
.cycle 14 33 true (0),
.cycle 0 33 true (-2),
.cycle 0 53 true (-1),
.split 16 (4,true) (byMove [
.cycle 13 8 true (-1),
.cycle 18 1 false (0),
.last 18 (4,false),
.cycle 51 1 false (3),
.last 18 (4,false),
.cycle 0 25 true (-2),
.cycle 0 53 true (-1),
.cycle 0 25 true (-1),
.last 18 (4,false),
.cycle 0 21 true (-1),
.last 21 (4,false),
.cycle 14 33 true (0),
.cycle 0 41 true (-1),
.cycle 12 6 true (-1),
.last 18 (4,false),
.cycle 0 29 true (-1),
.last 18 (4,false),
.cycle 12 5 false (1),
.cycle 0 62 true (-1),
.cycle 14 25 true (0),
.cycle 15 2 true (0),
.cycle 0 21 true (-1),
.last 21 (4,false),
.far true 1 ⟨0,[0, 0],[33, 33, 41, 8, 64, 32, 64],[33, 33, 16, 33, 33, 1, 64],80⟩
]),
.cycle 12 8 true (-1),
.cycle 0 19 true (-1),
.cycle 14 20 true (0),
.cycle 14 17 true (0),
.cycle 14 11 true (0),
.split 16 (4,true) (byMove [
.last 46 (4,false),
.cycle 10 16 true (-1),
.last 18 (4,false),
.cycle 14 21 true (0),
.last 20 (4,false),
.last 53 (4,false),
.cycle 14 11 true (0),
.cycle 0 19 true (-1),
.cycle 0 27 true (-1),
.last 45 (4,false),
.last 19 (4,false),
.last 21 (4,false),
.last 23 (4,false),
.cycle 14 25 true (0),
.cycle 15 2 true (1),
.cycle 0 21 true (-1),
.last 20 (4,false),
.last 31 (4,false),
.cycle 0 48 true (-1),
.cycle 14 19 true (0),
.cycle 14 17 true (0),
.cycle 0 41 true (-1),
.last 19 (4,false),
.last 21 (4,false)
]),
.cycle 42 5 true (5)
])
theorem kid11_part1291_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1291) = true := by rfl

def kid11_part1292 : Audit := .cycle 0 60 true (-2)
theorem kid11_part1292_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1292) = true := by rfl

def kid11_part1293 : Audit := .cycle 14 1 false (0)
theorem kid11_part1293_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1293) = true := by rfl

def kid11_part1294 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1294_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1294) = true := by rfl

def kid11_part1296 : Audit := .cycle 0 22 true (-2)
theorem kid11_part1296_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1296) = true := by rfl

def kid11_part1297 : Audit := .cycle 57 1 false (5)
theorem kid11_part1297_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1297) = true := by rfl

def kid11_part1298 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1298_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1298) = true := by rfl

def kid11_part1299 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1299_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1299) = true := by rfl

def kid11_part1300 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1300_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1300) = true := by rfl

def kid11_part1301 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1301_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1301) = true := by rfl

def kid11_part1302 : Audit := .cycle 0 22 true (-1)
theorem kid11_part1302_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1302) = true := by rfl

def kid11_part1303 : Audit := .split 15 (2,true) (byMove [
.cycle 33 1 false (7),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 24 true (-1),
.last 16 (4,true),
.cycle 0 111 true (-1),
.cycle 6 38 true (-1),
.cycle 46 25 true (5),
.cycle 77 1 false (15),
.cycle 0 87 true (-1),
.last 16 (4,true),
.cycle 16 32 true (1),
.cycle 33 1 false (7),
.cycle 41 1 false (7),
.cycle 36 1 false (8),
.cycle 32 1 false (8),
.last 16 (4,true),
.cycle 12 4 true (-1),
.last 34 (4,true),
.last 33 (4,true),
.last 30 (4,true),
.last 24 (4,true),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part1303_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1303) = true := by rfl

def kid11_part1304 : Audit := .cycle 21 1 false (5)
theorem kid11_part1304_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1304) = true := by rfl

def kid11_part1305 : Audit := .cycle 14 1 false (0)
theorem kid11_part1305_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1305) = true := by rfl

def kid11_part1306 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 36 1 true (4),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 25 1 true (3),
.cycle 16 1 false (0),
.cycle 19 1 true (3),
.cycle 28 1 false (8),
.last 16 (2,true),
.cycle 19 1 false (5),
.cycle 19 1 true (5),
.cycle 21 1 true (3),
.cycle 25 1 true (3),
.last 17 (2,true),
.cycle 21 1 true (3),
.cycle 16 1 false (0),
.cycle 14 2 true (0),
.cycle 16 1 false (0),
.cycle 19 1 true (3),
.cycle 1 20 true (-1),
.last 16 (2,true),
.cycle 5 11 true (-1),
.cycle 19 1 true (5),
.cycle 31 5 true (2)
])
theorem kid11_part1306_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1306) = true := by rfl

def kid11_part1307 : Audit := .cycle 14 1 false (0)
theorem kid11_part1307_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1307) = true := by rfl

def kid11_part1308 : Audit := .cycle 10 6 false (2)
theorem kid11_part1308_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1308) = true := by rfl

def kid11_part1309 : Audit := .split 15 (2,true) (byMove [
.cycle 26 132 true (-3),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 35 true (-2),
.last 16 (4,true),
.cycle 12 4 false (0),
.last 43 (4,true),
.cycle 12 42 true (-2),
.cycle 17 11 true (1),
.cycle 57 1 false (5),
.last 19 (4,true),
.cycle 10 6 false (2),
.cycle 18 1 false (0),
.cycle 12 5 false (0),
.cycle 48 1 false (8),
.cycle 40 1 false (8),
.last 16 (4,true),
.cycle 12 4 false (0),
.last 48 (4,true),
.last 47 (4,true),
.cycle 2 22 true (-2),
.cycle 12 109 true (-2),
.cycle 12 9 false (0),
.last 18 (4,true)
])
theorem kid11_part1309_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1309) = true := by rfl

def kid11_part1310 : Audit := .split 20 (2,true) (byMove [
.cycle 0 71 true (-2),
.cycle 0 32 true (-2),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 10 16 true (-2),
.cycle 21 1 false (-1),
.cycle 0 56 true (-2),
.cycle 22 1 false (2),
.cycle 32 1 false (8),
.cycle 0 28 true (-2),
.last 21 (4,true),
.cycle 0 38 true (-2),
.cycle 16 5 false (2),
.cycle 10 20 true (-2),
.cycle 31 1 false (5),
.cycle 21 1 false (-1),
.cycle 26 1 false (2),
.cycle 21 1 false (-1),
.last 38 (4,true),
.cycle 10 12 true (-2),
.last 40 (4,true),
.cycle 15 28 true (-1),
.last 21 (4,true),
.last 22 (4,true)
])
theorem kid11_part1310_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1310) = true := by rfl

def kid11_part1311 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1311_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1311) = true := by rfl

def kid11_part1312 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1312_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1312) = true := by rfl

def kid11_part1313 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1313_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1313) = true := by rfl

def kid11_part1314 : Audit := .split 35 (4,true) (byMove [
.cycle 37 22 true (3),
.cycle 42 1 false (0),
.last 36 (2,true),
.last 39 (2,true),
.last 58 (2,true),
.cycle 40 1 false (-2),
.cycle 14 22 true (0),
.last 37 (2,true),
.cycle 19 20 true (3),
.cycle 36 32 true (2),
.cycle 38 18 true (6),
.cycle 44 1 false (0),
.cycle 45 1 false (1),
.last 41 (2,true),
.last 36 (2,true),
.last 39 (2,true),
.last 51 (2,true),
.cycle 40 1 false (-2),
.cycle 14 22 true (0),
.last 37 (2,true),
.cycle 19 20 true (3),
.cycle 15 24 true (1),
.cycle 19 38 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 1, 34, 64],[2, 32, 64, 1, 32, 34, 64],64⟩
])
theorem kid11_part1314_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1314) = true := by rfl

def kid11_part1315 : Audit := .split 15 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 0, 8192, 16384, 512, 16418, 8192, 16384, 33554432, 67108864, 2097152, 128, 33554432, 1140850688, 33554432, 67108864, 134217728, 2048, 33554432, 1140850688, 33554432, 67108864, 134217728, 1711276032, 33554432, 1140850688, 1073741824],[2, 32, 16384, 1, 1073741824, 16384, 128, 2048, 67109120, 64, 1073741824, 1140850688, 524288, 8388608, 16384, 262144, 1073741824, 1073741824, 33554432, 536870912, 67108864, 16777216, 1073741824, 67108864, 33554432, 536870912, 67108864, 16777216, 1073741824, 1140850688, 1073741824],2145334336⟩,
.cycle 10 7 false (2),
.cycle 19 1 false (-1),
.cycle 0 24 true (-1),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 19 true (-1),
.last 34 (4,true),
.cycle 1 69 true (-1),
.last 25 (4,true),
.last 16 (4,true),
.last 34 (4,true),
.cycle 1 25 true (-1),
.last 46 (4,true),
.cycle 1 33 true (-2),
.cycle 1 53 true (-1),
.last 16 (4,true),
.last 17 (4,true),
.cycle 1 19 true (-1),
.last 33 (4,true),
.last 30 (4,true),
.last 24 (4,true),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part1315_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1315) = true := by rfl

def kid11_part1316 : Audit := .cycle 0 60 true (-2)
theorem kid11_part1316_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1316) = true := by rfl

def kid11_part1317 : Audit := .cycle 36 1 false (8)
theorem kid11_part1317_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1317) = true := by rfl

def kid11_part1318 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 24 true (-1),
.cycle 57 1 true (-5),
.cycle 18 1 false (-2),
.cycle 19 1 true (3),
.last 36 (2,true),
.last 16 (2,true),
.cycle 26 1 false (0),
.cycle 19 1 true (5),
.cycle 21 1 true (3),
.cycle 25 1 true (3),
.cycle 33 1 true (3),
.last 16 (2,true),
.cycle 53 1 true (7),
.cycle 16 3 false (0),
.cycle 18 1 false (-2),
.cycle 19 1 true (3),
.last 35 (2,true),
.last 16 (2,true),
.cycle 0 34 true (-1),
.cycle 19 1 true (5),
.cycle 11 13 false (2)
])
theorem kid11_part1318_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1318) = true := by rfl

def kid11_part1319 : Audit := .cycle 11 3 false (1)
theorem kid11_part1319_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1319) = true := by rfl

def kid11_part1295 : Audit := .split 13 (4,false) (byMove [(kid11_part1296),(kid11_part1297),(kid11_part1298),(kid11_part1299),(kid11_part1300),(kid11_part1301),(kid11_part1302),(kid11_part1303),(kid11_part1304),(kid11_part1305),(kid11_part1306),(kid11_part1307),(kid11_part1308),(kid11_part1309),(kid11_part1310),(kid11_part1311),(kid11_part1312),(kid11_part1313),(kid11_part1314),(kid11_part1315),(kid11_part1316),(kid11_part1317),(kid11_part1318),(kid11_part1319)])

theorem kid11_part1295_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1295) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1296),(kid11_part1297),(kid11_part1298),(kid11_part1299),(kid11_part1300),(kid11_part1301),(kid11_part1302),(kid11_part1303),(kid11_part1304),(kid11_part1305),(kid11_part1306),(kid11_part1307),(kid11_part1308),(kid11_part1309),(kid11_part1310),(kid11_part1311),(kid11_part1312),(kid11_part1313),(kid11_part1314),(kid11_part1315),(kid11_part1316),(kid11_part1317),(kid11_part1318),(kid11_part1319)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1296_checked

  · exact kid11_part1302_checked

  · exact kid11_part1308_checked

  · exact kid11_part1314_checked

  · exact kid11_part1297_checked

  · exact kid11_part1303_checked

  · exact kid11_part1309_checked

  · exact kid11_part1315_checked

  · exact kid11_part1298_checked

  · exact kid11_part1304_checked

  · exact kid11_part1310_checked

  · exact kid11_part1316_checked

  · exact kid11_part1299_checked

  · exact kid11_part1305_checked

  · exact kid11_part1311_checked

  · exact kid11_part1317_checked

  · exact kid11_part1300_checked

  · exact kid11_part1306_checked

  · exact kid11_part1312_checked

  · exact kid11_part1318_checked

  · exact kid11_part1301_checked

  · exact kid11_part1307_checked

  · exact kid11_part1313_checked

  · exact kid11_part1319_checked

def kid11_part1320 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1320_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1320) = true := by rfl

def kid11_part1321 : Audit := .cycle 24 1 false (8)
theorem kid11_part1321_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1321) = true := by rfl

def kid11_part1322 : Audit := .cycle 24 1 false (8)
theorem kid11_part1322_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1322) = true := by rfl

def kid11_part1323 : Audit := .split 13 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 64, 4, 64],[2, 32, 4, 1, 64, 4, 64],80⟩,
.cycle 12 31 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.split 14 (4,false) (byMove [
.cycle 12 35 true (-1),
.cycle 34 1 false (6),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 17 (4,true),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 16 (4,true),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.last 17 (4,true),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 17 (4,true),
.cycle 12 31 true (0),
.cycle 32 1 false (8),
.last 16 (4,true),
.cycle 11 4 true (0)
]),
.cycle 14 1 false (0),
.cycle 18 1 false (6),
.cycle 24 1 false (8),
.cycle 18 1 false (6),
.cycle 17 1 false (5),
.split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.last 43 (4,false),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 17 1 false (5),
.cycle 18 1 false (6),
.cycle 18 1 false (6),
.cycle 24 1 false (8),
.last 17 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 0 54 true (0),
.last 27 (4,false),
.last 34 (4,false),
.cycle 0 51 true (0),
.last 17 (4,false),
.last 17 (4,false)
]),
.cycle 18 1 false (6),
.cycle 16 19 true (2),
.cycle 34 1 false (6),
.cycle 20 1 false (6),
.cycle 14 1 false (0),
.split 14 (4,false) (byMove [
.last 18 (4,true),
.cycle 12 20 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.cycle 22 1 false (6),
.cycle 13 2 true (0),
.cycle 20 1 false (6),
.last 15 (4,true),
.cycle 26 1 false (6),
.cycle 26 14 true (2),
.last 17 (4,true),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 36 23 true (4),
.cycle 16 19 true (2),
.last 16 (4,true),
.cycle 5 27 true (0),
.last 15 (4,true),
.cycle 15 28 true (1)
]),
.cycle 14 1 false (0),
.cycle 0 47 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.split 14 (4,true) (byMove [
.last 42 (4,false),
.cycle 16 1 false (2),
.last 16 (4,false),
.last 29 (4,false),
.last 16 (4,false),
.cycle 26 1 false (8),
.cycle 6 9 true (0),
.last 47 (4,false),
.cycle 12 24 true (0),
.last 39 (4,false),
.last 17 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.cycle 22 1 false (6),
.cycle 13 2 true (1),
.cycle 20 1 false (6),
.last 16 (4,false),
.last 23 (4,false),
.cycle 0 54 true (0),
.last 27 (4,false),
.cycle 2 15 true (0),
.cycle 0 51 true (0),
.last 17 (4,false),
.last 17 (4,false)
]),
.cycle 12 24 true (0)
])
theorem kid11_part1323_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1323) = true := by rfl

def kid11_part1324 : Audit := .cycle 17 1 false (5)
theorem kid11_part1324_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1324) = true := by rfl

def kid11_part1326 : Audit := .split 16 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 272, 262144, 256, 128, 256, 32768, 2, 262144, 256, 128, 256, 8, 32, 262144, 256, 262144],[2, 32, 256, 1, 256, 16, 8192, 131072, 256, 4096, 256, 65536, 2, 32, 256, 1, 256, 16, 262144],345116⟩,
.cycle 10 8 true (0),
.cycle 20 1 false (0),
.last 21 (4,false),
.cycle 0 51 true (0),
.last 18 (4,false),
.cycle 6 11 true (0),
.last 19 (4,false),
.last 41 (4,false),
.cycle 0 43 true (0),
.last 21 (4,false),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.last 25 (4,false),
.cycle 0 25 true (-1),
.last 21 (4,false),
.cycle 13 8 true (0),
.cycle 0 29 true (0),
.last 48 (4,false),
.last 19 (4,false),
.cycle 2 17 true (0),
.last 41 (4,false),
.last 21 (4,false),
.cycle 0 19 true (0)
])
theorem kid11_part1326_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1326) = true := by rfl

def kid11_part1327 : Audit := .split 32 (4,false) (byMove [
.cycle 0 33 true (0),
.cycle 0 87 true (0),
.cycle 0 75 true (0),
.cycle 0 46 true (0),
.cycle 46 1 false (2),
.cycle 19 14 true (0),
.cycle 0 33 true (0),
.cycle 24 33 true (0),
.cycle 24 21 true (0),
.cycle 12 31 true (0),
.cycle 32 1 true (6),
.cycle 0 52 true (0),
.cycle 0 42 true (0),
.last 34 (2,true),
.cycle 0 35 true (0),
.cycle 0 73 true (0),
.cycle 0 49 true (-1),
.cycle 0 101 true (0),
.cycle 0 33 true (0),
.cycle 1 32 true (0),
.cycle 12 43 true (0),
.cycle 0 124 true (0),
.cycle 32 1 true (6),
.cycle 12 47 true (0)
])
theorem kid11_part1327_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1327) = true := by rfl

def kid11_part1328 : Audit := .cycle 15 1 false (1)
theorem kid11_part1328_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1328) = true := by rfl

def kid11_part1329 : Audit := .cycle 14 1 false (0)
theorem kid11_part1329_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1329) = true := by rfl

def kid11_part1330 : Audit := .split 14 (4,false) (byMove [
.cycle 0 37 true (-1),
.cycle 41 1 false (7),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 16 (2,true),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.cycle 23 1 true (3),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.last 16 (2,true),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 16 (2,true),
.cycle 12 43 true (0),
.cycle 32 1 false (8),
.cycle 41 1 true (-3),
.cycle 11 4 true (0)
])
theorem kid11_part1330_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1330) = true := by rfl

def kid11_part1331 : Audit := .cycle 14 1 false (0)
theorem kid11_part1331_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1331) = true := by rfl

def kid11_part1332 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 25 1 false (7),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 25 1 false (9),
.cycle 19 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 true (5),
.cycle 18 1 false (6),
.cycle 32 1 false (10),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 24 1 false (8),
.cycle 28 1 false (10),
.cycle 17 1 true (5),
.cycle 0 21 true (0)
])
theorem kid11_part1332_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1332) = true := by rfl

def kid11_part1333 : Audit := .cycle 24 1 false (8)
theorem kid11_part1333_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1333) = true := by rfl

def kid11_part1334 : Audit := .split 14 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 276, 262144, 256, 128, 256, 32768, 2, 262144, 4, 128, 256, 8, 32, 262144, 256, 262144],[2, 32, 256, 1, 4, 16, 8192, 131072, 256, 4096, 16384, 65536, 2, 32, 256, 1, 4, 16, 262144],347164⟩,
.cycle 55 13 true (5),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 17 1 false (5),
.last 17 (4,false),
.cycle 18 1 false (6),
.cycle 24 1 false (8),
.last 17 (4,false),
.cycle 18 1 false (6),
.cycle 28 7 true (4),
.last 25 (4,false),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.last 42 (4,false),
.last 17 (4,false),
.cycle 2 15 true (0),
.last 37 (4,false),
.last 17 (4,false),
.cycle 28 1 false (8)
])
theorem kid11_part1334_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1334) = true := by rfl

def kid11_part1335 : Audit := .cycle 17 1 false (5)
theorem kid11_part1335_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1335) = true := by rfl

def kid11_part1336 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 25 1 false (7),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 25 1 false (9),
.cycle 19 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 true (5),
.cycle 18 1 false (6),
.cycle 15 8 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 24 1 false (8),
.cycle 28 1 false (10),
.cycle 17 1 true (5),
.cycle 16 4 true (4)
])
theorem kid11_part1336_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1336) = true := by rfl

def kid11_part1337 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 25 1 false (7),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 25 1 false (9),
.cycle 19 1 false (7),
.cycle 18 1 false (6),
.cycle 17 1 true (5),
.cycle 18 1 false (6),
.cycle 14 8 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 17 1 false (5),
.cycle 18 1 false (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 24 1 false (8),
.cycle 28 1 false (10),
.cycle 17 1 true (5),
.cycle 21 1 false (7)
])
theorem kid11_part1337_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1337) = true := by rfl

def kid11_part1338 : Audit := .split 21 (4,false) (byMove [
.cycle 0 22 true (0),
.cycle 16 32 true (2),
.cycle 16 35 true (0),
.cycle 16 30 true (0),
.cycle 40 1 false (2),
.cycle 16 8 true (2),
.cycle 0 22 true (0),
.cycle 16 38 true (2),
.cycle 15 15 true (1),
.cycle 16 19 true (2),
.cycle 21 1 true (5),
.cycle 8 14 true (0),
.cycle 16 10 true (2),
.last 23 (2,true),
.cycle 0 24 true (0),
.cycle 16 31 true (0),
.cycle 13 11 true (0),
.cycle 16 18 true (2),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 12 26 true (0),
.cycle 12 36 true (0),
.cycle 21 1 true (5),
.cycle 16 13 true (2)
])
theorem kid11_part1338_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1338) = true := by rfl

def kid11_part1339 : Audit := .split 15 (2,true) (byMove [
.cycle 33 1 false (7),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 24 true (0),
.cycle 13 3 false (1),
.last 17 (4,false),
.last 19 (4,false),
.last 52 (4,false),
.last 69 (4,false),
.last 32 (4,false),
.last 25 (4,false),
.last 21 (4,false),
.last 25 (4,false),
.last 33 (4,false),
.cycle 36 1 false (8),
.cycle 32 1 false (8),
.cycle 13 3 false (1),
.cycle 12 4 true (0),
.last 19 (4,false),
.cycle 1 20 true (0),
.cycle 2 17 true (0),
.cycle 5 11 true (0),
.last 25 (4,false),
.last 21 (4,false)
])
theorem kid11_part1339_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1339) = true := by rfl

def kid11_part1340 : Audit := .split 19 (4,false) (byMove [
.cycle 0 20 true (0),
.cycle 27 1 false (7),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 20 1 false (4),
.cycle 0 20 true (0),
.cycle 27 1 false (9),
.cycle 21 1 false (7),
.cycle 20 1 false (6),
.cycle 19 1 true (5),
.cycle 20 1 false (6),
.cycle 36 1 false (10),
.last 21 (2,true),
.cycle 0 22 true (0),
.cycle 20 1 false (4),
.cycle 19 1 false (5),
.cycle 20 1 false (4),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 26 1 false (8),
.cycle 30 1 false (10),
.cycle 19 1 true (5),
.cycle 0 25 true (0)
])
theorem kid11_part1340_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1340) = true := by rfl

def kid11_part1341 : Audit := .cycle 14 1 false (0)
theorem kid11_part1341_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1341) = true := by rfl

def kid11_part1342 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 12 33 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.cycle 29 1 false (9),
.last 15 (2,true),
.cycle 20 1 false (6),
.cycle 13 2 true (0),
.cycle 26 1 false (6),
.cycle 22 16 true (1),
.last 16 (2,true),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 53 true (0),
.cycle 1 21 true (0),
.last 15 (2,true),
.cycle 46 24 true (4),
.cycle 13 3 false (1),
.cycle 21 6 true (3)
])
theorem kid11_part1342_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1342) = true := by rfl

def kid11_part1343 : Audit := .cycle 14 1 false (0)
theorem kid11_part1343_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1343) = true := by rfl

def kid11_part1344 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 0 56 true (0),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 0 22 true (0),
.cycle 18 7 true (1),
.cycle 0 18 true (0),
.cycle 12 25 true (0),
.cycle 28 7 true (4),
.cycle 0 47 true (0),
.cycle 17 1 true (5),
.cycle 0 29 true (0),
.cycle 0 43 true (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 26 true (0),
.cycle 0 26 true (0),
.cycle 9 9 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 35 7 true (5),
.cycle 0 47 true (0),
.cycle 17 1 true (5),
.cycle 0 21 true (0)
])
theorem kid11_part1344_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1344) = true := by rfl

def kid11_part1345 : Audit := .cycle 1 16 true (0)
theorem kid11_part1345_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1345) = true := by rfl

def kid11_part1346 : Audit := .split 14 (2,true) (byMove [
.cycle 29 1 false (7),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.last 19 (4,false),
.cycle 0 72 true (0),
.last 16 (4,false),
.cycle 6 9 true (0),
.last 17 (4,false),
.last 37 (4,false),
.cycle 0 64 true (0),
.last 17 (4,false),
.last 36 (4,false),
.cycle 25 1 false (7),
.last 21 (4,false),
.last 21 (4,false),
.last 19 (4,false),
.cycle 13 2 true (1),
.cycle 29 1 false (7),
.last 42 (4,false),
.last 17 (4,false),
.cycle 2 15 true (0),
.last 37 (4,false),
.last 17 (4,false),
.cycle 15 20 true (2)
])
theorem kid11_part1346_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1346) = true := by rfl

def kid11_part1347 : Audit := .cycle 5 9 true (0)
theorem kid11_part1347_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1347) = true := by rfl

def kid11_part1348 : Audit := .split 17 (4,false) (byMove [
.cycle 13 20 true (1),
.cycle 15 7 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 70 1 false (4),
.cycle 0 18 true (0),
.cycle 13 19 true (1),
.cycle 12 26 true (0),
.cycle 3 15 true (0),
.cycle 17 1 true (5),
.cycle 15 6 true (3),
.cycle 14 10 true (2),
.last 22 (2,true),
.last 18 (2,true),
.cycle 13 23 true (1),
.cycle 15 3 true (3),
.cycle 16 3 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 13 24 true (1),
.cycle 17 1 true (5),
.cycle 16 4 true (4)
])
theorem kid11_part1348_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1348) = true := by rfl

def kid11_part1349 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 33 3 true (5),
.cycle 41 3 true (7),
.cycle 19 3 true (3),
.cycle 18 3 true (3),
.cycle 0 18 true (0),
.cycle 12 21 true (0),
.cycle 26 3 true (6),
.cycle 12 24 true (0),
.cycle 17 1 true (5),
.cycle 23 3 true (5),
.cycle 14 8 true (2),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 31 3 true (5),
.cycle 20 3 true (4),
.cycle 14 5 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 33 3 true (7),
.cycle 41 3 true (9),
.cycle 17 1 true (5),
.cycle 18 3 true (5)
])
theorem kid11_part1349_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1349) = true := by rfl

def kid11_part1325 : Audit := .split 13 (4,true) (byMove [(kid11_part1326),(kid11_part1327),(kid11_part1328),(kid11_part1329),(kid11_part1330),(kid11_part1331),(kid11_part1332),(kid11_part1333),(kid11_part1334),(kid11_part1335),(kid11_part1336),(kid11_part1337),(kid11_part1338),(kid11_part1339),(kid11_part1340),(kid11_part1341),(kid11_part1342),(kid11_part1343),(kid11_part1344),(kid11_part1345),(kid11_part1346),(kid11_part1347),(kid11_part1348),(kid11_part1349)])

theorem kid11_part1325_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1325) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) 13 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1326),(kid11_part1327),(kid11_part1328),(kid11_part1329),(kid11_part1330),(kid11_part1331),(kid11_part1332),(kid11_part1333),(kid11_part1334),(kid11_part1335),(kid11_part1336),(kid11_part1337),(kid11_part1338),(kid11_part1339),(kid11_part1340),(kid11_part1341),(kid11_part1342),(kid11_part1343),(kid11_part1344),(kid11_part1345),(kid11_part1346),(kid11_part1347),(kid11_part1348),(kid11_part1349)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1326_checked

  · exact kid11_part1332_checked

  · exact kid11_part1338_checked

  · exact kid11_part1344_checked

  · exact kid11_part1327_checked

  · exact kid11_part1333_checked

  · exact kid11_part1339_checked

  · exact kid11_part1345_checked

  · exact kid11_part1328_checked

  · exact kid11_part1334_checked

  · exact kid11_part1340_checked

  · exact kid11_part1346_checked

  · exact kid11_part1329_checked

  · exact kid11_part1335_checked

  · exact kid11_part1341_checked

  · exact kid11_part1347_checked

  · exact kid11_part1330_checked

  · exact kid11_part1336_checked

  · exact kid11_part1342_checked

  · exact kid11_part1348_checked

  · exact kid11_part1331_checked

  · exact kid11_part1337_checked

  · exact kid11_part1343_checked

  · exact kid11_part1349_checked

def kid11_part1350 : Audit := .cycle 17 1 false (5)
theorem kid11_part1350_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1350) = true := by rfl

def kid11_part1351 : Audit := .cycle 20 11 true (2)
theorem kid11_part1351_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1351) = true := by rfl

def kid11_part1352 : Audit := .split 14 (2,true) (byMove [
.cycle 35 1 false (7),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 28 true (-1),
.split 15 (4,true) (byMove [
.cycle 0 26 true (-2),
.cycle 67 1 false (5),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 0 28 true (-1),
.cycle 35 1 false (7),
.cycle 25 1 false (5),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 1 false (0),
.cycle 10 8 false (2),
.cycle 13 3 false (0),
.last 25 (4,false),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 12 30 true (-1),
.cycle 12 29 true (-1),
.cycle 0 72 true (-2),
.cycle 42 1 false (8),
.last 16 (4,false),
.cycle 11 5 false (1)
]),
.cycle 12 3 false (0),
.cycle 0 47 true (-1),
.cycle 39 11 true (4),
.cycle 12 18 true (-1),
.cycle 0 60 true (-2),
.split 15 (4,true) (byMove [
.last 23 (4,false),
.last 40 (4,false),
.last 35 (4,false),
.last 27 (4,false),
.last 16 (4,false),
.cycle 11 5 false (1),
.last 21 (4,false),
.last 47 (4,false),
.last 19 (4,false),
.last 45 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.last 27 (4,false),
.last 23 (4,false),
.last 31 (4,false),
.last 16 (4,false),
.cycle 11 5 false (1),
.last 21 (4,false),
.cycle 1 20 true (-1),
.last 19 (4,false),
.cycle 5 11 true (-1),
.last 19 (4,false),
.last 27 (4,false)
]),
.cycle 18 13 true (1),
.cycle 37 1 false (5),
.cycle 12 4 true (-1),
.cycle 42 1 false (8),
.cycle 36 1 false (8),
.split 15 (4,true) (byMove [
.cycle 13 8 true (-2),
.cycle 12 40 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 36 1 false (8),
.cycle 37 1 false (5),
.last 17 (4,false),
.cycle 32 1 false (8),
.last 21 (4,false),
.cycle 12 4 true (-1),
.cycle 12 12 true (-2),
.cycle 13 3 false (0),
.cycle 42 1 false (8),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.cycle 47 15 true (4),
.cycle 21 19 true (1),
.cycle 14 2 true (-1),
.cycle 0 57 true (-1),
.last 21 (4,false),
.cycle 12 6 true (-1)
]),
.cycle 12 3 false (0),
.cycle 12 60 true (-1),
.cycle 12 24 true (-1),
.cycle 12 19 true (-1),
.cycle 37 26 true (2),
.split 15 (4,true) (byMove [
.last 23 (4,false),
.cycle 10 7 false (2),
.last 17 (4,false),
.cycle 0 24 true (-1),
.last 18 (4,false),
.last 21 (4,false),
.last 21 (4,false),
.last 58 (4,false),
.last 19 (4,false),
.last 36 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.last 27 (4,false),
.last 35 (4,false),
.cycle 14 2 true (0),
.last 55 (4,false),
.last 18 (4,false),
.cycle 12 6 true (-1),
.last 21 (4,false),
.cycle 12 22 true (-1),
.last 19 (4,false),
.cycle 12 13 true (-1),
.last 19 (4,false),
.last 27 (4,false)
]),
.cycle 25 11 true (2)
])
theorem kid11_part1352_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1352) = true := by rfl

def kid11_part1353 : Audit := .cycle 28 1 false (8)
theorem kid11_part1353_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1353) = true := by rfl

def kid11_part1354 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1354_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1354) = true := by rfl

def kid11_part1356 : Audit := .split 16 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 1, 4, 4],[128, 256, 8, 0, 16384, 0, 8192, 16384, 512, 1711292706, 67109120, 16384, 33554432, 67108864, 2097152, 128, 16384, 1140867328, 128, 256, 134217728, 2048, 67108864, 1140867328, 33554432, 67108864, 134217728, 1711292672, 67125504, 1140867328, 1073741824],[2, 32, 16384, 1, 1073741824, 16384, 128, 2048, 67109120, 64, 1073741824, 1140867328, 524288, 8388608, 16384, 262144, 1073741824, 1073741824, 33554432, 536870912, 67108864, 16777216, 1073741824, 16384, 33554432, 536870912, 67125504, 16777216, 1073741824, 1140867328, 1073741824],2145007426⟩,
.cycle 10 8 false (2),
.cycle 20 1 false (-2),
.cycle 0 34 true (-2),
.last 17 (4,true),
.last 18 (4,true),
.last 39 (4,true),
.last 42 (4,true),
.cycle 12 20 true (-2),
.cycle 3 22 true (-2),
.last 17 (4,true),
.cycle 25 17 true (1),
.last 51 (4,true),
.cycle 12 12 true (-2),
.cycle 67 1 false (5),
.cycle 12 44 true (-2),
.last 17 (4,true),
.last 18 (4,true),
.last 38 (4,true),
.last 41 (4,true),
.last 32 (4,true),
.last 42 (4,true),
.last 17 (4,true),
.last 18 (4,true)
])
theorem kid11_part1356_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1356) = true := by rfl

def kid11_part1357 : Audit := .cycle 12 34 true (-2)
theorem kid11_part1357_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1357) = true := by rfl

def kid11_part1358 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1358_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1358) = true := by rfl

def kid11_part1359 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1359_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1359) = true := by rfl

def kid11_part1360 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1360_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1360) = true := by rfl

def kid11_part1361 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1361_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1361) = true := by rfl

def kid11_part1362 : Audit := .cycle 30 1 false (8)
theorem kid11_part1362_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1362) = true := by rfl

def kid11_part1363 : Audit := .cycle 27 1 false (5)
theorem kid11_part1363_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1363) = true := by rfl

def kid11_part1364 : Audit := .split 14 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 4, 0, 8192, 16384, 512, 16418, 256, 16384, 33554432, 67108864, 2097152, 128, 1048576, 1140850944, 33554432, 67108864, 134217728, 2048, 67108864, 1140850944, 33554432, 67108864, 134217728, 1711276288, 67108864, 1140850944, 1073741824],[2, 32, 16384, 1, 1073741824, 16384, 128, 2048, 67109120, 64, 1073741824, 1140850944, 524288, 8388608, 16384, 262144, 1073741824, 1073741824, 33554432, 536870912, 67108864, 16777216, 1073741824, 67108864, 33554432, 536870912, 67108864, 16777216, 1073741824, 1140850688, 1073741824],2145333312⟩,
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 25 1 false (5),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.cycle 30 1 false (8),
.cycle 20 1 false (6),
.cycle 21 1 false (5),
.last 15 (4,true),
.cycle 27 1 false (5),
.last 40 (4,true),
.cycle 12 6 true (-1),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 15 1 false (-1),
.last 67 (4,true),
.cycle 1 22 true (-1),
.last 30 (4,true),
.cycle 0 56 true (-1),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid11_part1364_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1364) = true := by rfl

def kid11_part1365 : Audit := .cycle 28 1 false (8)
theorem kid11_part1365_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1365) = true := by rfl

def kid11_part1366 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 0 72 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 27 1 true (3),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.cycle 30 1 false (8),
.last 15 (2,true),
.cycle 21 1 false (5),
.cycle 19 1 true (5),
.cycle 27 1 false (5),
.cycle 21 21 true (1),
.last 16 (2,true),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.cycle 13 2 true (-1),
.cycle 15 1 false (-1),
.cycle 35 32 true (3),
.cycle 1 22 true (-1),
.last 15 (2,true),
.cycle 0 56 true (-1),
.cycle 19 1 true (5),
.cycle 14 2 true (0)
])
theorem kid11_part1366_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1366) = true := by rfl

def kid11_part1367 : Audit := .cycle 12 2 true (-1)
theorem kid11_part1367_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1367) = true := by rfl

def kid11_part1368 : Audit := .cycle 12 8 true (-2)
theorem kid11_part1368_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1368) = true := by rfl

def kid11_part1369 : Audit := .split 15 (2,true) (byMove [
.cycle 39 1 false (7),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 12 10 true (-2),
.last 16 (4,true),
.cycle 12 4 false (0),
.cycle 50 25 true (1),
.last 41 (4,true),
.far true 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[1024, 2048, 512, 512, 128, 2048, 1152, 2048, 2048, 512, 128, 2048, 1024, 1024, 512, 2097152, 524288, 8388608, 29885568, 29887616, 31984768, 2097152, 524288, 8388608, 16777216],[2048, 2048, 512, 128, 16777216, 1024, 2048, 128, 512, 2048, 16777216, 1024, 2048, 2048, 2048, 2176, 16777216, 4194304, 29887616, 8912896, 31985280, 29887616, 16777216, 4194304, 16777216],22872064⟩,
.cycle 12 34 true (-2),
.last 16 (4,true),
.cycle 12 7 false (0),
.cycle 12 6 true (-2),
.cycle 12 5 false (0),
.cycle 57 1 false (5),
.cycle 47 1 false (5),
.last 16 (4,true),
.cycle 12 4 false (0),
.last 42 (4,true),
.cycle 12 11 false (1),
.last 32 (4,true),
.last 39 (4,true),
.last 16 (4,true),
.last 17 (4,true)
])
theorem kid11_part1369_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1369) = true := by rfl

def kid11_part1370 : Audit := .cycle 36 1 false (8)
theorem kid11_part1370_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1370) = true := by rfl

def kid11_part1371 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1371_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1371) = true := by rfl

def kid11_part1372 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1372_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1372) = true := by rfl

def kid11_part1373 : Audit := .cycle 14 1 false (-2)
theorem kid11_part1373_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1373) = true := by rfl

def kid11_part1374 : Audit := .cycle 39 11 true (4)
theorem kid11_part1374_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1374) = true := by rfl

def kid11_part1375 : Audit := .split 30 (4,true) (byMove [
.last 33 (2,true),
.cycle 102 1 false (-2),
.last 31 (2,true),
.cycle 20 13 true (1),
.cycle 1 80 false (6),
.cycle 56 1 false (-4),
.cycle 18 20 true (1),
.cycle 20 11 true (2),
.last 31 (2,true),
.cycle 12 56 true (-1),
.cycle 1 34 true (-1),
.cycle 18 13 true (1),
.cycle 17 15 true (1),
.cycle 14 17 true (0),
.last 31 (2,true),
.cycle 14 34 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 34, 2, 32, 64],[2, 32, 64, 1, 32, 32, 64],64⟩,
.cycle 18 20 true (1),
.cycle 20 11 true (2),
.last 31 (2,true),
.cycle 5 48 true (-1),
.cycle 30 19 true (2),
.cycle 29 2 true (2)
])
theorem kid11_part1375_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1375) = true := by rfl

def kid11_part1376 : Audit := .split 14 (2,true) (byMove [
.cycle 35 1 false (7),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 28 true (-1),
.last 15 (4,true),
.cycle 12 3 false (0),
.cycle 0 47 true (-1),
.cycle 39 11 true (4),
.cycle 12 18 true (-1),
.cycle 0 60 true (-2),
.last 15 (4,true),
.last 30 (4,true),
.cycle 37 1 false (5),
.cycle 12 4 true (-1),
.cycle 42 1 false (8),
.cycle 36 1 false (8),
.last 15 (4,true),
.cycle 12 3 false (0),
.last 34 (4,true),
.last 35 (4,true),
.last 30 (4,true),
.last 62 (4,true),
.last 15 (4,true),
.last 16 (4,true)
])
theorem kid11_part1376_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1376) = true := by rfl

def kid11_part1377 : Audit := .cycle 0 47 true (-1)
theorem kid11_part1377_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1377) = true := by rfl

def kid11_part1378 : Audit := .split 14 (4,true) (byMove [
.last 17 (2,true),
.cycle 16 1 false (0),
.last 15 (2,true),
.cycle 0 28 true (-1),
.cycle 68 1 true (-6),
.cycle 12 3 false (0),
.cycle 0 47 true (-1),
.cycle 39 11 true (4),
.last 15 (2,true),
.cycle 0 60 true (-2),
.cycle 19 1 true (5),
.cycle 17 13 true (1),
.cycle 37 1 false (5),
.cycle 12 4 true (-1),
.last 15 (2,true),
.cycle 36 1 false (8),
.cycle 13 3 false (0),
.cycle 12 3 false (0),
.cycle 14 56 true (0),
.cycle 39 9 true (5),
.last 15 (2,true),
.cycle 0 85 true (-1),
.cycle 19 1 true (5),
.cycle 14 2 true (0)
])
theorem kid11_part1378_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1378) = true := by rfl

def kid11_part1379 : Audit := .split 15 (4,true) (byMove [
.last 18 (2,true),
.cycle 12 40 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 11 6 false (1),
.cycle 16 1 false (-2),
.cycle 36 1 false (8),
.cycle 37 1 false (5),
.last 16 (2,true),
.cycle 32 1 false (8),
.cycle 18 8 true (2),
.cycle 12 4 true (-1),
.cycle 12 12 true (-2),
.last 17 (2,true),
.cycle 42 1 false (8),
.cycle 16 1 false (-2),
.cycle 13 3 false (0),
.cycle 16 1 false (-2),
.cycle 47 15 true (4),
.cycle 24 15 true (1),
.last 16 (2,true),
.cycle 0 57 true (-1),
.cycle 18 6 true (2),
.cycle 14 2 true (-1)
])
theorem kid11_part1379_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1379) = true := by rfl

def kid11_part1355 : Audit := .split 13 (4,false) (byMove [(kid11_part1356),(kid11_part1357),(kid11_part1358),(kid11_part1359),(kid11_part1360),(kid11_part1361),(kid11_part1362),(kid11_part1363),(kid11_part1364),(kid11_part1365),(kid11_part1366),(kid11_part1367),(kid11_part1368),(kid11_part1369),(kid11_part1370),(kid11_part1371),(kid11_part1372),(kid11_part1373),(kid11_part1374),(kid11_part1375),(kid11_part1376),(kid11_part1377),(kid11_part1378),(kid11_part1379)])

theorem kid11_part1355_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1355) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1356),(kid11_part1357),(kid11_part1358),(kid11_part1359),(kid11_part1360),(kid11_part1361),(kid11_part1362),(kid11_part1363),(kid11_part1364),(kid11_part1365),(kid11_part1366),(kid11_part1367),(kid11_part1368),(kid11_part1369),(kid11_part1370),(kid11_part1371),(kid11_part1372),(kid11_part1373),(kid11_part1374),(kid11_part1375),(kid11_part1376),(kid11_part1377),(kid11_part1378),(kid11_part1379)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1356_checked

  · exact kid11_part1362_checked

  · exact kid11_part1368_checked

  · exact kid11_part1374_checked

  · exact kid11_part1357_checked

  · exact kid11_part1363_checked

  · exact kid11_part1369_checked

  · exact kid11_part1375_checked

  · exact kid11_part1358_checked

  · exact kid11_part1364_checked

  · exact kid11_part1370_checked

  · exact kid11_part1376_checked

  · exact kid11_part1359_checked

  · exact kid11_part1365_checked

  · exact kid11_part1371_checked

  · exact kid11_part1377_checked

  · exact kid11_part1360_checked

  · exact kid11_part1366_checked

  · exact kid11_part1372_checked

  · exact kid11_part1378_checked

  · exact kid11_part1361_checked

  · exact kid11_part1367_checked

  · exact kid11_part1373_checked

  · exact kid11_part1379_checked

def kid11_part1380 : Audit := .cycle 13 1 false (-1)
theorem kid11_part1380_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1380) = true := by rfl

def kid11_part1381 : Audit := .cycle 0 42 true (0)
theorem kid11_part1381_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1381) = true := by rfl

def kid11_part1382 : Audit := .cycle 1 16 true (0)
theorem kid11_part1382_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1382) = true := by rfl

def kid11_part1383 : Audit := .split 13 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 20 true (0),
.split 14 (4,true) (byMove [
.cycle 0 97 true (-1),
.cycle 39 1 false (7),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.cycle 31 1 false (7),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.cycle 13 3 false (1),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.cycle 1 23 true (0),
.cycle 0 85 true (0),
.cycle 32 1 false (8),
.last 15 (4,false),
.cycle 11 4 true (0)
]),
.cycle 0 85 true (0),
.cycle 6 30 true (0),
.cycle 38 19 true (6),
.cycle 67 1 false (15),
.cycle 0 73 true (0),
.split 14 (4,true) (byMove [
.cycle 0 19 true (0),
.last 43 (4,false),
.last 23 (4,false),
.cycle 31 1 false (7),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 73 true (0),
.cycle 7 30 true (0),
.last 31 (4,false),
.cycle 0 104 true (0),
.last 17 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.last 23 (4,false),
.cycle 0 85 true (0),
.last 21 (4,false),
.last 15 (4,false),
.cycle 11 4 true (0),
.last 61 (4,false),
.last 34 (4,false),
.last 34 (4,false),
.last 58 (4,false),
.last 17 (4,false),
.last 17 (4,false)
]),
.cycle 14 22 true (2),
.cycle 27 1 false (7),
.cycle 31 1 false (7),
.cycle 32 1 false (8),
.cycle 28 1 false (8),
.split 14 (4,true) (byMove [
.cycle 13 8 true (-1),
.cycle 12 31 true (-2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.cycle 27 1 false (7),
.last 16 (4,false),
.cycle 25 1 false (7),
.last 19 (4,false),
.cycle 31 1 false (7),
.cycle 12 37 true (-1),
.cycle 13 3 false (1),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 46 23 true (6),
.cycle 16 30 true (2),
.cycle 13 2 true (0),
.cycle 5 36 true (0),
.last 19 (4,false),
.cycle 2 23 true (0)
]),
.cycle 12 2 true (0),
.cycle 0 54 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 5 9 true (0),
.split 14 (4,true) (byMove [
.last 42 (4,false),
.cycle 10 6 true (0),
.last 16 (4,false),
.last 38 (4,false),
.last 17 (4,false),
.last 43 (4,false),
.cycle 6 9 true (0),
.last 54 (4,false),
.cycle 13 31 true (1),
.last 39 (4,false),
.last 17 (4,false),
.last 17 (4,false),
.last 19 (4,false),
.last 42 (4,false),
.cycle 13 2 true (1),
.cycle 5 36 true (0),
.last 17 (4,false),
.last 23 (4,false),
.last 61 (4,false),
.last 34 (4,false),
.cycle 2 15 true (0),
.last 58 (4,false),
.last 17 (4,false),
.last 17 (4,false)
]),
.cycle 2 15 true (0)
])
theorem kid11_part1383_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1383) = true := by rfl

def kid11_part1384 : Audit := .cycle 0 46 true (0)
theorem kid11_part1384_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1384) = true := by rfl

def kid11_part1386 : Audit := .split 16 (2,true) (byMove [
.cycle 31 1 false (7),
.cycle 18 1 false (2),
.cycle 19 1 false (1),
.last 21 (4,false),
.cycle 0 90 true (0),
.last 18 (4,false),
.cycle 6 11 true (0),
.last 19 (4,false),
.last 41 (4,false),
.cycle 0 74 true (0),
.last 21 (4,false),
.last 44 (4,false),
.cycle 29 1 false (7),
.last 25 (4,false),
.last 23 (4,false),
.last 21 (4,false),
.cycle 13 8 true (0),
.cycle 37 1 false (7),
.last 48 (4,false),
.last 19 (4,false),
.cycle 2 17 true (0),
.last 41 (4,false),
.last 21 (4,false),
.cycle 17 26 true (2)
])
theorem kid11_part1386_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1386) = true := by rfl

def kid11_part1387 : Audit := .cycle 15 1 false (1)
theorem kid11_part1387_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1387) = true := by rfl

def kid11_part1388 : Audit := .split 14 (2,true) (byMove [
.last 36 (4,false),
.last 33 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 19 (4,false),
.cycle 19 1 false (5),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 1 false (1),
.cycle 10 7 false (2),
.last 19 (4,false),
.cycle 0 24 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 0 20 true (0),
.last 19 (4,false),
.last 32 (4,false),
.cycle 32 1 false (8),
.last 15 (4,false),
.cycle 11 4 true (0)
])
theorem kid11_part1388_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1388) = true := by rfl

def kid11_part1389 : Audit := .cycle 0 20 true (0)
theorem kid11_part1389_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1389) = true := by rfl

def kid11_part1390 : Audit := .split 15 (4,false) (byMove [
.cycle 12 66 true (-2),
.cycle 23 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (2,true),
.cycle 18 23 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 25 1 true (3),
.cycle 16 1 false (0),
.cycle 10 8 false (2),
.last 17 (2,true),
.last 20 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.last 18 (2,true),
.cycle 0 113 true (-2),
.cycle 2 32 true (-1),
.last 20 (2,true),
.cycle 48 1 true (-4),
.cycle 11 5 false (1)
])
theorem kid11_part1390_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1390) = true := by rfl

def kid11_part1391 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.cycle 17 1 false (1),
.last 16 (2,true),
.cycle 0 24 true (0),
.cycle 17 1 false (-1),
.cycle 14 2 true (0),
.cycle 0 20 true (0),
.cycle 19 32 true (3),
.last 16 (2,true),
.cycle 0 85 true (0),
.cycle 65 1 true (1),
.cycle 16 8 true (2),
.cycle 28 1 false (6),
.cycle 29 3 true (3),
.last 16 (2,true),
.cycle 32 1 false (8),
.cycle 17 1 false (-1),
.cycle 12 4 true (0),
.cycle 0 20 true (0),
.cycle 1 20 true (0),
.last 16 (2,true),
.cycle 5 11 true (0),
.cycle 24 1 true (4),
.cycle 20 5 true (4)
])
theorem kid11_part1391_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1391) = true := by rfl

def kid11_part1392 : Audit := .split 17 (4,false) (byMove [
.cycle 12 26 true (0),
.cycle 0 30 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 0 36 true (0),
.cycle 14 9 true (2),
.cycle 6 30 true (0),
.cycle 17 1 true (5),
.cycle 20 20 true (4),
.cycle 18 20 true (0),
.cycle 15 3 true (3),
.last 18 (2,true),
.cycle 0 46 true (0),
.cycle 0 46 true (0),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 20 20 true (4),
.cycle 17 1 true (5),
.cycle 0 21 true (0)
])
theorem kid11_part1392_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1392) = true := by rfl

def kid11_part1393 : Audit := .split 42 (4,false) (byMove [
.cycle 12 49 true (0),
.cycle 7 36 true (0),
.last 43 (2,true),
.cycle 0 44 true (0),
.cycle 12 49 true (0),
.cycle 41 2 true (9),
.cycle 0 43 true (0),
.cycle 17 26 true (3),
.cycle 40 9 true (8),
.cycle 38 19 true (6),
.cycle 42 1 true (10),
.cycle 32 13 true (6),
.cycle 22 21 true (3),
.cycle 40 3 true (8),
.last 43 (2,true),
.cycle 29 34 true (3),
.cycle 23 21 true (3),
.cycle 15 28 true (3),
.cycle 0 43 true (0),
.cycle 1 42 true (0),
.cycle 2 41 true (0),
.cycle 38 24 true (6),
.cycle 42 1 true (10),
.cycle 15 29 true (3)
])
theorem kid11_part1393_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1393) = true := by rfl

def kid11_part1394 : Audit := .split 14 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 17664, 262144, 256, 128, 256, 32768, 2, 262144, 16384, 128, 256, 8, 32, 262144, 256, 262144],[2, 32, 256, 1, 4, 1024, 8192, 131072, 256, 4096, 16384, 1024, 2, 32, 256, 1, 4, 1024, 262144],347164⟩,
.last 51 (4,false),
.last 31 (4,false),
.cycle 38 1 false (8),
.last 15 (4,false),
.last 60 (4,false),
.last 28 (4,false),
.last 17 (4,false),
.last 61 (4,false),
.last 48 (4,false),
.last 17 (4,false),
.last 25 (4,false),
.last 27 (4,false),
.last 25 (4,false),
.last 32 (4,false),
.last 29 (4,false),
.last 15 (4,false),
.cycle 11 4 true (0),
.last 42 (4,false),
.last 17 (4,false),
.cycle 2 15 true (0),
.last 37 (4,false),
.last 17 (4,false),
.last 25 (4,false)
])
theorem kid11_part1394_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1394) = true := by rfl

def kid11_part1395 : Audit := .split 28 (4,false) (byMove [
.cycle 12 39 true (0),
.cycle 0 87 true (0),
.last 29 (2,true),
.cycle 0 30 true (0),
.cycle 0 65 true (0),
.cycle 27 2 true (5),
.cycle 0 29 true (0),
.cycle 14 19 true (0),
.cycle 24 9 true (2),
.cycle 0 73 true (0),
.cycle 28 1 true (6),
.cycle 0 34 true (0),
.cycle 0 46 true (0),
.cycle 26 3 true (4),
.last 29 (2,true),
.cycle 22 31 true (0),
.cycle 0 31 true (0),
.cycle 0 75 true (0),
.cycle 0 29 true (0),
.cycle 1 28 true (0),
.cycle 2 27 true (0),
.cycle 0 96 true (0),
.cycle 28 1 true (6),
.cycle 3 29 true (0)
])
theorem kid11_part1395_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1395) = true := by rfl

def kid11_part1396 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 24, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.last 40 (2,true),
.cycle 38 1 false (8),
.cycle 23 1 false (1),
.cycle 8 10 true (0),
.cycle 0 18 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 2, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 12 17 true (0),
.cycle 67 1 false (15),
.cycle 17 1 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 15 8 true (3),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 45 1 false (11),
.cycle 28 1 false (6),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 8, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 17 1 true (5),
.cycle 16 4 true (4)
])
theorem kid11_part1396_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1396) = true := by rfl

def kid11_part1397 : Audit := .split 17 (4,false) (byMove [
.cycle 12 22 true (0),
.cycle 14 14 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 14 14 true (2),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 14 24 true (2),
.cycle 16 9 true (4),
.cycle 14 22 true (2),
.cycle 17 1 true (5),
.cycle 14 6 true (2),
.cycle 6 12 true (0),
.cycle 16 3 true (4),
.last 18 (2,true),
.cycle 14 30 true (2),
.cycle 15 3 true (3),
.cycle 14 8 true (2),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 12 24 true (0),
.cycle 17 1 true (5),
.cycle 14 9 true (2)
])
theorem kid11_part1397_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1397) = true := by rfl

def kid11_part1398 : Audit := .split 21 (4,false) (byMove [
.cycle 30 1 false (8),
.cycle 23 1 false (5),
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 16 11 true (2),
.cycle 20 2 true (4),
.cycle 0 22 true (0),
.cycle 46 1 false (10),
.cycle 18 9 true (2),
.cycle 27 1 false (7),
.cycle 21 1 true (5),
.cycle 16 8 true (2),
.cycle 24 1 false (6),
.cycle 19 3 true (3),
.last 22 (2,true),
.cycle 31 1 false (9),
.cycle 19 5 true (3),
.cycle 26 1 false (6),
.cycle 0 22 true (0),
.cycle 1 21 true (0),
.cycle 2 20 true (0),
.cycle 12 30 true (0),
.cycle 21 1 true (5),
.cycle 38 1 false (8)
])
theorem kid11_part1398_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1398) = true := by rfl

def kid11_part1399 : Audit := .split 25 (4,false) (byMove [
.cycle 34 1 false (8),
.cycle 27 1 false (5),
.last 26 (2,true),
.cycle 0 27 true (0),
.last 28 (2,true),
.cycle 24 2 true (4),
.cycle 0 26 true (0),
.cycle 12 29 true (0),
.cycle 23 9 true (3),
.cycle 31 1 false (7),
.cycle 25 1 true (5),
.cycle 18 10 true (2),
.cycle 28 1 false (6),
.cycle 23 3 true (3),
.last 26 (2,true),
.cycle 35 1 false (9),
.last 28 (2,true),
.cycle 21 5 true (3),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 12 36 true (0),
.cycle 25 1 true (5),
.cycle 21 6 true (3)
])
theorem kid11_part1399_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1399) = true := by rfl

def kid11_part1400 : Audit := .split 14 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 1280, 262144, 256, 128, 256, 32768, 2, 262144, 256, 128, 256, 8, 32, 262144, 256, 262144],[2, 32, 256, 1, 1, 1024, 8192, 131072, 256, 4096, 256, 1024, 2, 32, 256, 1, 1, 1024, 262144],345116⟩,
.last 21 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 28 1 false (8),
.last 21 (4,false),
.cycle 20 1 false (6),
.last 19 (4,false),
.last 21 (4,false),
.last 25 (4,false),
.last 33 (4,false),
.cycle 12 6 true (-1),
.cycle 32 1 false (8),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.last 52 (4,false),
.last 21 (4,false),
.cycle 2 17 true (0),
.last 19 (4,false),
.cycle 13 2 true (0),
.last 25 (4,false)
])
theorem kid11_part1400_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1400) = true := by rfl

def kid11_part1401 : Audit := .cycle 28 1 false (8)
theorem kid11_part1401_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1401) = true := by rfl

def kid11_part1402 : Audit := .split 15 (4,false) (byMove [
.last 18 (2,true),
.cycle 12 40 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 26 true (-1),
.cycle 12 39 true (-1),
.last 16 (2,true),
.cycle 32 1 false (8),
.cycle 14 2 true (-1),
.cycle 12 4 true (-1),
.cycle 12 12 true (-2),
.last 17 (2,true),
.last 30 (2,true),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 12 34 true (-1),
.cycle 12 39 true (-1),
.last 16 (2,true),
.cycle 23 32 true (1),
.cycle 13 3 false (1),
.cycle 13 5 false (1)
])
theorem kid11_part1402_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1402) = true := by rfl

def kid11_part1403 : Audit := .cycle 12 2 true (0)
theorem kid11_part1403_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1403) = true := by rfl

def kid11_part1404 : Audit := .split 17 (4,false) (byMove [
.cycle 37 7 true (5),
.cycle 7 11 true (0),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 0 36 true (0),
.cycle 14 9 true (2),
.cycle 0 54 true (0),
.cycle 17 1 true (5),
.cycle 0 41 true (0),
.cycle 0 31 true (0),
.cycle 15 3 true (3),
.last 18 (2,true),
.cycle 12 27 true (0),
.cycle 0 38 true (0),
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 0 59 true (0),
.cycle 17 1 true (5),
.cycle 0 21 true (0)
])
theorem kid11_part1404_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1404) = true := by rfl

def kid11_part1405 : Audit := .cycle 1 16 true (0)
theorem kid11_part1405_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1405) = true := by rfl

def kid11_part1406 : Audit := .split 14 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 1280, 262144, 256, 128, 256, 32768, 2, 262144, 256, 128, 256, 8, 32, 262144, 256, 262144],[2, 32, 256, 1, 256, 1024, 8192, 131072, 256, 4096, 256, 1024, 2, 32, 256, 1, 256, 1024, 262144],345116⟩,
.cycle 10 6 true (0),
.cycle 18 1 false (0),
.last 19 (4,false),
.cycle 2 41 true (0),
.last 16 (4,false),
.cycle 6 9 true (0),
.last 17 (4,false),
.last 37 (4,false),
.cycle 2 37 true (0),
.last 17 (4,false),
.cycle 2 15 true (0),
.cycle 2 17 true (0),
.last 21 (4,false),
.cycle 2 21 true (-1),
.last 19 (4,false),
.cycle 13 2 true (1),
.cycle 2 21 true (0),
.last 42 (4,false),
.last 17 (4,false),
.cycle 2 15 true (0),
.last 37 (4,false),
.last 17 (4,false),
.cycle 2 15 true (0)
])
theorem kid11_part1406_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1406) = true := by rfl

def kid11_part1407 : Audit := .cycle 5 9 true (0)
theorem kid11_part1407_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1407) = true := by rfl

def kid11_part1408 : Audit := .split 17 (4,false) (byMove [
.cycle 13 20 true (1),
.cycle 15 7 true (3),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 16 2 true (4),
.cycle 17 2 true (4),
.cycle 0 18 true (0),
.cycle 13 19 true (1),
.cycle 17 9 true (4),
.cycle 3 15 true (0),
.cycle 17 1 true (5),
.cycle 15 6 true (3),
.cycle 14 10 true (2),
.cycle 17 3 true (4),
.last 18 (2,true),
.cycle 13 23 true (1),
.cycle 15 3 true (3),
.cycle 16 3 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 13 24 true (1),
.cycle 17 1 true (5),
.cycle 16 4 true (4)
])
theorem kid11_part1408_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1408) = true := by rfl

def kid11_part1409 : Audit := .split 17 (4,false) (byMove [
.cycle 35 3 true (7),
.cycle 14 7 true (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 18 3 true (4),
.cycle 16 2 true (4),
.cycle 0 18 true (0),
.cycle 34 3 true (8),
.cycle 16 9 true (4),
.cycle 3 15 true (0),
.cycle 17 1 true (5),
.cycle 14 6 true (2),
.cycle 25 3 true (5),
.cycle 16 3 true (4),
.last 18 (2,true),
.cycle 12 23 true (0),
.cycle 15 3 true (3),
.cycle 18 3 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 2 16 true (0),
.cycle 12 24 true (0),
.cycle 17 1 true (5),
.cycle 18 3 true (5)
])
theorem kid11_part1409_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1409) = true := by rfl

def kid11_part1385 : Audit := .split 13 (4,true) (byMove [(kid11_part1386),(kid11_part1387),(kid11_part1388),(kid11_part1389),(kid11_part1390),(kid11_part1391),(kid11_part1392),(kid11_part1393),(kid11_part1394),(kid11_part1395),(kid11_part1396),(kid11_part1397),(kid11_part1398),(kid11_part1399),(kid11_part1400),(kid11_part1401),(kid11_part1402),(kid11_part1403),(kid11_part1404),(kid11_part1405),(kid11_part1406),(kid11_part1407),(kid11_part1408),(kid11_part1409)])

theorem kid11_part1385_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1385) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 13 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1386),(kid11_part1387),(kid11_part1388),(kid11_part1389),(kid11_part1390),(kid11_part1391),(kid11_part1392),(kid11_part1393),(kid11_part1394),(kid11_part1395),(kid11_part1396),(kid11_part1397),(kid11_part1398),(kid11_part1399),(kid11_part1400),(kid11_part1401),(kid11_part1402),(kid11_part1403),(kid11_part1404),(kid11_part1405),(kid11_part1406),(kid11_part1407),(kid11_part1408),(kid11_part1409)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1386_checked

  · exact kid11_part1392_checked

  · exact kid11_part1398_checked

  · exact kid11_part1404_checked

  · exact kid11_part1387_checked

  · exact kid11_part1393_checked

  · exact kid11_part1399_checked

  · exact kid11_part1405_checked

  · exact kid11_part1388_checked

  · exact kid11_part1394_checked

  · exact kid11_part1400_checked

  · exact kid11_part1406_checked

  · exact kid11_part1389_checked

  · exact kid11_part1395_checked

  · exact kid11_part1401_checked

  · exact kid11_part1407_checked

  · exact kid11_part1390_checked

  · exact kid11_part1396_checked

  · exact kid11_part1402_checked

  · exact kid11_part1408_checked

  · exact kid11_part1391_checked

  · exact kid11_part1397_checked

  · exact kid11_part1403_checked

  · exact kid11_part1409_checked

def kid11_part1410 : Audit := .cycle 15 3 true (3)
theorem kid11_part1410_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1410) = true := by rfl

def kid11_part1290 : Audit := .split 12 (5,true) (byMove [(kid11_part1291),(kid11_part1292),(kid11_part1293),(kid11_part1294),(kid11_part1295),(kid11_part1320),(kid11_part1321),(kid11_part1322),(kid11_part1323),(kid11_part1324),(kid11_part1325),(kid11_part1350),(kid11_part1351),(kid11_part1352),(kid11_part1353),(kid11_part1354),(kid11_part1355),(kid11_part1380),(kid11_part1381),(kid11_part1382),(kid11_part1383),(kid11_part1384),(kid11_part1385),(kid11_part1410)])

theorem kid11_part1290_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (kid11_part1290) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part1291),(kid11_part1292),(kid11_part1293),(kid11_part1294),(kid11_part1295),(kid11_part1320),(kid11_part1321),(kid11_part1322),(kid11_part1323),(kid11_part1324),(kid11_part1325),(kid11_part1350),(kid11_part1351),(kid11_part1352),(kid11_part1353),(kid11_part1354),(kid11_part1355),(kid11_part1380),(kid11_part1381),(kid11_part1382),(kid11_part1383),(kid11_part1384),(kid11_part1385),(kid11_part1410)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1291_checked

  · exact kid11_part1321_checked

  · exact kid11_part1351_checked

  · exact kid11_part1381_checked

  · exact kid11_part1292_checked

  · exact kid11_part1322_checked

  · exact kid11_part1352_checked

  · exact kid11_part1382_checked

  · exact kid11_part1293_checked

  · exact kid11_part1323_checked

  · exact kid11_part1353_checked

  · exact kid11_part1383_checked

  · exact kid11_part1294_checked

  · exact kid11_part1324_checked

  · exact kid11_part1354_checked

  · exact kid11_part1384_checked

  · exact kid11_part1295_checked

  · exact kid11_part1325_checked

  · exact kid11_part1355_checked

  · exact kid11_part1385_checked

  · exact kid11_part1320_checked

  · exact kid11_part1350_checked

  · exact kid11_part1380_checked

  · exact kid11_part1410_checked

def kid11_part1411 : Audit := .cycle 0 9 true (0)
theorem kid11_part1411_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,0⟩)) (kid11_part1411) = true := by rfl

def kid11_part1412 : Audit := .cycle 1 8 true (1)
theorem kid11_part1412_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,1⟩)) (kid11_part1412) = true := by rfl

def kid11_part1413 : Audit := .cycle 2 7 true (1)
theorem kid11_part1413_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,2⟩)) (kid11_part1413) = true := by rfl

def kid11_part1414 : Audit := .cycle 1 11 true (1)
theorem kid11_part1414_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,3⟩)) (kid11_part1414) = true := by rfl

def kid11_part1416 : Audit := .cycle 1 10 true (1)
theorem kid11_part1416_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid11_part1416) = true := by rfl

def kid11_part1417 : Audit := .cycle 7 3 true (3)
theorem kid11_part1417_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid11_part1417) = true := by rfl

def kid11_part1419 : Audit := .cycle 0 11 true (0)
theorem kid11_part1419_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1419) = true := by rfl

def kid11_part1420 : Audit := .cycle 1 10 true (1)
theorem kid11_part1420_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1420) = true := by rfl

def kid11_part1421 : Audit := .split 19 (5,true) (byMove [
.cycle 26 1 false (2),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.cycle 22 1 false (4),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.cycle 24 1 false (2),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.last 21 (4,true),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 27 1 false (3)
])
theorem kid11_part1421_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1421) = true := by rfl

def kid11_part1422 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 28 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 28 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 20 1 false (4),
.cycle 21 1 false (3),
.cycle 36 1 false (6),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 20 1 false (2),
.cycle 0 22 true (0)
])
theorem kid11_part1422_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1422) = true := by rfl

def kid11_part1423 : Audit := .split 19 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 32 1 false (4),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 25 1 false (1),
.cycle 0 20 true (0),
.cycle 32 1 false (6),
.cycle 21 1 false (5),
.cycle 20 1 false (4),
.cycle 22 1 false (4),
.cycle 25 1 false (3),
.cycle 29 1 false (1),
.last 22 (4,true),
.cycle 0 22 true (0),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (0),
.cycle 31 1 false (5),
.cycle 35 1 false (7),
.cycle 24 1 false (2),
.last 23 (4,true)
])
theorem kid11_part1423_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1423) = true := by rfl

def kid11_part1424 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 false (5),
.cycle 28 3 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.cycle 21 3 false (0),
.cycle 0 21 true (0),
.cycle 28 3 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 21 3 false (2),
.cycle 14 9 false (3),
.cycle 19 3 false (1),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.last 22 (4,true),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 3 false (4),
.cycle 31 3 false (6),
.cycle 21 3 false (1),
.cycle 17 4 true (0)
])
theorem kid11_part1424_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1424) = true := by rfl

def kid11_part1425 : Audit := .cycle 0 11 true (0)
theorem kid11_part1425_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1425) = true := by rfl

def kid11_part1426 : Audit := .cycle 1 10 true (1)
theorem kid11_part1426_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1426) = true := by rfl

def kid11_part1427 : Audit := .split 21 (5,true) (byMove [
.cycle 0 61 true (0),
.cycle 48 34 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 33 1 false (9),
.cycle 0 25 true (0),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 29 1 false (9),
.last 22 (4,true),
.cycle 29 1 false (9),
.cycle 26 17 true (4),
.cycle 10 16 true (0),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.last 23 (4,true),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.cycle 65 1 false (17),
.cycle 5 17 true (0),
.last 22 (4,true),
.cycle 24 11 true (6)
])
theorem kid11_part1427_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1427) = true := by rfl

def kid11_part1428 : Audit := .split 19 (5,true) (byMove [
.cycle 0 24 true (0),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.cycle 0 22 true (0),
.cycle 32 1 false (10),
.last 20 (4,true),
.cycle 25 1 false (7),
.cycle 24 12 true (4),
.cycle 0 55 true (0),
.cycle 27 1 false (7),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.last 21 (4,true),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 0 22 true (0),
.cycle 5 73 true (0),
.last 20 (4,true),
.cycle 3 22 true (0)
])
theorem kid11_part1428_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1428) = true := by rfl

def kid11_part1429 : Audit := .split 21 (5,true) (byMove [
.last 25 (4,true),
.cycle 0 59 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.cycle 27 1 false (3),
.cycle 29 1 false (7),
.cycle 36 1 false (10),
.last 23 (4,true),
.cycle 36 1 false (10),
.last 22 (4,true),
.cycle 29 1 false (7),
.cycle 26 14 true (4),
.last 24 (4,true),
.cycle 31 1 false (7),
.cycle 22 1 false (2),
.cycle 24 1 false (2),
.last 23 (4,true),
.cycle 0 63 true (0),
.cycle 1 23 true (0),
.last 23 (4,true),
.cycle 5 79 true (0),
.last 22 (4,true),
.cycle 2 26 true (0)
])
theorem kid11_part1429_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1429) = true := by rfl

def kid11_part1430 : Audit := .cycle 8 3 true (4)
theorem kid11_part1430_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1430) = true := by rfl

def kid11_part1431 : Audit := .cycle 7 5 true (3)
theorem kid11_part1431_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1431) = true := by rfl

def kid11_part1432 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.cycle 26 1 false (2),
.cycle 31 7 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 42 1 false (8),
.cycle 40 1 false (10),
.last 26 (4,true),
.cycle 8 7 true (3),
.cycle 7 9 true (3),
.cycle 11 4 true (3),
.cycle 0 17 true (0),
.cycle 22 1 false (2),
.cycle 26 1 false (2),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (3),
.cycle 12 5 true (3)
])
theorem kid11_part1432_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1432) = true := by rfl

def kid11_part1433 : Audit := .cycle 0 13 true (0)
theorem kid11_part1433_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1433) = true := by rfl

def kid11_part1434 : Audit := .split 17 (5,true) (byMove [
.cycle 0 49 true (0),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.cycle 21 1 false (1),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.cycle 19 1 false (3),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.cycle 26 1 false (4),
.cycle 31 1 false (7),
.cycle 18 1 false (2),
.cycle 20 1 false (2),
.last 19 (4,true),
.cycle 0 48 true (0),
.cycle 29 1 false (5),
.cycle 31 1 false (7),
.cycle 0 19 true (0),
.last 18 (4,true),
.cycle 17 27 true (3)
])
theorem kid11_part1434_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1434) = true := by rfl

def kid11_part1435 : Audit := .split 19 (5,true) (byMove [
.last 23 (4,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.cycle 25 1 false (1),
.cycle 33 1 false (7),
.cycle 26 1 false (4),
.cycle 23 1 false (3),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 26 1 false (4),
.last 30 (4,true),
.last 22 (4,true),
.cycle 35 1 false (7),
.cycle 20 1 false (2),
.cycle 22 1 false (2),
.last 21 (4,true),
.cycle 0 54 true (0),
.cycle 28 1 false (2),
.last 21 (4,true),
.cycle 0 21 true (0),
.last 20 (4,true),
.last 24 (4,true)
])
theorem kid11_part1435_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1435) = true := by rfl

def kid11_part1436 : Audit := .split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 20 (5,true),
.cycle 0 14 true (0),
.cycle 29 1 false (1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.last 20 (5,true),
.cycle 1 14 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 15 (5,true),
.last 16 (5,true)
])
theorem kid11_part1436_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1436) = true := by rfl

def kid11_part1437 : Audit := .cycle 0 11 true (0)
theorem kid11_part1437_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1437) = true := by rfl

def kid11_part1438 : Audit := .cycle 1 10 true (1)
theorem kid11_part1438_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1438) = true := by rfl

def kid11_part1439 : Audit := .cycle 2 9 true (1)
theorem kid11_part1439_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1439) = true := by rfl

def kid11_part1440 : Audit := .cycle 1 13 true (1)
theorem kid11_part1440_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1440) = true := by rfl

def kid11_part1441 : Audit := .cycle 9 2 true (4)
theorem kid11_part1441_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1441) = true := by rfl

def kid11_part1442 : Audit := .cycle 8 3 true (4)
theorem kid11_part1442_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1442) = true := by rfl

def kid11_part1418 : Audit := .split 10 (2,true) (byMove [(kid11_part1419),(kid11_part1420),(kid11_part1421),(kid11_part1422),(kid11_part1423),(kid11_part1424),(kid11_part1425),(kid11_part1426),(kid11_part1427),(kid11_part1428),(kid11_part1429),(kid11_part1430),(kid11_part1431),(kid11_part1432),(kid11_part1433),(kid11_part1434),(kid11_part1435),(kid11_part1436),(kid11_part1437),(kid11_part1438),(kid11_part1439),(kid11_part1440),(kid11_part1441),(kid11_part1442)])

theorem kid11_part1418_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid11_part1418) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part1419),(kid11_part1420),(kid11_part1421),(kid11_part1422),(kid11_part1423),(kid11_part1424),(kid11_part1425),(kid11_part1426),(kid11_part1427),(kid11_part1428),(kid11_part1429),(kid11_part1430),(kid11_part1431),(kid11_part1432),(kid11_part1433),(kid11_part1434),(kid11_part1435),(kid11_part1436),(kid11_part1437),(kid11_part1438),(kid11_part1439),(kid11_part1440),(kid11_part1441),(kid11_part1442)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1419_checked

  · exact kid11_part1425_checked

  · exact kid11_part1431_checked

  · exact kid11_part1437_checked

  · exact kid11_part1420_checked

  · exact kid11_part1426_checked

  · exact kid11_part1432_checked

  · exact kid11_part1438_checked

  · exact kid11_part1421_checked

  · exact kid11_part1427_checked

  · exact kid11_part1433_checked

  · exact kid11_part1439_checked

  · exact kid11_part1422_checked

  · exact kid11_part1428_checked

  · exact kid11_part1434_checked

  · exact kid11_part1440_checked

  · exact kid11_part1423_checked

  · exact kid11_part1429_checked

  · exact kid11_part1435_checked

  · exact kid11_part1441_checked

  · exact kid11_part1424_checked

  · exact kid11_part1430_checked

  · exact kid11_part1436_checked

  · exact kid11_part1442_checked

def kid11_part1443 : Audit := .cycle 0 11 true (0)
theorem kid11_part1443_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid11_part1443) = true := by rfl

def kid11_part1445 : Audit := .cycle 0 11 true (0)
theorem kid11_part1445_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1445) = true := by rfl

def kid11_part1446 : Audit := .cycle 1 10 true (1)
theorem kid11_part1446_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1446) = true := by rfl

def kid11_part1447 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 23 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 32 1 false (8),
.cycle 25 1 false (5),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 22 1 false (4),
.cycle 25 1 false (5),
.cycle 2 26 true (0),
.last 21 (2,true),
.cycle 34 1 false (8),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.last 22 (2,true),
.cycle 0 54 true (0),
.cycle 34 1 false (6),
.last 20 (2,true),
.cycle 0 21 true (0),
.last 21 (2,true),
.last 24 (2,true)
])
theorem kid11_part1447_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1447) = true := by rfl

def kid11_part1448 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 28 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 28 1 false (6),
.cycle 19 1 false (5),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 21 1 false (3),
.cycle 36 1 false (6),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 0 21 true (0),
.cycle 0 18 true (0),
.cycle 1 17 true (0),
.cycle 27 1 false (5),
.cycle 31 1 false (7),
.cycle 20 1 false (2),
.cycle 0 22 true (0)
])
theorem kid11_part1448_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1448) = true := by rfl

def kid11_part1449 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1449_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1449) = true := by rfl

def kid11_part1450 : Audit := .split 20 (5,true) (byMove [
.cycle 0 21 false (5),
.cycle 28 3 false (3),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 21 3 false (0),
.cycle 0 21 true (0),
.cycle 28 3 false (5),
.cycle 22 1 false (2),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 21 3 false (2),
.cycle 14 9 false (3),
.last 22 (2,true),
.cycle 0 23 true (-1),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 19 3 false (1),
.cycle 0 21 true (0),
.cycle 1 20 true (0),
.cycle 27 3 false (4),
.cycle 31 3 false (6),
.cycle 21 3 false (1),
.cycle 17 4 true (0)
])
theorem kid11_part1450_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1450) = true := by rfl

def kid11_part1451 : Audit := .cycle 0 11 true (0)
theorem kid11_part1451_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1451) = true := by rfl

def kid11_part1452 : Audit := .cycle 1 10 true (1)
theorem kid11_part1452_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1452) = true := by rfl

def kid11_part1453 : Audit := .split 21 (5,true) (byMove [
.last 24 (2,true),
.cycle 48 34 true (4),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 33 1 false (9),
.cycle 0 25 true (0),
.cycle 29 1 false (9),
.last 22 (2,true),
.cycle 29 1 false (9),
.last 23 (2,true),
.cycle 29 1 false (9),
.cycle 26 17 true (4),
.last 23 (2,true),
.cycle 0 29 true (0),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.last 24 (2,true),
.cycle 0 25 true (0),
.cycle 22 13 true (4),
.last 22 (2,true),
.cycle 5 17 true (0),
.last 23 (2,true),
.cycle 24 11 true (6)
])
theorem kid11_part1453_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1453) = true := by rfl

def kid11_part1454 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 23 1 false (3),
.cycle 25 1 false (7),
.cycle 32 1 false (10),
.last 20 (2,true),
.cycle 32 1 false (10),
.cycle 0 22 true (0),
.cycle 25 1 false (7),
.cycle 24 12 true (4),
.last 21 (2,true),
.cycle 27 1 false (7),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 0 55 true (0),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 5 73 true (0),
.cycle 0 22 true (0),
.cycle 3 22 true (0)
])
theorem kid11_part1454_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1454) = true := by rfl

def kid11_part1455 : Audit := .cycle 17 1 false (1)
theorem kid11_part1455_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1455) = true := by rfl

def kid11_part1456 : Audit := .cycle 8 3 true (4)
theorem kid11_part1456_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1456) = true := by rfl

def kid11_part1457 : Audit := .cycle 7 5 true (3)
theorem kid11_part1457_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1457) = true := by rfl

def kid11_part1458 : Audit := .split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 21 (5,true),
.cycle 0 14 true (0),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 20 (5,true),
.cycle 3 10 true (1),
.last 27 (5,true),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.last 14 (5,true),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.last 16 (5,true),
.last 17 (5,true)
])
theorem kid11_part1458_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1458) = true := by rfl

def kid11_part1459 : Audit := .cycle 0 13 true (0)
theorem kid11_part1459_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1459) = true := by rfl

def kid11_part1460 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 29 1 false (7),
.cycle 22 1 false (4),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 19 1 false (3),
.cycle 22 1 false (4),
.cycle 4 22 true (0),
.last 19 (2,true),
.cycle 31 1 false (7),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 26 1 false (4),
.cycle 0 48 true (0),
.cycle 29 1 false (5),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 31 1 false (7),
.cycle 17 27 true (3)
])
theorem kid11_part1460_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1460) = true := by rfl

def kid11_part1461 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1461_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1461) = true := by rfl

def kid11_part1462 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 1 false (-2),
.cycle 20 6 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 10 4 true (3),
.cycle 8 7 true (3),
.cycle 15 11 true (3),
.last 15 (2,true),
.cycle 1 16 true (1),
.cycle 20 1 false (2),
.cycle 20 1 false (-2),
.cycle 20 3 false (0),
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 12 2 true (3),
.cycle 12 5 true (3)
])
theorem kid11_part1462_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1462) = true := by rfl

def kid11_part1463 : Audit := .cycle 0 11 true (0)
theorem kid11_part1463_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1463) = true := by rfl

def kid11_part1464 : Audit := .cycle 1 10 true (1)
theorem kid11_part1464_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1464) = true := by rfl

def kid11_part1465 : Audit := .cycle 2 9 true (1)
theorem kid11_part1465_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1465) = true := by rfl

def kid11_part1466 : Audit := .cycle 1 13 true (1)
theorem kid11_part1466_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1466) = true := by rfl

def kid11_part1467 : Audit := .cycle 9 2 true (4)
theorem kid11_part1467_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1467) = true := by rfl

def kid11_part1468 : Audit := .cycle 8 3 true (4)
theorem kid11_part1468_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1468) = true := by rfl

def kid11_part1444 : Audit := .split 10 (4,true) (byMove [(kid11_part1445),(kid11_part1446),(kid11_part1447),(kid11_part1448),(kid11_part1449),(kid11_part1450),(kid11_part1451),(kid11_part1452),(kid11_part1453),(kid11_part1454),(kid11_part1455),(kid11_part1456),(kid11_part1457),(kid11_part1458),(kid11_part1459),(kid11_part1460),(kid11_part1461),(kid11_part1462),(kid11_part1463),(kid11_part1464),(kid11_part1465),(kid11_part1466),(kid11_part1467),(kid11_part1468)])

theorem kid11_part1444_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid11_part1444) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1445),(kid11_part1446),(kid11_part1447),(kid11_part1448),(kid11_part1449),(kid11_part1450),(kid11_part1451),(kid11_part1452),(kid11_part1453),(kid11_part1454),(kid11_part1455),(kid11_part1456),(kid11_part1457),(kid11_part1458),(kid11_part1459),(kid11_part1460),(kid11_part1461),(kid11_part1462),(kid11_part1463),(kid11_part1464),(kid11_part1465),(kid11_part1466),(kid11_part1467),(kid11_part1468)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1445_checked

  · exact kid11_part1451_checked

  · exact kid11_part1457_checked

  · exact kid11_part1463_checked

  · exact kid11_part1446_checked

  · exact kid11_part1452_checked

  · exact kid11_part1458_checked

  · exact kid11_part1464_checked

  · exact kid11_part1447_checked

  · exact kid11_part1453_checked

  · exact kid11_part1459_checked

  · exact kid11_part1465_checked

  · exact kid11_part1448_checked

  · exact kid11_part1454_checked

  · exact kid11_part1460_checked

  · exact kid11_part1466_checked

  · exact kid11_part1449_checked

  · exact kid11_part1455_checked

  · exact kid11_part1461_checked

  · exact kid11_part1467_checked

  · exact kid11_part1450_checked

  · exact kid11_part1456_checked

  · exact kid11_part1462_checked

  · exact kid11_part1468_checked

def kid11_part1469 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (3),
.cycle 18 1 false (2),
.cycle 15 4 false (1),
.cycle 20 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.split 22 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 8, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 95 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 28 1 false (4),
.cycle 40 1 false (12),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.cycle 26 1 false (8),
.cycle 36 1 false (12),
.last 23 (4,true),
.cycle 29 1 false (9),
.cycle 24 15 true (4),
.cycle 38 1 false (8),
.cycle 31 1 false (9),
.cycle 23 1 false (3),
.cycle 35 1 false (9),
.last 24 (4,true),
.cycle 27 38 true (4),
.cycle 1 34 true (0),
.cycle 2 23 true (0),
.cycle 10 42 true (0),
.last 23 (4,true),
.cycle 27 24 true (4)
]),
.cycle 32 1 false (10),
.cycle 8 4 true (4),
.cycle 8 3 true (4),
.cycle 7 5 true (3),
.split 12 (2,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 26 1 false (2),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.cycle 10 8 true (3),
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.cycle 1 16 true (1),
.cycle 1 14 true (1),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.cycle 10 6 true (3),
.cycle 10 7 true (3)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (2),
.cycle 15 4 false (1),
.split 12 (4,true) (byMove [
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 7 false (0),
.cycle 20 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 10 10 true (3),
.cycle 3 10 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 5 true (3),
.cycle 6 7 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 1 14 true (1),
.cycle 18 7 false (0),
.cycle 20 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 15 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 0, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 26 5 false (2)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 13 true (1),
.cycle 9 2 true (4),
.cycle 8 3 true (4)
])
theorem kid11_part1469_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid11_part1469) = true := by rfl

def kid11_part1470 : Audit := .cycle 0 10 true (0)
theorem kid11_part1470_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid11_part1470) = true := by rfl

def kid11_part1471 : Audit := .cycle 1 9 true (1)
theorem kid11_part1471_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid11_part1471) = true := by rfl

def kid11_part1472 : Audit := .split 17 (5,true) (byMove [
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 31 1 false (3),
.cycle 28 1 false (2),
.cycle 0 41 true (0),
.cycle 8 10 true (4),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.split 32 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 0 143 true (0),
.cycle 34 1 false (4),
.cycle 33 1 false (3),
.cycle 42 1 false (10),
.cycle 41 28 true (6),
.cycle 56 1 false (18),
.cycle 39 1 false (11),
.cycle 39 1 false (11),
.cycle 38 1 false (10),
.last 33 (4,true),
.cycle 39 1 false (11),
.cycle 34 42 true (4),
.cycle 63 1 false (11),
.cycle 60 1 false (18),
.cycle 33 1 false (3),
.cycle 32 2 true (3),
.last 34 (4,true),
.cycle 0 105 true (0),
.cycle 1 47 true (0),
.cycle 2 36 true (0),
.cycle 0 90 true (0),
.last 33 (4,true),
.cycle 33 24 true (5)
]),
.cycle 0 35 true (0),
.split 34 (4,true) (byMove [
.last 37 (2,true),
.cycle 0 45 true (0),
.cycle 36 1 false (4),
.cycle 35 1 false (3),
.cycle 0 45 true (0),
.last 37 (2,true),
.cycle 53 1 false (17),
.cycle 60 1 false (20),
.last 35 (2,true),
.cycle 0 41 true (0),
.cycle 43 1 false (13),
.cycle 53 1 false (17),
.cycle 36 35 true (4),
.last 36 (2,true),
.cycle 57 1 false (17),
.cycle 35 1 false (3),
.last 36 (2,true),
.cycle 33 4 true (3),
.cycle 35 88 true (5),
.cycle 1 40 true (0),
.last 35 (2,true),
.cycle 0 41 true (0),
.cycle 37 26 true (7),
.cycle 39 38 true (9)
]),
.cycle 8 10 true (4),
.cycle 7 12 true (3),
.split 19 (2,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.cycle 36 1 false (2),
.cycle 0 21 true (0),
.last 20 (4,true),
.cycle 37 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.last 32 (4,true),
.cycle 8 12 true (4),
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.cycle 1 23 true (1),
.cycle 1 21 true (1),
.last 20 (4,true),
.cycle 37 3 false (1),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.cycle 0 20 true (0),
.cycle 28 1 false (2),
.split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 35 1 false (3),
.cycle 32 1 false (2),
.cycle 0 47 true (0),
.cycle 8 12 true (4),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 43 1 false (11),
.cycle 0 41 true (0),
.last 38 (4,true),
.cycle 8 12 true (4),
.cycle 7 14 true (3),
.cycle 16 6 true (6),
.cycle 0 22 true (0),
.cycle 32 1 false (2),
.cycle 18 2 true (6),
.last 21 (4,true),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.split 19 (4,true) (byMove [
.cycle 1 20 true (1),
.cycle 7 13 true (3),
.last 20 (2,true),
.cycle 0 21 true (0),
.cycle 39 1 false (3),
.cycle 36 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 10 10 true (4),
.cycle 3 17 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 4, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 8 12 true (4),
.cycle 6 14 true (2),
.cycle 16 4 true (6),
.last 20 (2,true),
.cycle 1 21 true (1),
.last 22 (2,true),
.cycle 36 3 false (0),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 1 22 true (1),
.cycle 9 11 true (4),
.cycle 8 12 true (4)
]),
.cycle 0 18 true (0),
.cycle 1 17 true (1),
.cycle 2 16 true (1),
.cycle 1 20 true (1),
.cycle 9 9 true (4),
.cycle 8 10 true (4)
])
theorem kid11_part1472_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid11_part1472) = true := by rfl

def kid11_part1473 : Audit := .cycle 3 7 true (1)
theorem kid11_part1473_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid11_part1473) = true := by rfl

def kid11_part1474 : Audit := .cycle 9 1 true (5)
theorem kid11_part1474_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid11_part1474) = true := by rfl

def kid11_part1475 : Audit := .cycle 8 2 true (4)
theorem kid11_part1475_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid11_part1475) = true := by rfl

def kid11_part1476 : Audit := .cycle 6 4 true (2)
theorem kid11_part1476_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid11_part1476) = true := by rfl

def kid11_part1477 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 29 1 false (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 20 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (3),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (3),
.cycle 6 9 true (2),
.cycle 28 5 false (1),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 20 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 36 9 false (2),
.cycle 45 13 false (3)
]),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 24 (2,true) (byMove [
.far false 1 ⟨0,[0, 0],[2, 4, 8, 38, 4, 16, 64],[2, 32, 4, 1, 64, 4, 64],64⟩,
.cycle 10 42 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.last 28 (4,true),
.cycle 45 1 false (9),
.cycle 29 1 false (9),
.cycle 40 1 false (14),
.cycle 29 1 false (9),
.cycle 33 1 false (11),
.last 25 (4,true),
.cycle 29 1 false (9),
.cycle 26 30 true (4),
.cycle 45 1 false (9),
.cycle 31 1 false (9),
.cycle 25 1 false (3),
.last 28 (4,true),
.last 26 (4,true),
.cycle 0 69 true (0),
.cycle 1 27 true (0),
.cycle 2 26 true (0),
.cycle 5 20 true (0),
.last 25 (4,true),
.cycle 10 24 true (0)
]),
.cycle 29 1 false (9),
.split 14 (2,true) (byMove [
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.last 26 (4,true),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 11 4 true (5),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 11 true (4),
.cycle 3 12 true (1),
.cycle 12 3 true (5),
.cycle 8 7 true (4),
.cycle 6 9 true (2),
.cycle 10 5 true (4),
.cycle 1 18 true (1),
.cycle 1 16 true (1),
.last 15 (4,true),
.last 16 (4,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 1 17 true (1),
.cycle 9 6 true (4),
.cycle 8 7 true (4)
]),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 28 1 false (2),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 25 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.cycle 12 3 true (4),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.cycle 1 17 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 25 3 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4)
]),
.cycle 0 14 true (0),
.cycle 20 1 false (2),
.split 14 (2,true) (byMove [
.cycle 1 18 true (1),
.last 17 (4,true),
.cycle 29 1 false (1),
.cycle 7 10 true (3),
.last 15 (4,true),
.last 20 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 36, 4, 1024, 128, 256, 8, 2, 4, 1024, 4096],[2, 32, 4, 1, 4096, 4, 2, 32, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 32 7 false (2),
.cycle 10 6 true (3),
.cycle 28 5 false (1),
.cycle 5 12 true (1),
.cycle 5 10 true (1),
.last 15 (4,true),
.last 20 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.last 16 (4,true)
]),
.split 13 (4,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 17 (2,true),
.cycle 24 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 10 true (4),
.cycle 3 11 true (1),
.last 16 (2,true),
.cycle 8 6 true (4),
.cycle 6 8 true (2),
.cycle 10 4 true (4),
.last 14 (2,true),
.cycle 1 15 true (1),
.last 17 (2,true),
.cycle 24 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (4),
.cycle 8 6 true (4)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1477_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid11_part1477) = true := by rfl

def kid11_part1479 : Audit := .cycle 1 14 true (1)
theorem kid11_part1479_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid11_part1479) = true := by rfl

def kid11_part1480 : Audit := .cycle 0 14 true (0)
theorem kid11_part1480_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid11_part1480) = true := by rfl

def kid11_part1481 : Audit := .split 19 (5,true) (byMove [
.cycle 26 1 false (2),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 29 1 false (3),
.cycle 24 1 false (2),
.cycle 26 1 false (6),
.cycle 33 1 false (9),
.cycle 22 1 false (4),
.cycle 33 1 false (9),
.last 20 (4,true),
.cycle 26 1 false (6),
.cycle 24 12 true (4),
.cycle 24 1 false (2),
.cycle 28 1 false (6),
.cycle 20 1 false (2),
.cycle 41 1 false (9),
.last 21 (4,true),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.cycle 23 1 false (3),
.cycle 5 73 true (0),
.last 20 (4,true),
.cycle 29 1 false (3)
])
theorem kid11_part1481_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid11_part1481) = true := by rfl

def kid11_part1482 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 36 1 false (6),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 0 25 true (0),
.cycle 21 1 false (1),
.cycle 0 29 true (0),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 32 1 false (8),
.last 19 (4,true),
.last 21 (4,true),
.cycle 0 25 true (0),
.cycle 0 31 true (0),
.cycle 18 1 false (2),
.cycle 0 25 true (0),
.last 19 (4,true),
.cycle 0 29 true (0),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 25 1 false (5),
.cycle 20 1 false (2),
.last 19 (4,true)
])
theorem kid11_part1482_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid11_part1482) = true := by rfl

def kid11_part1483 : Audit := .split 27 (4,true) (byMove [
.cycle 1 28 true (1),
.cycle 7 21 true (2),
.cycle 9 20 true (2),
.cycle 0 29 true (0),
.cycle 9 20 true (2),
.last 28 (5,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.last 35 (5,true),
.cycle 3 25 true (1),
.cycle 0 31 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 262178, 131105, 1024, 128, 256, 32768, 2, 131104, 1024, 2, 4, 8, 32, 1, 16, 262144],[2, 32, 1168, 1, 32, 262144, 8192, 131072, 1040, 4096, 131072, 262144, 2, 32, 1040, 1, 32, 262144, 262144],286732⟩,
.cycle 6 22 true (2),
.last 29 (5,true),
.cycle 18 10 true (2),
.cycle 1 29 true (1),
.last 36 (5,true),
.last 28 (5,true),
.cycle 0 28 true (0),
.cycle 1 27 true (1),
.cycle 2 26 true (1),
.cycle 1 30 true (1),
.proven (BB6.Agent11Raw39B0RBPumps.M929.table) (fun m hm => BB6.Agent11Raw39B0RBPumps.M929.never m hm),
.cycle 26 6 true (6)
])
theorem kid11_part1483_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid11_part1483) = true := by rfl

def kid11_part1484 : Audit := .split 20 (5,true) (byMove [
.cycle 0 28 true (-1),
.cycle 64 47 true (1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.last 28 (4,true),
.cycle 21 3 false (0),
.cycle 0 48 true (0),
.cycle 40 3 false (9),
.cycle 27 1 false (7),
.cycle 21 1 false (1),
.last 27 (4,true),
.last 22 (4,true),
.last 24 (4,true),
.cycle 19 3 false (1),
.cycle 0 58 true (-1),
.cycle 21 1 false (-1),
.cycle 60 3 false (9),
.last 22 (4,true),
.cycle 0 69 true (0),
.cycle 1 32 true (0),
.cycle 25 65 true (0),
.cycle 5 105 true (0),
.cycle 21 3 false (1),
.last 22 (4,true)
])
theorem kid11_part1484_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid11_part1484) = true := by rfl

def kid11_part1485 : Audit := .cycle 1 11 true (1)
theorem kid11_part1485_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid11_part1485) = true := by rfl

def kid11_part1486 : Audit := .cycle 7 4 true (3)
theorem kid11_part1486_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid11_part1486) = true := by rfl

def kid11_part1487 : Audit := .split 23 (5,true) (byMove [
.cycle 0 80 true (0),
.cycle 0 93 true (0),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 48 1 false (14),
.cycle 33 1 false (9),
.cycle 40 1 false (14),
.cycle 40 1 false (14),
.cycle 29 1 false (9),
.cycle 28 1 false (8),
.last 24 (4,true),
.cycle 33 1 false (11),
.cycle 28 22 true (4),
.cycle 10 18 true (0),
.cycle 44 1 false (14),
.cycle 24 1 false (2),
.cycle 52 1 false (14),
.last 25 (4,true),
.cycle 0 75 true (0),
.cycle 1 27 true (0),
.cycle 83 1 false (21),
.cycle 0 68 true (0),
.last 24 (4,true),
.cycle 26 14 true (6)
])
theorem kid11_part1487_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid11_part1487) = true := by rfl

def kid11_part1488 : Audit := .cycle 0 12 true (0)
theorem kid11_part1488_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid11_part1488) = true := by rfl

def kid11_part1489 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 19 (5,true),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1489_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid11_part1489) = true := by rfl

def kid11_part1490 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (9),
.cycle 29 1 false (9),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 8 6 true (4),
.cycle 0 14 true (0),
.cycle 20 1 false (2),
.cycle 1 15 true (1),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1490_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid11_part1490) = true := by rfl

def kid11_part1491 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 0 32 true (0),
.cycle 8 12 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 7 18 true (3),
.cycle 36 1 false (8),
.cycle 0 17 true (0),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.cycle 6 10 true (2),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 41 5 false (7),
.last 15 (4,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 12 6 true (4)
])
theorem kid11_part1491_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid11_part1491) = true := by rfl

def kid11_part1492 : Audit := .split 14 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 18 true (0),
.cycle 25 1 false (3),
.cycle 22 1 false (2),
.last 39 (4,true),
.cycle 31 7 false (1),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 53 1 false (9),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 8 8 true (3),
.cycle 7 12 true (3),
.cycle 11 4 true (3),
.cycle 1 17 true (1),
.cycle 22 1 false (2),
.cycle 5 12 true (1),
.last 16 (4,true),
.cycle 1 15 true (1),
.cycle 7 8 true (3),
.cycle 2 16 true (1),
.cycle 0 16 true (0),
.last 15 (4,true),
.cycle 12 6 true (3)
])
theorem kid11_part1492_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid11_part1492) = true := by rfl

def kid11_part1493 : Audit := .cycle 1 13 true (1)
theorem kid11_part1493_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid11_part1493) = true := by rfl

def kid11_part1494 : Audit := .split 17 (5,true) (byMove [
.cycle 5 16 true (0),
.cycle 0 51 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 26 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (5),
.cycle 30 1 false (8),
.cycle 19 1 false (3),
.cycle 30 1 false (8),
.last 18 (4,true),
.cycle 23 1 false (5),
.cycle 22 10 true (4),
.cycle 38 1 false (8),
.cycle 25 1 false (5),
.cycle 18 1 false (2),
.cycle 38 1 false (8),
.last 19 (4,true),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.cycle 25 1 false (5),
.cycle 5 67 true (0),
.last 18 (4,true),
.cycle 5 18 true (0)
])
theorem kid11_part1494_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid11_part1494) = true := by rfl

def kid11_part1495 : Audit := .cycle 5 8 true (1)
theorem kid11_part1495_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid11_part1495) = true := by rfl

def kid11_part1496 : Audit := .split 12 (4,true) (byMove [
.last 16 (5,true),
.cycle 7 9 true (3),
.last 20 (5,true),
.cycle 7 8 true (3),
.last 20 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 23 (5,true),
.cycle 0 14 true (0),
.cycle 0 17 true (0),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.last 20 (5,true),
.cycle 5 8 true (1),
.last 19 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.last 16 (5,true),
.last 13 (5,true)
])
theorem kid11_part1496_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid11_part1496) = true := by rfl

def kid11_part1497 : Audit := .cycle 1 11 true (1)
theorem kid11_part1497_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid11_part1497) = true := by rfl

def kid11_part1498 : Audit := .cycle 7 4 true (3)
theorem kid11_part1498_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid11_part1498) = true := by rfl

def kid11_part1499 : Audit := .cycle 2 10 true (1)
theorem kid11_part1499_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid11_part1499) = true := by rfl

def kid11_part1500 : Audit := .cycle 0 12 true (0)
theorem kid11_part1500_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid11_part1500) = true := by rfl

def kid11_part1501 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 9 4 true (4),
.cycle 0 13 true (0),
.cycle 0 16 true (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.cycle 5 10 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1501_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid11_part1501) = true := by rfl

def kid11_part1502 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 8 5 true (4),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 27 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 35 24 true (5),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 8 8 true (4),
.cycle 10 2 true (4),
.cycle 1 13 true (1),
.last 12 (4,true),
.last 14 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1502_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid11_part1502) = true := by rfl

def kid11_part1478 : Audit := .split 10 (2,true) (byMove [(kid11_part1479),(kid11_part1480),(kid11_part1481),(kid11_part1482),(kid11_part1483),(kid11_part1484),(kid11_part1485),(kid11_part1486),(kid11_part1487),(kid11_part1488),(kid11_part1489),(kid11_part1490),(kid11_part1491),(kid11_part1492),(kid11_part1493),(kid11_part1494),(kid11_part1495),(kid11_part1496),(kid11_part1497),(kid11_part1498),(kid11_part1499),(kid11_part1500),(kid11_part1501),(kid11_part1502)])

theorem kid11_part1478_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid11_part1478) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid11_part1479),(kid11_part1480),(kid11_part1481),(kid11_part1482),(kid11_part1483),(kid11_part1484),(kid11_part1485),(kid11_part1486),(kid11_part1487),(kid11_part1488),(kid11_part1489),(kid11_part1490),(kid11_part1491),(kid11_part1492),(kid11_part1493),(kid11_part1494),(kid11_part1495),(kid11_part1496),(kid11_part1497),(kid11_part1498),(kid11_part1499),(kid11_part1500),(kid11_part1501),(kid11_part1502)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1479_checked

  · exact kid11_part1485_checked

  · exact kid11_part1491_checked

  · exact kid11_part1497_checked

  · exact kid11_part1480_checked

  · exact kid11_part1486_checked

  · exact kid11_part1492_checked

  · exact kid11_part1498_checked

  · exact kid11_part1481_checked

  · exact kid11_part1487_checked

  · exact kid11_part1493_checked

  · exact kid11_part1499_checked

  · exact kid11_part1482_checked

  · exact kid11_part1488_checked

  · exact kid11_part1494_checked

  · exact kid11_part1500_checked

  · exact kid11_part1483_checked

  · exact kid11_part1489_checked

  · exact kid11_part1495_checked

  · exact kid11_part1501_checked

  · exact kid11_part1484_checked

  · exact kid11_part1490_checked

  · exact kid11_part1496_checked

  · exact kid11_part1502_checked

def kid11_part1503 : Audit := .cycle 1 11 true (1)
theorem kid11_part1503_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid11_part1503) = true := by rfl

def kid11_part1505 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.last 23 (5,true),
.cycle 0 15 true (0),
.cycle 1 15 true (1),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 21 (5,true),
.cycle 3 11 true (1),
.cycle 0 21 true (0),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.last 15 (5,true),
.cycle 5 12 true (1),
.cycle 1 15 true (1),
.cycle 10 8 true (3),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (4),
.cycle 12 6 true (4)
])
theorem kid11_part1505_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,0⟩)) (kid11_part1505) = true := by rfl

def kid11_part1506 : Audit := .cycle 0 14 true (0)
theorem kid11_part1506_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,1⟩)) (kid11_part1506) = true := by rfl

def kid11_part1507 : Audit := .split 19 (5,true) (byMove [
.last 22 (2,true),
.cycle 0 55 true (0),
.cycle 21 1 false (3),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 26 1 false (6),
.cycle 33 1 false (9),
.last 20 (2,true),
.cycle 33 1 false (9),
.cycle 22 1 false (4),
.cycle 26 1 false (6),
.cycle 24 12 true (4),
.last 21 (2,true),
.cycle 28 1 false (6),
.cycle 20 1 false (2),
.cycle 20 1 false (2),
.last 22 (2,true),
.cycle 0 57 true (0),
.cycle 1 21 true (0),
.last 20 (2,true),
.cycle 5 73 true (0),
.last 21 (2,true),
.last 25 (2,true)
])
theorem kid11_part1507_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,2⟩)) (kid11_part1507) = true := by rfl

def kid11_part1508 : Audit := .split 17 (5,true) (byMove [
.cycle 0 22 true (0),
.cycle 36 1 false (6),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.last 27 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 18 1 false (4),
.cycle 18 1 false (4),
.cycle 0 21 true (0),
.cycle 0 23 true (0),
.last 19 (2,true),
.last 29 (2,true),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.last 23 (2,true),
.last 27 (2,true),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 25 1 false (5),
.cycle 20 1 false (2),
.cycle 0 21 true (0)
])
theorem kid11_part1508_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,3⟩)) (kid11_part1508) = true := by rfl

def kid11_part1509 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1509_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,4⟩)) (kid11_part1509) = true := by rfl

def kid11_part1510 : Audit := .split 20 (5,true) (byMove [
.cycle 0 28 true (-1),
.cycle 64 47 true (1),
.cycle 22 1 false (0),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 21 3 false (0),
.cycle 0 48 true (0),
.last 22 (2,true),
.cycle 27 1 false (7),
.cycle 21 1 false (1),
.cycle 21 1 false (1),
.cycle 33 3 false (6),
.cycle 32 19 true (2),
.last 22 (2,true),
.cycle 0 58 true (-1),
.cycle 21 1 false (-1),
.cycle 21 1 false (-1),
.cycle 19 3 false (1),
.cycle 0 69 true (0),
.last 22 (2,true),
.last 62 (2,true),
.cycle 5 105 true (0),
.cycle 21 3 false (1),
.cycle 28 7 true (3)
])
theorem kid11_part1510_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,false,5⟩)) (kid11_part1510) = true := by rfl

def kid11_part1511 : Audit := .cycle 1 11 true (1)
theorem kid11_part1511_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,0⟩)) (kid11_part1511) = true := by rfl

def kid11_part1512 : Audit := .cycle 7 4 true (3)
theorem kid11_part1512_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,1⟩)) (kid11_part1512) = true := by rfl

def kid11_part1513 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 18 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (5,true),
.last 21 (5,true),
.cycle 26 1 false (8),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 15 (5,true),
.cycle 0 14 true (0),
.last 19 (5,true),
.cycle 18 1 false (0),
.last 21 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1513_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,2⟩)) (kid11_part1513) = true := by rfl

def kid11_part1514 : Audit := .cycle 0 12 true (0)
theorem kid11_part1514_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,3⟩)) (kid11_part1514) = true := by rfl

def kid11_part1515 : Audit := .cycle 25 1 false (7)
theorem kid11_part1515_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,4⟩)) (kid11_part1515) = true := by rfl

def kid11_part1516 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 23 1 false (3),
.cycle 20 1 false (2),
.cycle 18 1 false (0),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 24 (2,true),
.cycle 29 1 false (9),
.cycle 29 1 false (9),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 20 1 false (2),
.cycle 18 1 false (0),
.cycle 8 6 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1516_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨false,true,5⟩)) (kid11_part1516) = true := by rfl

def kid11_part1517 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 29 1 false (1),
.cycle 8 12 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 23 (2,true),
.cycle 36 1 false (8),
.cycle 10 11 true (2),
.cycle 8 6 true (3),
.cycle 7 8 true (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 29 1 false (1),
.cycle 6 10 true (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 9 5 true (3),
.cycle 12 6 true (4)
])
theorem kid11_part1517_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,0⟩)) (kid11_part1517) = true := by rfl

def kid11_part1518 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 17 (5,true),
.last 21 (5,true),
.cycle 7 8 true (3),
.last 21 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 22 (5,true),
.cycle 0 14 true (0),
.last 20 (5,true),
.last 13 (5,true),
.last 15 (5,true),
.last 14 (5,true),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.last 21 (5,true),
.last 13 (5,true),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 15 (5,true),
.last 13 (5,true)
])
theorem kid11_part1518_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,1⟩)) (kid11_part1518) = true := by rfl

def kid11_part1519 : Audit := .cycle 1 13 true (1)
theorem kid11_part1519_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,2⟩)) (kid11_part1519) = true := by rfl

def kid11_part1520 : Audit := .split 17 (5,true) (byMove [
.last 20 (2,true),
.cycle 0 51 true (0),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 21 1 false (1),
.cycle 23 1 false (5),
.cycle 30 1 false (8),
.last 18 (2,true),
.cycle 30 1 false (8),
.cycle 19 1 false (3),
.cycle 23 1 false (5),
.cycle 22 10 true (4),
.last 19 (2,true),
.cycle 25 1 false (5),
.cycle 18 1 false (2),
.cycle 18 1 false (2),
.cycle 38 1 false (8),
.cycle 0 51 true (0),
.cycle 1 19 true (0),
.last 18 (2,true),
.cycle 5 67 true (0),
.cycle 25 1 false (5),
.cycle 5 18 true (0)
])
theorem kid11_part1520_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,3⟩)) (kid11_part1520) = true := by rfl

def kid11_part1521 : Audit := .cycle 15 1 false (-1)
theorem kid11_part1521_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,4⟩)) (kid11_part1521) = true := by rfl

def kid11_part1522 : Audit := .split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 1 17 true (1),
.cycle 23 1 false (3),
.cycle 22 1 false (2),
.cycle 20 1 false (-2),
.cycle 20 6 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 10 4 true (3),
.cycle 8 8 true (3),
.cycle 15 14 true (3),
.last 15 (2,true),
.cycle 5 10 true (1),
.cycle 20 1 false (2),
.cycle 20 1 false (-2),
.cycle 20 3 false (0),
.cycle 6 8 true (2),
.cycle 1 15 true (1),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 12 2 true (3),
.cycle 12 6 true (3)
])
theorem kid11_part1522_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,false,5⟩)) (kid11_part1522) = true := by rfl

def kid11_part1523 : Audit := .cycle 1 11 true (1)
theorem kid11_part1523_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,0⟩)) (kid11_part1523) = true := by rfl

def kid11_part1524 : Audit := .cycle 7 4 true (3)
theorem kid11_part1524_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,1⟩)) (kid11_part1524) = true := by rfl

def kid11_part1525 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 21 (5,true),
.cycle 0 13 true (0),
.cycle 2 11 true (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 19 (5,true),
.cycle 3 9 true (1),
.cycle 2 15 true (1),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 13 (5,true),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1525_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,2⟩)) (kid11_part1525) = true := by rfl

def kid11_part1526 : Audit := .cycle 0 12 true (0)
theorem kid11_part1526_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,3⟩)) (kid11_part1526) = true := by rfl

def kid11_part1527 : Audit := .cycle 9 3 true (4)
theorem kid11_part1527_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,4⟩)) (kid11_part1527) = true := by rfl

def kid11_part1528 : Audit := .split 11 (5,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 8 5 true (4),
.cycle 27 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 34 (2,true),
.cycle 3 9 true (1),
.cycle 8 9 true (4),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.last 15 (2,true),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 10 2 true (4),
.cycle 26 5 false (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1528_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some ⟨true,true,5⟩)) (kid11_part1528) = true := by rfl

def kid11_part1504 : Audit := .split 10 (4,true) (byMove [(kid11_part1505),(kid11_part1506),(kid11_part1507),(kid11_part1508),(kid11_part1509),(kid11_part1510),(kid11_part1511),(kid11_part1512),(kid11_part1513),(kid11_part1514),(kid11_part1515),(kid11_part1516),(kid11_part1517),(kid11_part1518),(kid11_part1519),(kid11_part1520),(kid11_part1521),(kid11_part1522),(kid11_part1523),(kid11_part1524),(kid11_part1525),(kid11_part1526),(kid11_part1527),(kid11_part1528)])

theorem kid11_part1504_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid11_part1504) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 10 (4,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (4,true) (some mv)) (byMove [(kid11_part1505),(kid11_part1506),(kid11_part1507),(kid11_part1508),(kid11_part1509),(kid11_part1510),(kid11_part1511),(kid11_part1512),(kid11_part1513),(kid11_part1514),(kid11_part1515),(kid11_part1516),(kid11_part1517),(kid11_part1518),(kid11_part1519),(kid11_part1520),(kid11_part1521),(kid11_part1522),(kid11_part1523),(kid11_part1524),(kid11_part1525),(kid11_part1526),(kid11_part1527),(kid11_part1528)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1505_checked

  · exact kid11_part1511_checked

  · exact kid11_part1517_checked

  · exact kid11_part1523_checked

  · exact kid11_part1506_checked

  · exact kid11_part1512_checked

  · exact kid11_part1518_checked

  · exact kid11_part1524_checked

  · exact kid11_part1507_checked

  · exact kid11_part1513_checked

  · exact kid11_part1519_checked

  · exact kid11_part1525_checked

  · exact kid11_part1508_checked

  · exact kid11_part1514_checked

  · exact kid11_part1520_checked

  · exact kid11_part1526_checked

  · exact kid11_part1509_checked

  · exact kid11_part1515_checked

  · exact kid11_part1521_checked

  · exact kid11_part1527_checked

  · exact kid11_part1510_checked

  · exact kid11_part1516_checked

  · exact kid11_part1522_checked

  · exact kid11_part1528_checked

def kid11_part1530 : Audit := .split 13 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 7 7 true (3),
.cycle 0 24 true (0),
.cycle 0 15 true (0),
.last 14 (4,true),
.cycle 1 15 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 0 22 true (0),
.cycle 3 11 true (1),
.last 16 (4,true),
.cycle 8 6 true (3),
.cycle 6 8 true (2),
.cycle 0 16 true (0),
.cycle 5 12 true (1),
.cycle 1 15 true (1),
.last 14 (4,true),
.cycle 10 8 true (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 16 true (1),
.cycle 12 5 true (4),
.cycle 12 6 true (4)
])
theorem kid11_part1530_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid11_part1530) = true := by rfl

def kid11_part1531 : Audit := .cycle 0 14 true (0)
theorem kid11_part1531_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid11_part1531) = true := by rfl

def kid11_part1532 : Audit := .cycle 21 1 false (3)
theorem kid11_part1532_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid11_part1532) = true := by rfl

def kid11_part1533 : Audit := .cycle 18 1 false (2)
theorem kid11_part1533_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid11_part1533) = true := by rfl

def kid11_part1534 : Audit := .split 13 (4,true) (byMove [
.cycle 0 18 true (0),
.cycle 25 7 false (1),
.last 14 (2,true),
.last 17 (2,true),
.cycle 17 4 false (-1),
.cycle 16 4 false (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 51, 33, 16, 64],[2, 32, 64, 1, 1, 18, 64],64⟩,
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 3 20 true (1),
.cycle 17 3 true (5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 32, 16, 64],[2, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 6 12 true (2),
.cycle 22 5 false (0),
.last 14 (2,true),
.last 17 (2,true),
.cycle 17 4 false (-1),
.cycle 16 4 false (0),
.cycle 0 26 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 19 8 false (1),
.cycle 13 6 true (3)
])
theorem kid11_part1534_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid11_part1534) = true := by rfl

def kid11_part1535 : Audit := .cycle 20 3 false (0)
theorem kid11_part1535_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid11_part1535) = true := by rfl

def kid11_part1536 : Audit := .cycle 1 11 true (1)
theorem kid11_part1536_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid11_part1536) = true := by rfl

def kid11_part1537 : Audit := .cycle 7 4 true (3)
theorem kid11_part1537_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid11_part1537) = true := by rfl

def kid11_part1538 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (4),
.cycle 21 1 false (3),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (9),
.cycle 36 1 false (12),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.cycle 49 1 false (9),
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.last 14 (4,true),
.last 13 (4,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1538_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid11_part1538) = true := by rfl

def kid11_part1539 : Audit := .cycle 0 12 true (0)
theorem kid11_part1539_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid11_part1539) = true := by rfl

def kid11_part1540 : Audit := .split 11 (4,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (4),
.cycle 21 1 false (3),
.cycle 19 4 false (1),
.cycle 8 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 36 1 false (12),
.cycle 11 3 true (5),
.cycle 8 4 true (4),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 19 4 false (1),
.cycle 10 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1540_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid11_part1540) = true := by rfl

def kid11_part1541 : Audit := .cycle 8 4 true (4)
theorem kid11_part1541_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid11_part1541) = true := by rfl

def kid11_part1542 : Audit := .cycle 7 8 true (3)
theorem kid11_part1542_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid11_part1542) = true := by rfl

def kid11_part1543 : Audit := .split 12 (2,true) (byMove [
.cycle 1 16 true (1),
.last 15 (4,true),
.cycle 26 1 false (2),
.cycle 7 8 true (3),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 10 12 true (3),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.cycle 5 10 true (1),
.cycle 5 8 true (1),
.last 13 (4,true),
.cycle 21 3 false (1),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 13 (4,true),
.cycle 10 12 true (3)
])
theorem kid11_part1543_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid11_part1543) = true := by rfl

def kid11_part1544 : Audit := .cycle 1 13 true (1)
theorem kid11_part1544_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid11_part1544) = true := by rfl

def kid11_part1545 : Audit := .cycle 18 1 false (2)
theorem kid11_part1545_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid11_part1545) = true := by rfl

def kid11_part1546 : Audit := .split 13 (4,true) (byMove [
.last 16 (2,true),
.cycle 7 13 true (2),
.last 14 (2,true),
.cycle 28 9 false (2),
.cycle 17 4 false (-1),
.cycle 16 4 false (0),
.cycle 6 8 true (2),
.cycle 7 12 true (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 15 3 true (5),
.cycle 16 6 false (2),
.cycle 10 6 true (2),
.cycle 22 5 false (0),
.last 14 (2,true),
.cycle 5 16 true (1),
.cycle 17 4 false (-1),
.cycle 16 4 false (0),
.cycle 6 8 true (2),
.cycle 22 12 false (2),
.last 14 (2,true),
.cycle 1 15 true (1),
.cycle 13 5 true (3),
.cycle 13 2 true (3)
])
theorem kid11_part1546_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid11_part1546) = true := by rfl

def kid11_part1547 : Audit := .split 12 (4,true) (byMove [
.last 15 (2,true),
.cycle 7 9 true (3),
.last 13 (2,true),
.cycle 7 8 true (3),
.cycle 17 4 false (1),
.cycle 20 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 13 3 true (5),
.cycle 8 8 true (3),
.cycle 6 12 true (2),
.cycle 10 4 true (3),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 17 4 false (1),
.cycle 20 3 false (0),
.cycle 1 13 true (1),
.cycle 7 6 true (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 50, 16, 16, 64],[2, 32, 64, 1, 16, 16, 64],64⟩,
.cycle 24 5 false (2)
])
theorem kid11_part1547_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid11_part1547) = true := by rfl

def kid11_part1548 : Audit := .cycle 1 11 true (1)
theorem kid11_part1548_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid11_part1548) = true := by rfl

def kid11_part1549 : Audit := .cycle 7 4 true (3)
theorem kid11_part1549_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid11_part1549) = true := by rfl

def kid11_part1550 : Audit := .split 11 (2,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.cycle 25 1 false (3),
.cycle 0 13 true (0),
.last 12 (4,true),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 18 true (1),
.cycle 3 9 true (1),
.last 14 (4,true),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 2 12 true (1),
.cycle 1 15 true (1),
.cycle 1 13 true (1),
.last 12 (4,true),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1550_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid11_part1550) = true := by rfl

def kid11_part1551 : Audit := .cycle 0 12 true (0)
theorem kid11_part1551_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid11_part1551) = true := by rfl

def kid11_part1552 : Audit := .split 11 (4,true) (byMove [
.cycle 1 12 true (1),
.cycle 7 5 true (3),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 19 4 false (1),
.cycle 9 4 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 9 11 true (4),
.cycle 3 9 true (1),
.cycle 11 3 true (5),
.cycle 8 4 true (4),
.cycle 6 6 true (2),
.cycle 9 5 true (4),
.last 12 (2,true),
.cycle 1 13 true (1),
.cycle 19 4 false (1),
.cycle 10 2 true (4),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 14 true (1),
.cycle 9 3 true (4),
.cycle 8 4 true (4)
])
theorem kid11_part1552_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid11_part1552) = true := by rfl

def kid11_part1553 : Audit := .cycle 8 4 true (4)
theorem kid11_part1553_checked : zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid11_part1553) = true := by rfl

def kid11_part1529 : Audit := .split 10 (5,true) (byMove [(kid11_part1530),(kid11_part1531),(kid11_part1532),(kid11_part1533),(kid11_part1534),(kid11_part1535),(kid11_part1536),(kid11_part1537),(kid11_part1538),(kid11_part1539),(kid11_part1540),(kid11_part1541),(kid11_part1542),(kid11_part1543),(kid11_part1544),(kid11_part1545),(kid11_part1546),(kid11_part1547),(kid11_part1548),(kid11_part1549),(kid11_part1550),(kid11_part1551),(kid11_part1552),(kid11_part1553)])

theorem kid11_part1529_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid11_part1529) = true := by

  change (zipQueryOK 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 1271 (refine (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid11_part1530),(kid11_part1531),(kid11_part1532),(kid11_part1533),(kid11_part1534),(kid11_part1535),(kid11_part1536),(kid11_part1537),(kid11_part1538),(kid11_part1539),(kid11_part1540),(kid11_part1541),(kid11_part1542),(kid11_part1543),(kid11_part1544),(kid11_part1545),(kid11_part1546),(kid11_part1547),(kid11_part1548),(kid11_part1549),(kid11_part1550),(kid11_part1551),(kid11_part1552),(kid11_part1553)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1530_checked

  · exact kid11_part1536_checked

  · exact kid11_part1542_checked

  · exact kid11_part1548_checked

  · exact kid11_part1531_checked

  · exact kid11_part1537_checked

  · exact kid11_part1543_checked

  · exact kid11_part1549_checked

  · exact kid11_part1532_checked

  · exact kid11_part1538_checked

  · exact kid11_part1544_checked

  · exact kid11_part1550_checked

  · exact kid11_part1533_checked

  · exact kid11_part1539_checked

  · exact kid11_part1545_checked

  · exact kid11_part1551_checked

  · exact kid11_part1534_checked

  · exact kid11_part1540_checked

  · exact kid11_part1546_checked

  · exact kid11_part1552_checked

  · exact kid11_part1535_checked

  · exact kid11_part1541_checked

  · exact kid11_part1547_checked

  · exact kid11_part1553_checked

def kid11_part1554 : Audit := .cycle 0 10 true (0)
theorem kid11_part1554_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid11_part1554) = true := by rfl

def kid11_part1555 : Audit := .cycle 1 9 true (1)
theorem kid11_part1555_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid11_part1555) = true := by rfl

def kid11_part1556 : Audit := .cycle 2 8 true (1)
theorem kid11_part1556_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid11_part1556) = true := by rfl

def kid11_part1557 : Audit := .cycle 1 12 true (1)
theorem kid11_part1557_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid11_part1557) = true := by rfl

def kid11_part1558 : Audit := .cycle 9 1 true (5)
theorem kid11_part1558_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid11_part1558) = true := by rfl

def kid11_part1559 : Audit := .cycle 8 2 true (4)
theorem kid11_part1559_checked : zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid11_part1559) = true := by rfl

def kid11_part1415 : Audit := .split 9 (4,false) (byMove [(kid11_part1416),(kid11_part1417),(kid11_part1418),(kid11_part1443),(kid11_part1444),(kid11_part1469),(kid11_part1470),(kid11_part1471),(kid11_part1472),(kid11_part1473),(kid11_part1474),(kid11_part1475),(kid11_part1476),(kid11_part1477),(kid11_part1478),(kid11_part1503),(kid11_part1504),(kid11_part1529),(kid11_part1554),(kid11_part1555),(kid11_part1556),(kid11_part1557),(kid11_part1558),(kid11_part1559)])

theorem kid11_part1415_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (kid11_part1415) = true := by

  change (zipQueryOK 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 1271 (refine (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid11_part1416),(kid11_part1417),(kid11_part1418),(kid11_part1443),(kid11_part1444),(kid11_part1469),(kid11_part1470),(kid11_part1471),(kid11_part1472),(kid11_part1473),(kid11_part1474),(kid11_part1475),(kid11_part1476),(kid11_part1477),(kid11_part1478),(kid11_part1503),(kid11_part1504),(kid11_part1529),(kid11_part1554),(kid11_part1555),(kid11_part1556),(kid11_part1557),(kid11_part1558),(kid11_part1559)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1416_checked

  · exact kid11_part1470_checked

  · exact kid11_part1476_checked

  · exact kid11_part1554_checked

  · exact kid11_part1417_checked

  · exact kid11_part1471_checked

  · exact kid11_part1477_checked

  · exact kid11_part1555_checked

  · exact kid11_part1418_checked

  · exact kid11_part1472_checked

  · exact kid11_part1478_checked

  · exact kid11_part1556_checked

  · exact kid11_part1443_checked

  · exact kid11_part1473_checked

  · exact kid11_part1503_checked

  · exact kid11_part1557_checked

  · exact kid11_part1444_checked

  · exact kid11_part1474_checked

  · exact kid11_part1504_checked

  · exact kid11_part1558_checked

  · exact kid11_part1469_checked

  · exact kid11_part1475_checked

  · exact kid11_part1529_checked

  · exact kid11_part1559_checked

def kid11_part1560 : Audit := .cycle 8 1 true (4)
theorem kid11_part1560_checked : zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some ⟨true,true,5⟩)) (kid11_part1560) = true := by rfl

def kid11 : Audit := .split 8 (5,false) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part76),(kid11_part149),(kid11_part318),(kid11_part367),(kid11_part368),(kid11_part369),(kid11_part490),(kid11_part587),(kid11_part804),(kid11_part805),(kid11_part806),(kid11_part927),(kid11_part928),(kid11_part1001),(kid11_part1290),(kid11_part1411),(kid11_part1412),(kid11_part1413),(kid11_part1414),(kid11_part1415),(kid11_part1560)])

theorem check11 : zipCheck 1271 (child ⟨false,true,5⟩) (kid11) = true := by

  change (zipQueryOK 1271 (child ⟨false,true,5⟩) 8 (5,false) && allMoves (fun mv => zipCheck 1271 (refine (child ⟨false,true,5⟩) (5,false) (some mv)) (byMove [(kid11_part1),(kid11_part2),(kid11_part3),(kid11_part76),(kid11_part149),(kid11_part318),(kid11_part367),(kid11_part368),(kid11_part369),(kid11_part490),(kid11_part587),(kid11_part804),(kid11_part805),(kid11_part806),(kid11_part927),(kid11_part928),(kid11_part1001),(kid11_part1290),(kid11_part1411),(kid11_part1412),(kid11_part1413),(kid11_part1414),(kid11_part1415),(kid11_part1560)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid11_part1_checked

  · exact kid11_part367_checked

  · exact kid11_part805_checked

  · exact kid11_part1411_checked

  · exact kid11_part2_checked

  · exact kid11_part368_checked

  · exact kid11_part806_checked

  · exact kid11_part1412_checked

  · exact kid11_part3_checked

  · exact kid11_part369_checked

  · exact kid11_part927_checked

  · exact kid11_part1413_checked

  · exact kid11_part76_checked

  · exact kid11_part490_checked

  · exact kid11_part928_checked

  · exact kid11_part1414_checked

  · exact kid11_part149_checked

  · exact kid11_part587_checked

  · exact kid11_part1001_checked

  · exact kid11_part1415_checked

  · exact kid11_part318_checked

  · exact kid11_part804_checked

  · exact kid11_part1290_checked

  · exact kid11_part1560_checked

end BB6.Agent11Raw39B0RB
