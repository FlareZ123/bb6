import Raw39B0REBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid05_part1 : Audit := .cycle 0 9 true (0)
theorem kid05_part1_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,0⟩)) (kid05_part1) = true := by rfl

def kid05_part2 : Audit := .cycle 1 8 true (1)
theorem kid05_part2_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,1⟩)) (kid05_part2) = true := by rfl

def kid05_part3 : Audit := .cycle 17 1 false (1)
theorem kid05_part3_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,2⟩)) (kid05_part3) = true := by rfl

def kid05_part5 : Audit := .cycle 0 13 true (0)
theorem kid05_part5_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part5) = true := by rfl

def kid05_part6 : Audit := .cycle 21 1 false (1)
theorem kid05_part6_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part6) = true := by rfl

def kid05_part7 : Audit := .cycle 14 1 false (2)
theorem kid05_part7_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part7) = true := by rfl

def kid05_part8 : Audit := .cycle 13 1 false (1)
theorem kid05_part8_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part8) = true := by rfl

def kid05_part9 : Audit := .cycle 12 1 false (2)
theorem kid05_part9_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part9) = true := by rfl

def kid05_part10 : Audit := .cycle 14 1 false (0)
theorem kid05_part10_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part10) = true := by rfl

def kid05_part11 : Audit := .cycle 0 13 true (0)
theorem kid05_part11_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part11) = true := by rfl

def kid05_part12 : Audit := .cycle 21 1 false (3)
theorem kid05_part12_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part12) = true := by rfl

def kid05_part13 : Audit := .cycle 14 1 false (4)
theorem kid05_part13_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part13) = true := by rfl

def kid05_part14 : Audit := .cycle 13 1 false (3)
theorem kid05_part14_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part14) = true := by rfl

def kid05_part15 : Audit := .cycle 12 1 true (2)
theorem kid05_part15_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part15) = true := by rfl

def kid05_part16 : Audit := .cycle 14 1 false (2)
theorem kid05_part16_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part16) = true := by rfl

def kid05_part17 : Audit := .split 14 (1,true) (byMove [
.cycle 11 4 true (1),
.cycle 24 1 false (0),
.split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 24 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 12 4 true (1),
.cycle 17 1 false (1),
.cycle 13 3 false (2),
.cycle 20 1 false (0),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 23 1 false (1),
.cycle 9 7 true (0),
.cycle 20 1 false (0),
.cycle 0 18 true (0)
]),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 24 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 12 4 true (1),
.cycle 17 1 false (1),
.cycle 13 3 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 23 1 false (1),
.cycle 9 7 true (0),
.cycle 20 1 false (0),
.cycle 0 18 true (0)
]),
.cycle 0 15 true (0),
.cycle 29 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 12 3 true (1),
.cycle 8 7 true (0),
.cycle 18 1 false (0),
.split 17 (2,true) (byMove [
.cycle 11 7 false (2),
.cycle 15 3 false (1),
.cycle 20 1 false (0),
.cycle 13 6 true (0),
.cycle 20 1 false (-2),
.last 18 (5,true),
.cycle 11 7 true (0),
.cycle 3 26 true (0),
.cycle 28 1 false (0),
.cycle 0 19 true (0),
.cycle 0 21 true (0),
.last 18 (5,true),
.cycle 21 1 false (-1),
.cycle 15 3 false (1),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.last 18 (5,true),
.cycle 25 44 true (-1),
.cycle 14 5 false (2),
.cycle 2 17 true (0),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true)
]),
.split 15 (2,true) (byMove [
.cycle 11 13 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 0 19 true (0),
.cycle 18 1 false (4),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 13 3 false (2),
.cycle 24 1 false (0),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 14 2 true (1),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
]),
.cycle 10 5 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (2),
.cycle 13 3 false (2),
.last 17 (2,true),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 14 2 true (1),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 22 1 false (0),
.cycle 0 19 true (0)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 9 6 true (0),
.cycle 0 20 true (0),
.cycle 0 17 true (0)
])
theorem kid05_part17_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part17) = true := by rfl

def kid05_part18 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (1),
.split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 24 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 12 4 true (1),
.cycle 17 1 false (1),
.cycle 21 1 false (-1),
.cycle 13 3 false (2),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 23 1 false (1),
.cycle 9 7 true (0),
.last 19 (5,true),
.cycle 0 18 true (0)
]),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 24 1 false (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 24 1 false (2),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 12 4 true (1),
.cycle 17 1 false (1),
.last 17 (1,true),
.cycle 13 3 false (2),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 23 1 false (1),
.cycle 9 7 true (0),
.last 17 (1,true),
.cycle 0 18 true (0)
]),
.cycle 0 15 true (0),
.cycle 29 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 12 3 true (1),
.cycle 8 7 true (0),
.cycle 18 1 false (0),
.split 15 (1,true) (byMove [
.cycle 11 9 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 25 1 false (3),
.cycle 13 4 true (1),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.last 16 (5,true),
.cycle 21 1 false (-1),
.cycle 13 3 false (2),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.cycle 1 16 true (0),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
]),
.cycle 10 7 true (0),
.cycle 10 5 true (0),
.cycle 17 1 false (-1),
.split 15 (5,true) (byMove [
.cycle 11 9 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.last 16 (1,true),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 18 1 false (0),
.cycle 18 1 false (2),
.last 17 (1,true),
.cycle 13 3 false (2),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.cycle 12 4 false (2),
.cycle 17 1 false (-1),
.cycle 11 5 true (1),
.last 16 (1,true),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.last 19 (1,true),
.cycle 0 19 true (0)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 9 6 true (0),
.split 16 (1,true) (byMove [
.last 22 (5,true),
.cycle 26 1 false (0),
.cycle 21 1 false (1),
.cycle 0 21 true (0),
.cycle 19 1 false (-1),
.last 17 (5,true),
.cycle 11 6 true (1),
.cycle 33 1 false (1),
.cycle 14 3 true (2),
.cycle 0 18 true (0),
.cycle 0 20 true (0),
.last 17 (5,true),
.cycle 20 1 false (0),
.last 21 (5,true),
.last 19 (5,true),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.last 17 (5,true),
.cycle 11 6 true (1),
.cycle 1 17 true (0),
.cycle 14 3 true (2),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 17 (5,true)
]),
.cycle 0 17 true (0)
])
theorem kid05_part18_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part18) = true := by rfl

def kid05_part19 : Audit := .cycle 0 15 true (0)
theorem kid05_part19_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part19) = true := by rfl

def kid05_part20 : Audit := .cycle 13 1 false (1)
theorem kid05_part20_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part20) = true := by rfl

def kid05_part21 : Audit := .cycle 12 1 false (2)
theorem kid05_part21_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part21) = true := by rfl

def kid05_part22 : Audit := .cycle 14 1 false (0)
theorem kid05_part22_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part22) = true := by rfl

def kid05_part23 : Audit := .cycle 0 13 true (0)
theorem kid05_part23_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part23) = true := by rfl

def kid05_part24 : Audit := .cycle 1 12 true (0)
theorem kid05_part24_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part24) = true := by rfl

def kid05_part25 : Audit := .cycle 20 1 false (2)
theorem kid05_part25_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part25) = true := by rfl

def kid05_part26 : Audit := .cycle 9 4 true (0)
theorem kid05_part26_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part26) = true := by rfl

def kid05_part27 : Audit := .cycle 12 1 true (2)
theorem kid05_part27_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part27) = true := by rfl

def kid05_part28 : Audit := .cycle 0 15 true (0)
theorem kid05_part28_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part28) = true := by rfl

def kid05_part4 : Audit := .split 12 (4,false) (byMove [(kid05_part5),(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part19),(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28)])

theorem kid05_part4_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (kid05_part4) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) 12 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,3⟩)) (4,false) (some mv)) (byMove [(kid05_part5),(kid05_part6),(kid05_part7),(kid05_part8),(kid05_part9),(kid05_part10),(kid05_part11),(kid05_part12),(kid05_part13),(kid05_part14),(kid05_part15),(kid05_part16),(kid05_part17),(kid05_part18),(kid05_part19),(kid05_part20),(kid05_part21),(kid05_part22),(kid05_part23),(kid05_part24),(kid05_part25),(kid05_part26),(kid05_part27),(kid05_part28)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part5_checked

  · exact kid05_part11_checked

  · exact kid05_part17_checked

  · exact kid05_part23_checked

  · exact kid05_part6_checked

  · exact kid05_part12_checked

  · exact kid05_part18_checked

  · exact kid05_part24_checked

  · exact kid05_part7_checked

  · exact kid05_part13_checked

  · exact kid05_part19_checked

  · exact kid05_part25_checked

  · exact kid05_part8_checked

  · exact kid05_part14_checked

  · exact kid05_part20_checked

  · exact kid05_part26_checked

  · exact kid05_part9_checked

  · exact kid05_part15_checked

  · exact kid05_part21_checked

  · exact kid05_part27_checked

  · exact kid05_part10_checked

  · exact kid05_part16_checked

  · exact kid05_part22_checked

  · exact kid05_part28_checked

def kid05_part30 : Audit := .cycle 0 12 true (0)
theorem kid05_part30_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part30) = true := by rfl

def kid05_part31 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 false (3),
.cycle 11 9 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 9 false (0),
.cycle 11 9 false (-1),
.cycle 0 11 true (0),
.cycle 11 9 false (3),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 9 false (2),
.cycle 11 9 false (1),
.cycle 13 9 false (0),
.split 12 (2,true) (byMove [
.cycle 14 9 false (1),
.cycle 10 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 13 9 false (-1),
.last 13 (5,true),
.cycle 0 13 true (-1),
.cycle 1 21 false (3),
.cycle 15 9 false (1),
.cycle 13 9 false (1),
.cycle 1 13 false (3),
.cycle 8 5 false (2),
.cycle 13 9 false (0),
.cycle 10 3 false (0),
.cycle 17 9 false (2),
.cycle 15 9 false (2),
.cycle 13 9 false (-1),
.last 13 (5,true),
.last 32 (5,true),
.cycle 22 5 false (0),
.cycle 2 11 false (3),
.cycle 1 25 false (3),
.last 19 (5,true),
.last 15 (5,true)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 0 15 true (-2),
.cycle 11 9 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 11 9 false (2),
.cycle 14 9 false (3),
.cycle 9 2 true (0),
.cycle 12 9 false (0)
])
theorem kid05_part31_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part31) = true := by rfl

def kid05_part32 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 false (3),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 11 true (0),
.cycle 21 1 false (1),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.split 12 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 24 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 14 true (-1),
.cycle 17 1 false (-3),
.last 13 (5,true),
.cycle 0 13 true (-1),
.cycle 31 1 false (-1),
.cycle 23 1 false (-1),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.cycle 8 5 false (2),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 10 3 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (-3),
.last 13 (5,true),
.cycle 31 1 false (-3),
.cycle 28 1 false (-2),
.cycle 2 11 false (3),
.cycle 27 1 false (-1),
.cycle 20 1 false (-2),
.last 15 (5,true)
]),
.split 13 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.cycle 17 1 false (1),
.cycle 25 1 false (1),
.cycle 10 4 true (-1),
.cycle 0 15 true (-1),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 21 1 false (-3),
.cycle 11 3 false (0),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.cycle 25 1 false (-1),
.cycle 12 12 true (-1),
.cycle 12 2 true (-1),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 20 1 false (0),
.cycle 16 1 false (2),
.cycle 9 2 true (0),
.cycle 16 1 false (-2)
])
theorem kid05_part32_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part32) = true := by rfl

def kid05_part33 : Audit := .cycle 0 11 true (0)
theorem kid05_part33_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part33) = true := by rfl

def kid05_part34 : Audit := .cycle 12 1 false (-2)
theorem kid05_part34_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part34) = true := by rfl

def kid05_part35 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 false (3),
.cycle 18 2 false (0),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 11 true (0),
.cycle 18 2 false (2),
.cycle 12 1 false (2),
.cycle 11 1 false (1),
.cycle 11 2 false (1),
.cycle 11 2 false (1),
.split 12 (1,true) (byMove [
.cycle 14 2 false (0),
.cycle 21 2 false (-1),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 24 2 false (-2),
.cycle 20 2 false (0),
.cycle 18 2 false (0),
.cycle 16 2 false (-2),
.cycle 8 5 false (2),
.cycle 15 2 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 15 2 false (1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 28 2 false (-2),
.cycle 25 2 false (-1),
.cycle 2 11 false (3),
.cycle 8 9 false (2),
.cycle 17 2 false (-1),
.cycle 10 5 false (1)
]),
.split 12 (2,true) (byMove [
.cycle 14 2 false (0),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 24 2 false (-2),
.cycle 20 2 false (0),
.cycle 18 2 false (0),
.cycle 16 2 false (-2),
.cycle 8 5 false (2),
.cycle 15 2 false (-1),
.last 13 (1,true),
.cycle 17 2 false (1),
.cycle 15 2 false (1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 24 (1,true),
.last 23 (1,true),
.cycle 2 11 false (3),
.cycle 8 9 false (2),
.last 15 (1,true),
.cycle 10 5 false (1)
]),
.cycle 0 13 true (-1),
.cycle 11 1 false (-1),
.cycle 11 2 false (-1),
.cycle 11 2 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (0),
.cycle 17 2 false (1),
.cycle 14 2 false (2),
.cycle 9 2 true (0),
.cycle 13 2 false (-1)
])
theorem kid05_part35_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part35) = true := by rfl

def kid05_part36 : Audit := .cycle 0 10 true (0)
theorem kid05_part36_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part36) = true := by rfl

def kid05_part37 : Audit := .cycle 1 9 true (1)
theorem kid05_part37_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part37) = true := by rfl

def kid05_part38 : Audit := .cycle 20 1 false (2)
theorem kid05_part38_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part38) = true := by rfl

def kid05_part39 : Audit := .cycle 17 1 false (1)
theorem kid05_part39_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part39) = true := by rfl

def kid05_part40 : Audit := .cycle 9 1 true (1)
theorem kid05_part40_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part40) = true := by rfl

def kid05_part41 : Audit := .cycle 8 2 true (1)
theorem kid05_part41_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part41) = true := by rfl

def kid05_part43 : Audit := .cycle 13 4 true (-2)
theorem kid05_part43_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part43) = true := by rfl

def kid05_part44 : Audit := .cycle 10 12 false (1)
theorem kid05_part44_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part44) = true := by rfl

def kid05_part45 : Audit := .split 16 (2,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.cycle 21 1 false (-3),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 11 19 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 13 7 true (-2),
.cycle 9 8 false (1),
.cycle 11 7 false (1)
])
theorem kid05_part45_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part45) = true := by rfl

def kid05_part46 : Audit := .cycle 0 17 false (3)
theorem kid05_part46_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part46) = true := by rfl

def kid05_part47 : Audit := .cycle 11 5 false (1)
theorem kid05_part47_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part47) = true := by rfl

def kid05_part48 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 0 17 false (3),
.cycle 10 12 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.last 18 (2,true),
.cycle 0 19 false (3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 11 19 false (2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 13 7 true (-2),
.cycle 9 8 false (1),
.cycle 11 7 false (1)
])
theorem kid05_part48_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part48) = true := by rfl

def kid05_part49 : Audit := .cycle 6 20 false (3)
theorem kid05_part49_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part49) = true := by rfl

def kid05_part50 : Audit := .cycle 10 11 true (-2)
theorem kid05_part50_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part50) = true := by rfl

def kid05_part51 : Audit := .cycle 10 11 false (1)
theorem kid05_part51_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part51) = true := by rfl

def kid05_part52 : Audit := .cycle 10 9 false (1)
theorem kid05_part52_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part52) = true := by rfl

def kid05_part53 : Audit := .cycle 13 3 true (-2)
theorem kid05_part53_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part53) = true := by rfl

def kid05_part54 : Audit := .cycle 8 8 false (2)
theorem kid05_part54_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part54) = true := by rfl

def kid05_part55 : Audit := .cycle 10 6 false (1)
theorem kid05_part55_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part55) = true := by rfl

def kid05_part56 : Audit := .split 18 (2,true) (byMove [
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.cycle 21 1 false (-3),
.cycle 14 6 true (-3),
.cycle 11 8 false (1),
.last 19 (5,true),
.cycle 13 7 true (-3),
.far true 2 ⟨0,[0, 1, 0, 1],[144, 192, 512, 512, 64, 16, 128, 128, 128, 512, 64, 16, 4096],[128, 128, 128, 192, 32, 4096, 16, 128, 128, 192, 32, 4096, 4096],4096⟩,
.cycle 10 16 false (1),
.cycle 13 29 true (-4),
.cycle 11 10 false (1),
.last 19 (5,true),
.cycle 10 9 false (1),
.cycle 16 3 false (-2),
.cycle 10 12 false (1),
.cycle 10 10 false (1),
.cycle 11 8 false (1),
.last 19 (5,true),
.last 32 (5,true),
.cycle 15 5 false (-1),
.cycle 11 20 false (1),
.cycle 11 26 false (3),
.last 20 (5,true),
.last 19 (5,true)
])
theorem kid05_part56_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part56) = true := by rfl

def kid05_part57 : Audit := .split 16 (2,true) (byMove [
.cycle 13 13 false (-1),
.cycle 14 26 true (-4),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 13 5 true (-2),
.cycle 0 20 true (-2),
.cycle 19 1 false (1),
.cycle 0 18 true (-2),
.cycle 11 6 false (1),
.last 17 (5,true),
.cycle 14 3 false (-1),
.cycle 10 12 false (1),
.cycle 13 7 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 13 5 true (-2),
.cycle 15 2 true (-2),
.cycle 2 16 false (3),
.cycle 6 22 false (3),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part57_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part57) = true := by rfl

def kid05_part58 : Audit := .cycle 13 5 true (-2)
theorem kid05_part58_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part58) = true := by rfl

def kid05_part59 : Audit := .cycle 11 5 false (1)
theorem kid05_part59_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part59) = true := by rfl

def kid05_part60 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 11 68 false (3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 13 5 true (-2),
.cycle 12 6 false (0),
.last 17 (2,true),
.cycle 0 18 true (-2),
.cycle 11 6 false (1),
.cycle 12 6 true (-2),
.cycle 14 3 false (-1),
.last 18 (2,true),
.cycle 13 7 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 13 5 true (-2),
.cycle 15 2 true (-2),
.last 17 (2,true),
.cycle 6 22 false (3),
.cycle 9 10 false (1),
.cycle 11 11 false (1)
])
theorem kid05_part60_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part60) = true := by rfl

def kid05_part61 : Audit := .split 30 (5,true) (byMove [
.cycle 0 31 false (3),
.cycle 10 26 false (3),
.cycle 32 1 false (-2),
.cycle 31 1 false (-3),
.cycle 13 18 false (3),
.cycle 12 19 false (3),
.cycle 0 31 false (3),
.cycle 10 26 true (-2),
.cycle 32 1 false (0),
.cycle 31 1 false (-1),
.cycle 13 18 true (-2),
.cycle 12 19 false (3),
.cycle 14 17 false (3),
.last 32 (2,true),
.cycle 0 33 false (3),
.cycle 31 1 false (-3),
.far false 19 ⟨0,[0, 1, 6, 12, 8, 9, 3, 3, 11, 15, 11, 14, 17, 13, 5, 18, 4, 15, 10, 15, 11, 14, 4, 18, 2, 1, 15, 8, 9, 14, 15, 8, 18, 18, 9, 3, 9, 4],[128, 256, 8, 0, 4722366482869645213696, 128, 9444732965739290427392, 18889465931478580854784, 549755813888, 4503599627370512, 18889465931478580854784, 20769187434139310514121985316913152, 36028797018963968, 72057594037927936, 2251799813685248, 0, 4722366482869645213696, 20769187434139310514121985316880384, 524288, 1048576, 2097152, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 2475880078570760549798248448, 4951760157141521099596496896, 590295810358705651712, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 38685626227668133590597632, 77371252455336267181195264, 590295810358705651712, 0, 16777216, 0, 604462909807314587353088, 1208925819614629174706176, 40564819207303340847894502572032, 21423333655432907802691849225601472, 64, 32768, 649037107316853453566312041152512, 1298074214633706907132624082305024, 8589934592, 0, 0, 0, 2475880078570760549798248448, 4951760157141521099596496896, 134217728, 19807040628566084398385987584, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 2475880078570760549798248448, 4951760157141521099596496896, 9223372036854775808, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 38685626227668133590597632, 77371252455336267181195264, 590295810358705651712, 21423333655432907802691849225601472, 281474976710656, 21423333655432907802691849225601472, 649037107316853453566312041152512, 1298074214633706907132624082305024, 134217728, 21423333655432907802691849225601472, 19342813114115541772009472, 21423333655432907802691849225601472, 128, 256, 32768, 81129638414606681695789005144064, 20769187434139310514121985316880384, 128, 562949953421312, 1125899906842624, 9903520314283042199192993792, 288230376151711744, 0, 20769187434139310514121985316880384, 38685626227668133590597632, 77371252455336267181195264, 144115188075855872, 18446744073977987072, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 562949953421312, 1125899906842624, 9903520314283042199192993792, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 649037107316853453566312041152512, 1298074214633706907132624082305024, 2596148429267413814265248164610048, 0, 0, 0, 524288, 1048576, 144115188075855872, 21423333655432907802691849225601472, 281474976710656, 9444732965739290427392, 33554432, 67108864, 144115188075855872, 1180879851093563015168, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 20769187434139310514121985316880384],[16, 64, 20769187434139310514121985316880384, 1, 18889465931478580854784, 65536, 1099511627776, 4722366482869645213696, 20769187434139310514121985316880384, 68719476736, 4722366482869645213696, 20769187434139310514121985316880384, 4503599627370496, 18014398509481984, 20769187434139310514121985316880384, 281474976710656, 18889465931478580854784, 20769187434139310514121985316880384, 4194304, 262144, 20769187434139310514121985316880384, 262144, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 1180591620717411303424, 1237940039285380274899124224, 20769187434139310514121985316880384, 73786976294838206464, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 1180591620717411303424, 19342813113834066795298816, 20769187434139310514121985316880384, 73786976294838206464, 0, 0, 81129638414606681695789005144064, 302231454903657293676544, 20769187434139310514121985316880384, 5070602400912917605986812821504, 20769187434139310514121985316880384, 20769187434139310514121985316880384, 17179869184, 324518553658426726783156020576256, 20769187434139310514121985316880384, 1073741824, 0, 0, 268435456, 1237940039285380274899124224, 20769187434139310514121985316880384, 16777216, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 18446744073709551616, 1237940039285380274899124224, 20769187434139310514121985316880384, 1152921504606846976, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 1180591620717411303424, 19342813113834066795298816, 20769187434139310514121985316880384, 73786976294838206464, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 268435456, 324518553658426726783156020576256, 20769187434139310514121985316880384, 16777216, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 65536, 64, 20769187434139310514121985316880384, 4096, 20769187434139310514121985316880384, 65536, 19807040628566084398385987584, 281474976710656, 20769187434139310514121985316880384, 1237940039285380274899124224, 20769187434139310514121985316880384, 20769187434139310514121985316880384, 288230376151711744, 19342813113834066795298816, 20769187434139310514121985316880384, 18014398509481984, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 19807040628566084398385987584, 281474976710656, 20769187434139310514121985316880384, 1237940039285380274899124224, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 5192296858534827628530496329220096, 324518553658426726783156020576256, 20769187434139310514121985316880384, 324518553658426726783156020576256, 0, 0, 288230376151711744, 262144, 20769187434139310514121985316880384, 18014398509481984, 0, 1099511627776, 288230376151711744, 16777216, 20769187434139310514121985316880384, 18014398509481984, 21423333655432907802691849225601472, 21423333655432907802691849225601472, 20769187434139310514121985316880384],41533938086167391386747913837116226⟩,
.cycle 47 13 false (0),
.cycle 11 33 false (3),
.cycle 1 30 false (3),
.cycle 10 25 false (3),
.cycle 13 21 true (-2),
.cycle 9 22 false (3),
.cycle 11 21 false (3)
])
theorem kid05_part61_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part61) = true := by rfl

def kid05_part62 : Audit := .cycle 11 17 false (2)
theorem kid05_part62_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part62) = true := by rfl

def kid05_part63 : Audit := .cycle 2 14 false (3)
theorem kid05_part63_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part63) = true := by rfl

def kid05_part64 : Audit := .cycle 13 6 true (-2)
theorem kid05_part64_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part64) = true := by rfl

def kid05_part65 : Audit := .cycle 11 9 false (1)
theorem kid05_part65_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part65) = true := by rfl

def kid05_part66 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 10 14 false (1),
.cycle 20 1 false (-2),
.cycle 19 1 false (-3),
.cycle 13 6 false (0),
.cycle 12 7 false (0),
.cycle 0 19 false (3),
.cycle 10 14 true (-2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 13 6 true (-2),
.cycle 12 7 false (0),
.cycle 14 5 false (0),
.last 20 (2,true),
.cycle 0 21 false (3),
.cycle 19 1 false (-3),
.cycle 17 6 false (-1),
.cycle 12 7 false (0),
.cycle 11 21 false (2),
.cycle 1 18 false (3),
.cycle 10 13 false (1),
.cycle 13 9 true (-2),
.cycle 9 10 false (1),
.cycle 11 9 false (1)
])
theorem kid05_part66_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part66) = true := by rfl

def kid05_part42 : Audit := .split 15 (1,true) (byMove [(kid05_part43),(kid05_part44),(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66)])

theorem kid05_part42_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part42) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part43),(kid05_part44),(kid05_part45),(kid05_part46),(kid05_part47),(kid05_part48),(kid05_part49),(kid05_part50),(kid05_part51),(kid05_part52),(kid05_part53),(kid05_part54),(kid05_part55),(kid05_part56),(kid05_part57),(kid05_part58),(kid05_part59),(kid05_part60),(kid05_part61),(kid05_part62),(kid05_part63),(kid05_part64),(kid05_part65),(kid05_part66)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part43_checked

  · exact kid05_part49_checked

  · exact kid05_part55_checked

  · exact kid05_part61_checked

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

def kid05_part68 : Audit := .split 13 (2,true) (byMove [
.cycle 12 4 true (0),
.cycle 0 20 false (3),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (-1),
.cycle 12 11 true (0),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 12 3 true (0),
.last 21 (5,true),
.cycle 17 6 false (-1),
.cycle 10 9 false (1),
.cycle 21 7 true (-3),
.cycle 12 5 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 12 19 true (0),
.cycle 12 19 true (0),
.cycle 13 14 true (-1),
.cycle 12 6 true (0),
.last 21 (5,true),
.last 16 (5,true)
])
theorem kid05_part68_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part68) = true := by rfl

def kid05_part69 : Audit := .cycle 0 14 true (-1)
theorem kid05_part69_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part69) = true := by rfl

def kid05_part70 : Audit := .cycle 12 1 false (0)
theorem kid05_part70_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part70) = true := by rfl

def kid05_part71 : Audit := .cycle 11 1 false (-1)
theorem kid05_part71_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part71) = true := by rfl

def kid05_part72 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1595932672, 128, 16384, 8192, 16384, 8, 16, 128, 2097152, 33554432, 67108864, 2097152, 16, 16777216, 1073741824, 33554432, 67108864, 134217728, 2097152, 1595932672, 33554432, 33554432, 67108864, 134217728, 1595932672, 1595932672, 1595932672, 1073741824],[16, 16384, 1595932800, 1, 2097152, 1073741824, 16, 2097152, 128, 1, 1073741824, 1073741824, 4194304, 1073741824, 128, 262144, 1073741824, 1073741824, 268435456, 33554432, 128, 16777216, 1073741824, 1073741824, 268435456, 1595932672, 1595932672, 16777216, 1595932672, 1073741824, 1073741824],2145333582⟩,
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 9 25 false (1),
.cycle 14 11 true (0),
.cycle 0 16 true (-2),
.cycle 11 9 false (0),
.last 20 (5,true),
.cycle 8 6 false (2),
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 27 7 true (-3),
.cycle 23 5 true (-2),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 17 (5,true),
.last 27 (5,true),
.cycle 0 16 true (-2),
.cycle 4 10 false (3),
.cycle 11 7 false (0),
.last 16 (5,true)
])
theorem kid05_part72_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part72) = true := by rfl

def kid05_part73 : Audit := .split 14 (2,true) (byMove [
.cycle 12 4 true (-3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.last 34 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 31 (5,true),
.cycle 64 11 true (2),
.cycle 11 11 false (0),
.cycle 11 9 false (-1),
.last 24 (5,true),
.cycle 8 7 false (2),
.cycle 11 6 false (-1),
.cycle 10 5 false (0),
.cycle 35 7 true (-3),
.cycle 29 5 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 29 (5,true),
.last 32 (5,true),
.cycle 2 13 false (3),
.last 35 (5,true),
.last 17 (5,true),
.last 17 (5,true)
])
theorem kid05_part73_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part73) = true := by rfl

def kid05_part74 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (1),
.cycle 0 16 true (0),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 12 5 false (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 12 11 true (1),
.cycle 12 11 false (4),
.cycle 12 9 false (3),
.cycle 12 3 true (1),
.cycle 8 7 true (0),
.cycle 12 6 false (2),
.cycle 10 5 true (0),
.cycle 11 7 true (0),
.cycle 11 5 true (1),
.cycle 12 5 false (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 11 6 true (1),
.cycle 9 6 true (0),
.last 17 (5,true)
])
theorem kid05_part74_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part74) = true := by rfl

def kid05_part75 : Audit := .split 22 (2,true) (byMove [
.cycle 20 4 true (1),
.cycle 11 12 true (1),
.cycle 25 1 false (1),
.cycle 0 24 true (0),
.cycle 18 5 false (4),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 12 11 true (1),
.cycle 14 11 false (4),
.cycle 14 9 false (4),
.cycle 20 3 true (1),
.cycle 8 15 true (0),
.cycle 17 6 false (4),
.cycle 10 13 true (0),
.cycle 20 7 true (0),
.cycle 20 5 true (1),
.cycle 18 5 false (4),
.last 23 (5,true),
.cycle 0 23 true (0),
.cycle 1 22 true (0),
.cycle 2 21 true (0),
.cycle 20 6 true (1),
.cycle 9 14 true (0),
.last 25 (5,true)
])
theorem kid05_part75_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part75) = true := by rfl

def kid05_part76 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 25 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 5 false (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 11 11 true (1),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 3 true (1),
.cycle 8 8 true (0),
.cycle 19 6 false (2),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 5 false (0),
.last 16 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 20 true (0),
.cycle 11 6 true (1),
.cycle 9 3 true (0),
.last 20 (5,true)
])
theorem kid05_part76_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part76) = true := by rfl

def kid05_part77 : Audit := .cycle 0 12 true (0)
theorem kid05_part77_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part77) = true := by rfl

def kid05_part78 : Audit := .split 15 (2,true) (byMove [
.cycle 13 4 true (-2),
.cycle 13 4 true (-2),
.cycle 18 1 false (-2),
.cycle 0 17 false (3),
.cycle 11 5 false (1),
.last 16 (5,true),
.cycle 7 20 false (3),
.cycle 11 11 true (-2),
.cycle 11 11 false (1),
.cycle 11 9 false (1),
.cycle 13 3 true (-2),
.cycle 8 8 false (2),
.cycle 11 6 false (1),
.cycle 10 6 false (1),
.cycle 13 7 true (-3),
.cycle 13 5 true (-2),
.cycle 11 5 false (1),
.last 16 (5,true),
.last 30 (5,true),
.cycle 11 17 false (2),
.cycle 2 14 false (3),
.cycle 13 6 true (-2),
.cycle 11 9 false (1),
.last 18 (5,true)
])
theorem kid05_part78_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part78) = true := by rfl

def kid05_part79 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.last 22 (2,true),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (2,true),
.last 15 (2,true),
.cycle 0 12 true (0),
.last 22 (2,true),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.last 14 (2,true),
.last 15 (2,true),
.cycle 8 6 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.last 14 (2,true),
.last 15 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.last 21 (2,true),
.last 17 (2,true),
.cycle 9 3 true (0),
.last 17 (2,true)
])
theorem kid05_part79_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part79) = true := by rfl

def kid05_part80 : Audit := .split 18 (2,true) (byMove [
.cycle 16 4 true (-3),
.cycle 10 9 false (0),
.cycle 21 1 false (-3),
.proven (BB6.Agent11Raw39B0REPumps.M112.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M112.never m hm),
.cycle 14 5 false (0),
.last 19 (5,true),
.last 39 (5,true),
.cycle 76 11 true (2),
.cycle 13 11 false (0),
.cycle 13 9 false (0),
.last 28 (5,true),
.cycle 8 11 false (2),
.cycle 13 6 false (0),
.cycle 10 9 false (0),
.cycle 39 7 true (-3),
.cycle 33 5 true (-2),
.cycle 14 5 false (0),
.last 19 (5,true),
.last 37 (5,true),
.last 122 (5,true),
.cycle 2 17 false (3),
.last 43 (5,true),
.cycle 12 8 false (0),
.last 21 (5,true)
])
theorem kid05_part80_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part80) = true := by rfl

def kid05_part81 : Audit := .split 12 (2,true) (byMove [
.cycle 11 4 true (-1),
.cycle 10 3 false (0),
.cycle 15 1 false (-1),
.cycle 10 6 true (-1),
.cycle 11 5 false (0),
.last 13 (5,true),
.cycle 0 17 true (-1),
.cycle 14 11 true (0),
.cycle 16 11 false (2),
.cycle 0 14 true (-1),
.cycle 17 3 true (-4),
.last 13 (5,true),
.cycle 11 6 false (0),
.cycle 10 3 false (0),
.cycle 19 7 true (-3),
.cycle 17 5 true (-2),
.cycle 11 5 false (0),
.last 13 (5,true),
.last 38 (5,true),
.cycle 10 5 false (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[18, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 0 14 true (-1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part81_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part81) = true := by rfl

def kid05_part82 : Audit := .split 16 (2,true) (byMove [
.cycle 13 4 true (1),
.cycle 0 20 true (-1),
.cycle 19 1 false (1),
.cycle 0 18 true (-1),
.cycle 14 5 false (2),
.last 17 (5,true),
.cycle 0 17 true (-1),
.cycle 14 11 true (1),
.cycle 14 11 false (4),
.cycle 14 9 false (3),
.cycle 14 3 true (1),
.cycle 8 9 true (-1),
.cycle 14 6 false (2),
.cycle 10 7 true (-1),
.cycle 11 7 true (-1),
.cycle 12 5 true (0),
.cycle 14 5 false (2),
.last 17 (5,true),
.last 33 (5,true),
.cycle 26 2 true (1),
.cycle 2 15 true (-1),
.cycle 12 6 true (0),
.last 21 (5,true),
.last 19 (5,true)
])
theorem kid05_part82_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part82) = true := by rfl

def kid05_part83 : Audit := .cycle 11 1 false (-1)
theorem kid05_part83_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part83) = true := by rfl

def kid05_part84 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.last 140 (5,true),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 6 8 false (3),
.cycle 9 6 false (1),
.cycle 19 11 false (1),
.cycle 3 34 false (3),
.last 36 (5,true),
.last 14 (5,true),
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 43 7 true (-3),
.cycle 35 5 true (-2),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 26 (5,true),
.cycle 14 6 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part84_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part84) = true := by rfl

def kid05_part85 : Audit := .split 14 (2,true) (byMove [
.cycle 12 4 true (-3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.last 22 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.last 78 (5,true),
.cycle 12 137 true (-6),
.cycle 11 9 false (-1),
.last 21 (5,true),
.cycle 8 7 false (2),
.cycle 11 6 false (-1),
.cycle 10 5 false (0),
.cycle 51 7 true (-3),
.cycle 41 5 true (-2),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 17 (5,true),
.last 18 (5,true),
.last 33 (5,true),
.cycle 4 11 false (3),
.last 17 (5,true),
.last 17 (5,true)
])
theorem kid05_part85_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part85) = true := by rfl

def kid05_part86 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (1),
.cycle 0 16 true (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 12 11 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 12 3 true (1),
.cycle 8 7 true (0),
.cycle 18 6 false (0),
.cycle 10 5 true (0),
.cycle 22 7 true (-2),
.cycle 11 5 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 11 6 true (1),
.cycle 9 6 true (0),
.last 17 (5,true)
])
theorem kid05_part86_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part86) = true := by rfl

def kid05_part87 : Audit := .cycle 1 11 true (0)
theorem kid05_part87_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part87) = true := by rfl

def kid05_part88 : Audit := .split 11 (2,true) (byMove [
.cycle 11 4 true (0),
.cycle 11 11 false (2),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 11 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 11 11 true (1),
.cycle 11 11 false (3),
.cycle 11 9 false (2),
.cycle 11 3 true (1),
.cycle 8 4 true (0),
.cycle 11 6 false (1),
.cycle 10 2 true (0),
.cycle 11 7 true (-1),
.cycle 11 5 true (0),
.cycle 11 5 false (1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 6 true (1),
.cycle 9 3 true (0),
.last 14 (5,true)
])
theorem kid05_part88_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part88) = true := by rfl

def kid05_part89 : Audit := .cycle 0 12 true (0)
theorem kid05_part89_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part89) = true := by rfl

def kid05_part90 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.last 23 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.last 23 (2,true),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 15 (2,true),
.last 16 (2,true),
.last 24 (2,true),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.last 22 (2,true),
.last 18 (2,true),
.cycle 9 4 true (0),
.last 18 (2,true)
])
theorem kid05_part90_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part90) = true := by rfl

def kid05_part91 : Audit := .split 11 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 12 true (0),
.last 22 (2,true),
.last 22 (2,true),
.last 20 (2,true),
.last 14 (2,true),
.cycle 8 4 true (0),
.last 17 (2,true),
.cycle 10 2 true (0),
.last 12 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.last 17 (2,true),
.cycle 9 3 true (0),
.last 20 (2,true)
])
theorem kid05_part91_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part91) = true := by rfl

def kid05_part67 : Audit := .split 10 (1,true) (byMove [(kid05_part68),(kid05_part69),(kid05_part70),(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91)])

theorem kid05_part67_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part67) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part68),(kid05_part69),(kid05_part70),(kid05_part71),(kid05_part72),(kid05_part73),(kid05_part74),(kid05_part75),(kid05_part76),(kid05_part77),(kid05_part78),(kid05_part79),(kid05_part80),(kid05_part81),(kid05_part82),(kid05_part83),(kid05_part84),(kid05_part85),(kid05_part86),(kid05_part87),(kid05_part88),(kid05_part89),(kid05_part90),(kid05_part91)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part68_checked

  · exact kid05_part74_checked

  · exact kid05_part80_checked

  · exact kid05_part86_checked

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

def kid05_part93 : Audit := .cycle 0 18 true (-1)
theorem kid05_part93_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part93) = true := by rfl

def kid05_part94 : Audit := .cycle 0 14 true (-1)
theorem kid05_part94_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part94) = true := by rfl

def kid05_part95 : Audit := .cycle 12 1 false (0)
theorem kid05_part95_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part95) = true := by rfl

def kid05_part96 : Audit := .cycle 11 1 false (-1)
theorem kid05_part96_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part96) = true := by rfl

def kid05_part97 : Audit := .split 15 (1,true) (byMove [
.cycle 0 20 true (-2),
.cycle 0 28 true (-2),
.cycle 0 20 true (-2),
.cycle 0 17 true (-2),
.cycle 0 21 false (3),
.last 16 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 1073758208, 1, 128, 8192, 16384, 8, 16, 1, 2097152, 33554432, 67108864, 2097152, 16, 16777216, 1073741824, 33554432, 67108864, 134217728, 16384, 16777216, 33554432, 33554432, 67108864, 134217728, 1593835520, 1593835520, 1593835520, 1073741824],[16, 1, 128, 1, 16384, 1073741824, 16, 1, 2097152, 1, 1073741824, 1073741824, 4194304, 262144, 1073741824, 262144, 1073741824, 1073741824, 268435456, 16777216, 33554432, 16777216, 1073741824, 1073741824, 268435456, 16777216, 1593835520, 16777216, 1593835520, 1073741824, 1073741824],2145333582⟩,
.cycle 0 27 true (-2),
.last 31 (5,true),
.cycle 0 25 true (-2),
.cycle 0 19 true (-2),
.cycle 8 8 true (-2),
.cycle 0 22 true (-2),
.last 50 (5,true),
.cycle 10 6 true (-2),
.cycle 0 21 true (-2),
.last 25 (5,true),
.last 16 (5,true),
.last 28 (5,true),
.proven (BB6.Agent11Raw39B0REPumps.M115.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M115.never m hm),
.cycle 2 14 true (-2),
.cycle 0 22 true (-2),
.proven (BB6.Agent11Raw39B0REPumps.M116.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M116.never m hm),
.last 18 (5,true)
])
theorem kid05_part97_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part97) = true := by rfl

def kid05_part98 : Audit := .split 18 (5,true) (byMove [
.cycle 0 23 true (-3),
.last 19 (1,true),
.cycle 0 24 false (3),
.cycle 0 20 true (-3),
.cycle 0 24 false (3),
.cycle 0 24 false (3),
.last 75 (1,true),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 256, 1, 136, 128, 256, 8, 16, 256, 8, 4096],[16, 4096, 256, 1, 256, 2, 16, 4096, 256, 1, 256, 2, 4096],4096⟩,
.cycle 11 15 true (-3),
.cycle 0 28 true (-3),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 16401, 1, 128, 8192, 16384, 8, 16, 1, 2097152, 33554432, 67108864, 2097152, 16, 16, 128, 33554432, 67108864, 134217728, 16384, 16777216, 1, 33554432, 67108864, 134217728, 1595949201, 1595949201, 1595949201, 1073741824],[16, 1073741824, 16384, 1, 16384, 16, 16, 1073741824, 1, 1, 1, 16, 4194304, 1073741824, 1, 262144, 1, 4194304, 268435456, 1073741824, 16384, 16777216, 16384, 268435456, 268435456, 1073741824, 1595949201, 16777216, 1595949201, 268435456, 1073741824],2136748096⟩,
.cycle 8 11 false (2),
.cycle 0 25 false (3),
.last 19 (1,true),
.cycle 10 9 false (1),
.cycle 0 24 true (-3),
.cycle 11 9 false (1),
.last 25 (1,true),
.last 32 (1,true),
.cycle 16 14 true (-1),
.cycle 2 17 false (3),
.cycle 0 25 true (-3),
.cycle 9 13 false (1),
.cycle 0 28 false (3)
])
theorem kid05_part98_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part98) = true := by rfl

def kid05_part99 : Audit := .cycle 0 15 true (0)
theorem kid05_part99_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part99) = true := by rfl

def kid05_part100 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 15 true (-1),
.cycle 0 16 true (-2),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.cycle 0 20 true (-2),
.cycle 0 25 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 0 19 true (-1),
.last 18 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 9 3 true (0),
.cycle 0 18 true (-2)
])
theorem kid05_part100_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part100) = true := by rfl

def kid05_part101 : Audit := .cycle 13 1 false (3)
theorem kid05_part101_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part101) = true := by rfl

def kid05_part102 : Audit := .cycle 0 12 true (0)
theorem kid05_part102_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part102) = true := by rfl

def kid05_part103 : Audit := .cycle 0 16 true (-2)
theorem kid05_part103_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part103) = true := by rfl

def kid05_part104 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 0 23 true (-1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 15 true (-1),
.cycle 0 16 true (-2),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 13 (1,true),
.cycle 8 6 true (0),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 0 19 true (-1),
.last 17 (1,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 0 22 true (0),
.cycle 0 18 true (0),
.cycle 9 3 true (0),
.cycle 0 18 true (-2)
])
theorem kid05_part104_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part104) = true := by rfl

def kid05_part105 : Audit := .split 12 (1,true) (byMove [
.cycle 0 21 true (-1),
.cycle 0 36 false (3),
.cycle 10 3 false (0),
.cycle 0 17 true (-1),
.last 38 (5,true),
.last 13 (5,true),
.cycle 0 17 true (-1),
.cycle 0 25 true (-1),
.cycle 3 15 false (3),
.cycle 0 14 true (-1),
.cycle 0 20 false (3),
.last 13 (5,true),
.cycle 0 30 false (3),
.cycle 0 33 false (3),
.cycle 10 3 false (0),
.cycle 0 20 true (-2),
.cycle 0 29 false (3),
.last 13 (5,true),
.cycle 0 17 true (-1),
.last 79 (5,true),
.cycle 0 22 false (3),
.cycle 0 14 true (-1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part105_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part105) = true := by rfl

def kid05_part106 : Audit := .split 13 (1,true) (byMove [
.cycle 0 28 true (-2),
.cycle 0 21 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.far true 2 ⟨0,[0, 1, 0, 1],[176, 384, 512, 512, 256, 16, 32, 16, 256, 512, 256, 16, 4096],[256, 16, 128, 272, 32, 4096, 16, 16, 128, 256, 32, 4096, 4096],4096⟩,
.last 22 (5,true),
.cycle 0 20 true (-2),
.cycle 0 27 true (-1),
.cycle 10 4 true (-1),
.cycle 0 19 true (-1),
.cycle 0 30 false (3),
.last 14 (5,true),
.cycle 15 10 true (-4),
.cycle 11 3 false (0),
.cycle 0 22 true (-2),
.cycle 14 1 false (-2),
.cycle 18 9 false (1),
.last 20 (5,true),
.cycle 0 22 false (3),
.cycle 12 13 true (-1),
.cycle 12 2 true (-1),
.cycle 0 19 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part106_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part106) = true := by rfl

def kid05_part107 : Audit := .cycle 0 17 true (-1)
theorem kid05_part107_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part107) = true := by rfl

def kid05_part108 : Audit := .cycle 11 1 false (-1)
theorem kid05_part108_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part108) = true := by rfl

def kid05_part109 : Audit := .cycle 0 20 true (-2)
theorem kid05_part109_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part109) = true := by rfl

def kid05_part110 : Audit := .split 16 (1,true) (byMove [
.cycle 0 25 true (-3),
.last 32 (5,true),
.cycle 10 7 false (0),
.cycle 0 21 true (-3),
.last 40 (5,true),
.last 17 (5,true),
.cycle 0 21 true (-3),
.cycle 0 29 true (-3),
.last 42 (5,true),
.far true 7 ⟨0,[0, 1, 2, 3, 4, 5, 2, 4, 4, 4, 4, 6, 2, 4],[8388608, 256, 2097152, 512, 256, 16, 256, 4398046511104, 4294967296, 2097152, 1048576, 65536, 4398046511104, 7152127246336, 134217728, 8589934592, 4294967296, 268435456, 2199023255552, 4398046511104, 4294967296, 134217728, 67108864, 65536, 7152127246336, 7152127246336, 4952298618880, 134217728, 67108864, 268435456, 4952567119872, 4398046511104, 4294967296, 549755813888, 274877906944, 268435456, 2199023255552, 4398046511104, 4952298618880, 134217728, 67108864, 65536, 4398046511104],[4294967296, 2097152, 2048, 65536, 32, 4398046511104, 16, 4294967296, 8388608, 4294967296, 131072, 4398046511104, 4952298618880, 134217728, 34359738368, 4295032832, 536870912, 4398046511104, 268435456, 4294967296, 536870912, 256, 131072, 4398046511104, 4952567054336, 4952298618880, 536870912, 4952567119872, 536870912, 4398046511104, 268435456, 4294967296, 2199023255552, 4952298618880, 536870912, 4398046511104, 268435456, 4952298618880, 536870912, 67108864, 131072, 4398046511104, 4398046511104],5965563441280⟩,
.cycle 0 24 false (3),
.last 17 (5,true),
.last 26 (5,true),
.last 20 (5,true),
.cycle 10 7 false (0),
.cycle 0 24 true (-3),
.last 25 (5,true),
.last 17 (5,true),
.last 35 (5,true),
.last 28 (5,true),
.last 18 (5,true),
.last 31 (5,true),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part110_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part110) = true := by rfl

def kid05_part111 : Audit := .cycle 0 15 true (0)
theorem kid05_part111_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part111) = true := by rfl

def kid05_part112 : Audit := .split 11 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 0 24 true (-2),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 0 17 false (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 1 74 true (-1),
.cycle 0 21 true (-1),
.cycle 0 15 true (0),
.cycle 8 4 true (0),
.cycle 0 18 true (-2),
.cycle 11 5 false (1),
.cycle 10 2 true (0),
.cycle 0 17 true (0),
.last 32 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 18 true (0),
.cycle 9 3 true (0),
.last 14 (5,true)
])
theorem kid05_part112_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part112) = true := by rfl

def kid05_part113 : Audit := .cycle 2 10 true (0)
theorem kid05_part113_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part113) = true := by rfl

def kid05_part114 : Audit := .cycle 0 12 true (0)
theorem kid05_part114_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part114) = true := by rfl

def kid05_part115 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 0 24 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 16 true (-2),
.cycle 0 17 false (3),
.cycle 0 13 true (0),
.cycle 0 24 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 0 16 true (0),
.cycle 0 17 true (-1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 20 true (-2),
.last 18 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 0 23 true (-1),
.cycle 0 19 true (0),
.cycle 9 4 true (0),
.cycle 0 19 false (3)
])
theorem kid05_part115_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part115) = true := by rfl

def kid05_part116 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 0 19 false (3),
.cycle 0 13 true (0),
.cycle 0 17 false (3),
.cycle 0 17 false (3),
.cycle 0 12 true (0),
.cycle 0 23 true (0),
.cycle 11 17 true (-1),
.cycle 0 21 true (-1),
.cycle 0 15 true (0),
.cycle 8 4 true (0),
.cycle 0 18 true (-2),
.last 12 (1,true),
.cycle 10 2 true (0),
.cycle 0 17 true (0),
.cycle 11 11 false (2),
.last 18 (1,true),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 0 18 true (0),
.cycle 9 3 true (0),
.cycle 0 21 false (3)
])
theorem kid05_part116_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part116) = true := by rfl

def kid05_part92 : Audit := .split 10 (2,true) (byMove [(kid05_part93),(kid05_part94),(kid05_part95),(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116)])

theorem kid05_part92_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part92) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part93),(kid05_part94),(kid05_part95),(kid05_part96),(kid05_part97),(kid05_part98),(kid05_part99),(kid05_part100),(kid05_part101),(kid05_part102),(kid05_part103),(kid05_part104),(kid05_part105),(kid05_part106),(kid05_part107),(kid05_part108),(kid05_part109),(kid05_part110),(kid05_part111),(kid05_part112),(kid05_part113),(kid05_part114),(kid05_part115),(kid05_part116)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part93_checked

  · exact kid05_part99_checked

  · exact kid05_part105_checked

  · exact kid05_part111_checked

  · exact kid05_part94_checked

  · exact kid05_part100_checked

  · exact kid05_part106_checked

  · exact kid05_part112_checked

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

def kid05_part117 : Audit := .cycle 13 1 false (1)
theorem kid05_part117_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part117) = true := by rfl

def kid05_part118 : Audit := .cycle 12 1 false (-2)
theorem kid05_part118_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part118) = true := by rfl

def kid05_part120 : Audit := .split 13 (2,true) (byMove [
.cycle 18 2 false (-2),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (-1),
.cycle 0 16 false (3),
.cycle 16 2 false (0),
.cycle 0 14 true (-1),
.cycle 86 2 false (-2),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 0 18 false (3),
.cycle 18 2 false (0),
.cycle 18 2 false (-2),
.last 14 (1,true),
.cycle 20 2 false (0),
.cycle 8 9 false (2),
.cycle 0 20 true (-2),
.cycle 16 2 false (0),
.cycle 58 2 false (-2),
.cycle 28 2 false (-2),
.cycle 24 2 false (0),
.cycle 22 2 false (0),
.cycle 20 2 false (-2),
.cycle 18 2 false (0)
])
theorem kid05_part120_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part120) = true := by rfl

def kid05_part121 : Audit := .cycle 0 14 true (-1)
theorem kid05_part121_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part121) = true := by rfl

def kid05_part122 : Audit := .cycle 12 1 false (0)
theorem kid05_part122_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part122) = true := by rfl

def kid05_part123 : Audit := .cycle 11 1 false (-1)
theorem kid05_part123_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part123) = true := by rfl

def kid05_part124 : Audit := .cycle 11 2 false (-1)
theorem kid05_part124_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part124) = true := by rfl

def kid05_part125 : Audit := .cycle 11 2 false (-1)
theorem kid05_part125_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part125) = true := by rfl

def kid05_part126 : Audit := .cycle 12 2 false (2)
theorem kid05_part126_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part126) = true := by rfl

def kid05_part127 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 19 2 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 19 2 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 12 2 false (2),
.cycle 16 2 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 15 2 false (3),
.cycle 9 3 true (0),
.cycle 14 2 false (0)
])
theorem kid05_part127_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part127) = true := by rfl

def kid05_part128 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 19 2 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 19 2 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 12 2 false (2),
.cycle 12 2 false (2),
.last 13 (1,true),
.last 14 (1,true),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 2 false (2),
.cycle 15 2 false (3),
.cycle 9 3 true (0),
.cycle 14 2 false (0)
])
theorem kid05_part128_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part128) = true := by rfl

def kid05_part129 : Audit := .cycle 0 12 true (0)
theorem kid05_part129_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part129) = true := by rfl

def kid05_part130 : Audit := .cycle 12 2 false (0)
theorem kid05_part130_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part130) = true := by rfl

def kid05_part131 : Audit := .cycle 12 2 false (2)
theorem kid05_part131_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part131) = true := by rfl

def kid05_part132 : Audit := .split 12 (1,true) (byMove [
.cycle 14 2 false (0),
.cycle 21 2 false (-1),
.last 13 (2,true),
.cycle 0 17 true (-1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 8 7 false (2),
.last 30 (2,true),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 16 2 false (-2),
.cycle 21 2 false (-1),
.cycle 15 2 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 16 2 false (0),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 22 (2,true),
.cycle 28 2 false (-2),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 17 2 false (-1),
.cycle 18 2 false (-2)
])
theorem kid05_part132_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part132) = true := by rfl

def kid05_part133 : Audit := .split 12 (2,true) (byMove [
.cycle 14 2 false (0),
.last 13 (1,true),
.cycle 15 1 false (-1),
.last 15 (1,true),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 8 7 false (2),
.last 13 (1,true),
.cycle 22 2 false (0),
.cycle 0 14 true (-1),
.cycle 16 2 false (-2),
.last 19 (1,true),
.cycle 15 2 false (-1),
.last 13 (1,true),
.cycle 18 2 false (0),
.cycle 16 2 false (0),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 34 (1,true),
.last 13 (1,true),
.last 23 (1,true),
.cycle 0 14 true (-1),
.last 15 (1,true),
.last 14 (1,true)
])
theorem kid05_part133_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part133) = true := by rfl

def kid05_part134 : Audit := .cycle 14 2 false (2)
theorem kid05_part134_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part134) = true := by rfl

def kid05_part135 : Audit := .cycle 11 1 false (-1)
theorem kid05_part135_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part135) = true := by rfl

def kid05_part136 : Audit := .cycle 11 2 false (-1)
theorem kid05_part136_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part136) = true := by rfl

def kid05_part137 : Audit := .cycle 11 2 false (-1)
theorem kid05_part137_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part137) = true := by rfl

def kid05_part138 : Audit := .cycle 15 2 false (-1)
theorem kid05_part138_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part138) = true := by rfl

def kid05_part139 : Audit := .split 11 (1,true) (byMove [
.cycle 13 2 false (1),
.cycle 20 2 false (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 2 false (-1),
.cycle 1 12 true (0),
.cycle 0 12 true (0),
.cycle 23 2 false (-1),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 15 2 false (-1),
.cycle 8 4 true (0),
.cycle 14 2 false (0),
.last 14 (2,true),
.last 12 (2,true),
.cycle 14 2 false (2),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 4 16 true (0),
.cycle 9 3 true (0),
.cycle 1 14 true (0)
])
theorem kid05_part139_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part139) = true := by rfl

def kid05_part140 : Audit := .split 11 (2,true) (byMove [
.cycle 13 2 false (1),
.last 12 (1,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 13 2 false (-1),
.cycle 19 2 false (1),
.cycle 0 12 true (0),
.cycle 23 2 false (-1),
.cycle 19 2 false (1),
.cycle 17 2 false (1),
.cycle 15 2 false (-1),
.cycle 8 4 true (0),
.cycle 14 2 false (0),
.last 12 (1,true),
.cycle 16 2 false (2),
.cycle 14 2 false (2),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 4 16 true (0),
.cycle 9 3 true (0),
.cycle 21 2 false (1)
])
theorem kid05_part140_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part140) = true := by rfl

def kid05_part141 : Audit := .cycle 0 12 true (0)
theorem kid05_part141_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part141) = true := by rfl

def kid05_part142 : Audit := .cycle 9 4 true (0)
theorem kid05_part142_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part142) = true := by rfl

def kid05_part143 : Audit := .cycle 17 2 false (-1)
theorem kid05_part143_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part143) = true := by rfl

def kid05_part119 : Audit := .split 10 (5,true) (byMove [(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125),(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143)])

theorem kid05_part119_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part119) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part120),(kid05_part121),(kid05_part122),(kid05_part123),(kid05_part124),(kid05_part125),(kid05_part126),(kid05_part127),(kid05_part128),(kid05_part129),(kid05_part130),(kid05_part131),(kid05_part132),(kid05_part133),(kid05_part134),(kid05_part135),(kid05_part136),(kid05_part137),(kid05_part138),(kid05_part139),(kid05_part140),(kid05_part141),(kid05_part142),(kid05_part143)] mv))) = true

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
theorem kid05_part144_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part144) = true := by rfl

def kid05_part145 : Audit := .cycle 1 9 true (1)
theorem kid05_part145_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part145) = true := by rfl

def kid05_part146 : Audit := .cycle 2 8 true (1)
theorem kid05_part146_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part146) = true := by rfl

def kid05_part147 : Audit := .cycle 9 4 true (1)
theorem kid05_part147_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part147) = true := by rfl

def kid05_part148 : Audit := .cycle 9 1 true (1)
theorem kid05_part148_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part148) = true := by rfl

def kid05_part149 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 4 false (2),
.cycle 13 4 false (1),
.split 14 (1,true) (byMove [
.cycle 16 4 false (1),
.cycle 22 4 false (0),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 26 4 false (0),
.cycle 21 4 false (1),
.cycle 19 4 false (1),
.cycle 18 4 false (0),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.last 17 (2,true),
.last 15 (2,true),
.cycle 17 4 false (2),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 30 4 false (0),
.cycle 28 4 false (0),
.cycle 2 13 false (3),
.cycle 7 13 false (3),
.cycle 20 4 false (0),
.cycle 10 5 false (2)
]),
.split 14 (2,true) (byMove [
.cycle 16 4 false (1),
.last 15 (1,true),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 26 4 false (0),
.cycle 21 4 false (1),
.cycle 19 4 false (1),
.cycle 18 4 false (0),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.last 15 (1,true),
.cycle 19 4 false (2),
.cycle 17 4 false (2),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.last 28 (1,true),
.last 27 (1,true),
.cycle 2 13 false (3),
.cycle 7 13 false (3),
.last 19 (1,true),
.cycle 10 5 false (2)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 4 false (-1),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 16 4 false (3),
.cycle 9 4 true (0),
.cycle 13 4 false (1)
])
theorem kid05_part149_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part149) = true := by rfl

def kid05_part29 : Audit := .split 9 (4,false) (byMove [(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42),(kid05_part67),(kid05_part92),(kid05_part117),(kid05_part118),(kid05_part119),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)])

theorem kid05_part29_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (kid05_part29) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part30),(kid05_part31),(kid05_part32),(kid05_part33),(kid05_part34),(kid05_part35),(kid05_part36),(kid05_part37),(kid05_part38),(kid05_part39),(kid05_part40),(kid05_part41),(kid05_part42),(kid05_part67),(kid05_part92),(kid05_part117),(kid05_part118),(kid05_part119),(kid05_part144),(kid05_part145),(kid05_part146),(kid05_part147),(kid05_part148),(kid05_part149)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part30_checked

  · exact kid05_part36_checked

  · exact kid05_part42_checked

  · exact kid05_part144_checked

  · exact kid05_part31_checked

  · exact kid05_part37_checked

  · exact kid05_part67_checked

  · exact kid05_part145_checked

  · exact kid05_part32_checked

  · exact kid05_part38_checked

  · exact kid05_part92_checked

  · exact kid05_part146_checked

  · exact kid05_part33_checked

  · exact kid05_part39_checked

  · exact kid05_part117_checked

  · exact kid05_part147_checked

  · exact kid05_part34_checked

  · exact kid05_part40_checked

  · exact kid05_part118_checked

  · exact kid05_part148_checked

  · exact kid05_part35_checked

  · exact kid05_part41_checked

  · exact kid05_part119_checked

  · exact kid05_part149_checked

def kid05_part151 : Audit := .cycle 0 11 false (3)
theorem kid05_part151_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part151) = true := by rfl

def kid05_part152 : Audit := .cycle 18 1 false (0)
theorem kid05_part152_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part152) = true := by rfl

def kid05_part153 : Audit := .cycle 12 1 false (0)
theorem kid05_part153_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part153) = true := by rfl

def kid05_part154 : Audit := .cycle 11 1 false (-1)
theorem kid05_part154_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part154) = true := by rfl

def kid05_part155 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 false (3),
.cycle 19 1 false (-1),
.cycle 13 1 false (-1),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 0 12 true (-1),
.cycle 19 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 true (-1),
.cycle 12 1 false (0),
.split 13 (1,true) (byMove [
.cycle 11 4 true (-2),
.cycle 22 1 false (-2),
.last 14 (2,true),
.cycle 0 15 false (3),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 28 1 false (-2),
.cycle 8 14 false (2),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 11 3 true (-2),
.cycle 8 6 false (2),
.cycle 16 1 false (-2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 11 5 true (-2),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 10 16 false (3),
.cycle 25 1 false (-3),
.cycle 2 12 false (3),
.cycle 11 6 true (-2),
.cycle 9 8 false (1),
.cycle 17 1 false (-3)
]),
.split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 0 15 false (3),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 26 (1,true),
.cycle 8 14 false (2),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 11 3 true (-2),
.cycle 8 6 false (2),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 11 7 true (-3),
.cycle 11 5 true (-2),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 10 16 false (3),
.cycle 25 1 false (-3),
.cycle 2 12 false (3),
.cycle 11 6 true (-2),
.last 15 (1,true),
.cycle 17 1 false (-3)
]),
.cycle 0 14 true (-2),
.cycle 12 1 false (-2),
.cycle 11 1 false (-1),
.cycle 12 1 false (-2),
.cycle 24 1 false (-2),
.cycle 1 11 false (3),
.cycle 18 1 false (0),
.cycle 11 4 true (-1),
.cycle 11 1 true (-1),
.cycle 9 3 false (1)
])
theorem kid05_part155_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part155) = true := by rfl

def kid05_part156 : Audit := .cycle 11 1 false (-1)
theorem kid05_part156_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part156) = true := by rfl

def kid05_part157 : Audit := .cycle 0 11 true (0)
theorem kid05_part157_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part157) = true := by rfl

def kid05_part158 : Audit := .cycle 18 1 false (2)
theorem kid05_part158_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part158) = true := by rfl

def kid05_part159 : Audit := .cycle 12 1 false (2)
theorem kid05_part159_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part159) = true := by rfl

def kid05_part160 : Audit := .cycle 11 1 false (1)
theorem kid05_part160_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part160) = true := by rfl

def kid05_part161 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 19 1 false (1),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 19 1 false (3),
.cycle 13 1 false (3),
.cycle 12 1 false (2),
.cycle 11 1 true (1),
.cycle 12 1 false (2),
.split 13 (1,true) (byMove [
.cycle 11 4 true (0),
.cycle 22 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 11 3 true (0),
.cycle 8 6 true (0),
.cycle 16 1 false (0),
.last 16 (2,true),
.last 14 (2,true),
.cycle 11 5 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 11 6 true (0),
.cycle 9 8 true (0),
.cycle 9 5 true (0)
]),
.split 13 (2,true) (byMove [
.cycle 11 4 true (0),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 14 true (0),
.cycle 8 14 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 11 3 true (0),
.cycle 8 6 true (0),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 11 7 true (-1),
.cycle 11 5 true (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 11 6 true (0),
.last 15 (1,true),
.cycle 9 5 true (0)
]),
.cycle 0 14 true (0),
.cycle 12 1 false (0),
.cycle 11 1 false (1),
.cycle 12 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 18 1 false (2),
.cycle 11 4 true (1),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid05_part161_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part161) = true := by rfl

def kid05_part162 : Audit := .cycle 11 1 false (1)
theorem kid05_part162_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part162) = true := by rfl

def kid05_part164 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 22 1 false (2),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.cycle 15 1 false (1),
.cycle 11 4 true (-1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 28 1 false (0),
.cycle 1 14 true (-1),
.cycle 21 1 false (1),
.cycle 13 4 true (-1),
.cycle 14 1 true (0),
.cycle 9 6 true (-1)
])
theorem kid05_part164_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part164) = true := by rfl

def kid05_part165 : Audit := .cycle 21 1 false (-1)
theorem kid05_part165_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part165) = true := by rfl

def kid05_part166 : Audit := .split 13 (2,true) (byMove [
.cycle 0 14 false (3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 18 1 false (-2),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.last 17 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid05_part166_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part166) = true := by rfl

def kid05_part167 : Audit := .cycle 0 14 true (-1)
theorem kid05_part167_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part167) = true := by rfl

def kid05_part168 : Audit := .cycle 14 1 false (-2)
theorem kid05_part168_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part168) = true := by rfl

def kid05_part169 : Audit := .cycle 10 3 false (0)
theorem kid05_part169_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part169) = true := by rfl

def kid05_part170 : Audit := .cycle 0 13 true (-1)
theorem kid05_part170_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part170) = true := by rfl

def kid05_part171 : Audit := .cycle 8 13 false (3)
theorem kid05_part171_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part171) = true := by rfl

def kid05_part172 : Audit := .cycle 20 1 false (0)
theorem kid05_part172_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part172) = true := by rfl

def kid05_part173 : Audit := .cycle 18 1 false (0)
theorem kid05_part173_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part173) = true := by rfl

def kid05_part174 : Audit := .split 13 (4,false) (byMove [
.cycle 27 1 false (-1),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 9 5 false (1),
.cycle 0 14 true (-1),
.cycle 8 15 false (4),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 13 1 true (1),
.cycle 8 7 false (2),
.cycle 11 3 true (-1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 9 5 false (1),
.cycle 6 19 false (5),
.cycle 1 13 true (-1),
.cycle 8 13 false (3),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.cycle 9 5 true (-1)
])
theorem kid05_part174_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part174) = true := by rfl

def kid05_part175 : Audit := .cycle 8 5 false (2)
theorem kid05_part175_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part175) = true := by rfl

def kid05_part176 : Audit := .cycle 15 1 false (-1)
theorem kid05_part176_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part176) = true := by rfl

def kid05_part177 : Audit := .split 15 (2,true) (byMove [
.last 17 (4,false),
.cycle 13 3 false (-1),
.cycle 18 1 false (-2),
.cycle 11 6 true (-2),
.cycle 17 1 false (-3),
.cycle 10 6 false (0),
.last 17 (4,false),
.cycle 32 1 false (-2),
.cycle 25 1 false (-1),
.cycle 0 17 true (-2),
.cycle 9 8 false (1),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-3),
.cycle 10 6 false (0),
.last 17 (4,false),
.cycle 12 5 false (0),
.cycle 28 1 false (-2),
.cycle 43 1 false (-3),
.cycle 20 1 false (-2),
.cycle 9 10 false (1)
])
theorem kid05_part177_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part177) = true := by rfl

def kid05_part178 : Audit := .split 13 (2,true) (byMove [
.last 18 (4,false),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 15 (4,false),
.cycle 0 17 true (-1),
.cycle 16 1 false (2),
.cycle 0 15 true (-1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 11 3 false (0),
.cycle 21 1 false (-1),
.last 17 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 15 (4,false),
.cycle 12 2 true (-1),
.cycle 2 13 false (3),
.cycle 0 15 true (-1),
.cycle 10 5 false (0),
.cycle 17 1 false (-1)
])
theorem kid05_part178_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part178) = true := by rfl

def kid05_part179 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 23 1 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 16 true (-1),
.cycle 23 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 true (1),
.cycle 16 1 false (2),
.cycle 11 5 true (-1),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 29 1 false (1),
.cycle 1 15 true (-1),
.cycle 22 1 false (2),
.cycle 13 4 true (-1),
.cycle 15 1 true (1),
.cycle 9 7 true (-1)
])
theorem kid05_part179_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part179) = true := by rfl

def kid05_part180 : Audit := .cycle 14 1 false (-2)
theorem kid05_part180_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part180) = true := by rfl

def kid05_part181 : Audit := .cycle 10 3 false (0)
theorem kid05_part181_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part181) = true := by rfl

def kid05_part182 : Audit := .cycle 9 17 false (4)
theorem kid05_part182_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part182) = true := by rfl

def kid05_part183 : Audit := .cycle 25 1 false (-1)
theorem kid05_part183_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part183) = true := by rfl

def kid05_part184 : Audit := .cycle 2 11 false (3)
theorem kid05_part184_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part184) = true := by rfl

def kid05_part185 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 8 17 false (3),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 8 9 false (2),
.cycle 0 17 true (-1),
.cycle 8 19 false (5),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 16 1 true (2),
.cycle 8 11 false (3),
.cycle 11 6 true (-1),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 8 9 false (2),
.cycle 8 23 false (6),
.cycle 1 16 true (-1),
.cycle 8 17 false (4),
.cycle 13 4 true (0),
.cycle 16 1 true (2),
.cycle 9 8 true (-1)
])
theorem kid05_part185_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part185) = true := by rfl

def kid05_part186 : Audit := .split 13 (4,false) (byMove [
.cycle 29 1 false (-1),
.cycle 12 2 true (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 10 5 false (1),
.cycle 17 1 false (-1),
.cycle 0 14 true (-1),
.cycle 27 1 false (-1),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 13 1 true (1),
.cycle 19 1 false (-1),
.cycle 9 7 false (1),
.cycle 19 1 false (-1),
.last 14 (2,true),
.cycle 22 1 false (0),
.cycle 10 5 false (1),
.cycle 17 1 false (-1),
.cycle 31 1 false (-1),
.cycle 9 17 false (4),
.cycle 25 1 false (-1),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.cycle 9 9 false (2)
])
theorem kid05_part186_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part186) = true := by rfl

def kid05_part187 : Audit := .cycle 17 1 false (-1)
theorem kid05_part187_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part187) = true := by rfl

def kid05_part163 : Audit := .split 12 (1,true) (byMove [(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173),(kid05_part174),(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179),(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187)])

theorem kid05_part163_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part163) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part164),(kid05_part165),(kid05_part166),(kid05_part167),(kid05_part168),(kid05_part169),(kid05_part170),(kid05_part171),(kid05_part172),(kid05_part173),(kid05_part174),(kid05_part175),(kid05_part176),(kid05_part177),(kid05_part178),(kid05_part179),(kid05_part180),(kid05_part181),(kid05_part182),(kid05_part183),(kid05_part184),(kid05_part185),(kid05_part186),(kid05_part187)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part164_checked

  · exact kid05_part170_checked

  · exact kid05_part176_checked

  · exact kid05_part182_checked

  · exact kid05_part165_checked

  · exact kid05_part171_checked

  · exact kid05_part177_checked

  · exact kid05_part183_checked

  · exact kid05_part166_checked

  · exact kid05_part172_checked

  · exact kid05_part178_checked

  · exact kid05_part184_checked

  · exact kid05_part167_checked

  · exact kid05_part173_checked

  · exact kid05_part179_checked

  · exact kid05_part185_checked

  · exact kid05_part168_checked

  · exact kid05_part174_checked

  · exact kid05_part180_checked

  · exact kid05_part186_checked

  · exact kid05_part169_checked

  · exact kid05_part175_checked

  · exact kid05_part181_checked

  · exact kid05_part187_checked

def kid05_part189 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 false (3),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 15 true (-1),
.cycle 22 1 false (2),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 true (0),
.cycle 15 1 false (1),
.last 16 (1,true),
.cycle 11 4 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 26 (1,true),
.cycle 1 14 true (-1),
.cycle 21 1 false (1),
.cycle 13 4 true (-1),
.cycle 14 1 true (0),
.cycle 9 6 true (-1)
])
theorem kid05_part189_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part189) = true := by rfl

def kid05_part190 : Audit := .split 13 (1,true) (byMove [
.cycle 0 14 false (3),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 0 14 true (-1),
.cycle 21 1 false (1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 3 false (0),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 27 (4,false),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.last 17 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid05_part190_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part190) = true := by rfl

def kid05_part191 : Audit := .cycle 15 1 false (-1)
theorem kid05_part191_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part191) = true := by rfl

def kid05_part192 : Audit := .cycle 0 14 true (-1)
theorem kid05_part192_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part192) = true := by rfl

def kid05_part193 : Audit := .cycle 14 1 false (-2)
theorem kid05_part193_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part193) = true := by rfl

def kid05_part194 : Audit := .cycle 10 3 false (0)
theorem kid05_part194_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part194) = true := by rfl

def kid05_part195 : Audit := .cycle 0 13 true (-1)
theorem kid05_part195_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part195) = true := by rfl

def kid05_part196 : Audit := .cycle 8 13 false (3)
theorem kid05_part196_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part196) = true := by rfl

def kid05_part197 : Audit := .cycle 20 1 false (0)
theorem kid05_part197_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part197) = true := by rfl

def kid05_part198 : Audit := .cycle 18 1 false (0)
theorem kid05_part198_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part198) = true := by rfl

def kid05_part199 : Audit := .split 13 (4,false) (byMove [
.last 25 (1,true),
.cycle 1 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 9 5 false (1),
.cycle 0 14 true (-1),
.cycle 8 15 false (4),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 13 1 true (1),
.cycle 8 7 false (2),
.last 15 (1,true),
.cycle 11 3 true (-1),
.cycle 0 16 true (-1),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 9 5 false (1),
.last 25 (1,true),
.cycle 1 13 true (-1),
.cycle 8 13 false (3),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.cycle 9 5 true (-1)
])
theorem kid05_part199_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part199) = true := by rfl

def kid05_part200 : Audit := .cycle 8 5 false (2)
theorem kid05_part200_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part200) = true := by rfl

def kid05_part201 : Audit := .cycle 15 1 false (-1)
theorem kid05_part201_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part201) = true := by rfl

def kid05_part202 : Audit := .split 13 (1,true) (byMove [
.last 19 (4,false),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 15 (4,false),
.cycle 22 1 false (2),
.cycle 11 4 true (-1),
.cycle 0 15 true (-1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 18 1 false (-2),
.cycle 11 3 false (0),
.last 17 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 15 (4,false),
.cycle 13 12 true (-1),
.cycle 12 2 true (-1),
.cycle 0 15 true (-1),
.cycle 10 5 false (0),
.cycle 13 2 true (-1)
])
theorem kid05_part202_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part202) = true := by rfl

def kid05_part203 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (-2),
.cycle 25 1 false (1),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 0 18 true (-2),
.cycle 25 1 false (3),
.cycle 19 1 false (3),
.cycle 18 1 false (2),
.cycle 17 1 true (1),
.cycle 18 1 false (2),
.last 19 (1,true),
.cycle 11 7 true (-2),
.cycle 0 20 true (-2),
.cycle 18 1 false (0),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.last 29 (1,true),
.cycle 1 17 true (-2),
.cycle 24 1 false (2),
.cycle 15 4 true (-1),
.cycle 17 1 true (1),
.cycle 9 9 true (-2)
])
theorem kid05_part203_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part203) = true := by rfl

def kid05_part204 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 23 1 false (1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 0 16 true (-1),
.cycle 23 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 true (1),
.cycle 16 1 false (2),
.last 17 (1,true),
.cycle 11 5 true (-1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.last 27 (1,true),
.cycle 1 15 true (-1),
.cycle 22 1 false (2),
.cycle 13 4 true (-1),
.cycle 15 1 true (1),
.cycle 9 7 true (-1)
])
theorem kid05_part204_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part204) = true := by rfl

def kid05_part205 : Audit := .cycle 14 1 false (-2)
theorem kid05_part205_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part205) = true := by rfl

def kid05_part206 : Audit := .cycle 10 3 false (0)
theorem kid05_part206_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part206) = true := by rfl

def kid05_part207 : Audit := .split 24 (1,true) (byMove [
.last 26 (4,false),
.cycle 33 1 false (-1),
.cycle 12 16 true (-1),
.cycle 0 29 true (-1),
.cycle 26 1 false (-2),
.cycle 23 7 false (1),
.last 26 (4,false),
.cycle 8 27 false (4),
.cycle 12 13 true (0),
.cycle 0 26 true (-1),
.cycle 9 17 false (4),
.cycle 10 15 true (-1),
.cycle 27 1 false (-1),
.last 36 (4,false),
.cycle 9 19 false (4),
.cycle 28 1 false (0),
.cycle 26 1 false (-2),
.cycle 33 1 false (-3),
.last 26 (4,false),
.cycle 14 12 true (0),
.cycle 12 13 true (0),
.cycle 0 26 true (-1),
.cycle 10 19 false (4),
.cycle 23 2 true (0)
])
theorem kid05_part207_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part207) = true := by rfl

def kid05_part208 : Audit := .split 23 (1,true) (byMove [
.last 39 (4,false),
.cycle 0 27 true (-2),
.cycle 25 1 false (-1),
.cycle 24 1 false (-2),
.last 24 (4,false),
.cycle 24 1 false (-2),
.last 25 (4,false),
.cycle 32 1 false (2),
.cycle 1 24 true (-1),
.cycle 0 25 true (-1),
.cycle 25 1 false (-1),
.cycle 10 14 true (-1),
.cycle 28 1 false (-2),
.cycle 23 5 false (0),
.last 27 (4,false),
.cycle 24 1 false (-2),
.last 24 (4,false),
.cycle 24 1 false (-2),
.last 25 (4,false),
.cycle 13 12 true (-1),
.cycle 12 12 true (-1),
.cycle 0 25 true (-1),
.cycle 10 15 false (3),
.cycle 22 2 true (-1)
])
theorem kid05_part208_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part208) = true := by rfl

def kid05_part209 : Audit := .cycle 2 11 false (3)
theorem kid05_part209_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part209) = true := by rfl

def kid05_part210 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 8 17 false (3),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 8 9 false (2),
.cycle 0 17 true (-1),
.cycle 8 19 false (5),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 16 1 true (2),
.cycle 8 11 false (3),
.last 18 (1,true),
.cycle 11 6 true (-1),
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 8 9 false (2),
.last 28 (1,true),
.cycle 1 16 true (-1),
.cycle 8 17 false (4),
.cycle 13 4 true (0),
.cycle 16 1 true (2),
.cycle 9 8 true (-1)
])
theorem kid05_part210_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part210) = true := by rfl

def kid05_part211 : Audit := .split 13 (4,false) (byMove [
.last 27 (1,true),
.last 14 (1,true),
.cycle 12 2 true (0),
.cycle 0 15 true (-1),
.cycle 10 5 false (1),
.last 15 (1,true),
.cycle 0 14 true (-1),
.last 25 (1,true),
.cycle 3 13 false (3),
.cycle 3 11 false (3),
.cycle 13 1 true (1),
.last 17 (1,true),
.cycle 9 7 false (1),
.last 14 (1,true),
.last 17 (1,true),
.cycle 22 1 false (0),
.cycle 10 5 false (1),
.last 15 (1,true),
.last 25 (1,true),
.last 24 (1,true),
.last 23 (1,true),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.last 16 (1,true)
])
theorem kid05_part211_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part211) = true := by rfl

def kid05_part212 : Audit := .split 15 (1,true) (byMove [
.last 23 (4,false),
.cycle 0 19 true (-2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.last 17 (4,false),
.cycle 24 1 false (2),
.cycle 9 8 true (-1),
.cycle 0 17 true (-1),
.cycle 17 1 false (-1),
.cycle 10 6 true (-1),
.cycle 20 1 false (-2),
.cycle 15 5 false (0),
.last 19 (4,false),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.last 17 (4,false),
.cycle 13 12 true (-1),
.cycle 12 4 true (-1),
.cycle 0 17 true (-1),
.cycle 10 7 false (1),
.cycle 14 2 true (-1)
])
theorem kid05_part212_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part212) = true := by rfl

def kid05_part188 : Audit := .split 12 (2,true) (byMove [(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212)])

theorem kid05_part188_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part188) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part189),(kid05_part190),(kid05_part191),(kid05_part192),(kid05_part193),(kid05_part194),(kid05_part195),(kid05_part196),(kid05_part197),(kid05_part198),(kid05_part199),(kid05_part200),(kid05_part201),(kid05_part202),(kid05_part203),(kid05_part204),(kid05_part205),(kid05_part206),(kid05_part207),(kid05_part208),(kid05_part209),(kid05_part210),(kid05_part211),(kid05_part212)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part189_checked

  · exact kid05_part195_checked

  · exact kid05_part201_checked

  · exact kid05_part207_checked

  · exact kid05_part190_checked

  · exact kid05_part196_checked

  · exact kid05_part202_checked

  · exact kid05_part208_checked

  · exact kid05_part191_checked

  · exact kid05_part197_checked

  · exact kid05_part203_checked

  · exact kid05_part209_checked

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

def kid05_part213 : Audit := .cycle 0 13 true (-1)
theorem kid05_part213_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part213) = true := by rfl

def kid05_part214 : Audit := .cycle 11 1 false (-1)
theorem kid05_part214_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part214) = true := by rfl

def kid05_part216 : Audit := .split 14 (2,true) (byMove [
.cycle 29 1 false (-3),
.last 15 (1,true),
.cycle 18 1 false (-2),
.cycle 11 18 true (-2),
.cycle 10 6 false (0),
.cycle 17 1 false (-3),
.cycle 11 17 true (-2),
.cycle 27 1 false (-3),
.cycle 3 14 false (3),
.cycle 3 12 false (3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 256, 524288, 1048576, 2097152, 256, 256, 32768, 33554432, 67108864, 134217728, 268500992, 67108864, 256, 33554432, 67108864, 134217728, 1594196224, 67108864, 1594196224, 1073741824],[16, 1073741824, 16, 1, 0, 65536, 65536, 1073741824, 65536, 4096, 256, 65536, 4194304, 1073741824, 4194304, 262144, 32768, 65536, 268435456, 1073741824, 268435456, 16777216, 256, 327680, 268435456, 1073741824, 268435456, 16777216, 1594196224, 1594196224, 1073741824],2138862080⟩,
.cycle 19 1 false (-3),
.cycle 9 8 false (1),
.last 15 (1,true),
.cycle 21 1 false (-1),
.cycle 11 20 true (-2),
.cycle 10 6 false (0),
.cycle 17 1 false (-3),
.cycle 29 1 false (-3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 256, 524288, 1048576, 2097152, 256, 256, 32768, 33554432, 67108864, 134217728, 268435584, 67108864, 256, 33554432, 67108864, 134217728, 1594130816, 67108864, 1594130816, 1073741824],[16, 1073741824, 128, 1, 0, 128, 65536, 1073741824, 128, 4096, 256, 128, 4194304, 1073741824, 524288, 262144, 32768, 128, 268435456, 1073741824, 33554432, 16777216, 256, 262272, 268435456, 1073741824, 33554432, 16777216, 1594130816, 1594130816, 1073741824],2138862080⟩,
.cycle 25 1 false (-3),
.cycle 11 21 true (-2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 256, 524288, 1048576, 2097152, 256, 256, 32768, 33554432, 67108864, 134217728, 268436480, 67108864, 256, 33554432, 67108864, 134217728, 1594131712, 67108864, 1594131712, 1073741824],[16, 1073741824, 1024, 1, 0, 1024, 65536, 1073741824, 1024, 4096, 256, 1024, 4194304, 1073741824, 4194304, 262144, 32768, 1024, 268435456, 1073741824, 268435456, 16777216, 256, 263168, 268435456, 1073741824, 268435456, 16777216, 1594131712, 1594131712, 1073741824],2138862080⟩,
.cycle 10 8 false (1)
])
theorem kid05_part216_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part216) = true := by rfl

def kid05_part217 : Audit := .cycle 0 15 true (-2)
theorem kid05_part217_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part217) = true := by rfl

def kid05_part218 : Audit := .cycle 13 1 false (-1)
theorem kid05_part218_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part218) = true := by rfl

def kid05_part219 : Audit := .cycle 12 1 false (-2)
theorem kid05_part219_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part219) = true := by rfl

def kid05_part220 : Audit := .cycle 11 1 false (-1)
theorem kid05_part220_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part220) = true := by rfl

def kid05_part221 : Audit := .cycle 12 1 false (-2)
theorem kid05_part221_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part221) = true := by rfl

def kid05_part222 : Audit := .cycle 0 14 true (-1)
theorem kid05_part222_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part222) = true := by rfl

def kid05_part223 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (1),
.cycle 13 1 false (-1),
.cycle 0 13 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (3),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 13 1 false (-1),
.cycle 25 1 false (-1),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 24 1 false (4),
.cycle 8 14 true (-1),
.cycle 9 4 true (-1)
])
theorem kid05_part223_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part223) = true := by rfl

def kid05_part224 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 13 1 false (-1),
.cycle 0 13 true (-1),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (3),
.cycle 13 1 false (1),
.last 14 (1,true),
.last 15 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 13 1 false (-1),
.cycle 25 1 false (-1),
.cycle 1 12 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (4),
.cycle 21 1 false (1),
.cycle 9 4 true (-1)
])
theorem kid05_part224_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part224) = true := by rfl

def kid05_part225 : Audit := .cycle 0 13 true (-1)
theorem kid05_part225_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part225) = true := by rfl

def kid05_part226 : Audit := .cycle 13 1 false (-1)
theorem kid05_part226_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part226) = true := by rfl

def kid05_part227 : Audit := .cycle 10 2 true (-1)
theorem kid05_part227_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part227) = true := by rfl

def kid05_part228 : Audit := .split 13 (1,true) (byMove [
.cycle 11 4 true (-2),
.cycle 22 1 false (-2),
.last 14 (2,true),
.cycle 0 18 true (-2),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 44 (2,true),
.cycle 8 16 false (3),
.last 14 (2,true),
.cycle 0 15 true (-2),
.cycle 9 6 false (1),
.cycle 18 1 false (-2),
.cycle 16 1 false (-2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 64, 0, 128, 256, 32768, 4194320, 128, 64, 524288, 1048576, 2097152, 384, 64, 128, 33554432, 67108864, 134217728, 1342177344, 16777600, 384, 33554432, 67108864, 134217728, 1594196416, 1594196416, 1594196416, 1073741824],[16, 64, 1073741824, 1, 0, 65536, 65536, 64, 1073741824, 4096, 64, 65536, 4194304, 262144, 1073741824, 262144, 128, 64, 268435456, 16777216, 1073741824, 16777216, 384, 65600, 268435456, 16777216, 1073741824, 16777216, 1594196416, 1594196416, 1073741824],2138862080⟩,
.last 32 (2,true),
.last 14 (2,true),
.last 37 (2,true),
.cycle 17 1 false (-3),
.cycle 10 6 false (0)
])
theorem kid05_part228_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part228) = true := by rfl

def kid05_part229 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 30 (1,true),
.last 14 (1,true),
.cycle 23 1 false (-1),
.cycle 0 15 true (-2),
.cycle 9 6 false (1),
.last 16 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 64, 0, 128, 256, 32768, 4194320, 1073741824, 64, 33554432, 67108864, 2097152, 256, 64, 128, 33554432, 67108864, 134217728, 64, 16777216, 256, 33554432, 67108864, 134217728, 1594196416, 1090519040, 1594196416, 1073741824],[16, 1073741824, 64, 1, 0, 65536, 65536, 1073741824, 64, 4096, 64, 65536, 4194304, 1073741824, 16777216, 262144, 128, 1073741824, 268435456, 1073741824, 16777216, 16777216, 256, 65536, 268435456, 1073741824, 16777216, 16777216, 1594196416, 1594196416, 1073741824],2136749568⟩,
.last 14 (1,true),
.cycle 25 1 false (-3),
.last 27 (1,true),
.cycle 17 1 false (-3),
.cycle 10 6 false (0)
])
theorem kid05_part229_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part229) = true := by rfl

def kid05_part230 : Audit := .cycle 0 18 true (-2)
theorem kid05_part230_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part230) = true := by rfl

def kid05_part231 : Audit := .cycle 12 1 false (-2)
theorem kid05_part231_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part231) = true := by rfl

def kid05_part232 : Audit := .cycle 11 1 false (-1)
theorem kid05_part232_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part232) = true := by rfl

def kid05_part233 : Audit := .cycle 12 1 false (-2)
theorem kid05_part233_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part233) = true := by rfl

def kid05_part234 : Audit := .split 32 (1,true) (byMove [
.cycle 12 21 true (-2),
.cycle 1 34 false (5),
.last 33 (2,true),
.cycle 65 79 true (-3),
.cycle 53 1 false (-3),
.cycle 24 9 false (2),
.cycle 28 37 true (-2),
.cycle 22 19 false (5),
.last 48 (2,true),
.cycle 59 1 false (-3),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 3, 4, 4, 4],[128, 256, 8, 0, 64, 0, 128, 256, 32768, 4194320, 64, 64, 128, 256, 2097152, 33024, 64, 128, 33554432, 67108864, 2097152, 1078231296, 16777216, 33024, 33554432, 67108864, 134217728, 1598390720, 16777216, 1598390720, 1073741824],[16, 16, 1073741824, 1, 0, 65536, 65536, 65536, 1073741824, 4096, 64, 65536, 4194304, 4194304, 1073741824, 262144, 128, 65536, 4194304, 4194304, 1073741824, 262144, 33024, 268500992, 268435456, 268435456, 1073741824, 16777216, 1598390720, 1598390720, 1073741824],2138849792⟩,
.cycle 22 11 false (4),
.cycle 55 1 false (-3),
.last 36 (2,true),
.last 33 (2,true),
.last 56 (2,true),
.cycle 11 26 true (-2),
.cycle 24 9 false (2),
.proven (BB6.Agent11Raw39B0REPumps.M127.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M127.never m hm),
.cycle 11 36 true (-2),
.cycle 16 17 false (5),
.proven (BB6.Agent11Raw39B0REPumps.M128.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M128.never m hm),
.cycle 11 42 true (-2),
.cycle 11 28 true (-2)
])
theorem kid05_part234_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part234) = true := by rfl

def kid05_part235 : Audit := .split 12 (1,true) (byMove [
.cycle 1 14 true (-1),
.cycle 21 1 false (-1),
.last 13 (2,true),
.cycle 0 14 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 1 13 true (-1),
.cycle 8 5 false (2),
.cycle 15 1 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 1 15 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 128, 0, 128, 256, 32768, 4194320, 128, 128, 524288, 1048576, 2097152, 32896, 524288, 256, 33554432, 67108864, 134217728, 268697664, 33554432, 32896, 33554432, 67108864, 134217728, 1594720704, 33554432, 1594720704, 1073741824],[16, 64, 1073741824, 1, 0, 64, 65536, 64, 1073741824, 4096, 128, 64, 4194304, 262144, 1073741824, 262144, 256, 64, 268435456, 16777216, 1073741824, 16777216, 32896, 1090519040, 268435456, 16777216, 1073741824, 16777216, 1594720704, 1594720704, 1073741824],2138927616⟩,
.cycle 24 1 false (-2),
.cycle 2 11 false (3),
.cycle 1 16 true (-1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 128, 0, 128, 256, 32768, 4194320, 128, 128, 524288, 1048576, 2097152, 32896, 524288, 256, 33554432, 67108864, 134217728, 268698624, 33554432, 32896, 33554432, 67108864, 134217728, 1594131840, 33554432, 1594131840, 1073741824],[16, 1024, 1073741824, 1, 0, 1024, 65536, 1024, 1073741824, 4096, 128, 1024, 4194304, 4194304, 1073741824, 262144, 256, 1024, 268435456, 268435456, 1073741824, 16777216, 32896, 1342177280, 268435456, 268435456, 1073741824, 16777216, 1594131840, 1594131840, 1073741824],2138927616⟩,
.cycle 16 1 false (-2)
])
theorem kid05_part235_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part235) = true := by rfl

def kid05_part236 : Audit := .split 12 (2,true) (byMove [
.cycle 21 1 false (1),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 14 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 0 13 true (-1),
.cycle 8 13 false (3),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 8 13 false (3),
.cycle 8 5 false (2),
.cycle 15 1 false (-1),
.last 13 (1,true),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.last 29 (1,true),
.cycle 24 1 false (-2),
.cycle 2 11 false (3),
.cycle 8 17 false (4),
.cycle 24 1 false (-2),
.cycle 16 1 false (-2)
])
theorem kid05_part236_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part236) = true := by rfl

def kid05_part237 : Audit := .cycle 0 13 true (-1)
theorem kid05_part237_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part237) = true := by rfl

def kid05_part238 : Audit := .cycle 10 3 false (0)
theorem kid05_part238_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part238) = true := by rfl

def kid05_part239 : Audit := .cycle 14 1 false (-2)
theorem kid05_part239_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part239) = true := by rfl

def kid05_part215 : Audit := .split 11 (4,false) (byMove [(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part237),(kid05_part238),(kid05_part239)])

theorem kid05_part215_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part215) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part216),(kid05_part217),(kid05_part218),(kid05_part219),(kid05_part220),(kid05_part221),(kid05_part222),(kid05_part223),(kid05_part224),(kid05_part225),(kid05_part226),(kid05_part227),(kid05_part228),(kid05_part229),(kid05_part230),(kid05_part231),(kid05_part232),(kid05_part233),(kid05_part234),(kid05_part235),(kid05_part236),(kid05_part237),(kid05_part238),(kid05_part239)] mv))) = true

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
theorem kid05_part240_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part240) = true := by rfl

def kid05_part241 : Audit := .cycle 0 11 true (0)
theorem kid05_part241_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part241) = true := by rfl

def kid05_part242 : Audit := .cycle 1 10 true (0)
theorem kid05_part242_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part242) = true := by rfl

def kid05_part243 : Audit := .cycle 17 1 false (1)
theorem kid05_part243_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part243) = true := by rfl

def kid05_part244 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (4),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 15 1 false (3),
.split 16 (1,true) (byMove [
.cycle 13 4 true (1),
.cycle 25 1 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 18 1 false (0),
.cycle 10 7 true (0),
.cycle 0 17 true (0),
.cycle 8 17 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 14 3 true (1),
.cycle 8 9 true (0),
.cycle 19 1 false (1),
.last 19 (2,true),
.last 17 (2,true),
.cycle 12 5 true (0),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 11 6 true (0),
.cycle 9 11 true (0),
.cycle 9 8 true (0)
]),
.split 16 (2,true) (byMove [
.cycle 13 4 true (1),
.last 17 (1,true),
.cycle 19 1 false (1),
.cycle 0 18 true (0),
.cycle 18 1 false (0),
.cycle 10 7 true (0),
.cycle 0 17 true (0),
.cycle 8 17 true (0),
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 14 3 true (1),
.cycle 8 9 true (0),
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 12 7 true (0),
.cycle 12 5 true (0),
.cycle 18 1 false (0),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 11 6 true (0),
.last 18 (1,true),
.cycle 9 8 true (0)
]),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (3),
.cycle 11 4 true (0),
.cycle 14 1 true (2),
.cycle 9 6 true (0)
])
theorem kid05_part244_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part244) = true := by rfl

def kid05_part245 : Audit := .split 11 (4,false) (byMove [
.cycle 0 14 true (0),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 21 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 21 1 false (1),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 0 17 true (-2),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 24 1 false (2),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.last 15 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 1 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 11 2 true (0),
.cycle 9 4 true (0)
]),
.cycle 0 13 true (0),
.cycle 13 1 false (-1),
.cycle 10 2 true (0),
.cycle 0 12 true (0),
.cycle 8 12 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 11 1 true (1),
.cycle 8 4 true (0),
.cycle 14 1 false (0),
.split 12 (1,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 21 1 false (3),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 10 3 true (0),
.cycle 17 1 false (-1),
.last 14 (2,true),
.last 18 (2,true),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 13 1 false (-1),
.last 16 (2,true),
.cycle 1 13 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 10 4 true (0),
.cycle 10 3 true (0)
]),
.split 12 (2,true) (byMove [
.cycle 0 20 true (-1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 17 (1,true),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.last 13 (1,true),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 10 3 true (0),
.last 14 (1,true),
.last 15 (1,true),
.cycle 0 19 true (-1),
.cycle 13 1 false (-1),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 true (0),
.last 13 (1,true),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 10 4 true (0),
.cycle 10 3 true (0)
]),
.cycle 15 1 false (1),
.cycle 13 1 false (-1),
.cycle 10 4 true (0),
.cycle 0 12 true (0),
.cycle 1 11 true (0),
.cycle 2 10 true (0),
.cycle 11 4 true (1),
.cycle 11 1 true (1),
.cycle 9 3 true (0)
])
theorem kid05_part245_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part245) = true := by rfl

def kid05_part246 : Audit := .cycle 9 2 true (0)
theorem kid05_part246_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part246) = true := by rfl

def kid05_part150 : Audit := .split 10 (5,true) (byMove [(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part188),(kid05_part213),(kid05_part214),(kid05_part215),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246)])

theorem kid05_part150_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (kid05_part150) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part151),(kid05_part152),(kid05_part153),(kid05_part154),(kid05_part155),(kid05_part156),(kid05_part157),(kid05_part158),(kid05_part159),(kid05_part160),(kid05_part161),(kid05_part162),(kid05_part163),(kid05_part188),(kid05_part213),(kid05_part214),(kid05_part215),(kid05_part240),(kid05_part241),(kid05_part242),(kid05_part243),(kid05_part244),(kid05_part245),(kid05_part246)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part151_checked

  · exact kid05_part157_checked

  · exact kid05_part163_checked

  · exact kid05_part241_checked

  · exact kid05_part152_checked

  · exact kid05_part158_checked

  · exact kid05_part188_checked

  · exact kid05_part242_checked

  · exact kid05_part153_checked

  · exact kid05_part159_checked

  · exact kid05_part213_checked

  · exact kid05_part243_checked

  · exact kid05_part154_checked

  · exact kid05_part160_checked

  · exact kid05_part214_checked

  · exact kid05_part244_checked

  · exact kid05_part155_checked

  · exact kid05_part161_checked

  · exact kid05_part215_checked

  · exact kid05_part245_checked

  · exact kid05_part156_checked

  · exact kid05_part162_checked

  · exact kid05_part240_checked

  · exact kid05_part246_checked

def kid05_part247 : Audit := .cycle 0 9 true (0)
theorem kid05_part247_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (kid05_part247) = true := by rfl

def kid05_part248 : Audit := .cycle 1 8 true (1)
theorem kid05_part248_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,1⟩)) (kid05_part248) = true := by rfl

def kid05_part250 : Audit := .cycle 0 22 true (0)
theorem kid05_part250_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part250) = true := by rfl

def kid05_part251 : Audit := .cycle 31 1 false (7)
theorem kid05_part251_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part251) = true := by rfl

def kid05_part252 : Audit := .cycle 23 1 false (5)
theorem kid05_part252_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part252) = true := by rfl

def kid05_part253 : Audit := .cycle 22 1 false (4)
theorem kid05_part253_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part253) = true := by rfl

def kid05_part254 : Audit := .cycle 21 1 false (5)
theorem kid05_part254_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part254) = true := by rfl

def kid05_part255 : Audit := .cycle 24 1 false (6)
theorem kid05_part255_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part255) = true := by rfl

def kid05_part256 : Audit := .cycle 0 22 true (0)
theorem kid05_part256_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part256) = true := by rfl

def kid05_part257 : Audit := .cycle 31 1 false (9)
theorem kid05_part257_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part257) = true := by rfl

def kid05_part258 : Audit := .cycle 23 1 false (7)
theorem kid05_part258_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part258) = true := by rfl

def kid05_part259 : Audit := .cycle 22 1 false (6)
theorem kid05_part259_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part259) = true := by rfl

def kid05_part260 : Audit := .cycle 21 1 true (5)
theorem kid05_part260_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part260) = true := by rfl

def kid05_part261 : Audit := .cycle 24 1 false (8)
theorem kid05_part261_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part261) = true := by rfl

def kid05_part262 : Audit := .split 23 (1,true) (byMove [
.cycle 20 4 true (4),
.cycle 34 1 false (6),
.split 24 (2,true) (byMove [
.cycle 0 25 true (0),
.cycle 34 1 false (6),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 27 1 false (5),
.cycle 0 25 true (0),
.cycle 34 1 false (8),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 21 4 true (4),
.cycle 27 1 false (7),
.cycle 22 3 false (5),
.cycle 29 1 false (3),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 24 2 true (3),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 33 1 false (7),
.cycle 19 7 true (3),
.cycle 30 1 false (6),
.cycle 0 36 true (0)
]),
.cycle 0 25 true (0),
.cycle 27 1 false (5),
.split 24 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 34 1 false (6),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 27 1 false (5),
.cycle 0 25 true (0),
.cycle 34 1 false (8),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 21 4 true (4),
.cycle 27 1 false (7),
.cycle 22 3 false (5),
.last 26 (2,true),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.last 26 (2,true),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 33 1 false (7),
.cycle 19 7 true (3),
.cycle 30 1 false (6),
.cycle 0 36 true (0)
]),
.cycle 0 24 true (0),
.cycle 48 1 false (10),
.cycle 0 34 true (0),
.cycle 31 1 false (7),
.cycle 21 3 true (4),
.cycle 8 16 true (0),
.cycle 28 1 false (6),
.split 26 (2,true) (byMove [
.cycle 20 7 false (5),
.cycle 24 3 false (4),
.cycle 29 1 false (3),
.cycle 22 6 true (3),
.cycle 30 1 false (4),
.last 27 (5,true),
.cycle 20 7 true (3),
.cycle 14 52 true (0),
.cycle 9 19 true (0),
.cycle 0 28 true (0),
.cycle 0 39 true (0),
.last 27 (5,true),
.cycle 0 32 true (0),
.cycle 24 3 false (4),
.cycle 34 1 false (6),
.cycle 32 1 false (6),
.cycle 16 11 true (1),
.last 27 (5,true),
.cycle 0 41 true (0),
.cycle 23 5 false (5),
.cycle 2 26 true (0),
.cycle 0 28 true (0),
.last 28 (5,true),
.last 27 (5,true)
]),
.split 24 (2,true) (byMove [
.cycle 20 13 false (5),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 0 28 true (0),
.cycle 20 5 true (4),
.cycle 0 28 true (0),
.cycle 27 1 false (7),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.last 25 (5,true),
.cycle 22 3 false (5),
.cycle 34 1 false (6),
.cycle 18 7 true (2),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 24 2 true (3),
.cycle 20 5 true (4),
.cycle 23 2 true (4),
.cycle 2 24 true (0),
.cycle 0 26 true (0),
.last 26 (5,true),
.last 25 (5,true)
]),
.cycle 19 5 true (3),
.cycle 0 28 true (0),
.split 24 (5,true) (byMove [
.last 27 (2,true),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 0 28 true (0),
.cycle 20 5 true (4),
.last 27 (2,true),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.cycle 28 1 false (8),
.cycle 22 3 false (5),
.last 26 (2,true),
.cycle 18 7 true (2),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.last 26 (2,true),
.cycle 20 5 true (4),
.cycle 23 2 true (4),
.last 25 (2,true),
.cycle 0 26 true (0),
.cycle 32 1 false (6),
.cycle 0 37 true (0)
]),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 19 6 true (3),
.cycle 0 38 true (0),
.cycle 0 35 true (0)
])
theorem kid05_part262_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part262) = true := by rfl

def kid05_part263 : Audit := .split 23 (2,true) (byMove [
.cycle 20 4 true (4),
.split 24 (1,true) (byMove [
.cycle 0 25 true (0),
.cycle 34 1 false (6),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 27 1 false (5),
.cycle 0 25 true (0),
.cycle 34 1 false (8),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 21 4 true (4),
.cycle 27 1 false (7),
.cycle 31 1 false (5),
.cycle 22 3 false (5),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 36 1 false (6),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 33 1 false (7),
.cycle 19 7 true (3),
.last 28 (5,true),
.cycle 0 36 true (0)
]),
.cycle 26 1 false (4),
.cycle 0 25 true (0),
.cycle 27 1 false (5),
.split 24 (5,true) (byMove [
.cycle 0 25 true (0),
.cycle 34 1 false (6),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 27 1 false (5),
.cycle 0 25 true (0),
.cycle 34 1 false (8),
.cycle 26 1 false (6),
.cycle 25 1 false (5),
.cycle 21 4 true (4),
.cycle 27 1 false (7),
.last 26 (1,true),
.cycle 22 3 false (5),
.cycle 0 27 true (0),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 29 1 false (5),
.cycle 0 25 true (0),
.cycle 1 24 true (0),
.cycle 33 1 false (7),
.cycle 19 7 true (3),
.last 26 (1,true),
.cycle 0 36 true (0)
]),
.cycle 0 24 true (0),
.cycle 48 1 false (10),
.cycle 0 34 true (0),
.cycle 31 1 false (7),
.cycle 21 3 true (4),
.cycle 8 16 true (0),
.cycle 28 1 false (6),
.split 24 (1,true) (byMove [
.cycle 20 9 false (5),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 0 28 true (0),
.cycle 20 5 true (4),
.cycle 35 1 false (9),
.cycle 22 4 true (4),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.last 25 (5,true),
.cycle 0 32 true (0),
.cycle 22 3 false (5),
.cycle 18 7 true (2),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 22 5 false (5),
.cycle 20 5 true (4),
.cycle 1 25 true (0),
.cycle 23 2 true (4),
.cycle 0 26 true (0),
.last 26 (5,true),
.last 25 (5,true)
]),
.cycle 18 7 true (2),
.cycle 19 5 true (3),
.cycle 0 28 true (0),
.split 24 (5,true) (byMove [
.cycle 20 9 false (5),
.cycle 0 28 true (0),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 0 28 true (0),
.cycle 20 5 true (4),
.last 25 (1,true),
.cycle 25 2 true (4),
.cycle 0 26 true (0),
.cycle 28 1 false (6),
.cycle 28 1 false (8),
.last 26 (1,true),
.cycle 22 3 false (5),
.cycle 18 7 true (2),
.cycle 25 1 false (3),
.cycle 21 4 false (5),
.cycle 25 2 true (3),
.cycle 20 5 true (4),
.last 25 (1,true),
.cycle 23 2 true (4),
.cycle 0 26 true (0),
.last 28 (1,true),
.cycle 0 37 true (0)
]),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 2 22 true (0),
.cycle 19 6 true (3),
.split 25 (1,true) (byMove [
.last 31 (5,true),
.cycle 0 37 true (0),
.cycle 30 1 false (4),
.cycle 0 30 true (0),
.cycle 29 1 false (5),
.last 26 (5,true),
.cycle 20 6 true (4),
.cycle 0 53 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 0 38 true (0),
.last 26 (5,true),
.cycle 0 31 true (0),
.last 30 (5,true),
.last 28 (5,true),
.cycle 31 1 false (7),
.cycle 16 10 true (1),
.last 26 (5,true),
.cycle 20 6 true (4),
.cycle 1 26 true (0),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.last 27 (5,true),
.last 26 (5,true)
]),
.cycle 0 35 true (0)
])
theorem kid05_part263_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part263) = true := by rfl

def kid05_part264 : Audit := .cycle 0 24 true (0)
theorem kid05_part264_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part264) = true := by rfl

def kid05_part265 : Audit := .cycle 22 1 false (4)
theorem kid05_part265_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part265) = true := by rfl

def kid05_part266 : Audit := .cycle 21 1 false (5)
theorem kid05_part266_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part266) = true := by rfl

def kid05_part267 : Audit := .split 23 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 33 1 false (7),
.cycle 25 1 false (5),
.cycle 24 1 false (4),
.cycle 21 3 false (5),
.cycle 26 1 false (6),
.cycle 0 24 true (0),
.cycle 33 1 false (9),
.cycle 25 1 false (7),
.cycle 24 1 false (6),
.cycle 21 3 true (4),
.cycle 26 1 false (8),
.split 25 (1,true) (byMove [
.cycle 20 6 true (4),
.cycle 36 1 false (6),
.cycle 23 3 false (5),
.cycle 0 27 true (0),
.cycle 29 1 false (5),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 50 1 false (10),
.cycle 0 36 true (0),
.cycle 33 1 false (7),
.cycle 21 5 true (4),
.cycle 8 18 true (0),
.cycle 30 1 false (6),
.cycle 0 34 true (0),
.cycle 23 3 false (5),
.cycle 19 7 true (3),
.cycle 0 30 true (0),
.last 26 (5,true),
.cycle 0 26 true (0),
.cycle 1 25 true (0),
.cycle 2 24 true (0),
.cycle 19 8 true (3),
.last 27 (5,true),
.cycle 0 37 true (0)
]),
.split 26 (1,true) (byMove [
.cycle 20 11 false (5),
.cycle 0 30 true (0),
.cycle 28 1 false (4),
.cycle 27 1 false (3),
.cycle 21 6 false (5),
.cycle 0 30 true (0),
.cycle 20 7 true (4),
.cycle 37 1 false (9),
.cycle 23 4 true (4),
.cycle 0 28 true (0),
.cycle 30 1 false (6),
.last 27 (5,true),
.cycle 0 34 true (0),
.cycle 24 3 false (5),
.cycle 18 9 true (2),
.cycle 27 1 false (3),
.cycle 21 6 false (5),
.cycle 22 5 false (5),
.cycle 20 7 true (4),
.cycle 1 27 true (0),
.cycle 25 2 true (4),
.cycle 0 28 true (0),
.last 28 (5,true),
.last 27 (5,true)
]),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 21 3 false (5),
.cycle 22 2 true (4),
.cycle 0 24 true (0),
.cycle 1 23 true (0),
.cycle 32 1 false (8),
.cycle 19 6 true (3),
.split 25 (5,true) (byMove [
.cycle 0 37 true (0),
.cycle 0 29 true (0),
.cycle 27 1 false (5),
.cycle 26 1 false (4),
.cycle 21 5 false (6),
.cycle 0 29 true (0),
.cycle 20 6 true (4),
.last 26 (1,true),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 29 1 false (7),
.cycle 29 1 false (9),
.last 27 (1,true),
.last 30 (1,true),
.cycle 18 8 true (2),
.cycle 26 1 false (4),
.cycle 25 5 false (5),
.cycle 22 8 true (4),
.cycle 20 6 true (4),
.last 26 (1,true),
.cycle 23 3 true (5),
.cycle 0 27 true (0),
.cycle 24 4 true (5),
.cycle 0 38 true (0)
]),
.cycle 0 35 true (0)
])
theorem kid05_part267_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part267) = true := by rfl

def kid05_part268 : Audit := .cycle 0 22 true (0)
theorem kid05_part268_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part268) = true := by rfl

def kid05_part269 : Audit := .cycle 1 21 true (0)
theorem kid05_part269_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part269) = true := by rfl

def kid05_part270 : Audit := .cycle 30 1 false (8)
theorem kid05_part270_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part270) = true := by rfl

def kid05_part271 : Audit := .cycle 19 4 true (3)
theorem kid05_part271_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part271) = true := by rfl

def kid05_part272 : Audit := .cycle 21 1 true (5)
theorem kid05_part272_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part272) = true := by rfl

def kid05_part273 : Audit := .cycle 0 33 true (0)
theorem kid05_part273_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part273) = true := by rfl

def kid05_part249 : Audit := .split 21 (4,false) (byMove [(kid05_part250),(kid05_part251),(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part265),(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273)])

theorem kid05_part249_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (kid05_part249) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) 21 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,2⟩)) (4,false) (some mv)) (byMove [(kid05_part250),(kid05_part251),(kid05_part252),(kid05_part253),(kid05_part254),(kid05_part255),(kid05_part256),(kid05_part257),(kid05_part258),(kid05_part259),(kid05_part260),(kid05_part261),(kid05_part262),(kid05_part263),(kid05_part264),(kid05_part265),(kid05_part266),(kid05_part267),(kid05_part268),(kid05_part269),(kid05_part270),(kid05_part271),(kid05_part272),(kid05_part273)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part250_checked

  · exact kid05_part256_checked

  · exact kid05_part262_checked

  · exact kid05_part268_checked

  · exact kid05_part251_checked

  · exact kid05_part257_checked

  · exact kid05_part263_checked

  · exact kid05_part269_checked

  · exact kid05_part252_checked

  · exact kid05_part258_checked

  · exact kid05_part264_checked

  · exact kid05_part270_checked

  · exact kid05_part253_checked

  · exact kid05_part259_checked

  · exact kid05_part265_checked

  · exact kid05_part271_checked

  · exact kid05_part254_checked

  · exact kid05_part260_checked

  · exact kid05_part266_checked

  · exact kid05_part272_checked

  · exact kid05_part255_checked

  · exact kid05_part261_checked

  · exact kid05_part267_checked

  · exact kid05_part273_checked

def kid05_part274 : Audit := .cycle 16 1 false (2)
theorem kid05_part274_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,3⟩)) (kid05_part274) = true := by rfl

def kid05_part276 : Audit := .cycle 0 10 true (0)
theorem kid05_part276_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part276) = true := by rfl

def kid05_part277 : Audit := .cycle 1 9 true (1)
theorem kid05_part277_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part277) = true := by rfl

def kid05_part278 : Audit := .cycle 20 1 false (2)
theorem kid05_part278_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part278) = true := by rfl

def kid05_part279 : Audit := .cycle 17 1 false (1)
theorem kid05_part279_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part279) = true := by rfl

def kid05_part280 : Audit := .cycle 14 1 false (0)
theorem kid05_part280_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part280) = true := by rfl

def kid05_part281 : Audit := .cycle 8 2 true (2)
theorem kid05_part281_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part281) = true := by rfl

def kid05_part282 : Audit := .cycle 0 10 true (0)
theorem kid05_part282_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part282) = true := by rfl

def kid05_part283 : Audit := .cycle 1 9 true (1)
theorem kid05_part283_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part283) = true := by rfl

def kid05_part285 : Audit := .cycle 0 28 true (0)
theorem kid05_part285_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part285) = true := by rfl

def kid05_part286 : Audit := .cycle 26 20 true (2)
theorem kid05_part286_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part286) = true := by rfl

def kid05_part287 : Audit := .cycle 23 1 false (3)
theorem kid05_part287_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part287) = true := by rfl

def kid05_part288 : Audit := .cycle 22 1 false (2)
theorem kid05_part288_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part288) = true := by rfl

def kid05_part289 : Audit := .cycle 28 1 false (8)
theorem kid05_part289_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part289) = true := by rfl

def kid05_part290 : Audit := .cycle 31 1 false (7)
theorem kid05_part290_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part290) = true := by rfl

def kid05_part291 : Audit := .cycle 27 1 false (7)
theorem kid05_part291_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part291) = true := by rfl

def kid05_part292 : Audit := .split 22 (1,true) (byMove [
.cycle 0 53 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.cycle 36 1 false (10),
.cycle 26 1 false (8),
.cycle 34 1 false (10),
.cycle 34 1 false (10),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.last 23 (5,true),
.cycle 40 1 false (10),
.cycle 21 31 true (3),
.cycle 28 1 false (8),
.cycle 23 1 false (3),
.cycle 38 1 false (10),
.cycle 38 1 false (10),
.cycle 0 37 true (0),
.cycle 1 23 true (0),
.cycle 25 24 true (4),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true)
])
theorem kid05_part292_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part292) = true := by rfl

def kid05_part293 : Audit := .cycle 25 1 false (7)
theorem kid05_part293_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part293) = true := by rfl

def kid05_part294 : Audit := .cycle 26 1 false (8)
theorem kid05_part294_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part294) = true := by rfl

def kid05_part295 : Audit := .cycle 28 1 false (8)
theorem kid05_part295_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part295) = true := by rfl

def kid05_part296 : Audit := .split 22 (5,true) (byMove [
.cycle 8 18 true (0),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 23 1 false (3),
.cycle 0 26 true (0),
.cycle 29 1 false (9),
.cycle 26 1 false (8),
.last 23 (1,true),
.cycle 27 1 false (9),
.cycle 0 24 true (0),
.cycle 27 1 false (7),
.cycle 27 1 false (9),
.last 24 (1,true),
.cycle 8 20 true (0),
.cycle 28 1 false (8),
.cycle 23 1 false (3),
.cycle 31 1 false (9),
.cycle 31 1 false (9),
.cycle 0 37 true (0),
.last 23 (1,true),
.cycle 8 16 true (0),
.cycle 0 24 true (0),
.cycle 39 1 false (11),
.cycle 23 14 true (5)
])
theorem kid05_part296_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part296) = true := by rfl

def kid05_part297 : Audit := .split 23 (1,true) (byMove [
.cycle 37 1 false (7),
.cycle 61 1 false (7),
.cycle 21 3 false (3),
.cycle 0 31 true (0),
.cycle 32 1 false (8),
.last 24 (5,true),
.cycle 6 18 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 1, 8, 32, 64, 64],64⟩,
.cycle 27 12 true (4),
.cycle 26 20 true (2),
.cycle 30 16 true (4),
.last 24 (5,true),
.cycle 43 1 false (7),
.cycle 17 10 true (1),
.cycle 21 3 false (3),
.cycle 36 1 false (8),
.cycle 18 6 true (1),
.last 24 (5,true),
.cycle 27 15 true (3),
.cycle 1 25 true (0),
.cycle 2 30 true (0),
.cycle 9 17 true (0),
.last 25 (5,true),
.last 24 (5,true)
])
theorem kid05_part297_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part297) = true := by rfl

def kid05_part298 : Audit := .split 24 (1,true) (byMove [
.cycle 20 10 true (1),
.cycle 0 62 true (0),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 33 1 false (7),
.cycle 19 6 true (1),
.cycle 36 1 false (8),
.cycle 38 1 false (10),
.cycle 21 4 true (2),
.cycle 31 1 false (7),
.cycle 43 1 false (7),
.last 25 (5,true),
.cycle 17 10 true (1),
.cycle 22 3 false (3),
.cycle 40 1 false (8),
.cycle 25 1 false (1),
.cycle 20 5 false (3),
.cycle 18 8 true (1),
.cycle 34 18 true (4),
.cycle 1 27 true (0),
.cycle 23 2 true (2),
.cycle 5 20 true (0),
.last 26 (5,true),
.last 25 (5,true)
])
theorem kid05_part298_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part298) = true := by rfl

def kid05_part299 : Audit := .cycle 29 1 false (7)
theorem kid05_part299_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part299) = true := by rfl

def kid05_part300 : Audit := .cycle 22 1 false (2)
theorem kid05_part300_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part300) = true := by rfl

def kid05_part301 : Audit := .cycle 20 2 true (2)
theorem kid05_part301_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part301) = true := by rfl

def kid05_part302 : Audit := .cycle 37 1 false (7)
theorem kid05_part302_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part302) = true := by rfl

def kid05_part303 : Audit := .cycle 25 13 true (3)
theorem kid05_part303_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part303) = true := by rfl

def kid05_part304 : Audit := .split 22 (1,true) (byMove [
.cycle 1 25 true (0),
.cycle 1 33 true (0),
.cycle 1 25 true (0),
.cycle 0 27 true (0),
.cycle 0 28 true (0),
.last 23 (5,true),
.cycle 9 15 true (0),
.far true 1 ⟨0,[0, 0],[8, 8, 8, 8, 8, 8, 64],[8, 8, 8, 8, 32, 64, 64],64⟩,
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.cycle 25 13 true (3),
.last 23 (5,true),
.cycle 1 27 true (0),
.cycle 22 5 false (4),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.cycle 1 31 true (0),
.last 23 (5,true),
.cycle 0 37 true (0),
.cycle 1 23 true (0),
.cycle 1 23 true (0),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true)
])
theorem kid05_part304_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part304) = true := by rfl

def kid05_part305 : Audit := .cycle 2 22 true (0)
theorem kid05_part305_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part305) = true := by rfl

def kid05_part306 : Audit := .cycle 9 15 true (0)
theorem kid05_part306_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part306) = true := by rfl

def kid05_part307 : Audit := .split 23 (5,true) (byMove [
.cycle 0 28 true (0),
.cycle 26 11 true (2),
.cycle 25 1 false (3),
.cycle 24 1 false (2),
.cycle 26 1 false (4),
.cycle 0 28 true (0),
.last 25 (1,true),
.cycle 25 11 true (5),
.cycle 0 26 true (0),
.cycle 24 1 false (4),
.cycle 24 11 true (4),
.cycle 29 1 false (7),
.last 25 (1,true),
.cycle 26 11 true (4),
.last 27 (1,true),
.cycle 24 1 false (2),
.cycle 26 11 true (4),
.cycle 0 30 true (0),
.last 25 (1,true),
.cycle 25 11 true (5),
.cycle 0 26 true (0),
.cycle 31 1 false (7),
.cycle 24 11 true (4),
.cycle 26 15 true (3)
])
theorem kid05_part307_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part307) = true := by rfl

def kid05_part308 : Audit := .split 22 (5,true) (byMove [
.cycle 43 1 false (11),
.last 23 (1,true),
.cycle 26 15 true (3),
.last 25 (1,true),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 9 15 true (0),
.last 23 (1,true),
.cycle 23 24 true (5),
.cycle 0 24 true (0),
.cycle 25 13 true (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 52, 4, 16, 64],[16, 64, 32, 1, 20, 32, 64],64⟩,
.cycle 47 1 false (11),
.last 23 (1,true),
.cycle 21 2 true (3),
.cycle 29 1 false (7),
.cycle 23 18 true (2),
.cycle 25 20 true (2),
.cycle 0 37 true (0),
.last 23 (1,true),
.cycle 2 36 true (0),
.cycle 0 24 true (0),
.cycle 24 25 true (4),
.cycle 23 14 true (5)
])
theorem kid05_part308_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part308) = true := by rfl

def kid05_part284 : Audit := .split 21 (2,true) (byMove [(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288),(kid05_part289),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308)])

theorem kid05_part284_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part284) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) 21 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part285),(kid05_part286),(kid05_part287),(kid05_part288),(kid05_part289),(kid05_part290),(kid05_part291),(kid05_part292),(kid05_part293),(kid05_part294),(kid05_part295),(kid05_part296),(kid05_part297),(kid05_part298),(kid05_part299),(kid05_part300),(kid05_part301),(kid05_part302),(kid05_part303),(kid05_part304),(kid05_part305),(kid05_part306),(kid05_part307),(kid05_part308)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part285_checked

  · exact kid05_part291_checked

  · exact kid05_part297_checked

  · exact kid05_part303_checked

  · exact kid05_part286_checked

  · exact kid05_part292_checked

  · exact kid05_part298_checked

  · exact kid05_part304_checked

  · exact kid05_part287_checked

  · exact kid05_part293_checked

  · exact kid05_part299_checked

  · exact kid05_part305_checked

  · exact kid05_part288_checked

  · exact kid05_part294_checked

  · exact kid05_part300_checked

  · exact kid05_part306_checked

  · exact kid05_part289_checked

  · exact kid05_part295_checked

  · exact kid05_part301_checked

  · exact kid05_part307_checked

  · exact kid05_part290_checked

  · exact kid05_part296_checked

  · exact kid05_part302_checked

  · exact kid05_part308_checked

def kid05_part309 : Audit := .cycle 22 1 false (6)
theorem kid05_part309_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part309) = true := by rfl

def kid05_part310 : Audit := .cycle 9 1 true (3)
theorem kid05_part310_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part310) = true := by rfl

def kid05_part311 : Audit := .cycle 8 2 true (2)
theorem kid05_part311_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part311) = true := by rfl

def kid05_part313 : Audit := .cycle 9 4 true (2)
theorem kid05_part313_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part313) = true := by rfl

def kid05_part314 : Audit := .cycle 1 12 true (1)
theorem kid05_part314_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part314) = true := by rfl

def kid05_part315 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 4 false (1),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 8 5 true (2),
.cycle 20 3 false (1),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.last 20 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 9 7 true (2),
.cycle 6 8 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part315_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part315) = true := by rfl

def kid05_part316 : Audit := .cycle 0 13 true (0)
theorem kid05_part316_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part316) = true := by rfl

def kid05_part317 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 19 5 false (0),
.cycle 0 19 true (0),
.cycle 25 5 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 5 false (1),
.cycle 19 5 false (2),
.cycle 19 5 false (0),
.last 20 (2,true),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 20 5 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 5 false (2),
.cycle 22 5 false (2),
.cycle 21 5 false (1),
.cycle 13 6 true (0)
])
theorem kid05_part317_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part317) = true := by rfl

def kid05_part318 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 4 false (1),
.cycle 18 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 8 5 true (2),
.cycle 20 3 false (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.cycle 20 7 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 9 7 true (2),
.cycle 6 8 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part318_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part318) = true := by rfl

def kid05_part319 : Audit := .cycle 0 12 true (0)
theorem kid05_part319_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part319) = true := by rfl

def kid05_part320 : Audit := .cycle 1 11 true (1)
theorem kid05_part320_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part320) = true := by rfl

def kid05_part321 : Audit := .split 23 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 9 18 true (2),
.cycle 6 19 true (2),
.cycle 8 16 true (2),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 1, 0, 64],[0, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 13 11 true (2),
.cycle 9 15 true (2),
.cycle 8 16 true (2),
.cycle 10 14 true (2),
.cycle 22 4 true (4),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.cycle 17 8 true (3),
.cycle 7 18 true (2),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 9 18 true (2),
.cycle 6 19 true (2),
.cycle 8 16 true (2)
])
theorem kid05_part321_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part321) = true := by rfl

def kid05_part322 : Audit := .cycle 3 9 true (1)
theorem kid05_part322_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part322) = true := by rfl

def kid05_part323 : Audit := .cycle 9 3 true (2)
theorem kid05_part323_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part323) = true := by rfl

def kid05_part324 : Audit := .cycle 8 4 true (2)
theorem kid05_part324_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part324) = true := by rfl

def kid05_part325 : Audit := .cycle 6 6 true (2)
theorem kid05_part325_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part325) = true := by rfl

def kid05_part326 : Audit := .split 14 (2,true) (byMove [
.cycle 19 7 false (1),
.cycle 16 3 false (0),
.cycle 18 1 false (0),
.cycle 10 6 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 9 7 true (1),
.cycle 1 17 true (1),
.far true 1 ⟨0,[0, 0],[2, 0, 8, 8, 1, 2, 64],[2, 2, 8, 0, 32, 64, 64],64⟩,
.cycle 0 16 true (0),
.cycle 20 9 false (2),
.last 15 (5,true),
.cycle 21 9 false (1),
.cycle 16 3 false (0),
.cycle 15 12 true (-1),
.cycle 5 10 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 19 11 false (3),
.cycle 16 5 false (2),
.cycle 2 14 true (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid05_part326_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part326) = true := by rfl

def kid05_part327 : Audit := .split 12 (2,true) (byMove [
.cycle 20 13 false (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 4 false (1),
.last 18 (5,true),
.cycle 9 5 true (2),
.cycle 0 16 true (0),
.cycle 33 1 false (7),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 20 3 false (1),
.cycle 15 12 true (-2),
.cycle 9 7 true (1),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.last 20 (5,true),
.cycle 9 5 true (2),
.cycle 11 2 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part327_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part327) = true := by rfl

def kid05_part328 : Audit := .cycle 9 5 true (2)
theorem kid05_part328_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part328) = true := by rfl

def kid05_part329 : Audit := .split 18 (5,true) (byMove [
.cycle 40 5 false (0),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 19 5 false (0),
.cycle 19 5 false (2),
.last 20 (2,true),
.cycle 22 5 false (4),
.cycle 19 1 false (1),
.cycle 19 5 false (1),
.cycle 20 5 false (2),
.cycle 19 5 false (0),
.last 20 (2,true),
.cycle 21 5 false (2),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 20 5 false (0),
.cycle 15 4 true (0),
.last 20 (2,true),
.cycle 22 20 true (0),
.cycle 22 5 false (2),
.cycle 21 5 false (1),
.cycle 12 8 true (0)
])
theorem kid05_part329_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part329) = true := by rfl

def kid05_part330 : Audit := .split 12 (5,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 17 4 false (1),
.cycle 18 5 false (0),
.cycle 9 5 true (2),
.cycle 7 8 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 8 6 true (2),
.cycle 20 3 false (1),
.last 14 (2,true),
.cycle 9 7 true (1),
.cycle 22 1 false (0),
.cycle 17 4 false (1),
.cycle 20 7 false (0),
.cycle 9 5 true (2),
.cycle 11 2 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 6 10 true (2),
.cycle 8 6 true (2)
])
theorem kid05_part330_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part330) = true := by rfl

def kid05_part331 : Audit := .cycle 0 12 true (0)
theorem kid05_part331_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part331) = true := by rfl

def kid05_part332 : Audit := .cycle 1 11 true (1)
theorem kid05_part332_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part332) = true := by rfl

def kid05_part333 : Audit := .cycle 2 10 true (1)
theorem kid05_part333_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part333) = true := by rfl

def kid05_part334 : Audit := .cycle 9 6 true (2)
theorem kid05_part334_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part334) = true := by rfl

def kid05_part335 : Audit := .cycle 6 7 true (2)
theorem kid05_part335_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part335) = true := by rfl

def kid05_part336 : Audit := .cycle 8 4 true (2)
theorem kid05_part336_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part336) = true := by rfl

def kid05_part312 : Audit := .split 11 (1,true) (byMove [(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316),(kid05_part317),(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336)])

theorem kid05_part312_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part312) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part313),(kid05_part314),(kid05_part315),(kid05_part316),(kid05_part317),(kid05_part318),(kid05_part319),(kid05_part320),(kid05_part321),(kid05_part322),(kid05_part323),(kid05_part324),(kid05_part325),(kid05_part326),(kid05_part327),(kid05_part328),(kid05_part329),(kid05_part330),(kid05_part331),(kid05_part332),(kid05_part333),(kid05_part334),(kid05_part335),(kid05_part336)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part313_checked

  · exact kid05_part319_checked

  · exact kid05_part325_checked

  · exact kid05_part331_checked

  · exact kid05_part314_checked

  · exact kid05_part320_checked

  · exact kid05_part326_checked

  · exact kid05_part332_checked

  · exact kid05_part315_checked

  · exact kid05_part321_checked

  · exact kid05_part327_checked

  · exact kid05_part333_checked

  · exact kid05_part316_checked

  · exact kid05_part322_checked

  · exact kid05_part328_checked

  · exact kid05_part334_checked

  · exact kid05_part317_checked

  · exact kid05_part323_checked

  · exact kid05_part329_checked

  · exact kid05_part335_checked

  · exact kid05_part318_checked

  · exact kid05_part324_checked

  · exact kid05_part330_checked

  · exact kid05_part336_checked

def kid05_part338 : Audit := .cycle 9 4 true (2)
theorem kid05_part338_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part338) = true := by rfl

def kid05_part339 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 14 4 false (0),
.last 18 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 8 5 true (2),
.cycle 21 9 false (1),
.cycle 16 3 false (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 14 4 false (0),
.last 20 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 9 7 true (2),
.last 16 (5,true),
.cycle 8 5 true (2)
])
theorem kid05_part339_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part339) = true := by rfl

def kid05_part340 : Audit := .cycle 25 1 false (1)
theorem kid05_part340_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part340) = true := by rfl

def kid05_part341 : Audit := .cycle 0 13 true (0)
theorem kid05_part341_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part341) = true := by rfl

def kid05_part342 : Audit := .split 18 (5,true) (byMove [
.cycle 0 19 false (3),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 19 5 false (0),
.cycle 0 19 true (0),
.cycle 25 5 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 5 false (1),
.cycle 19 5 false (2),
.last 20 (1,true),
.cycle 19 5 false (0),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 20 5 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 5 false (2),
.cycle 22 5 false (2),
.last 20 (1,true),
.cycle 13 6 true (0)
])
theorem kid05_part342_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part342) = true := by rfl

def kid05_part343 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.last 14 (1,true),
.cycle 18 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 34 1 false (6),
.cycle 24 1 false (2),
.cycle 9 4 true (2),
.cycle 8 5 true (2),
.last 14 (1,true),
.last 16 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 20 7 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 9 7 true (2),
.last 14 (1,true),
.cycle 8 5 true (2)
])
theorem kid05_part343_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part343) = true := by rfl

def kid05_part344 : Audit := .cycle 0 12 true (0)
theorem kid05_part344_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part344) = true := by rfl

def kid05_part345 : Audit := .cycle 1 11 true (1)
theorem kid05_part345_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part345) = true := by rfl

def kid05_part346 : Audit := .far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 16, 128, 256, 8, 16, 4096, 16, 4096],[16, 4096, 4, 1, 4, 4096, 16, 4096, 4, 1, 4096, 4096, 4096],5120⟩
theorem kid05_part346_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part346) = true := by rfl

def kid05_part347 : Audit := .cycle 3 9 true (1)
theorem kid05_part347_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part347) = true := by rfl

def kid05_part348 : Audit := .cycle 9 3 true (2)
theorem kid05_part348_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part348) = true := by rfl

def kid05_part349 : Audit := .cycle 8 4 true (2)
theorem kid05_part349_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part349) = true := by rfl

def kid05_part350 : Audit := .cycle 6 6 true (2)
theorem kid05_part350_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part350) = true := by rfl

def kid05_part351 : Audit := .split 12 (1,true) (byMove [
.cycle 19 9 false (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.cycle 14 4 false (0),
.last 18 (5,true),
.cycle 9 5 true (2),
.cycle 1 13 true (1),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.last 13 (5,true),
.cycle 21 9 false (1),
.cycle 16 3 false (0),
.cycle 9 7 true (1),
.cycle 22 1 false (0),
.cycle 14 4 false (0),
.last 20 (5,true),
.cycle 9 5 true (2),
.cycle 1 13 true (1),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part351_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part351) = true := by rfl

def kid05_part352 : Audit := .cycle 9 7 true (1)
theorem kid05_part352_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part352) = true := by rfl

def kid05_part353 : Audit := .cycle 9 5 true (2)
theorem kid05_part353_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part353) = true := by rfl

def kid05_part354 : Audit := .split 18 (5,true) (byMove [
.cycle 40 5 false (0),
.cycle 25 5 false (1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 19 5 false (0),
.last 20 (1,true),
.cycle 19 5 false (2),
.cycle 22 5 false (4),
.cycle 19 1 false (1),
.cycle 19 5 false (1),
.cycle 20 5 false (2),
.last 20 (1,true),
.cycle 19 5 false (0),
.last 22 (1,true),
.cycle 19 1 false (-1),
.cycle 19 5 false (-1),
.cycle 20 5 false (0),
.last 20 (1,true),
.cycle 15 4 true (0),
.cycle 22 20 true (0),
.cycle 22 5 false (2),
.last 20 (1,true),
.cycle 12 8 true (0)
])
theorem kid05_part354_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part354) = true := by rfl

def kid05_part355 : Audit := .split 12 (5,true) (byMove [
.cycle 19 9 false (2),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 20 1 false (0),
.last 14 (1,true),
.cycle 18 5 false (0),
.cycle 9 5 true (2),
.last 13 (1,true),
.cycle 7 8 true (2),
.cycle 0 14 true (0),
.cycle 7 6 true (2),
.cycle 8 6 true (2),
.last 14 (1,true),
.last 16 (1,true),
.cycle 9 7 true (1),
.cycle 22 1 false (0),
.last 14 (1,true),
.cycle 20 7 false (0),
.cycle 9 5 true (2),
.last 13 (1,true),
.cycle 11 2 true (2),
.cycle 0 14 true (0),
.last 16 (1,true),
.cycle 8 6 true (2)
])
theorem kid05_part355_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part355) = true := by rfl

def kid05_part356 : Audit := .cycle 0 12 true (0)
theorem kid05_part356_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part356) = true := by rfl

def kid05_part357 : Audit := .cycle 1 11 true (1)
theorem kid05_part357_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part357) = true := by rfl

def kid05_part358 : Audit := .cycle 2 10 true (1)
theorem kid05_part358_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part358) = true := by rfl

def kid05_part359 : Audit := .cycle 9 6 true (2)
theorem kid05_part359_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part359) = true := by rfl

def kid05_part360 : Audit := .split 13 (1,true) (byMove [
.last 19 (5,true),
.last 27 (5,true),
.last 28 (5,true),
.cycle 0 18 true (0),
.last 22 (5,true),
.last 14 (5,true),
.cycle 9 6 true (2),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.cycle 7 7 true (2),
.last 14 (5,true),
.last 21 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.cycle 5 9 true (1),
.last 20 (5,true),
.last 14 (5,true),
.cycle 9 6 true (2),
.cycle 1 14 true (1),
.cycle 11 3 true (3),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part360_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part360) = true := by rfl

def kid05_part361 : Audit := .cycle 8 4 true (2)
theorem kid05_part361_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part361) = true := by rfl

def kid05_part337 : Audit := .split 11 (2,true) (byMove [(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347),(kid05_part348),(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part360),(kid05_part361)])

theorem kid05_part337_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part337) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part338),(kid05_part339),(kid05_part340),(kid05_part341),(kid05_part342),(kid05_part343),(kid05_part344),(kid05_part345),(kid05_part346),(kid05_part347),(kid05_part348),(kid05_part349),(kid05_part350),(kid05_part351),(kid05_part352),(kid05_part353),(kid05_part354),(kid05_part355),(kid05_part356),(kid05_part357),(kid05_part358),(kid05_part359),(kid05_part360),(kid05_part361)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part338_checked

  · exact kid05_part344_checked

  · exact kid05_part350_checked

  · exact kid05_part356_checked

  · exact kid05_part339_checked

  · exact kid05_part345_checked

  · exact kid05_part351_checked

  · exact kid05_part357_checked

  · exact kid05_part340_checked

  · exact kid05_part346_checked

  · exact kid05_part352_checked

  · exact kid05_part358_checked

  · exact kid05_part341_checked

  · exact kid05_part347_checked

  · exact kid05_part353_checked

  · exact kid05_part359_checked

  · exact kid05_part342_checked

  · exact kid05_part348_checked

  · exact kid05_part354_checked

  · exact kid05_part360_checked

  · exact kid05_part343_checked

  · exact kid05_part349_checked

  · exact kid05_part355_checked

  · exact kid05_part361_checked

def kid05_part362 : Audit := .cycle 0 12 true (0)
theorem kid05_part362_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part362) = true := by rfl

def kid05_part363 : Audit := .cycle 17 1 false (1)
theorem kid05_part363_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part363) = true := by rfl

def kid05_part364 : Audit := .cycle 14 1 false (0)
theorem kid05_part364_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part364) = true := by rfl

def kid05_part365 : Audit := .cycle 7 4 true (2)
theorem kid05_part365_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part365) = true := by rfl

def kid05_part366 : Audit := .cycle 0 10 true (0)
theorem kid05_part366_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part366) = true := by rfl

def kid05_part367 : Audit := .cycle 1 9 true (1)
theorem kid05_part367_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part367) = true := by rfl

def kid05_part368 : Audit := .cycle 2 8 true (1)
theorem kid05_part368_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part368) = true := by rfl

def kid05_part369 : Audit := .cycle 9 4 true (3)
theorem kid05_part369_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part369) = true := by rfl

def kid05_part370 : Audit := .cycle 9 1 true (3)
theorem kid05_part370_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part370) = true := by rfl

def kid05_part371 : Audit := .cycle 8 2 true (2)
theorem kid05_part371_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part371) = true := by rfl

def kid05_part275 : Audit := .split 9 (4,false) (byMove [(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part337),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371)])

theorem kid05_part275_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (kid05_part275) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part276),(kid05_part277),(kid05_part278),(kid05_part279),(kid05_part280),(kid05_part281),(kid05_part282),(kid05_part283),(kid05_part284),(kid05_part309),(kid05_part310),(kid05_part311),(kid05_part312),(kid05_part337),(kid05_part362),(kid05_part363),(kid05_part364),(kid05_part365),(kid05_part366),(kid05_part367),(kid05_part368),(kid05_part369),(kid05_part370),(kid05_part371)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part276_checked

  · exact kid05_part282_checked

  · exact kid05_part312_checked

  · exact kid05_part366_checked

  · exact kid05_part277_checked

  · exact kid05_part283_checked

  · exact kid05_part337_checked

  · exact kid05_part367_checked

  · exact kid05_part278_checked

  · exact kid05_part284_checked

  · exact kid05_part362_checked

  · exact kid05_part368_checked

  · exact kid05_part279_checked

  · exact kid05_part309_checked

  · exact kid05_part363_checked

  · exact kid05_part369_checked

  · exact kid05_part280_checked

  · exact kid05_part310_checked

  · exact kid05_part364_checked

  · exact kid05_part370_checked

  · exact kid05_part281_checked

  · exact kid05_part311_checked

  · exact kid05_part365_checked

  · exact kid05_part371_checked

def kid05_part372 : Audit := .cycle 8 1 true (2)
theorem kid05_part372_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨false,true,5⟩)) (kid05_part372) = true := by rfl

def kid05_part374 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 9 4 true (1),
.split 14 (2,true) (byMove [
.cycle 11 4 true (1),
.cycle 0 21 false (3),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 12 3 true (1),
.cycle 8 7 true (1),
.cycle 18 9 false (1),
.cycle 13 9 false (2),
.cycle 24 7 true (-1),
.cycle 11 5 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 6 true (1),
.last 22 (5,true),
.cycle 18 13 false (2)
]),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 4 true (1),
.cycle 12 1 true (2),
.cycle 6 8 true (1)
])
theorem kid05_part374_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part374) = true := by rfl

def kid05_part375 : Audit := .cycle 11 11 false (1)
theorem kid05_part375_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part375) = true := by rfl

def kid05_part377 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 0 25 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 18 false (3),
.cycle 0 14 true (0),
.cycle 0 25 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 0 18 true (0),
.cycle 0 17 false (3),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 22 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 24 true (0),
.cycle 12 4 true (0),
.cycle 13 1 true (1),
.cycle 0 21 false (3)
])
theorem kid05_part377_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part377) = true := by rfl

def kid05_part378 : Audit := .cycle 14 1 false (0)
theorem kid05_part378_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part378) = true := by rfl

def kid05_part379 : Audit := .cycle 14 1 false (0)
theorem kid05_part379_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part379) = true := by rfl

def kid05_part380 : Audit := .cycle 0 13 true (0)
theorem kid05_part380_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part380) = true := by rfl

def kid05_part381 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 18 false (3),
.cycle 12 12 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 31 (5,true),
.cycle 1 17 false (3),
.cycle 12 11 false (0),
.cycle 17 4 true (-3),
.cycle 17 1 true (-3),
.cycle 12 8 false (0)
])
theorem kid05_part381_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part381) = true := by rfl

def kid05_part382 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 20 4 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 4 false (1),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 4 false (0)
])
theorem kid05_part382_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part382) = true := by rfl

def kid05_part383 : Audit := .cycle 0 12 true (0)
theorem kid05_part383_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part383) = true := by rfl

def kid05_part384 : Audit := .cycle 1 11 true (1)
theorem kid05_part384_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part384) = true := by rfl

def kid05_part385 : Audit := .cycle 24 1 false (2)
theorem kid05_part385_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part385) = true := by rfl

def kid05_part386 : Audit := .cycle 21 1 false (1)
theorem kid05_part386_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part386) = true := by rfl

def kid05_part387 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 9 4 true (1),
.cycle 11 3 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.cycle 6 8 true (1)
])
theorem kid05_part387_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part387) = true := by rfl

def kid05_part388 : Audit := .cycle 8 4 true (1)
theorem kid05_part388_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part388) = true := by rfl

def kid05_part389 : Audit := .cycle 15 3 false (0)
theorem kid05_part389_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part389) = true := by rfl

def kid05_part390 : Audit := .cycle 14 1 false (0)
theorem kid05_part390_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part390) = true := by rfl

def kid05_part391 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 0 30 true (-1),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 0 23 true (-1),
.cycle 0 17 true (-1),
.cycle 0 30 true (-1),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 true (2),
.cycle 0 23 true (-1),
.cycle 0 22 true (-1),
.cycle 11 7 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 0 28 true (-1),
.cycle 0 41 true (-1),
.cycle 1 16 true (-1),
.cycle 0 29 true (-1),
.cycle 14 4 true (0),
.cycle 16 1 true (2),
.cycle 0 26 true (-1)
])
theorem kid05_part391_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part391) = true := by rfl

def kid05_part392 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 26 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.cycle 11 5 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 12 4 true (0),
.cycle 14 1 true (2),
.cycle 22 1 false (0)
])
theorem kid05_part392_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part392) = true := by rfl

def kid05_part393 : Audit := .split 17 (4,false) (byMove [
.last 22 (5,true),
.last 25 (5,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 26 true (-3),
.cycle 20 1 false (-2),
.cycle 16 2 true (-3),
.last 23 (5,true),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 0 34 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 38 (5,true),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.last 23 (5,true),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid05_part393_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part393) = true := by rfl

def kid05_part394 : Audit := .split 12 (5,true) (byMove [
.last 18 (4,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.last 14 (4,false),
.cycle 15 1 false (1),
.cycle 13 4 false (1),
.cycle 0 14 true (0),
.cycle 14 4 false (0),
.cycle 14 4 false (2),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.last 16 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.last 14 (4,false),
.cycle 13 4 false (1),
.cycle 11 2 true (0),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 20 4 false (0)
])
theorem kid05_part394_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part394) = true := by rfl

def kid05_part395 : Audit := .cycle 0 12 true (0)
theorem kid05_part395_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part395) = true := by rfl

def kid05_part396 : Audit := .cycle 1 11 true (1)
theorem kid05_part396_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part396) = true := by rfl

def kid05_part397 : Audit := .cycle 2 10 true (1)
theorem kid05_part397_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part397) = true := by rfl

def kid05_part398 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 8 8 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 13 21 true (0),
.cycle 34 1 false (6),
.cycle 15 1 true (3),
.cycle 8 8 true (1),
.cycle 9 7 true (1),
.cycle 11 6 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 4 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.cycle 6 11 true (1)
])
theorem kid05_part398_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part398) = true := by rfl

def kid05_part399 : Audit := .split 12 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 18 1 false (0),
.cycle 11 2 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 18 1 false (0),
.last 15 (5,true),
.cycle 29 1 false (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.cycle 16 11 false (2)
])
theorem kid05_part399_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part399) = true := by rfl

def kid05_part400 : Audit := .cycle 15 7 false (1)
theorem kid05_part400_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part400) = true := by rfl

def kid05_part376 : Audit := .split 11 (2,true) (byMove [(kid05_part377),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383),(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400)])

theorem kid05_part376_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part376) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part377),(kid05_part378),(kid05_part379),(kid05_part380),(kid05_part381),(kid05_part382),(kid05_part383),(kid05_part384),(kid05_part385),(kid05_part386),(kid05_part387),(kid05_part388),(kid05_part389),(kid05_part390),(kid05_part391),(kid05_part392),(kid05_part393),(kid05_part394),(kid05_part395),(kid05_part396),(kid05_part397),(kid05_part398),(kid05_part399),(kid05_part400)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part377_checked

  · exact kid05_part383_checked

  · exact kid05_part389_checked

  · exact kid05_part395_checked

  · exact kid05_part378_checked

  · exact kid05_part384_checked

  · exact kid05_part390_checked

  · exact kid05_part396_checked

  · exact kid05_part379_checked

  · exact kid05_part385_checked

  · exact kid05_part391_checked

  · exact kid05_part397_checked

  · exact kid05_part380_checked

  · exact kid05_part386_checked

  · exact kid05_part392_checked

  · exact kid05_part398_checked

  · exact kid05_part381_checked

  · exact kid05_part387_checked

  · exact kid05_part393_checked

  · exact kid05_part399_checked

  · exact kid05_part382_checked

  · exact kid05_part388_checked

  · exact kid05_part394_checked

  · exact kid05_part400_checked

def kid05_part401 : Audit := .cycle 0 12 true (0)
theorem kid05_part401_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part401) = true := by rfl

def kid05_part402 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 14 true (-1),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 4 false (0),
.cycle 14 4 false (-1),
.last 15 (2,true),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 27 4 false (-1),
.cycle 1 13 false (3),
.cycle 19 4 false (1),
.cycle 13 4 true (-1),
.cycle 13 1 true (-1),
.cycle 16 4 false (0)
]),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 20 4 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 14 4 false (2),
.cycle 14 4 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (3),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.cycle 16 4 false (2)
]),
.cycle 13 4 false (1),
.cycle 13 4 false (0),
.split 14 (2,true) (byMove [
.last 16 (4,false),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 16 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 28 4 false (0),
.cycle 21 4 false (1),
.cycle 19 4 false (1),
.last 15 (4,false),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.last 16 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 28 4 false (0),
.last 28 (4,false),
.cycle 2 13 false (3),
.last 18 (4,false),
.last 15 (4,false),
.cycle 20 4 false (0)
]),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 16 true (-1),
.cycle 22 4 false (2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 14 4 false (0),
.cycle 12 2 true (-1),
.cycle 14 4 false (-1),
.last 15 (2,true),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 32 4 false (0),
.cycle 14 4 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.cycle 15 4 false (-1)
]),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 23 4 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 4 false (1),
.cycle 0 17 true (0),
.cycle 23 4 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 true (2),
.cycle 17 4 false (3),
.cycle 17 4 false (2),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 4 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 22 4 false (4),
.cycle 13 4 true (0),
.cycle 16 1 true (2),
.cycle 19 4 false (3)
]),
.split 13 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 22 4 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 4 false (0),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.cycle 27 4 false (1),
.cycle 20 4 false (2),
.cycle 18 4 false (2),
.cycle 13 1 true (1),
.cycle 8 6 true (0),
.cycle 15 4 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 14 4 false (0),
.cycle 11 4 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.cycle 19 4 false (1)
]),
.cycle 15 4 false (1)
])
theorem kid05_part402_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part402) = true := by rfl

def kid05_part404 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 0 25 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 18 false (3),
.cycle 0 14 true (0),
.cycle 0 25 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 0 18 true (0),
.cycle 0 17 false (3),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 22 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 24 true (0),
.cycle 12 4 true (0),
.cycle 13 1 true (1),
.cycle 0 21 false (3)
])
theorem kid05_part404_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part404) = true := by rfl

def kid05_part405 : Audit := .cycle 13 11 false (-1)
theorem kid05_part405_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part405) = true := by rfl

def kid05_part406 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 21 1 false (-1)
])
theorem kid05_part406_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part406) = true := by rfl

def kid05_part407 : Audit := .cycle 0 13 true (0)
theorem kid05_part407_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part407) = true := by rfl

def kid05_part408 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 18 false (3),
.cycle 12 12 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.last 19 (2,true),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 16 15 false (1),
.cycle 1 17 false (3),
.cycle 12 11 false (0),
.cycle 17 4 true (-3),
.cycle 17 1 true (-3),
.cycle 12 8 false (0)
])
theorem kid05_part408_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part408) = true := by rfl

def kid05_part409 : Audit := .cycle 12 4 false (0)
theorem kid05_part409_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part409) = true := by rfl

def kid05_part410 : Audit := .cycle 0 12 true (0)
theorem kid05_part410_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part410) = true := by rfl

def kid05_part411 : Audit := .cycle 1 11 true (1)
theorem kid05_part411_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part411) = true := by rfl

def kid05_part412 : Audit := .cycle 24 1 false (2)
theorem kid05_part412_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part412) = true := by rfl

def kid05_part413 : Audit := .cycle 21 1 false (1)
theorem kid05_part413_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part413) = true := by rfl

def kid05_part414 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 9 4 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.cycle 6 8 true (1)
])
theorem kid05_part414_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part414) = true := by rfl

def kid05_part415 : Audit := .cycle 8 4 true (1)
theorem kid05_part415_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part415) = true := by rfl

def kid05_part416 : Audit := .cycle 15 3 false (0)
theorem kid05_part416_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part416) = true := by rfl

def kid05_part417 : Audit := .split 18 (2,true) (byMove [
.last 20 (4,false),
.cycle 12 7 false (0),
.cycle 21 1 false (-3),
.cycle 17 30 true (-3),
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.cycle 6 33 false (5),
.cycle 66 13 true (2),
.cycle 13 13 false (0),
.cycle 13 11 false (-1),
.last 19 (4,false),
.cycle 8 11 false (2),
.cycle 13 8 false (-1),
.cycle 12 7 false (0),
.last 23 (4,false),
.last 21 (4,false),
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.cycle 36 7 false (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 33169, 262144, 33152, 128, 256, 32768, 16, 262144, 33024, 2, 4, 8, 33024, 262144, 33152, 262144],[16, 33024, 128, 1, 33024, 129, 65536, 33152, 128, 4096, 33152, 33153, 16, 33024, 2, 1, 33024, 128, 262144],353820⟩,
.cycle 2 17 false (3),
.last 22 (4,false),
.last 19 (4,false),
.cycle 13 12 false (-1)
])
theorem kid05_part417_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part417) = true := by rfl

def kid05_part418 : Audit := .split 12 (2,true) (byMove [
.last 17 (4,false),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 11 11 false (1),
.last 14 (4,false),
.cycle 0 20 true (-2),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 20 true (-2),
.cycle 0 16 true (0),
.cycle 0 23 true (-2),
.cycle 0 39 true (-4),
.last 16 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 0 29 true (-3),
.last 14 (4,false),
.cycle 0 17 true (-1),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 0 17 true (-1),
.cycle 11 2 true (0)
])
theorem kid05_part418_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part418) = true := by rfl

def kid05_part419 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 26 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 19 1 false (1),
.cycle 18 1 false (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 12 4 true (0),
.cycle 14 1 true (2),
.cycle 22 1 false (0)
])
theorem kid05_part419_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part419) = true := by rfl

def kid05_part420 : Audit := .split 17 (4,false) (byMove [
.last 20 (2,true),
.last 23 (2,true),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 26 true (-3),
.cycle 13 6 false (-1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 12 6 false (0),
.cycle 16 2 true (-3),
.cycle 14 4 false (-1),
.last 19 (2,true),
.cycle 0 34 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 36 (2,true),
.cycle 15 3 false (-1),
.last 18 (2,true),
.last 21 (2,true),
.cycle 16 3 false (-2),
.cycle 11 7 false (1)
])
theorem kid05_part420_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part420) = true := by rfl

def kid05_part421 : Audit := .cycle 12 4 false (0)
theorem kid05_part421_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part421) = true := by rfl

def kid05_part422 : Audit := .cycle 0 12 true (0)
theorem kid05_part422_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part422) = true := by rfl

def kid05_part423 : Audit := .cycle 1 11 true (1)
theorem kid05_part423_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part423) = true := by rfl

def kid05_part424 : Audit := .cycle 2 10 true (1)
theorem kid05_part424_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part424) = true := by rfl

def kid05_part425 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 8 8 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.last 33 (2,true),
.cycle 34 1 false (6),
.cycle 15 1 true (3),
.cycle 8 8 true (1),
.cycle 9 7 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 4 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.cycle 6 11 true (1)
])
theorem kid05_part425_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part425) = true := by rfl

def kid05_part426 : Audit := .split 12 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 13 6 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 6 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 13 6 false (1),
.last 13 (2,true),
.cycle 29 1 false (1),
.cycle 14 6 false (1),
.cycle 11 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.cycle 16 11 false (2)
])
theorem kid05_part426_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part426) = true := by rfl

def kid05_part427 : Audit := .cycle 15 7 false (1)
theorem kid05_part427_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part427) = true := by rfl

def kid05_part403 : Audit := .split 11 (5,true) (byMove [(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413),(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420),(kid05_part421),(kid05_part422),(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427)])

theorem kid05_part403_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part403) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part404),(kid05_part405),(kid05_part406),(kid05_part407),(kid05_part408),(kid05_part409),(kid05_part410),(kid05_part411),(kid05_part412),(kid05_part413),(kid05_part414),(kid05_part415),(kid05_part416),(kid05_part417),(kid05_part418),(kid05_part419),(kid05_part420),(kid05_part421),(kid05_part422),(kid05_part423),(kid05_part424),(kid05_part425),(kid05_part426),(kid05_part427)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part404_checked

  · exact kid05_part410_checked

  · exact kid05_part416_checked

  · exact kid05_part422_checked

  · exact kid05_part405_checked

  · exact kid05_part411_checked

  · exact kid05_part417_checked

  · exact kid05_part423_checked

  · exact kid05_part406_checked

  · exact kid05_part412_checked

  · exact kid05_part418_checked

  · exact kid05_part424_checked

  · exact kid05_part407_checked

  · exact kid05_part413_checked

  · exact kid05_part419_checked

  · exact kid05_part425_checked

  · exact kid05_part408_checked

  · exact kid05_part414_checked

  · exact kid05_part420_checked

  · exact kid05_part426_checked

  · exact kid05_part409_checked

  · exact kid05_part415_checked

  · exact kid05_part421_checked

  · exact kid05_part427_checked

def kid05_part428 : Audit := .cycle 0 11 true (0)
theorem kid05_part428_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part428) = true := by rfl

def kid05_part429 : Audit := .cycle 1 10 true (1)
theorem kid05_part429_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part429) = true := by rfl

def kid05_part430 : Audit := .cycle 0 23 true (0)
theorem kid05_part430_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part430) = true := by rfl

def kid05_part431 : Audit := .cycle 3 8 true (1)
theorem kid05_part431_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part431) = true := by rfl

def kid05_part432 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 29 1 false (1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 0 15 true (0),
.cycle 21 6 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 6 false (2),
.cycle 15 6 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 21 6 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 6 false (2),
.cycle 18 1 false (2),
.cycle 15 6 false (1),
.cycle 17 6 false (1)
]),
.cycle 15 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.split 24 (2,true) (byMove [
.cycle 11 18 true (1),
.cycle 0 28 true (0),
.cycle 14 12 true (1),
.cycle 0 36 true (0),
.cycle 0 28 true (0),
.cycle 8 22 true (1),
.cycle 18 25 true (1),
.cycle 19 25 true (1),
.far true 1 ⟨0,[0, 0],[9, 9, 9, 8, 9, 1, 64],[9, 9, 9, 9, 32, 64, 64],64⟩,
.cycle 0 26 true (0),
.cycle 7 18 true (1),
.last 25 (5,true),
.cycle 6 23 true (1),
.cycle 7 30 true (1),
.cycle 17 29 true (1),
.cycle 15 10 true (1),
.cycle 23 2 true (3),
.cycle 31 27 false (3),
.cycle 11 15 true (1),
.cycle 10 15 true (1),
.cycle 2 24 true (1),
.cycle 0 26 true (0),
.last 26 (5,true),
.last 25 (5,true)
]),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 8 4 true (1),
.cycle 9 3 true (1),
.split 13 (2,true) (byMove [
.cycle 11 4 true (2),
.cycle 10 4 true (2),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far true 1 ⟨0,[0, 0],[1, 1, 9, 8, 2, 1, 64],[1, 1, 9, 1, 32, 64, 64],64⟩,
.cycle 3 11 true (1),
.cycle 11 3 true (2),
.cycle 8 6 true (1),
.cycle 17 11 false (2),
.cycle 18 11 false (2),
.cycle 14 12 true (-1),
.cycle 11 5 true (2),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 11 6 true (2),
.cycle 19 15 false (3),
.cycle 17 15 false (3)
]),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 14 (5,true) (byMove [
.cycle 43 6 false (-1),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 20 6 false (2),
.last 16 (2,true),
.cycle 18 1 false (4),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 21 6 false (1),
.cycle 15 6 false (1),
.last 16 (2,true),
.cycle 22 6 false (2),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 21 6 false (-1),
.cycle 23 6 false (1),
.last 16 (2,true),
.cycle 20 6 false (2),
.cycle 18 6 false (2),
.cycle 15 6 false (1),
.cycle 17 6 false (1)
]),
.cycle 15 7 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 11 4 true (3),
.cycle 11 1 true (3),
.cycle 6 7 true (1)
])
theorem kid05_part432_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part432) = true := by rfl

def kid05_part433 : Audit := .cycle 8 3 true (1)
theorem kid05_part433_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part433) = true := by rfl

def kid05_part434 : Audit := .cycle 14 5 false (1)
theorem kid05_part434_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part434) = true := by rfl

def kid05_part436 : Audit := .split 16 (4,false) (byMove [
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 1, 1, 64],[3, 2, 1, 3, 32, 64, 64],64⟩,
.cycle 0 40 true (-1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 11 8 false (1),
.cycle 0 29 true (-1),
.cycle 17 20 true (0),
.cycle 0 88 true (-1),
.cycle 20 1 false (4),
.cycle 11 9 false (1),
.last 17 (5,true),
.cycle 11 7 false (1),
.cycle 13 4 true (-1),
.cycle 0 35 true (-1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 11 8 false (1),
.far true 1 ⟨0,[0, 0],[3, 3, 11, 8, 3, 1, 64],[3, 2, 1, 3, 32, 64, 64],64⟩,
.cycle 11 6 true (-1),
.cycle 17 17 true (0),
.cycle 17 4 true (1),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part436_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part436) = true := by rfl

def kid05_part437 : Audit := .cycle 12 3 false (0)
theorem kid05_part437_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part437) = true := by rfl

def kid05_part438 : Audit := .cycle 17 1 false (-1)
theorem kid05_part438_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part438) = true := by rfl

def kid05_part439 : Audit := .cycle 11 6 true (-1)
theorem kid05_part439_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part439) = true := by rfl

def kid05_part440 : Audit := .cycle 11 7 false (1)
theorem kid05_part440_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part440) = true := by rfl

def kid05_part441 : Audit := .split 15 (5,true) (byMove [
.last 21 (4,false),
.cycle 11 14 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 11 7 false (1),
.cycle 11 6 true (-1),
.cycle 16 17 true (0),
.last 19 (4,false),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 11 7 false (1),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 8 true (-2),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 11 7 false (1),
.cycle 9 7 false (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 32768, 128, 256, 8, 32768, 262144, 256, 262144],[16, 256, 32768, 1, 32768, 128, 65536, 256, 256, 4096, 256, 128, 16, 256, 32768, 1, 32768, 128, 262144],345628⟩,
.last 19 (4,false),
.cycle 11 11 false (1),
.last 16 (4,false),
.cycle 11 10 false (1)
])
theorem kid05_part441_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part441) = true := by rfl

def kid05_part442 : Audit := .cycle 6 9 false (3)
theorem kid05_part442_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part442) = true := by rfl

def kid05_part443 : Audit := .cycle 15 16 true (0)
theorem kid05_part443_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part443) = true := by rfl

def kid05_part444 : Audit := .split 62 (4,false) (byMove [
.cycle 0 63 true (-2),
.cycle 34 33 true (0),
.cycle 0 93 true (-2),
.cycle 18 45 true (-2),
.cycle 71 32 false (1),
.cycle 37 26 true (0),
.cycle 0 63 true (-2),
.cycle 34 33 true (0),
.cycle 23 60 true (-2),
.cycle 49 32 true (-1),
.cycle 62 1 true (6),
.cycle 37 26 true (0),
.cycle 38 25 true (0),
.cycle 0 81 true (-2),
.cycle 0 65 true (-2),
.cycle 0 91 true (-2),
.cycle 23 113 true (-5),
.cycle 11 54 true (-2),
.cycle 0 112 true (-2),
.cycle 1 62 true (-2),
.cycle 34 32 true (0),
.cycle 60 4 true (4),
.cycle 62 1 true (6),
.cycle 35 29 true (0)
])
theorem kid05_part444_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part444) = true := by rfl

def kid05_part445 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (-1),
.cycle 0 32 true (-1),
.cycle 11 23 true (-2),
.cycle 0 37 true (-2),
.cycle 21 32 false (2),
.cycle 0 25 true (-1),
.cycle 0 18 true (-1),
.cycle 0 32 true (-1),
.cycle 0 56 true (-2),
.cycle 0 48 true (-2),
.cycle 17 1 true (3),
.cycle 0 25 true (-1),
.cycle 0 24 true (-1),
.cycle 0 32 true (-1),
.cycle 0 20 true (-1),
.cycle 11 21 true (-2),
.proven (BB6.Agent11Raw39B0REPumps.M143.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M143.never m hm),
.cycle 11 9 true (-1),
.cycle 0 44 true (-1),
.cycle 1 17 true (-1),
.cycle 0 31 true (-1),
.cycle 15 4 true (1),
.cycle 17 1 true (3),
.cycle 0 28 true (-1)
])
theorem kid05_part445_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part445) = true := by rfl

def kid05_part446 : Audit := .cycle 11 10 false (1)
theorem kid05_part446_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part446) = true := by rfl

def kid05_part447 : Audit := .split 15 (5,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 164113, 262144, 131328, 128, 256, 32768, 16, 262144, 164096, 128, 256, 8, 164096, 262144, 131328, 262144],[16, 131072, 32, 1, 164096, 256, 65536, 131328, 131072, 4096, 294912, 262144, 16, 131072, 32, 1, 164096, 256, 262144],345628⟩,
.cycle 0 19 true (-1),
.cycle 11 13 false (1),
.last 19 (4,false),
.last 16 (4,false),
.cycle 11 10 false (1),
.last 17 (4,false),
.cycle 8 11 true (-1),
.last 42 (4,false),
.cycle 0 17 true (-1),
.cycle 7 9 false (3),
.cycle 16 7 true (1),
.cycle 9 7 false (2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 32, 128, 256, 8, 16, 4096, 32, 4096],[16, 32, 32, 1, 32, 32, 16, 32, 32, 1, 32, 32, 4096],5648⟩,
.last 19 (4,false),
.cycle 11 11 false (1),
.last 16 (4,false),
.cycle 11 10 false (1),
.last 17 (4,false),
.cycle 1 20 true (-1),
.cycle 8 9 true (-1),
.cycle 0 17 true (-1),
.last 18 (4,false),
.cycle 6 15 false (3)
])
theorem kid05_part447_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part447) = true := by rfl

def kid05_part448 : Audit := .cycle 11 8 false (1)
theorem kid05_part448_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part448) = true := by rfl

def kid05_part449 : Audit := .cycle 12 3 false (0)
theorem kid05_part449_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part449) = true := by rfl

def kid05_part450 : Audit := .cycle 11 11 false (1)
theorem kid05_part450_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part450) = true := by rfl

def kid05_part451 : Audit := .cycle 11 9 false (1)
theorem kid05_part451_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part451) = true := by rfl

def kid05_part452 : Audit := .cycle 11 7 false (1)
theorem kid05_part452_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part452) = true := by rfl

def kid05_part453 : Audit := .split 15 (5,true) (byMove [
.last 21 (4,false),
.last 62 (4,false),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 11 7 false (1),
.cycle 11 9 false (1),
.cycle 12 4 true (-1),
.cycle 11 8 false (1),
.last 28 (4,false),
.cycle 11 8 false (1),
.cycle 16 9 true (0),
.cycle 11 6 false (1),
.cycle 13 3 false (0),
.cycle 11 11 false (1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 11 7 false (1),
.cycle 11 12 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (-1),
.cycle 5 11 false (3),
.last 18 (4,false),
.cycle 22 18 false (2)
])
theorem kid05_part453_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part453) = true := by rfl

def kid05_part454 : Audit := .split 30 (4,false) (byMove [
.cycle 10 33 false (2),
.cycle 10 31 false (2),
.cycle 2 29 false (3),
.cycle 21 17 false (0),
.last 33 (5,true),
.cycle 17 14 false (1),
.cycle 331 71 false (-3),
.cycle 21 15 true (-3),
.cycle 3 31 false (3),
.cycle 3 29 false (3),
.cycle 30 1 true (0),
.cycle 23 8 true (-3),
.cycle 10 23 false (2),
.cycle 15 73 false (4),
.cycle 349 75 false (-3),
.cycle 4 27 false (3),
.last 33 (5,true),
.cycle 17 14 false (1),
.cycle 15 38 false (4),
.cycle 15 36 false (3),
.cycle 21 14 true (-3),
.cycle 29 4 true (-1),
.cycle 30 1 true (0),
.cycle 10 27 false (2)
])
theorem kid05_part454_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part454) = true := by rfl

def kid05_part455 : Audit := .cycle 10 5 false (2)
theorem kid05_part455_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part455) = true := by rfl

def kid05_part456 : Audit := .far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 32768, 128, 256, 8, 32768, 262144, 256, 262144],[16, 256, 256, 1, 32768, 262144, 65536, 256, 256, 4096, 262144, 262144, 16, 256, 256, 1, 32768, 262144, 262144],345628⟩
theorem kid05_part456_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part456) = true := by rfl

def kid05_part457 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 true (-1),
.cycle 0 32 true (-1),
.cycle 3 17 false (3),
.cycle 3 15 false (3),
.last 21 (5,true),
.cycle 18 11 false (2),
.cycle 0 18 true (-1),
.cycle 0 32 true (-1),
.cycle 93 11 false (1),
.cycle 110 11 false (0),
.cycle 17 1 true (3),
.cycle 0 25 true (-1),
.cycle 0 24 true (-1),
.cycle 15 6 true (1),
.cycle 0 20 true (-1),
.cycle 3 15 false (3),
.last 21 (5,true),
.cycle 18 11 false (2),
.cycle 52 11 false (2),
.cycle 1 17 true (-1),
.cycle 0 31 true (-1),
.cycle 15 4 true (1),
.cycle 17 1 true (3),
.cycle 0 28 true (-1)
])
theorem kid05_part457_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part457) = true := by rfl

def kid05_part458 : Audit := .split 16 (5,true) (byMove [
.last 18 (4,false),
.last 20 (4,false),
.last 18 (4,false),
.last 21 (4,false),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.cycle 0 24 true (-1),
.last 19 (4,false),
.cycle 0 19 true (-1),
.cycle 11 13 false (1),
.last 17 (4,false),
.cycle 8 9 false (2),
.cycle 11 10 false (1),
.cycle 12 5 false (1),
.last 25 (4,false),
.last 19 (4,false),
.cycle 11 9 false (1),
.cycle 11 9 false (1),
.cycle 10 9 false (2),
.last 19 (4,false),
.cycle 0 19 true (-1),
.cycle 4 13 false (3),
.last 17 (4,false),
.cycle 11 14 false (1)
])
theorem kid05_part458_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part458) = true := by rfl

def kid05_part459 : Audit := .split 15 (5,true) (byMove [
.last 17 (4,false),
.cycle 11 5 false (1),
.cycle 11 14 false (1),
.cycle 0 24 true (-1),
.last 18 (4,false),
.cycle 11 9 false (1),
.last 17 (4,false),
.cycle 29 14 true (-3),
.cycle 0 47 true (-2),
.cycle 0 17 true (-1),
.last 30 (4,false),
.cycle 36 18 true (2),
.cycle 11 12 false (1),
.cycle 11 5 false (1),
.cycle 14 2 true (0),
.cycle 5 11 false (3),
.last 18 (4,false),
.cycle 11 9 false (1),
.last 17 (4,false),
.cycle 10 7 false (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 262144, 2304, 128, 256, 32768, 16, 262144, 32768, 128, 256, 8, 32768, 262144, 2304, 262144],[16, 2048, 2048, 1, 32768, 256, 65536, 2304, 2048, 4096, 32768, 256, 16, 2048, 2048, 1, 32768, 256, 262144],345628⟩,
.cycle 0 17 true (-1),
.last 18 (4,false),
.cycle 20 16 false (2)
])
theorem kid05_part459_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part459) = true := by rfl

def kid05_part435 : Audit := .split 14 (2,true) (byMove [(kid05_part436),(kid05_part437),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444),(kid05_part445),(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part451),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part458),(kid05_part459)])

theorem kid05_part435_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part435) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part436),(kid05_part437),(kid05_part438),(kid05_part439),(kid05_part440),(kid05_part441),(kid05_part442),(kid05_part443),(kid05_part444),(kid05_part445),(kid05_part446),(kid05_part447),(kid05_part448),(kid05_part449),(kid05_part450),(kid05_part451),(kid05_part452),(kid05_part453),(kid05_part454),(kid05_part455),(kid05_part456),(kid05_part457),(kid05_part458),(kid05_part459)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part436_checked

  · exact kid05_part442_checked

  · exact kid05_part448_checked

  · exact kid05_part454_checked

  · exact kid05_part437_checked

  · exact kid05_part443_checked

  · exact kid05_part449_checked

  · exact kid05_part455_checked

  · exact kid05_part438_checked

  · exact kid05_part444_checked

  · exact kid05_part450_checked

  · exact kid05_part456_checked

  · exact kid05_part439_checked

  · exact kid05_part445_checked

  · exact kid05_part451_checked

  · exact kid05_part457_checked

  · exact kid05_part440_checked

  · exact kid05_part446_checked

  · exact kid05_part452_checked

  · exact kid05_part458_checked

  · exact kid05_part441_checked

  · exact kid05_part447_checked

  · exact kid05_part453_checked

  · exact kid05_part459_checked

def kid05_part461 : Audit := .split 13 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 12 false (0),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.cycle 23 1 true (1),
.last 14 (5,true),
.cycle 9 13 false (2),
.cycle 11 4 true (0),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 12 false (0),
.cycle 0 16 true (0),
.cycle 1 20 true (0),
.cycle 14 15 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part461_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part461) = true := by rfl

def kid05_part462 : Audit := .cycle 0 21 true (-1)
theorem kid05_part462_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part462) = true := by rfl

def kid05_part463 : Audit := .cycle 14 1 false (0)
theorem kid05_part463_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part463) = true := by rfl

def kid05_part464 : Audit := .cycle 16 1 false (0)
theorem kid05_part464_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part464) = true := by rfl

def kid05_part465 : Audit := .split 17 (4,false) (byMove [
.last 26 (5,true),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 14 4 true (-3),
.cycle 11 8 false (1),
.last 24 (5,true),
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 9 9 false (2),
.last 21 (5,true),
.last 24 (5,true),
.cycle 12 9 false (0),
.last 20 (5,true),
.cycle 12 8 false (0)
])
theorem kid05_part465_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part465) = true := by rfl

def kid05_part466 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 13 4 false (2),
.cycle 23 4 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 4 false (1),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.cycle 15 4 false (2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 9 4 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 4 false (1),
.last 13 (4,false),
.cycle 16 4 false (0)
])
theorem kid05_part466_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part466) = true := by rfl

def kid05_part467 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 39 1 false (7),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 6 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 6 9 true (1)
])
theorem kid05_part467_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part467) = true := by rfl

def kid05_part468 : Audit := .cycle 0 15 true (0)
theorem kid05_part468_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part468) = true := by rfl

def kid05_part469 : Audit := .split 29 (4,false) (byMove [
.cycle 0 30 true (0),
.cycle 43 1 false (7),
.cycle 31 1 false (5),
.cycle 30 1 false (4),
.cycle 29 1 false (5),
.cycle 36 1 false (6),
.cycle 0 30 true (0),
.cycle 43 1 false (9),
.cycle 31 1 false (7),
.cycle 30 1 false (6),
.cycle 29 1 true (5),
.cycle 36 1 false (8),
.cycle 35 1 false (7),
.cycle 0 46 true (0),
.cycle 0 32 true (0),
.cycle 30 1 false (4),
.cycle 29 1 false (5),
.cycle 37 1 false (7),
.cycle 0 30 true (0),
.cycle 1 29 true (0),
.cycle 42 1 false (8),
.cycle 27 4 true (3),
.cycle 29 1 true (5),
.cycle 39 1 false (7)
])
theorem kid05_part469_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part469) = true := by rfl

def kid05_part470 : Audit := .cycle 0 13 true (0)
theorem kid05_part470_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part470) = true := by rfl

def kid05_part471 : Audit := .cycle 15 5 false (1)
theorem kid05_part471_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part471) = true := by rfl

def kid05_part472 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,false),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 9 4 true (1),
.cycle 8 7 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 6 8 true (1)
])
theorem kid05_part472_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part472) = true := by rfl

def kid05_part473 : Audit := .cycle 15 3 false (0)
theorem kid05_part473_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part473) = true := by rfl

def kid05_part474 : Audit := .cycle 11 11 false (2)
theorem kid05_part474_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part474) = true := by rfl

def kid05_part475 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (-1),
.cycle 14 15 true (-1),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 24 1 false (2),
.cycle 17 8 true (-1),
.cycle 0 25 true (-1),
.cycle 14 15 true (-1),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 24 1 true (2),
.cycle 17 8 true (-1),
.cycle 18 7 true (-1),
.cycle 20 7 true (-1),
.cycle 0 27 true (-1),
.cycle 25 1 false (1),
.cycle 24 1 false (2),
.cycle 12 16 true (-1),
.cycle 23 28 true (1),
.cycle 1 24 true (-1),
.cycle 14 14 true (-1),
.cycle 22 4 true (0),
.cycle 24 1 true (2),
.cycle 15 11 true (-1)
])
theorem kid05_part475_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part475) = true := by rfl

def kid05_part476 : Audit := .cycle 19 1 false (-1)
theorem kid05_part476_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part476) = true := by rfl

def kid05_part477 : Audit := .split 17 (4,false) (byMove [
.last 22 (5,true),
.cycle 22 17 true (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.cycle 22 17 true (0),
.cycle 16 2 true (-3),
.cycle 24 1 false (4),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 14 4 false (-1),
.cycle 11 8 false (1),
.cycle 12 9 false (0),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 10 false (0),
.cycle 15 3 false (-1),
.cycle 11 7 false (1),
.cycle 21 4 true (1),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid05_part477_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part477) = true := by rfl

def kid05_part478 : Audit := .split 12 (5,true) (byMove [
.last 18 (4,false),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 15 4 false (1),
.last 17 (4,false),
.cycle 13 4 false (1),
.last 15 (4,false),
.cycle 14 4 false (0),
.cycle 15 4 false (3),
.cycle 13 4 false (0),
.cycle 11 3 false (1),
.cycle 17 4 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 18 4 false (0),
.cycle 13 4 false (1),
.cycle 11 2 true (0),
.last 15 (4,false),
.last 15 (4,false),
.cycle 24 4 false (0)
])
theorem kid05_part478_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part478) = true := by rfl

def kid05_part479 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 33 1 false (1),
.last 16 (5,true),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 17 true (1),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (5,true),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 6 9 true (1)
])
theorem kid05_part479_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part479) = true := by rfl

def kid05_part480 : Audit := .cycle 10 2 true (1)
theorem kid05_part480_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part480) = true := by rfl

def kid05_part481 : Audit := .cycle 2 11 true (1)
theorem kid05_part481_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part481) = true := by rfl

def kid05_part482 : Audit := .cycle 0 13 true (0)
theorem kid05_part482_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part482) = true := by rfl

def kid05_part483 : Audit := .split 13 (5,true) (byMove [
.last 15 (4,false),
.cycle 0 17 true (-1),
.last 15 (4,false),
.cycle 0 15 true (0),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 8 6 true (1),
.cycle 17 5 false (0),
.last 18 (4,false),
.cycle 0 19 true (-1),
.last 16 (4,false),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 17 9 false (1)
])
theorem kid05_part483_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part483) = true := by rfl

def kid05_part484 : Audit := .split 12 (5,true) (byMove [
.last 14 (4,false),
.cycle 0 19 true (-1),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.last 30 (4,false),
.cycle 11 2 true (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 11 false (2)
])
theorem kid05_part484_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part484) = true := by rfl

def kid05_part460 : Audit := .split 11 (2,true) (byMove [(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part481),(kid05_part482),(kid05_part483),(kid05_part484)])

theorem kid05_part460_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part460) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part461),(kid05_part462),(kid05_part463),(kid05_part464),(kid05_part465),(kid05_part466),(kid05_part467),(kid05_part468),(kid05_part469),(kid05_part470),(kid05_part471),(kid05_part472),(kid05_part473),(kid05_part474),(kid05_part475),(kid05_part476),(kid05_part477),(kid05_part478),(kid05_part479),(kid05_part480),(kid05_part481),(kid05_part482),(kid05_part483),(kid05_part484)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part464_checked

  · exact kid05_part470_checked

  · exact kid05_part476_checked

  · exact kid05_part482_checked

  · exact kid05_part465_checked

  · exact kid05_part471_checked

  · exact kid05_part477_checked

  · exact kid05_part483_checked

  · exact kid05_part466_checked

  · exact kid05_part472_checked

  · exact kid05_part478_checked

  · exact kid05_part484_checked

def kid05_part485 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.split 29 (2,true) (byMove [
.cycle 0 36 true (0),
.cycle 32 28 true (2),
.cycle 31 1 false (3),
.cycle 30 1 false (2),
.cycle 36 1 false (8),
.cycle 51 1 false (7),
.cycle 39 1 false (7),
.cycle 31 1 false (3),
.cycle 33 1 false (7),
.cycle 34 1 false (8),
.cycle 40 1 false (8),
.last 30 (5,true),
.cycle 48 1 false (8),
.cycle 33 1 false (1),
.cycle 41 1 false (7),
.cycle 30 1 false (2),
.cycle 28 2 true (2),
.cycle 69 1 false (7),
.cycle 42 1 false (6),
.cycle 41 1 false (7),
.cycle 2 30 true (0),
.cycle 11 19 true (0),
.last 31 (5,true),
.last 30 (5,true)
]),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 9 5 true (1),
.split 15 (2,true) (byMove [
.cycle 12 4 true (2),
.cycle 30 1 false (0),
.cycle 33 1 false (1),
.cycle 0 17 true (0),
.cycle 19 9 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.far true 1 ⟨0,[0, 0],[0, 0, 8, 8, 2, 1, 64],[1, 8, 8, 0, 32, 64, 64],64⟩,
.cycle 3 13 true (1),
.cycle 13 3 true (2),
.cycle 8 8 true (1),
.cycle 6 10 true (1),
.cycle 30 1 false (0),
.cycle 11 7 true (1),
.cycle 11 5 true (1),
.cycle 19 9 false (1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 11 6 true (1),
.cycle 5 13 true (1),
.cycle 6 14 true (1)
]),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 5 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 11 4 true (1),
.cycle 13 1 true (3),
.cycle 6 9 true (1)
])
theorem kid05_part485_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part485) = true := by rfl

def kid05_part487 : Audit := .cycle 0 17 true (-1)
theorem kid05_part487_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part487) = true := by rfl

def kid05_part488 : Audit := .cycle 19 4 false (1)
theorem kid05_part488_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part488) = true := by rfl

def kid05_part489 : Audit := .cycle 14 1 false (0)
theorem kid05_part489_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part489) = true := by rfl

def kid05_part490 : Audit := .cycle 13 1 false (-1)
theorem kid05_part490_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part490) = true := by rfl

def kid05_part491 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 4 false (2),
.cycle 14 4 false (0),
.cycle 14 4 false (-1),
.last 15 (2,true),
.last 18 (2,true),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 0 19 true (-1),
.cycle 20 1 true (-2),
.cycle 16 4 false (0)
])
theorem kid05_part491_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part491) = true := by rfl

def kid05_part492 : Audit := .cycle 13 4 false (-1)
theorem kid05_part492_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part492) = true := by rfl

def kid05_part493 : Audit := .cycle 13 4 false (2)
theorem kid05_part493_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part493) = true := by rfl

def kid05_part494 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.last 16 (4,false),
.cycle 17 1 false (1),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 22 4 false (4),
.cycle 0 15 true (0),
.cycle 28 4 false (2),
.cycle 21 4 false (3),
.cycle 19 4 false (3),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 16 4 false (2),
.last 16 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 15 4 false (1),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 20 4 false (2)
])
theorem kid05_part494_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part494) = true := by rfl

def kid05_part495 : Audit := .cycle 0 15 true (0)
theorem kid05_part495_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part495) = true := by rfl

def kid05_part496 : Audit := .cycle 13 1 false (1)
theorem kid05_part496_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part496) = true := by rfl

def kid05_part497 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 4 false (2),
.cycle 16 4 false (4),
.cycle 14 4 false (1),
.last 15 (2,true),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 16 true (0),
.cycle 14 4 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 1 true (2),
.cycle 6 11 true (0)
])
theorem kid05_part497_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part497) = true := by rfl

def kid05_part498 : Audit := .cycle 13 4 false (1)
theorem kid05_part498_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part498) = true := by rfl

def kid05_part499 : Audit := .cycle 13 4 false (0)
theorem kid05_part499_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part499) = true := by rfl

def kid05_part500 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.last 16 (4,false),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 20 4 false (0),
.cycle 0 43 true (-2),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.last 15 (4,false),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.last 16 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.last 20 (4,false),
.cycle 39 4 false (-1),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 15 (4,false),
.cycle 20 4 false (0)
])
theorem kid05_part500_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part500) = true := by rfl

def kid05_part501 : Audit := .cycle 15 4 false (2)
theorem kid05_part501_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part501) = true := by rfl

def kid05_part502 : Audit := .cycle 13 1 false (-1)
theorem kid05_part502_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part502) = true := by rfl

def kid05_part503 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 7 12 false (3),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 18 true (-1),
.cycle 13 2 true (-1),
.last 14 (2,true),
.cycle 15 4 false (2),
.cycle 14 4 false (0),
.cycle 12 2 true (-1),
.cycle 14 4 false (-1),
.last 15 (2,true),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 13 38 true (-2),
.cycle 14 4 false (0),
.last 14 (2,true),
.cycle 20 4 false (0),
.cycle 11 3 false (1),
.cycle 15 4 false (-1)
])
theorem kid05_part503_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part503) = true := by rfl

def kid05_part504 : Audit := .cycle 13 4 false (-1)
theorem kid05_part504_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part504) = true := by rfl

def kid05_part505 : Audit := .cycle 9 4 true (0)
theorem kid05_part505_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part505) = true := by rfl

def kid05_part506 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.cycle 15 4 false (1),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 31 4 false (1),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 19 4 false (1),
.cycle 15 4 false (1),
.cycle 20 4 false (2),
.last 17 (4,false),
.cycle 11 4 true (0),
.cycle 10 6 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 23 4 false (1)
])
theorem kid05_part506_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part506) = true := by rfl

def kid05_part507 : Audit := .cycle 0 15 true (0)
theorem kid05_part507_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part507) = true := by rfl

def kid05_part508 : Audit := .cycle 16 4 false (2)
theorem kid05_part508_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part508) = true := by rfl

def kid05_part509 : Audit := .split 13 (4,false) (byMove [
.last 18 (2,true),
.cycle 7 14 false (3),
.last 14 (2,true),
.cycle 15 4 false (2),
.cycle 14 4 false (0),
.cycle 12 2 true (0),
.cycle 0 16 true (0),
.cycle 13 2 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 4 false (1),
.cycle 8 8 true (0),
.cycle 15 4 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 16 4 false (2),
.cycle 14 4 false (0),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.cycle 10 4 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 1 true (2),
.cycle 27 4 false (1)
])
theorem kid05_part509_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part509) = true := by rfl

def kid05_part510 : Audit := .cycle 15 4 false (1)
theorem kid05_part510_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part510) = true := by rfl

def kid05_part486 : Audit := .split 12 (5,true) (byMove [(kid05_part487),(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510)])

theorem kid05_part486_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part486) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid05_part487),(kid05_part488),(kid05_part489),(kid05_part490),(kid05_part491),(kid05_part492),(kid05_part493),(kid05_part494),(kid05_part495),(kid05_part496),(kid05_part497),(kid05_part498),(kid05_part499),(kid05_part500),(kid05_part501),(kid05_part502),(kid05_part503),(kid05_part504),(kid05_part505),(kid05_part506),(kid05_part507),(kid05_part508),(kid05_part509),(kid05_part510)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part487_checked

  · exact kid05_part493_checked

  · exact kid05_part499_checked

  · exact kid05_part505_checked

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

def kid05_part512 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.last 20 (2,true),
.cycle 0 16 true (0),
.last 21 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 21 (2,true),
.cycle 0 15 true (0),
.last 19 (2,true),
.last 15 (2,true),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.last 20 (2,true),
.cycle 0 16 true (0),
.last 18 (2,true),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 26 (2,true)
])
theorem kid05_part512_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part512) = true := by rfl

def kid05_part513 : Audit := .split 21 (4,false) (byMove [
.last 24 (2,true),
.proven (BB6.Agent11Raw39B0REPumps.M149.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M149.never m hm),
.cycle 14 60 true (-4),
.cycle 96 75 true (-6),
.cycle 8 38 false (2),
.last 68 (2,true),
.cycle 0 24 true (-3),
.last 92 (2,true),
.last 22 (2,true),
.cycle 0 23 true (-3),
.proven (BB6.Agent11Raw39B0REPumps.M150.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M150.never m hm),
.last 666 (2,true),
.last 104 (2,true),
.last 23 (2,true),
.cycle 0 28 true (-3),
.cycle 14 58 true (-4),
.cycle 6 58 false (3),
.last 85 (2,true),
.last 80 (2,true),
.proven (BB6.Agent11Raw39B0REPumps.M151.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M151.never m hm),
.last 22 (2,true),
.proven (BB6.Agent11Raw39B0REPumps.M152.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M152.never m hm),
.proven (BB6.Agent11Raw39B0REPumps.M153.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M153.never m hm),
.last 76 (2,true)
])
theorem kid05_part513_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part513) = true := by rfl

def kid05_part514 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 18 1 false (-2),
.cycle 17 1 false (1),
.cycle 37 1 false (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 21 1 false (-3),
.cycle 19 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 18 1 false (-2),
.cycle 9 4 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 21 1 false (-1)
])
theorem kid05_part514_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part514) = true := by rfl

def kid05_part515 : Audit := .cycle 16 1 false (0)
theorem kid05_part515_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part515) = true := by rfl

def kid05_part516 : Audit := .split 17 (4,false) (byMove [
.last 24 (2,true),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 14 4 true (-3),
.last 19 (2,true),
.last 22 (2,true),
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.cycle 14 4 false (-1),
.last 19 (2,true),
.cycle 14 6 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 9 9 false (2),
.last 19 (2,true),
.last 22 (2,true),
.cycle 12 9 false (0),
.cycle 11 9 false (1),
.cycle 12 8 false (0)
])
theorem kid05_part516_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part516) = true := by rfl

def kid05_part517 : Audit := .cycle 12 4 false (0)
theorem kid05_part517_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part517) = true := by rfl

def kid05_part518 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 29 (2,true),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 9 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 6 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 6 9 true (1)
])
theorem kid05_part518_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part518) = true := by rfl

def kid05_part519 : Audit := .cycle 16 5 false (0)
theorem kid05_part519_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part519) = true := by rfl

def kid05_part520 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,false),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 9 4 true (1),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 6 8 true (1)
])
theorem kid05_part520_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part520) = true := by rfl

def kid05_part521 : Audit := .cycle 0 13 true (0)
theorem kid05_part521_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part521) = true := by rfl

def kid05_part522 : Audit := .cycle 15 5 false (1)
theorem kid05_part522_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part522) = true := by rfl

def kid05_part523 : Audit := .cycle 8 5 true (1)
theorem kid05_part523_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part523) = true := by rfl

def kid05_part524 : Audit := .cycle 15 3 false (0)
theorem kid05_part524_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part524) = true := by rfl

def kid05_part525 : Audit := .split 18 (2,true) (byMove [
.last 20 (4,false),
.cycle 12 7 false (0),
.cycle 21 1 false (-3),
.cycle 14 6 true (-3),
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.cycle 6 13 false (3),
.cycle 13 10 false (-1),
.last 55 (4,false),
.last 86 (4,false),
.cycle 13 10 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 32, 128, 256, 8, 16, 4096, 32, 4096],[16, 32, 32, 1, 32, 32, 16, 32, 32, 1, 32, 32, 4096],5648⟩,
.cycle 13 8 false (-1),
.cycle 12 7 false (0),
.cycle 13 11 false (-1),
.cycle 13 9 false (-1),
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.last 34 (4,false),
.cycle 10 9 false (2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 256, 128, 256, 32768, 4194320, 1073741824, 32768, 524288, 1048576, 2097152, 32768, 1073741824, 256, 33554432, 67108864, 134217728, 268697600, 1073741824, 33024, 33554432, 67108864, 134217728, 1594130688, 1073741824, 1594130688, 1073741824],[16, 256, 256, 1, 32768, 256, 65536, 256, 256, 4096, 32768, 256, 4194304, 262144, 1048576, 262144, 32768, 256, 268435456, 256, 67108864, 16777216, 32768, 335544320, 268435456, 1594130688, 67108864, 16777216, 1594130688, 1594130688, 1073741824],2138928656⟩,
.cycle 15 11 false (1),
.cycle 11 9 false (1),
.cycle 15 5 false (-1)
])
theorem kid05_part525_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part525) = true := by rfl

def kid05_part526 : Audit := .split 12 (2,true) (byMove [
.last 17 (4,false),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 20 (4,false),
.last 22 (4,false),
.last 29 (4,false),
.cycle 16 1 false (4),
.last 15 (4,false),
.last 21 (4,false),
.last 17 (4,false),
.last 27 (4,false),
.last 31 (4,false),
.last 24 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 28 (4,false),
.last 25 (4,false),
.last 26 (4,false),
.cycle 2 13 true (0),
.last 15 (4,false),
.last 23 (4,false),
.cycle 11 2 true (0)
])
theorem kid05_part526_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part526) = true := by rfl

def kid05_part527 : Audit := .cycle 19 1 false (-1)
theorem kid05_part527_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part527) = true := by rfl

def kid05_part528 : Audit := .split 17 (4,false) (byMove [
.last 20 (2,true),
.cycle 22 17 true (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.cycle 13 6 false (-1),
.last 18 (2,true),
.cycle 24 1 false (4),
.cycle 12 6 false (0),
.cycle 16 2 true (-3),
.cycle 14 4 false (-1),
.last 19 (2,true),
.cycle 12 9 false (0),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 10 false (0),
.cycle 15 3 false (-1),
.last 18 (2,true),
.cycle 21 4 true (1),
.cycle 16 3 false (-2),
.cycle 11 7 false (1)
])
theorem kid05_part528_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part528) = true := by rfl

def kid05_part529 : Audit := .cycle 12 4 false (0)
theorem kid05_part529_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part529) = true := by rfl

def kid05_part530 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 33 1 false (1),
.cycle 0 17 true (0),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 28 (2,true),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 9 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 27 8 false (1),
.cycle 17 9 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 6 9 true (1)
])
theorem kid05_part530_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part530) = true := by rfl

def kid05_part531 : Audit := .cycle 10 2 true (1)
theorem kid05_part531_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part531) = true := by rfl

def kid05_part532 : Audit := .split 12 (2,true) (byMove [
.last 14 (4,false),
.cycle 13 6 false (1),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 20 6 false (2),
.cycle 2 12 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 13 6 false (1),
.last 28 (4,false),
.last 15 (4,false),
.cycle 0 17 true (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 11 false (2)
])
theorem kid05_part532_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part532) = true := by rfl

def kid05_part533 : Audit := .cycle 0 13 true (0)
theorem kid05_part533_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part533) = true := by rfl

def kid05_part534 : Audit := .split 14 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 15 8 false (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 14 1 true (2),
.cycle 8 7 true (1),
.cycle 18 9 false (1),
.cycle 15 8 false (1),
.last 15 (2,true),
.cycle 33 1 false (1),
.cycle 15 8 false (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 14 4 true (2),
.cycle 14 1 true (2),
.cycle 18 13 false (2)
])
theorem kid05_part534_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part534) = true := by rfl

def kid05_part535 : Audit := .cycle 16 11 false (2)
theorem kid05_part535_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part535) = true := by rfl

def kid05_part511 : Audit := .split 11 (5,true) (byMove [(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534),(kid05_part535)])

theorem kid05_part511_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part511) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part512),(kid05_part513),(kid05_part514),(kid05_part515),(kid05_part516),(kid05_part517),(kid05_part518),(kid05_part519),(kid05_part520),(kid05_part521),(kid05_part522),(kid05_part523),(kid05_part524),(kid05_part525),(kid05_part526),(kid05_part527),(kid05_part528),(kid05_part529),(kid05_part530),(kid05_part531),(kid05_part532),(kid05_part533),(kid05_part534),(kid05_part535)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part517_checked

  · exact kid05_part523_checked

  · exact kid05_part529_checked

  · exact kid05_part535_checked

def kid05_part536 : Audit := .cycle 0 11 true (0)
theorem kid05_part536_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part536) = true := by rfl

def kid05_part537 : Audit := .cycle 1 10 true (1)
theorem kid05_part537_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part537) = true := by rfl

def kid05_part538 : Audit := .cycle 2 9 true (1)
theorem kid05_part538_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part538) = true := by rfl

def kid05_part539 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 21 true (1),
.cycle 3 12 true (1),
.split 18 (5,true) (byMove [
.cycle 0 19 false (4),
.cycle 25 10 false (2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 19 10 false (1),
.cycle 0 19 true (0),
.cycle 25 10 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 19 10 false (3),
.cycle 19 10 false (2),
.last 20 (2,true),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 47 10 false (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 10 false (3),
.cycle 22 1 false (2),
.cycle 19 10 false (1),
.cycle 21 10 false (2)
]),
.cycle 8 7 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 37 true (1),
.cycle 4 28 true (1),
.cycle 14 1 true (4),
.cycle 8 7 true (1),
.cycle 9 6 true (1),
.split 16 (2,true) (byMove [
.cycle 13 4 true (3),
.cycle 10 7 true (2),
.cycle 2 16 true (1),
.cycle 0 18 true (0),
.cycle 20 13 false (2),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 4 23 true (1),
.cycle 3 14 true (1),
.cycle 14 3 true (3),
.cycle 8 9 true (1),
.cycle 6 11 true (1),
.cycle 0 19 true (0),
.cycle 12 7 true (2),
.cycle 12 5 true (2),
.cycle 20 13 false (2),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 11 6 true (2),
.cycle 0 20 true (0),
.cycle 6 15 true (1)
]),
.cycle 0 17 true (0),
.cycle 4 19 true (1),
.split 18 (5,true) (byMove [
.cycle 113 1 false (-5),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 24, 64],[16, 8, 64, 1, 16, 24, 64],64⟩,
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 84 44 false (-2),
.cycle 12 9 true (0),
.last 20 (2,true),
.cycle 4 46 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 5 17 true (0),
.cycle 19 47 false (5),
.last 20 (2,true),
.cycle 12 11 true (-1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 16, 16, 528, 128, 256, 32768, 16, 528, 16, 2, 4, 8, 16, 4112, 512, 262144],[16, 512, 262144, 1, 16, 4112, 65536, 512, 262144, 4096, 18, 16, 16, 8, 262144, 1, 16, 16, 262144],262144⟩,
.cycle 12 9 true (0),
.last 20 (2,true),
.cycle 121 65 false (1),
.cycle 4 29 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 24, 64],[16, 8, 64, 1, 16, 16, 64],64⟩,
.cycle 21 51 false (5)
]),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 4 true (2),
.cycle 14 1 true (4),
.cycle 6 10 true (1)
])
theorem kid05_part539_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part539) = true := by rfl

def kid05_part541 : Audit := .cycle 0 14 true (0)
theorem kid05_part541_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part541) = true := by rfl

def kid05_part542 : Audit := .cycle 10 2 true (2)
theorem kid05_part542_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part542) = true := by rfl

def kid05_part543 : Audit := .split 12 (2,true) (byMove [
.cycle 29 1 false (1),
.cycle 13 15 false (2),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.last 15 (5,true),
.cycle 30 1 false (2),
.cycle 32 1 false (2),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 25 true (1),
.cycle 11 2 true (2),
.cycle 16 11 false (2)
])
theorem kid05_part543_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part543) = true := by rfl

def kid05_part544 : Audit := .cycle 0 13 true (0)
theorem kid05_part544_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part544) = true := by rfl

def kid05_part545 : Audit := .split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.cycle 16 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 21 1 false (-3),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 23 1 false (-1),
.cycle 8 6 true (1),
.cycle 17 5 false (1),
.last 18 (2,true),
.last 14 (2,true),
.cycle 16 1 false (2),
.cycle 21 1 false (-3),
.cycle 12 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 30 1 false (0),
.cycle 14 8 false (2),
.cycle 17 9 false (1)
])
theorem kid05_part545_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part545) = true := by rfl

def kid05_part546 : Audit := .split 12 (5,true) (byMove [
.cycle 18 7 false (1),
.cycle 13 15 false (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 16 6 false (-1),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 17 9 false (1),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 8 8 true (1),
.cycle 16 6 false (-1),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.cycle 11 2 true (2),
.cycle 16 11 false (2)
])
theorem kid05_part546_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part546) = true := by rfl

def kid05_part547 : Audit := .cycle 0 12 true (0)
theorem kid05_part547_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part547) = true := by rfl

def kid05_part548 : Audit := .cycle 1 11 true (1)
theorem kid05_part548_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part548) = true := by rfl

def kid05_part549 : Audit := .split 23 (2,true) (byMove [
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 0 64 true (0),
.cycle 11 13 true (2),
.cycle 27 25 false (3),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 32768, 16, 16384, 16396, 128, 256, 8, 16384, 4, 1024, 262144],[16, 1024, 4, 1, 16384, 262144, 65536, 1024, 16384, 4096, 262144, 262144, 16, 1024, 4, 1, 12, 262144, 262144],262144⟩,
.cycle 13 11 true (2),
.cycle 18 21 true (2),
.cycle 8 16 true (1),
.cycle 9 15 true (1),
.last 28 (5,true),
.cycle 0 26 true (0),
.cycle 4 20 true (1),
.cycle 22 2 true (4),
.cycle 27 25 false (3),
.cycle 0 24 true (0),
.cycle 1 23 true (1),
.cycle 2 22 true (1),
.cycle 5 38 true (1),
.cycle 11 13 true (2),
.cycle 6 19 true (1)
])
theorem kid05_part549_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part549) = true := by rfl

def kid05_part550 : Audit := .cycle 3 9 true (1)
theorem kid05_part550_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part550) = true := by rfl

def kid05_part551 : Audit := .cycle 11 1 true (3)
theorem kid05_part551_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part551) = true := by rfl

def kid05_part552 : Audit := .cycle 8 4 true (1)
theorem kid05_part552_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part552) = true := by rfl

def kid05_part553 : Audit := .cycle 15 9 false (2)
theorem kid05_part553_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part553) = true := by rfl

def kid05_part554 : Audit := .split 14 (5,true) (byMove [
.last 18 (2,true),
.cycle 15 19 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.last 19 (2,true),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.last 17 (2,true),
.cycle 8 7 true (1),
.cycle 18 9 false (1),
.last 22 (2,true),
.last 15 (2,true),
.last 19 (2,true),
.last 19 (2,true),
.cycle 15 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 20 (2,true),
.cycle 11 4 true (2),
.cycle 18 13 false (2)
])
theorem kid05_part554_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part554) = true := by rfl

def kid05_part555 : Audit := .split 12 (2,true) (byMove [
.cycle 0 21 true (0),
.cycle 0 39 true (-1),
.cycle 16 1 false (0),
.cycle 9 5 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 10 3 true (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 4, 1, 1024, 128, 256, 32768, 16, 4, 12, 128, 256, 8, 4, 1, 1024, 262144],[16, 1024, 4, 1, 4, 262144, 65536, 1024, 16384, 4096, 262144, 262144, 16, 1024, 4, 1, 12, 262144, 262144],262144⟩,
.cycle 0 14 true (0),
.cycle 16 9 false (2),
.last 13 (5,true),
.cycle 16 7 false (1),
.last 15 (5,true),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 10 3 true (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part555_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part555) = true := by rfl

def kid05_part556 : Audit := .cycle 5 19 true (1)
theorem kid05_part556_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part556) = true := by rfl

def kid05_part557 : Audit := .split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.cycle 16 13 false (0),
.last 14 (2,true),
.last 17 (2,true),
.cycle 21 1 false (-3),
.cycle 14 6 false (0),
.cycle 9 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (-1),
.cycle 8 11 true (1),
.cycle 17 5 false (1),
.last 18 (2,true),
.last 14 (2,true),
.cycle 16 1 false (2),
.cycle 21 1 false (-3),
.cycle 12 6 false (2),
.cycle 9 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 14 8 false (2),
.cycle 17 9 false (1)
])
theorem kid05_part557_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part557) = true := by rfl

def kid05_part558 : Audit := .split 12 (5,true) (byMove [
.cycle 22 7 false (0),
.cycle 0 48 true (-1),
.last 13 (2,true),
.cycle 9 5 true (1),
.cycle 20 6 false (-2),
.cycle 13 6 false (1),
.cycle 0 20 true (0),
.cycle 10 3 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 16 9 false (2),
.cycle 8 6 true (1),
.cycle 16 7 false (1),
.last 20 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 20 6 false (-2),
.cycle 13 6 false (1),
.cycle 18 13 false (2),
.cycle 10 3 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 11 4 true (2),
.cycle 17 15 false (3)
])
theorem kid05_part558_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part558) = true := by rfl

def kid05_part559 : Audit := .cycle 0 12 true (0)
theorem kid05_part559_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part559) = true := by rfl

def kid05_part560 : Audit := .cycle 1 11 true (1)
theorem kid05_part560_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part560) = true := by rfl

def kid05_part561 : Audit := .cycle 2 10 true (1)
theorem kid05_part561_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part561) = true := by rfl

def kid05_part562 : Audit := .cycle 11 4 true (3)
theorem kid05_part562_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part562) = true := by rfl

def kid05_part563 : Audit := .cycle 11 1 true (3)
theorem kid05_part563_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part563) = true := by rfl

def kid05_part564 : Audit := .cycle 15 13 false (3)
theorem kid05_part564_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part564) = true := by rfl

def kid05_part540 : Audit := .split 11 (4,false) (byMove [(kid05_part541),(kid05_part542),(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part546),(kid05_part547),(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564)])

theorem kid05_part540_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part540) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part541),(kid05_part542),(kid05_part543),(kid05_part544),(kid05_part545),(kid05_part546),(kid05_part547),(kid05_part548),(kid05_part549),(kid05_part550),(kid05_part551),(kid05_part552),(kid05_part553),(kid05_part554),(kid05_part555),(kid05_part556),(kid05_part557),(kid05_part558),(kid05_part559),(kid05_part560),(kid05_part561),(kid05_part562),(kid05_part563),(kid05_part564)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part541_checked

  · exact kid05_part547_checked

  · exact kid05_part553_checked

  · exact kid05_part559_checked

  · exact kid05_part542_checked

  · exact kid05_part548_checked

  · exact kid05_part554_checked

  · exact kid05_part560_checked

  · exact kid05_part543_checked

  · exact kid05_part549_checked

  · exact kid05_part555_checked

  · exact kid05_part561_checked

  · exact kid05_part544_checked

  · exact kid05_part550_checked

  · exact kid05_part556_checked

  · exact kid05_part562_checked

  · exact kid05_part545_checked

  · exact kid05_part551_checked

  · exact kid05_part557_checked

  · exact kid05_part563_checked

  · exact kid05_part546_checked

  · exact kid05_part552_checked

  · exact kid05_part558_checked

  · exact kid05_part564_checked

def kid05_part565 : Audit := .cycle 14 9 false (2)
theorem kid05_part565_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part565) = true := by rfl

def kid05_part373 : Audit := .split 10 (1,true) (byMove [(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part460),(kid05_part485),(kid05_part486),(kid05_part511),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part565)])

theorem kid05_part373_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (kid05_part373) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part374),(kid05_part375),(kid05_part376),(kid05_part401),(kid05_part402),(kid05_part403),(kid05_part428),(kid05_part429),(kid05_part430),(kid05_part431),(kid05_part432),(kid05_part433),(kid05_part434),(kid05_part435),(kid05_part460),(kid05_part485),(kid05_part486),(kid05_part511),(kid05_part536),(kid05_part537),(kid05_part538),(kid05_part539),(kid05_part540),(kid05_part565)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part374_checked

  · exact kid05_part428_checked

  · exact kid05_part434_checked

  · exact kid05_part536_checked

  · exact kid05_part375_checked

  · exact kid05_part429_checked

  · exact kid05_part435_checked

  · exact kid05_part537_checked

  · exact kid05_part376_checked

  · exact kid05_part430_checked

  · exact kid05_part460_checked

  · exact kid05_part538_checked

  · exact kid05_part401_checked

  · exact kid05_part431_checked

  · exact kid05_part485_checked

  · exact kid05_part539_checked

  · exact kid05_part402_checked

  · exact kid05_part432_checked

  · exact kid05_part486_checked

  · exact kid05_part540_checked

  · exact kid05_part403_checked

  · exact kid05_part433_checked

  · exact kid05_part511_checked

  · exact kid05_part565_checked

def kid05_part567 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (2),
.cycle 23 5 false (3),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 16 5 false (0),
.last 15 (5,true),
.cycle 19 5 false (-1),
.cycle 15 5 false (0),
.cycle 17 5 false (2),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 11 4 true (0),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.split 14 (1,true) (byMove [
.cycle 11 4 true (1),
.cycle 15 15 false (1),
.cycle 0 21 false (3),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 12 3 true (1),
.cycle 8 7 true (1),
.cycle 19 9 false (0),
.cycle 15 7 false (1),
.cycle 9 13 false (2),
.cycle 11 5 true (1),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 6 true (1),
.last 21 (5,true),
.last 17 (5,true)
]),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 20 17 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 17 5 false (1),
.cycle 24 5 false (4),
.cycle 9 8 true (0),
.cycle 16 5 false (3),
.cycle 16 5 false (0),
.last 15 (5,true),
.cycle 19 5 false (-1),
.cycle 15 5 false (0),
.cycle 19 5 false (1),
.cycle 15 1 false (-1),
.cycle 15 5 false (-1),
.cycle 15 5 false (-1),
.cycle 11 8 true (0),
.cycle 1 16 true (0),
.cycle 15 5 false (1),
.cycle 5 20 true (0),
.last 16 (5,true),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 11 4 true (1),
.cycle 12 1 true (2),
.split 14 (1,true) (byMove [
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.last 19 (5,true),
.cycle 23 3 false (0),
.cycle 15 7 false (1),
.cycle 11 4 true (1),
.cycle 1 15 true (1),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 7 8 true (1),
.last 15 (5,true),
.cycle 19 11 false (1),
.last 19 (5,true),
.cycle 11 6 true (1),
.cycle 26 1 false (0),
.last 16 (5,true),
.last 22 (5,true),
.cycle 11 4 true (1),
.cycle 1 15 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
])
])
theorem kid05_part567_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part567) = true := by rfl

def kid05_part569 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 0 25 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 18 false (3),
.cycle 0 14 true (0),
.cycle 0 25 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 0 18 true (0),
.cycle 11 4 true (0),
.cycle 0 17 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 22 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 24 true (0),
.cycle 12 4 true (0),
.cycle 13 1 true (1),
.cycle 9 8 true (0)
])
theorem kid05_part569_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part569) = true := by rfl

def kid05_part570 : Audit := .cycle 12 11 false (1)
theorem kid05_part570_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part570) = true := by rfl

def kid05_part571 : Audit := .cycle 25 1 false (-1)
theorem kid05_part571_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part571) = true := by rfl

def kid05_part572 : Audit := .cycle 0 13 true (0)
theorem kid05_part572_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part572) = true := by rfl

def kid05_part573 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 18 false (3),
.cycle 12 12 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 13 5 false (-1),
.cycle 11 8 false (1),
.cycle 14 4 false (-1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 31 (5,true),
.cycle 1 17 false (3),
.cycle 12 11 false (0),
.cycle 17 4 true (-3),
.cycle 17 1 true (-3),
.cycle 16 3 false (-2)
])
theorem kid05_part573_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part573) = true := by rfl

def kid05_part574 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 20 4 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 4 false (1),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 4 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 14 4 false (0)
])
theorem kid05_part574_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part574) = true := by rfl

def kid05_part575 : Audit := .cycle 0 12 true (0)
theorem kid05_part575_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part575) = true := by rfl

def kid05_part576 : Audit := .cycle 1 11 true (1)
theorem kid05_part576_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part576) = true := by rfl

def kid05_part577 : Audit := .cycle 24 1 false (2)
theorem kid05_part577_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part577) = true := by rfl

def kid05_part578 : Audit := .cycle 21 1 false (1)
theorem kid05_part578_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part578) = true := by rfl

def kid05_part579 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.cycle 11 3 true (1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.cycle 16 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.cycle 7 8 true (1)
])
theorem kid05_part579_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part579) = true := by rfl

def kid05_part580 : Audit := .cycle 8 4 true (1)
theorem kid05_part580_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part580) = true := by rfl

def kid05_part581 : Audit := .cycle 11 8 false (1)
theorem kid05_part581_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part581) = true := by rfl

def kid05_part582 : Audit := .cycle 12 3 false (0)
theorem kid05_part582_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part582) = true := by rfl

def kid05_part583 : Audit := .cycle 0 16 true (-1)
theorem kid05_part583_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part583) = true := by rfl

def kid05_part584 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 26 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 19 1 false (1),
.cycle 11 5 true (0),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 12 4 true (0),
.cycle 14 1 true (2),
.cycle 17 1 false (1)
])
theorem kid05_part584_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part584) = true := by rfl

def kid05_part585 : Audit := .split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 7 18 false (3),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 11 10 true (-3),
.cycle 16 2 true (-3),
.cycle 12 13 false (0),
.cycle 9 11 false (2),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 11 8 false (1),
.cycle 14 4 false (-1),
.cycle 11 14 true (-4),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 23 (5,true),
.cycle 11 7 false (1),
.cycle 15 3 false (-1),
.cycle 20 20 true (-4),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid05_part585_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part585) = true := by rfl

def kid05_part586 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.last 14 (4,false),
.cycle 13 4 false (1),
.cycle 21 4 false (1),
.cycle 0 14 true (0),
.cycle 14 4 false (0),
.cycle 14 4 false (2),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.last 16 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.last 14 (4,false),
.cycle 11 2 true (0),
.cycle 13 4 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 12 5 true (0)
])
theorem kid05_part586_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part586) = true := by rfl

def kid05_part587 : Audit := .cycle 0 12 true (0)
theorem kid05_part587_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part587) = true := by rfl

def kid05_part588 : Audit := .cycle 1 11 true (1)
theorem kid05_part588_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part588) = true := by rfl

def kid05_part589 : Audit := .cycle 2 10 true (1)
theorem kid05_part589_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part589) = true := by rfl

def kid05_part590 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 8 8 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 36 32 true (2),
.cycle 34 1 false (6),
.cycle 15 1 true (3),
.cycle 8 8 true (1),
.cycle 11 6 true (1),
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 4 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.cycle 0 19 true (0)
])
theorem kid05_part590_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part590) = true := by rfl

def kid05_part591 : Audit := .split 12 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 11 2 true (1),
.cycle 13 13 false (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.last 18 (5,true),
.last 15 (5,true),
.cycle 0 24 true (-1),
.cycle 29 1 false (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.last 16 (5,true)
])
theorem kid05_part591_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part591) = true := by rfl

def kid05_part592 : Audit := .split 14 (5,true) (byMove [
.last 16 (4,false),
.cycle 11 4 true (1),
.cycle 15 15 false (1),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 8 7 true (1),
.cycle 17 9 false (1),
.cycle 13 2 true (1),
.last 25 (4,false),
.last 17 (4,false),
.last 17 (4,false),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 18 (4,false),
.last 15 (4,false),
.cycle 12 3 true (1)
])
theorem kid05_part592_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part592) = true := by rfl

def kid05_part568 : Audit := .split 11 (1,true) (byMove [(kid05_part569),(kid05_part570),(kid05_part571),(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592)])

theorem kid05_part568_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part568) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part569),(kid05_part570),(kid05_part571),(kid05_part572),(kid05_part573),(kid05_part574),(kid05_part575),(kid05_part576),(kid05_part577),(kid05_part578),(kid05_part579),(kid05_part580),(kid05_part581),(kid05_part582),(kid05_part583),(kid05_part584),(kid05_part585),(kid05_part586),(kid05_part587),(kid05_part588),(kid05_part589),(kid05_part590),(kid05_part591),(kid05_part592)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part569_checked

  · exact kid05_part575_checked

  · exact kid05_part581_checked

  · exact kid05_part587_checked

  · exact kid05_part570_checked

  · exact kid05_part576_checked

  · exact kid05_part582_checked

  · exact kid05_part588_checked

  · exact kid05_part571_checked

  · exact kid05_part577_checked

  · exact kid05_part583_checked

  · exact kid05_part589_checked

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

def kid05_part593 : Audit := .cycle 14 1 false (0)
theorem kid05_part593_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part593) = true := by rfl

def kid05_part594 : Audit := .cycle 0 12 true (0)
theorem kid05_part594_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part594) = true := by rfl

def kid05_part596 : Audit := .cycle 0 13 false (3)
theorem kid05_part596_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part596) = true := by rfl

def kid05_part597 : Audit := .cycle 19 4 false (1)
theorem kid05_part597_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part597) = true := by rfl

def kid05_part598 : Audit := .cycle 14 1 false (0)
theorem kid05_part598_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part598) = true := by rfl

def kid05_part599 : Audit := .cycle 13 1 false (-1)
theorem kid05_part599_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part599) = true := by rfl

def kid05_part600 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 14 true (-1),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 true (-1),
.cycle 14 4 false (0),
.last 15 (1,true),
.cycle 14 4 false (-1),
.cycle 0 16 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 27 4 false (-1),
.cycle 1 13 false (3),
.cycle 19 4 false (1),
.cycle 13 4 true (-1),
.cycle 13 1 true (-1),
.last 15 (1,true)
])
theorem kid05_part600_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part600) = true := by rfl

def kid05_part601 : Audit := .cycle 13 4 false (-1)
theorem kid05_part601_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part601) = true := by rfl

def kid05_part602 : Audit := .cycle 0 13 true (0)
theorem kid05_part602_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part602) = true := by rfl

def kid05_part603 : Audit := .cycle 19 4 false (3)
theorem kid05_part603_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part603) = true := by rfl

def kid05_part604 : Audit := .cycle 14 1 false (2)
theorem kid05_part604_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part604) = true := by rfl

def kid05_part605 : Audit := .cycle 13 1 false (1)
theorem kid05_part605_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part605) = true := by rfl

def kid05_part606 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 20 4 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 20 4 false (4),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 14 4 false (2),
.last 15 (1,true),
.cycle 14 4 false (1),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 19 4 false (3),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.last 15 (1,true)
])
theorem kid05_part606_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part606) = true := by rfl

def kid05_part607 : Audit := .cycle 13 4 false (1)
theorem kid05_part607_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part607) = true := by rfl

def kid05_part608 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 22 4 false (0),
.last 16 (4,false),
.cycle 0 16 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 15 true (-1),
.cycle 35 4 false (3),
.cycle 21 4 false (1),
.cycle 19 4 false (1),
.last 15 (4,false),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.cycle 16 4 false (-1),
.last 16 (4,false),
.last 17 (4,false),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.last 33 (4,false),
.cycle 28 4 false (0),
.cycle 2 13 false (3),
.last 18 (4,false),
.last 15 (4,false),
.cycle 24 4 false (0)
])
theorem kid05_part608_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part608) = true := by rfl

def kid05_part609 : Audit := .cycle 13 4 false (0)
theorem kid05_part609_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part609) = true := by rfl

def kid05_part610 : Audit := .cycle 0 15 true (-1)
theorem kid05_part610_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part610) = true := by rfl

def kid05_part611 : Audit := .cycle 13 1 false (-1)
theorem kid05_part611_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part611) = true := by rfl

def kid05_part612 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.cycle 0 17 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 16 true (-1),
.last 14 (1,true),
.cycle 17 1 false (1),
.cycle 0 15 true (-1),
.cycle 14 4 false (0),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 14 4 false (-1),
.cycle 0 20 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.last 31 (1,true),
.last 14 (1,true),
.cycle 14 4 false (0),
.cycle 0 15 true (-1),
.cycle 11 3 false (1),
.cycle 15 4 false (-1)
])
theorem kid05_part612_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part612) = true := by rfl

def kid05_part613 : Audit := .cycle 13 4 false (-1)
theorem kid05_part613_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part613) = true := by rfl

def kid05_part614 : Audit := .cycle 0 13 true (0)
theorem kid05_part614_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part614) = true := by rfl

def kid05_part615 : Audit := .cycle 1 12 true (0)
theorem kid05_part615_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part615) = true := by rfl

def kid05_part616 : Audit := .cycle 18 4 false (2)
theorem kid05_part616_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part616) = true := by rfl

def kid05_part617 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 23 4 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 4 false (1),
.cycle 0 17 true (0),
.cycle 23 4 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 true (2),
.cycle 17 4 false (3),
.last 18 (1,true),
.cycle 17 4 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 4 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 22 4 false (4),
.cycle 13 4 true (0),
.cycle 16 1 true (2),
.last 18 (1,true)
])
theorem kid05_part617_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part617) = true := by rfl

def kid05_part618 : Audit := .split 13 (4,false) (byMove [
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 17 1 false (-1),
.cycle 0 15 true (0),
.cycle 14 4 false (0),
.cycle 12 2 true (0),
.cycle 0 14 true (0),
.last 26 (1,true),
.cycle 20 4 false (2),
.cycle 18 4 false (2),
.cycle 13 1 true (1),
.cycle 8 6 true (0),
.cycle 15 4 false (1),
.last 14 (1,true),
.last 19 (1,true),
.cycle 17 1 false (1),
.cycle 14 4 false (0),
.cycle 11 4 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 13 4 true (1),
.cycle 13 1 true (1),
.last 15 (1,true)
])
theorem kid05_part618_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part618) = true := by rfl

def kid05_part619 : Audit := .split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.last 16 (4,false),
.cycle 22 4 false (4),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 12 3 true (0),
.cycle 18 4 false (0),
.cycle 15 4 false (0),
.last 18 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.cycle 11 4 true (0),
.cycle 12 3 true (0)
])
theorem kid05_part619_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part619) = true := by rfl

def kid05_part595 : Audit := .split 12 (5,true) (byMove [(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part599),(kid05_part600),(kid05_part601),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619)])

theorem kid05_part595_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part595) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (5,true) (some mv)) (byMove [(kid05_part596),(kid05_part597),(kid05_part598),(kid05_part599),(kid05_part600),(kid05_part601),(kid05_part602),(kid05_part603),(kid05_part604),(kid05_part605),(kid05_part606),(kid05_part607),(kid05_part608),(kid05_part609),(kid05_part610),(kid05_part611),(kid05_part612),(kid05_part613),(kid05_part614),(kid05_part615),(kid05_part616),(kid05_part617),(kid05_part618),(kid05_part619)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part596_checked

  · exact kid05_part602_checked

  · exact kid05_part608_checked

  · exact kid05_part614_checked

  · exact kid05_part597_checked

  · exact kid05_part603_checked

  · exact kid05_part609_checked

  · exact kid05_part615_checked

  · exact kid05_part598_checked

  · exact kid05_part604_checked

  · exact kid05_part610_checked

  · exact kid05_part616_checked

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

def kid05_part621 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 0 25 false (3),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 18 false (3),
.cycle 0 14 true (0),
.cycle 0 25 true (0),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 true (1),
.cycle 0 18 true (0),
.last 15 (1,true),
.cycle 0 17 false (3),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 0 22 true (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 24 true (0),
.cycle 12 4 true (0),
.cycle 13 1 true (1),
.last 15 (1,true)
])
theorem kid05_part621_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part621) = true := by rfl

def kid05_part622 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 11 false (-1),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 11 false (1),
.cycle 15 11 false (0),
.cycle 13 11 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 11 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.last 16 (4,false),
.last 13 (4,false),
.cycle 11 4 true (0)
])
theorem kid05_part622_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part622) = true := by rfl

def kid05_part623 : Audit := .cycle 18 1 false (-2)
theorem kid05_part623_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part623) = true := by rfl

def kid05_part624 : Audit := .cycle 0 13 true (0)
theorem kid05_part624_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part624) = true := by rfl

def kid05_part625 : Audit := .split 17 (4,false) (byMove [
.cycle 0 18 false (3),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 0 18 false (3),
.cycle 12 12 true (-3),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.cycle 17 1 true (-3),
.cycle 13 5 false (-1),
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 0 20 false (3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 16 15 false (1),
.cycle 1 17 false (3),
.cycle 12 11 false (0),
.cycle 17 4 true (-3),
.cycle 17 1 true (-3),
.last 19 (1,true)
])
theorem kid05_part625_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part625) = true := by rfl

def kid05_part626 : Audit := .cycle 12 4 false (0)
theorem kid05_part626_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part626) = true := by rfl

def kid05_part627 : Audit := .cycle 0 12 true (0)
theorem kid05_part627_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part627) = true := by rfl

def kid05_part628 : Audit := .cycle 1 11 true (1)
theorem kid05_part628_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part628) = true := by rfl

def kid05_part629 : Audit := .cycle 24 1 false (2)
theorem kid05_part629_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part629) = true := by rfl

def kid05_part630 : Audit := .cycle 21 1 false (1)
theorem kid05_part630_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part630) = true := by rfl

def kid05_part631 : Audit := .split 12 (4,false) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 17 1 false (1),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 31 1 false (7),
.cycle 24 1 false (2),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.last 14 (1,true),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 19 1 false (-1),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.last 14 (1,true)
])
theorem kid05_part631_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part631) = true := by rfl

def kid05_part632 : Audit := .cycle 8 4 true (1)
theorem kid05_part632_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part632) = true := by rfl

def kid05_part633 : Audit := .split 19 (1,true) (byMove [
.last 21 (4,false),
.cycle 12 14 false (1),
.cycle 14 7 false (0),
.cycle 0 21 false (3),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.last 20 (4,false),
.cycle 8 12 false (2),
.cycle 12 8 false (1),
.cycle 15 6 false (0),
.cycle 14 7 false (0),
.last 22 (4,false),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.last 37 (4,false),
.cycle 19 16 true (-2),
.cycle 2 18 false (3),
.last 23 (4,false),
.last 20 (4,false),
.cycle 11 16 false (1)
])
theorem kid05_part633_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part633) = true := by rfl

def kid05_part634 : Audit := .split 12 (1,true) (byMove [
.cycle 9 5 false (2),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 14 3 false (-1),
.last 14 (4,false),
.cycle 22 3 false (3),
.cycle 15 3 false (0),
.cycle 0 14 true (0),
.cycle 15 3 false (0),
.cycle 13 3 false (1),
.cycle 18 3 false (-1),
.cycle 13 3 false (0),
.last 16 (4,false),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 14 3 false (-1),
.last 14 (4,false),
.cycle 1 13 true (0),
.cycle 13 3 false (1),
.cycle 0 14 true (0),
.cycle 14 3 false (0),
.cycle 11 2 true (0)
])
theorem kid05_part634_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part634) = true := by rfl

def kid05_part635 : Audit := .cycle 9 11 false (2)
theorem kid05_part635_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part635) = true := by rfl

def kid05_part636 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 26 1 false (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 26 1 false (2),
.cycle 16 1 false (4),
.cycle 15 1 false (3),
.cycle 14 1 true (2),
.cycle 19 1 false (1),
.last 16 (1,true),
.cycle 18 1 false (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (2),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 25 1 false (1),
.cycle 12 4 true (0),
.cycle 14 1 true (2),
.last 16 (1,true)
])
theorem kid05_part636_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part636) = true := by rfl

def kid05_part637 : Audit := .split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 7 18 false (3),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 21 (1,true),
.last 18 (1,true),
.cycle 13 6 false (-1),
.cycle 9 11 false (2),
.cycle 12 6 false (0),
.cycle 16 2 true (-3),
.last 19 (1,true),
.cycle 14 4 false (-1),
.last 25 (1,true),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 21 (1,true),
.last 18 (1,true),
.cycle 15 3 false (-1),
.last 25 (1,true),
.cycle 16 3 false (-2),
.cycle 11 7 false (1)
])
theorem kid05_part637_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part637) = true := by rfl

def kid05_part638 : Audit := .cycle 12 4 false (0)
theorem kid05_part638_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part638) = true := by rfl

def kid05_part639 : Audit := .cycle 0 12 true (0)
theorem kid05_part639_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part639) = true := by rfl

def kid05_part640 : Audit := .cycle 1 11 true (1)
theorem kid05_part640_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part640) = true := by rfl

def kid05_part641 : Audit := .cycle 2 10 true (1)
theorem kid05_part641_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part641) = true := by rfl

def kid05_part642 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 32 1 false (2),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 8 8 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 61 1 false (7),
.cycle 34 1 false (6),
.cycle 15 1 true (3),
.cycle 8 8 true (1),
.last 17 (1,true),
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 26 1 false (0),
.cycle 4 16 true (1),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 12 4 true (1),
.cycle 15 1 true (3),
.last 17 (1,true)
])
theorem kid05_part642_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part642) = true := by rfl

def kid05_part643 : Audit := .split 12 (4,false) (byMove [
.cycle 0 15 true (0),
.last 13 (1,true),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 14 6 false (1),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 12 1 true (2),
.cycle 8 5 true (1),
.last 16 (1,true),
.last 13 (1,true),
.cycle 13 6 false (1),
.cycle 29 1 false (1),
.cycle 14 6 false (1),
.cycle 11 4 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 12 4 true (2),
.cycle 12 1 true (2),
.last 14 (1,true)
])
theorem kid05_part643_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part643) = true := by rfl

def kid05_part644 : Audit := .split 13 (1,true) (byMove [
.last 15 (4,false),
.cycle 0 50 true (-2),
.cycle 22 1 false (-2),
.cycle 0 18 true (0),
.last 21 (4,false),
.cycle 14 6 false (1),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 15 7 false (1),
.cycle 0 15 true (0),
.cycle 15 7 false (1),
.cycle 11 3 true (1),
.cycle 13 10 false (1),
.cycle 14 5 false (0),
.last 24 (4,false),
.cycle 23 1 false (-1),
.last 21 (4,false),
.cycle 11 5 true (0),
.last 15 (4,false),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 11 4 true (1),
.cycle 11 3 true (1)
])
theorem kid05_part644_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part644) = true := by rfl

def kid05_part620 : Audit := .split 11 (5,true) (byMove [(kid05_part621),(kid05_part622),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644)])

theorem kid05_part620_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part620) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part621),(kid05_part622),(kid05_part623),(kid05_part624),(kid05_part625),(kid05_part626),(kid05_part627),(kid05_part628),(kid05_part629),(kid05_part630),(kid05_part631),(kid05_part632),(kid05_part633),(kid05_part634),(kid05_part635),(kid05_part636),(kid05_part637),(kid05_part638),(kid05_part639),(kid05_part640),(kid05_part641),(kid05_part642),(kid05_part643),(kid05_part644)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part621_checked

  · exact kid05_part627_checked

  · exact kid05_part633_checked

  · exact kid05_part639_checked

  · exact kid05_part622_checked

  · exact kid05_part628_checked

  · exact kid05_part634_checked

  · exact kid05_part640_checked

  · exact kid05_part623_checked

  · exact kid05_part629_checked

  · exact kid05_part635_checked

  · exact kid05_part641_checked

  · exact kid05_part624_checked

  · exact kid05_part630_checked

  · exact kid05_part636_checked

  · exact kid05_part642_checked

  · exact kid05_part625_checked

  · exact kid05_part631_checked

  · exact kid05_part637_checked

  · exact kid05_part643_checked

  · exact kid05_part626_checked

  · exact kid05_part632_checked

  · exact kid05_part638_checked

  · exact kid05_part644_checked

def kid05_part645 : Audit := .cycle 0 11 true (0)
theorem kid05_part645_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part645) = true := by rfl

def kid05_part646 : Audit := .cycle 1 10 true (1)
theorem kid05_part646_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part646) = true := by rfl

def kid05_part647 : Audit := .cycle 0 23 true (0)
theorem kid05_part647_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part647) = true := by rfl

def kid05_part648 : Audit := .cycle 3 8 true (1)
theorem kid05_part648_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part648) = true := by rfl

def kid05_part649 : Audit := .split 11 (4,false) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 29 1 false (1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.cycle 0 15 true (0),
.cycle 21 6 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 6 false (2),
.last 16 (1,true),
.cycle 15 6 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 20 (1,true),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 6 false (2),
.cycle 18 1 false (2),
.cycle 15 6 false (1),
.last 16 (1,true)
]),
.split 13 (1,true) (byMove [
.cycle 9 14 false (3),
.cycle 0 50 true (-2),
.cycle 23 1 false (-1),
.cycle 0 18 true (0),
.cycle 15 7 false (0),
.last 14 (5,true),
.cycle 8 8 true (1),
.cycle 1 14 true (1),
.cycle 8 8 true (1),
.cycle 0 15 true (0),
.cycle 15 7 false (1),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 5 false (1),
.cycle 16 10 true (-2),
.cycle 23 1 false (-1),
.cycle 15 7 false (0),
.last 14 (5,true),
.cycle 11 4 true (1),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 7 18 true (1),
.cycle 0 23 true (0),
.cycle 11 1 true (3),
.cycle 8 4 true (1),
.split 13 (1,true) (byMove [
.cycle 11 4 true (2),
.cycle 14 15 false (2),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 17 true (2),
.cycle 3 11 true (1),
.cycle 11 3 true (2),
.cycle 8 6 true (1),
.cycle 17 14 false (1),
.cycle 16 5 false (1),
.cycle 17 18 true (-2),
.cycle 11 5 true (2),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 11 6 true (2),
.last 20 (5,true),
.last 16 (5,true)
]),
.cycle 9 3 true (1),
.cycle 0 14 true (0),
.cycle 4 8 true (1),
.split 14 (5,true) (byMove [
.last 39 (1,true),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 6 false (0),
.last 16 (1,true),
.last 19 (1,true),
.cycle 18 1 false (4),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.last 20 (1,true),
.last 16 (1,true),
.cycle 15 6 false (1),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.last 20 (1,true),
.last 16 (1,true),
.last 19 (1,true),
.cycle 20 6 false (2),
.cycle 18 6 false (2),
.cycle 15 6 false (1),
.last 16 (1,true)
]),
.split 13 (1,true) (byMove [
.cycle 9 14 false (3),
.cycle 0 64 true (-2),
.cycle 23 1 false (-1),
.cycle 0 21 true (0),
.cycle 19 7 false (-1),
.last 14 (5,true),
.cycle 6 8 true (1),
.cycle 1 15 true (1),
.cycle 7 8 true (1),
.cycle 0 24 true (0),
.cycle 15 7 false (1),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 5 false (1),
.cycle 15 10 true (-2),
.cycle 23 1 false (-1),
.cycle 19 7 false (-1),
.last 14 (5,true),
.cycle 11 8 true (1),
.cycle 1 15 true (1),
.cycle 10 8 true (1),
.cycle 0 24 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 11 4 true (3),
.cycle 11 1 true (3),
.split 13 (1,true) (byMove [
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.last 24 (5,true),
.last 18 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.cycle 11 4 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.cycle 7 7 true (1),
.last 14 (5,true),
.last 26 (5,true),
.cycle 20 5 false (1),
.cycle 11 6 true (2),
.last 22 (5,true),
.last 15 (5,true),
.last 16 (5,true),
.cycle 11 4 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
])
theorem kid05_part649_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part649) = true := by rfl

def kid05_part650 : Audit := .cycle 8 3 true (1)
theorem kid05_part650_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part650) = true := by rfl

def kid05_part652 : Audit := .cycle 9 7 false (2)
theorem kid05_part652_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part652) = true := by rfl

def kid05_part653 : Audit := .cycle 0 18 true (-1)
theorem kid05_part653_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part653) = true := by rfl

def kid05_part654 : Audit := .cycle 16 1 false (0)
theorem kid05_part654_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part654) = true := by rfl

def kid05_part655 : Audit := .cycle 15 1 false (-1)
theorem kid05_part655_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part655) = true := by rfl

def kid05_part656 : Audit := .split 15 (4,false) (byMove [
.cycle 0 20 true (-2),
.cycle 21 5 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 5 false (-2),
.cycle 18 5 false (0),
.cycle 16 5 false (1),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 17 5 false (1),
.cycle 16 5 false (0),
.cycle 18 5 false (-2),
.cycle 16 5 false (-1),
.cycle 20 5 false (0),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 5 false (-2),
.last 19 (5,true),
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 18 5 false (1),
.last 18 (5,true),
.cycle 13 3 false (1)
])
theorem kid05_part656_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part656) = true := by rfl

def kid05_part657 : Audit := .cycle 15 5 false (-1)
theorem kid05_part657_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part657) = true := by rfl

def kid05_part658 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 22 5 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 5 false (1),
.cycle 0 17 true (0),
.cycle 22 5 false (5),
.cycle 18 1 false (4),
.cycle 17 1 false (3),
.cycle 16 1 true (2),
.cycle 17 5 false (3),
.cycle 0 19 true (0),
.cycle 17 5 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 16 1 false (2),
.cycle 17 5 false (1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 21 5 false (4),
.cycle 15 4 true (1),
.cycle 16 1 true (2),
.cycle 13 4 true (0)
])
theorem kid05_part658_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part658) = true := by rfl

def kid05_part659 : Audit := .cycle 21 5 false (4)
theorem kid05_part659_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part659) = true := by rfl

def kid05_part660 : Audit := .cycle 23 5 false (2)
theorem kid05_part660_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part660) = true := by rfl

def kid05_part661 : Audit := .cycle 0 16 true (0)
theorem kid05_part661_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part661) = true := by rfl

def kid05_part662 : Audit := .cycle 15 5 false (1)
theorem kid05_part662_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part662) = true := by rfl

def kid05_part663 : Audit := .split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 21 5 false (2),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 5 false (0),
.cycle 0 16 true (0),
.cycle 21 5 false (4),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.last 16 (4,false),
.cycle 16 5 false (2),
.cycle 8 10 true (0),
.cycle 16 5 false (1),
.cycle 0 18 true (0),
.cycle 16 1 false (0),
.last 16 (4,false),
.cycle 16 5 false (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 20 5 false (3),
.last 19 (4,false),
.last 16 (4,false),
.cycle 13 3 true (0)
])
theorem kid05_part663_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part663) = true := by rfl

def kid05_part664 : Audit := .cycle 17 5 false (0)
theorem kid05_part664_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part664) = true := by rfl

def kid05_part665 : Audit := .cycle 15 5 false (0)
theorem kid05_part665_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part665) = true := by rfl

def kid05_part666 : Audit := .split 18 (4,false) (byMove [
.cycle 0 19 true (-1),
.cycle 24 5 false (3),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 19 5 false (1),
.cycle 0 19 true (-1),
.cycle 24 5 false (5),
.cycle 20 1 false (4),
.cycle 19 1 false (3),
.cycle 18 1 true (2),
.cycle 19 5 false (3),
.cycle 19 3 false (2),
.cycle 19 5 false (2),
.cycle 0 21 true (-1),
.cycle 19 1 false (1),
.cycle 18 1 false (2),
.cycle 19 5 false (1),
.cycle 33 3 false (3),
.cycle 1 18 true (-1),
.cycle 23 5 false (4),
.cycle 16 4 true (0),
.cycle 18 1 true (2),
.cycle 13 6 true (-1)
])
theorem kid05_part666_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part666) = true := by rfl

def kid05_part667 : Audit := .cycle 15 1 false (-1)
theorem kid05_part667_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part667) = true := by rfl

def kid05_part668 : Audit := .split 15 (4,false) (byMove [
.cycle 9 8 false (2),
.cycle 6 30 false (3),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 5 false (-2),
.cycle 16 5 false (1),
.cycle 14 2 true (-1),
.cycle 19 5 false (-1),
.cycle 19 1 false (3),
.cycle 16 5 false (0),
.last 16 (5,true),
.cycle 18 5 false (-2),
.cycle 16 5 false (-1),
.cycle 18 5 false (1),
.cycle 16 1 false (-2),
.cycle 15 1 false (-1),
.cycle 16 5 false (-2),
.cycle 11 5 false (2),
.cycle 17 5 false (-1),
.cycle 16 5 false (0),
.cycle 16 4 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part668_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part668) = true := by rfl

def kid05_part669 : Audit := .cycle 15 5 false (-1)
theorem kid05_part669_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part669) = true := by rfl

def kid05_part670 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 21 5 false (2),
.cycle 21 1 false (1),
.cycle 18 5 false (0),
.cycle 13 4 true (0),
.cycle 0 17 true (0),
.cycle 6 26 true (0),
.cycle 23 5 false (2),
.cycle 21 5 false (2),
.cycle 16 1 true (2),
.cycle 6 14 true (0),
.cycle 0 19 true (0),
.cycle 9 8 true (0),
.cycle 0 19 true (0),
.cycle 19 5 false (2),
.cycle 18 5 false (0),
.cycle 11 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 6 20 true (0),
.cycle 15 4 true (1),
.cycle 16 1 true (2),
.cycle 13 4 true (0)
])
theorem kid05_part670_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part670) = true := by rfl

def kid05_part671 : Audit := .cycle 1 15 true (0)
theorem kid05_part671_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part671) = true := by rfl

def kid05_part672 : Audit := .cycle 15 5 false (1)
theorem kid05_part672_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part672) = true := by rfl

def kid05_part673 : Audit := .cycle 0 16 true (0)
theorem kid05_part673_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part673) = true := by rfl

def kid05_part674 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 22 5 false (1),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 5 false (-1),
.cycle 0 17 true (0),
.cycle 22 5 false (3),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.last 17 (4,false),
.cycle 17 5 false (1),
.last 19 (4,false),
.cycle 17 5 false (0),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.last 17 (4,false),
.cycle 17 5 false (-1),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 21 5 false (2),
.last 20 (4,false),
.last 17 (4,false),
.cycle 13 4 true (0)
])
theorem kid05_part674_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part674) = true := by rfl

def kid05_part675 : Audit := .split 15 (5,true) (byMove [
.last 17 (4,false),
.cycle 13 4 true (0),
.cycle 22 5 false (0),
.cycle 0 17 true (0),
.cycle 16 5 false (0),
.cycle 17 5 false (-1),
.cycle 0 16 true (0),
.cycle 6 20 true (0),
.cycle 21 5 false (2),
.cycle 19 5 false (2),
.last 16 (4,false),
.cycle 8 8 true (0),
.cycle 16 5 false (1),
.cycle 14 2 true (0),
.cycle 20 5 false (0),
.last 18 (4,false),
.cycle 16 5 false (0),
.cycle 17 5 false (-1),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.last 19 (4,false),
.last 16 (4,false),
.cycle 13 3 true (0)
])
theorem kid05_part675_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part675) = true := by rfl

def kid05_part651 : Audit := .split 14 (1,true) (byMove [(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661),(kid05_part662),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part666),(kid05_part667),(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675)])

theorem kid05_part651_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part651) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) 14 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part652),(kid05_part653),(kid05_part654),(kid05_part655),(kid05_part656),(kid05_part657),(kid05_part658),(kid05_part659),(kid05_part660),(kid05_part661),(kid05_part662),(kid05_part663),(kid05_part664),(kid05_part665),(kid05_part666),(kid05_part667),(kid05_part668),(kid05_part669),(kid05_part670),(kid05_part671),(kid05_part672),(kid05_part673),(kid05_part674),(kid05_part675)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part652_checked

  · exact kid05_part658_checked

  · exact kid05_part664_checked

  · exact kid05_part670_checked

  · exact kid05_part653_checked

  · exact kid05_part659_checked

  · exact kid05_part665_checked

  · exact kid05_part671_checked

  · exact kid05_part654_checked

  · exact kid05_part660_checked

  · exact kid05_part666_checked

  · exact kid05_part672_checked

  · exact kid05_part655_checked

  · exact kid05_part661_checked

  · exact kid05_part667_checked

  · exact kid05_part673_checked

  · exact kid05_part656_checked

  · exact kid05_part662_checked

  · exact kid05_part668_checked

  · exact kid05_part674_checked

  · exact kid05_part657_checked

  · exact kid05_part663_checked

  · exact kid05_part669_checked

  · exact kid05_part675_checked

def kid05_part677 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 9 10 false (2),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 9 10 true (0),
.cycle 0 15 true (0),
.cycle 9 11 false (2),
.last 14 (5,true),
.cycle 11 4 true (0),
.cycle 9 9 false (2),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 9 10 false (2),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 9 8 true (0),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part677_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part677) = true := by rfl

def kid05_part678 : Audit := .cycle 0 44 true (-2)
theorem kid05_part678_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part678) = true := by rfl

def kid05_part679 : Audit := .cycle 17 1 false (-1)
theorem kid05_part679_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part679) = true := by rfl

def kid05_part680 : Audit := .cycle 0 16 true (0)
theorem kid05_part680_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part680) = true := by rfl

def kid05_part681 : Audit := .split 17 (4,false) (byMove [
.last 32 (5,true),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 11 8 false (1),
.cycle 14 4 true (-3),
.cycle 9 12 true (-3),
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.cycle 11 8 false (1),
.cycle 14 4 false (-1),
.cycle 11 10 false (1),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 21 (5,true),
.cycle 9 9 false (2),
.cycle 7 17 false (3),
.cycle 12 9 false (0),
.last 20 (5,true),
.cycle 16 3 false (-2)
])
theorem kid05_part681_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part681) = true := by rfl

def kid05_part682 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 4 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 16 true (0),
.cycle 13 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 4 false (1),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 0 16 true (0),
.cycle 9 4 true (0),
.cycle 0 15 true (0),
.cycle 17 4 false (1),
.last 13 (4,false),
.cycle 14 4 false (0)
])
theorem kid05_part682_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part682) = true := by rfl

def kid05_part683 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 48 1 false (8),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 0 16 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 6 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid05_part683_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part683) = true := by rfl

def kid05_part684 : Audit := .cycle 1 12 true (1)
theorem kid05_part684_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part684) = true := by rfl

def kid05_part685 : Audit := .cycle 9 4 true (1)
theorem kid05_part685_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part685) = true := by rfl

def kid05_part686 : Audit := .cycle 0 13 true (0)
theorem kid05_part686_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part686) = true := by rfl

def kid05_part687 : Audit := .cycle 14 5 false (1)
theorem kid05_part687_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part687) = true := by rfl

def kid05_part688 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,false),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 8 7 true (1),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 14 5 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 11 3 true (1)
])
theorem kid05_part688_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part688) = true := by rfl

def kid05_part689 : Audit := .cycle 11 8 false (1)
theorem kid05_part689_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part689) = true := by rfl

def kid05_part690 : Audit := .cycle 12 3 false (0)
theorem kid05_part690_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part690) = true := by rfl

def kid05_part691 : Audit := .split 27 (4,false) (byMove [
.cycle 9 20 true (-2),
.cycle 0 31 true (-2),
.cycle 29 1 false (1),
.cycle 28 1 false (0),
.cycle 27 1 false (1),
.cycle 20 8 true (-2),
.cycle 0 30 true (-2),
.cycle 0 31 true (-2),
.cycle 37 1 false (5),
.cycle 0 29 true (-2),
.cycle 36 1 true (2),
.last 28 (5,true),
.cycle 11 18 true (-2),
.cycle 36 7 true (-1),
.cycle 0 34 true (-2),
.cycle 28 1 false (0),
.cycle 27 1 false (1),
.cycle 13 16 true (-2),
.cycle 14 28 true (-2),
.cycle 1 44 true (-2),
.cycle 28 14 true (0),
.cycle 5 56 true (-2),
.last 29 (5,true),
.last 28 (5,true)
])
theorem kid05_part691_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part691) = true := by rfl

def kid05_part692 : Audit := .cycle 19 1 false (-1)
theorem kid05_part692_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part692) = true := by rfl

def kid05_part693 : Audit := .split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 22 17 true (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.cycle 16 2 true (-3),
.cycle 14 5 false (-1),
.cycle 24 1 false (4),
.cycle 12 6 false (0),
.last 18 (5,true),
.cycle 11 8 false (1),
.cycle 14 4 false (-1),
.cycle 12 9 false (0),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 16 5 false (-1),
.cycle 11 7 false (1),
.cycle 15 3 false (-1),
.cycle 21 4 true (1),
.last 19 (5,true),
.last 18 (5,true)
])
theorem kid05_part693_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part693) = true := by rfl

def kid05_part694 : Audit := .split 12 (5,true) (byMove [
.cycle 9 5 false (2),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 15 4 false (1),
.cycle 13 4 false (1),
.cycle 14 4 false (1),
.last 15 (4,false),
.cycle 14 4 false (0),
.cycle 15 4 false (3),
.cycle 11 3 false (1),
.cycle 13 4 false (0),
.cycle 17 4 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 4 false (-1),
.cycle 16 4 false (0),
.cycle 11 2 true (0),
.cycle 13 4 false (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 11 5 true (0)
])
theorem kid05_part694_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part694) = true := by rfl

def kid05_part695 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 33 1 false (1),
.last 16 (5,true),
.cycle 11 4 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 11 24 true (1),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.cycle 0 16 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 16 (5,true),
.cycle 11 8 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 11 4 true (1)
])
theorem kid05_part695_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part695) = true := by rfl

def kid05_part696 : Audit := .cycle 1 12 true (1)
theorem kid05_part696_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part696) = true := by rfl

def kid05_part697 : Audit := .cycle 10 2 true (1)
theorem kid05_part697_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part697) = true := by rfl

def kid05_part698 : Audit := .cycle 0 13 true (0)
theorem kid05_part698_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part698) = true := by rfl

def kid05_part699 : Audit := .split 13 (5,true) (byMove [
.last 15 (4,false),
.last 15 (4,false),
.cycle 21 1 false (-1),
.cycle 0 15 true (0),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 8 6 true (1),
.last 24 (4,false),
.cycle 14 5 false (1),
.last 24 (4,false),
.last 16 (4,false),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 11 4 true (1)
])
theorem kid05_part699_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part699) = true := by rfl

def kid05_part700 : Audit := .split 12 (5,true) (byMove [
.last 14 (4,false),
.cycle 11 4 true (1),
.cycle 13 5 false (1),
.cycle 0 14 true (0),
.last 15 (4,false),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 16 7 false (1),
.cycle 11 2 true (1),
.cycle 13 5 false (1),
.last 15 (4,false),
.last 15 (4,false),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 11 3 true (1)
])
theorem kid05_part700_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part700) = true := by rfl

def kid05_part676 : Audit := .split 11 (1,true) (byMove [(kid05_part677),(kid05_part678),(kid05_part679),(kid05_part680),(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700)])

theorem kid05_part676_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part676) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part677),(kid05_part678),(kid05_part679),(kid05_part680),(kid05_part681),(kid05_part682),(kid05_part683),(kid05_part684),(kid05_part685),(kid05_part686),(kid05_part687),(kid05_part688),(kid05_part689),(kid05_part690),(kid05_part691),(kid05_part692),(kid05_part693),(kid05_part694),(kid05_part695),(kid05_part696),(kid05_part697),(kid05_part698),(kid05_part699),(kid05_part700)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part677_checked

  · exact kid05_part683_checked

  · exact kid05_part689_checked

  · exact kid05_part695_checked

  · exact kid05_part678_checked

  · exact kid05_part684_checked

  · exact kid05_part690_checked

  · exact kid05_part696_checked

  · exact kid05_part679_checked

  · exact kid05_part685_checked

  · exact kid05_part691_checked

  · exact kid05_part697_checked

  · exact kid05_part680_checked

  · exact kid05_part686_checked

  · exact kid05_part692_checked

  · exact kid05_part698_checked

  · exact kid05_part681_checked

  · exact kid05_part687_checked

  · exact kid05_part693_checked

  · exact kid05_part699_checked

  · exact kid05_part682_checked

  · exact kid05_part688_checked

  · exact kid05_part694_checked

  · exact kid05_part700_checked

def kid05_part701 : Audit := .split 24 (4,false) (byMove [
.cycle 0 25 true (-1),
.cycle 14 15 true (-1),
.cycle 26 1 false (2),
.cycle 25 1 false (1),
.cycle 24 1 false (2),
.cycle 17 8 true (-1),
.cycle 0 25 true (-1),
.cycle 14 15 true (-1),
.cycle 26 1 false (4),
.cycle 25 1 false (3),
.cycle 24 1 true (2),
.cycle 17 8 true (-1),
.split 26 (1,true) (byMove [
.cycle 23 4 true (1),
.cycle 14 18 true (-1),
.cycle 0 30 true (-1),
.cycle 0 28 true (-1),
.cycle 16 11 false (2),
.last 27 (5,true),
.cycle 0 27 true (-1),
.cycle 14 17 true (-1),
.cycle 0 47 true (-1),
.cycle 14 15 true (-1),
.cycle 24 3 true (1),
.cycle 8 19 true (-1),
.cycle 15 12 true (-1),
.cycle 11 18 true (-1),
.cycle 20 7 true (-1),
.cycle 22 5 true (0),
.cycle 16 11 false (2),
.last 27 (5,true),
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 1, 2, 64],[14, 12, 4, 12, 32, 64, 64],64⟩,
.far true 1 ⟨0,[0, 0],[12, 12, 8, 8, 1, 2, 64],[14, 12, 4, 12, 32, 64, 64],64⟩,
.cycle 2 25 true (-1),
.cycle 22 6 true (0),
.last 33 (5,true),
.last 29 (5,true)
]),
.cycle 18 7 true (-1),
.cycle 0 27 true (-1),
.cycle 25 1 false (1),
.cycle 24 1 false (2),
.cycle 11 16 true (-1),
.cycle 23 28 true (1),
.cycle 1 24 true (-1),
.cycle 14 14 true (-1),
.cycle 22 4 true (0),
.cycle 24 1 true (2),
.split 26 (1,true) (byMove [
.cycle 9 19 true (-1),
.cycle 0 30 true (-1),
.cycle 28 1 false (2),
.cycle 27 1 false (1),
.cycle 24 3 false (3),
.last 35 (5,true),
.cycle 23 4 true (1),
.cycle 14 18 true (-1),
.cycle 0 30 true (-1),
.cycle 0 28 true (-1),
.cycle 16 11 true (-1),
.last 27 (5,true),
.last 39 (5,true),
.cycle 11 17 true (-1),
.cycle 21 6 true (-1),
.cycle 27 1 false (1),
.last 28 (5,true),
.last 43 (5,true),
.cycle 23 4 true (1),
.last 53 (5,true),
.cycle 19 8 true (-1),
.cycle 0 28 true (-1),
.last 28 (5,true),
.last 27 (5,true)
])
])
theorem kid05_part701_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part701) = true := by rfl

def kid05_part702 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 30 1 false (2),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.split 15 (1,true) (byMove [
.cycle 12 4 true (2),
.cycle 1 16 true (1),
.cycle 30 1 false (0),
.cycle 0 17 true (0),
.cycle 19 9 false (-1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 4 28 true (1),
.cycle 3 13 true (1),
.cycle 13 3 true (2),
.cycle 8 8 true (1),
.cycle 6 10 true (1),
.cycle 5 14 true (1),
.cycle 30 1 false (0),
.cycle 11 5 true (1),
.cycle 19 9 false (-1),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 11 6 true (1),
.last 22 (5,true),
.last 18 (5,true)
]),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 5 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 11 4 true (1),
.cycle 13 1 true (3),
.split 15 (1,true) (byMove [
.cycle 9 8 true (1),
.cycle 0 19 true (0),
.last 29 (5,true),
.cycle 29 1 false (1),
.cycle 28 3 false (1),
.last 22 (5,true),
.cycle 12 4 true (2),
.cycle 1 16 true (1),
.last 29 (5,true),
.cycle 0 17 true (0),
.cycle 7 9 true (1),
.last 16 (5,true),
.last 26 (5,true),
.cycle 5 13 true (1),
.cycle 11 6 true (1),
.last 27 (5,true),
.last 17 (5,true),
.last 28 (5,true),
.cycle 12 4 true (2),
.cycle 1 16 true (1),
.cycle 10 6 true (1),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
])
theorem kid05_part702_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part702) = true := by rfl

def kid05_part704 : Audit := .cycle 0 17 true (-1)
theorem kid05_part704_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part704) = true := by rfl

def kid05_part705 : Audit := .cycle 19 4 false (1)
theorem kid05_part705_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part705) = true := by rfl

def kid05_part706 : Audit := .cycle 14 1 false (0)
theorem kid05_part706_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part706) = true := by rfl

def kid05_part707 : Audit := .cycle 13 1 false (-1)
theorem kid05_part707_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part707) = true := by rfl

def kid05_part708 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 false (3),
.cycle 20 4 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 9 6 true (-1),
.cycle 0 17 true (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 16 4 false (2),
.cycle 14 4 false (0),
.last 15 (1,true),
.cycle 14 4 false (-1),
.cycle 9 8 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 19 4 false (-1),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 0 19 true (-1),
.cycle 20 1 true (-2),
.last 15 (1,true)
])
theorem kid05_part708_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part708) = true := by rfl

def kid05_part709 : Audit := .cycle 13 4 false (-1)
theorem kid05_part709_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part709) = true := by rfl

def kid05_part710 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 22 4 false (2),
.last 16 (4,false),
.cycle 0 16 true (0),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 29 4 false (4),
.cycle 21 4 false (3),
.cycle 19 4 false (3),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 16 4 false (2),
.cycle 16 4 false (1),
.last 16 (4,false),
.last 17 (4,false),
.cycle 15 4 false (1),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 18 true (0)
])
theorem kid05_part710_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part710) = true := by rfl

def kid05_part711 : Audit := .cycle 13 4 false (2)
theorem kid05_part711_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part711) = true := by rfl

def kid05_part712 : Audit := .cycle 0 15 true (0)
theorem kid05_part712_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part712) = true := by rfl

def kid05_part713 : Audit := .cycle 13 1 false (1)
theorem kid05_part713_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part713) = true := by rfl

def kid05_part714 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 14 4 false (2),
.cycle 16 4 false (4),
.last 15 (1,true),
.cycle 14 4 false (1),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 4 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 14 4 false (2),
.cycle 0 15 true (0),
.cycle 16 1 true (2),
.last 17 (1,true)
])
theorem kid05_part714_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part714) = true := by rfl

def kid05_part715 : Audit := .cycle 13 4 false (1)
theorem kid05_part715_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part715) = true := by rfl

def kid05_part716 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 22 4 false (0),
.last 16 (4,false),
.cycle 9 8 true (-1),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.cycle 0 17 true (-1),
.cycle 21 4 false (2),
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.last 15 (4,false),
.cycle 8 7 false (2),
.cycle 16 4 false (0),
.cycle 16 4 false (-1),
.last 16 (4,false),
.last 17 (4,false),
.cycle 15 4 false (-1),
.cycle 12 3 false (0),
.last 35 (4,false),
.cycle 20 4 false (0),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 15 (4,false),
.cycle 24 4 false (0)
])
theorem kid05_part716_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part716) = true := by rfl

def kid05_part717 : Audit := .cycle 13 4 false (0)
theorem kid05_part717_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part717) = true := by rfl

def kid05_part718 : Audit := .split 16 (1,true) (byMove [
.last 18 (4,false),
.cycle 24 4 false (2),
.last 18 (4,false),
.cycle 0 18 true (-1),
.cycle 17 4 false (1),
.cycle 0 20 true (-1),
.cycle 0 17 true (-1),
.cycle 31 4 false (4),
.cycle 23 4 false (3),
.cycle 21 4 false (3),
.last 17 (4,false),
.cycle 8 9 true (-1),
.cycle 18 4 false (2),
.cycle 18 4 false (1),
.last 18 (4,false),
.last 19 (4,false),
.cycle 17 4 false (1),
.last 21 (4,false),
.cycle 30 4 false (2),
.last 30 (4,false),
.cycle 2 15 true (-1),
.last 20 (4,false),
.last 17 (4,false),
.cycle 20 4 false (2)
])
theorem kid05_part718_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part718) = true := by rfl

def kid05_part719 : Audit := .cycle 13 1 false (-1)
theorem kid05_part719_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part719) = true := by rfl

def kid05_part720 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 false (2),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.cycle 0 18 true (-1),
.last 14 (1,true),
.cycle 13 2 true (-1),
.last 16 (1,true),
.cycle 14 4 false (0),
.cycle 12 2 true (-1),
.last 15 (1,true),
.cycle 14 4 false (-1),
.cycle 0 24 true (-2),
.cycle 14 1 false (-2),
.cycle 13 1 false (-1),
.cycle 14 4 false (-2),
.last 33 (1,true),
.last 14 (1,true),
.cycle 14 4 false (0),
.last 16 (1,true),
.cycle 11 3 false (1),
.cycle 15 4 false (-1)
])
theorem kid05_part720_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part720) = true := by rfl

def kid05_part721 : Audit := .cycle 13 4 false (-1)
theorem kid05_part721_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part721) = true := by rfl

def kid05_part722 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 23 4 false (1),
.cycle 15 4 false (1),
.cycle 0 16 true (0),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.cycle 23 16 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 22 4 false (0),
.cycle 17 4 false (0),
.cycle 15 4 false (1),
.last 17 (4,false),
.cycle 11 4 true (0),
.last 17 (4,false),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 18 true (0)
])
theorem kid05_part722_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part722) = true := by rfl

def kid05_part723 : Audit := .cycle 9 4 true (0)
theorem kid05_part723_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part723) = true := by rfl

def kid05_part724 : Audit := .cycle 0 15 true (0)
theorem kid05_part724_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part724) = true := by rfl

def kid05_part725 : Audit := .cycle 16 4 false (2)
theorem kid05_part725_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part725) = true := by rfl

def kid05_part726 : Audit := .split 13 (4,false) (byMove [
.cycle 9 8 true (0),
.last 14 (1,true),
.cycle 17 1 false (-1),
.last 16 (1,true),
.cycle 14 4 false (0),
.cycle 12 2 true (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.last 16 (1,true),
.cycle 8 8 true (0),
.cycle 15 4 false (1),
.last 14 (1,true),
.cycle 19 4 false (1),
.cycle 16 4 false (2),
.cycle 14 4 false (0),
.cycle 11 4 true (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.cycle 16 1 true (2),
.last 17 (1,true)
])
theorem kid05_part726_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part726) = true := by rfl

def kid05_part727 : Audit := .split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.last 19 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.cycle 16 4 false (2),
.cycle 23 4 false (5),
.last 16 (4,false),
.last 17 (4,false),
.cycle 15 4 false (1),
.cycle 16 3 true (2),
.cycle 18 4 false (0),
.cycle 15 4 false (0),
.cycle 18 4 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 4 false (-1),
.last 20 (4,false),
.cycle 1 16 true (0),
.cycle 15 4 false (1),
.last 17 (4,false),
.cycle 11 4 true (0),
.cycle 16 3 true (2)
])
theorem kid05_part727_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part727) = true := by rfl

def kid05_part703 : Audit := .split 12 (5,true) (byMove [(kid05_part704),(kid05_part705),(kid05_part706),(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718),(kid05_part719),(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727)])

theorem kid05_part703_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part703) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) 12 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid05_part704),(kid05_part705),(kid05_part706),(kid05_part707),(kid05_part708),(kid05_part709),(kid05_part710),(kid05_part711),(kid05_part712),(kid05_part713),(kid05_part714),(kid05_part715),(kid05_part716),(kid05_part717),(kid05_part718),(kid05_part719),(kid05_part720),(kid05_part721),(kid05_part722),(kid05_part723),(kid05_part724),(kid05_part725),(kid05_part726),(kid05_part727)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part704_checked

  · exact kid05_part710_checked

  · exact kid05_part716_checked

  · exact kid05_part722_checked

  · exact kid05_part705_checked

  · exact kid05_part711_checked

  · exact kid05_part717_checked

  · exact kid05_part723_checked

  · exact kid05_part706_checked

  · exact kid05_part712_checked

  · exact kid05_part718_checked

  · exact kid05_part724_checked

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

def kid05_part729 : Audit := .split 13 (4,false) (byMove [
.cycle 9 6 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 9 10 false (2),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 9 11 false (2),
.cycle 0 15 true (0),
.cycle 9 11 false (2),
.cycle 0 15 true (0),
.last 15 (1,true),
.cycle 9 9 false (2),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 9 10 false (2),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 9 8 true (0),
.cycle 0 15 true (0),
.cycle 0 16 true (0),
.last 18 (1,true)
])
theorem kid05_part729_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part729) = true := by rfl

def kid05_part730 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 44 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 8 17 false (2),
.cycle 0 15 true (0),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.last 21 (4,false),
.cycle 6 25 false (3),
.last 29 (4,false),
.cycle 0 34 true (-2),
.cycle 13 1 false (-1),
.last 13 (4,false),
.last 21 (4,false),
.cycle 0 15 true (0),
.cycle 9 4 true (0),
.cycle 0 15 true (0),
.cycle 0 24 true (-1),
.last 13 (4,false),
.cycle 11 4 true (0)
])
theorem kid05_part730_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part730) = true := by rfl

def kid05_part731 : Audit := .cycle 18 1 false (-2)
theorem kid05_part731_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part731) = true := by rfl

def kid05_part732 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 27 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 16 true (0),
.cycle 20 1 false (-2),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.last 29 (4,false),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 20 1 false (-2),
.last 17 (4,false),
.cycle 20 1 false (-2),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 19 true (0)
])
theorem kid05_part732_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part732) = true := by rfl

def kid05_part733 : Audit := .split 17 (4,false) (byMove [
.cycle 0 34 false (3),
.cycle 12 12 false (0),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 19 (1,true),
.cycle 14 4 true (-3),
.cycle 9 12 true (-3),
.cycle 18 1 false (-2),
.cycle 12 7 false (0),
.cycle 13 5 false (-1),
.last 19 (1,true),
.cycle 14 4 false (-1),
.last 21 (1,true),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 19 (1,true),
.cycle 9 9 false (2),
.cycle 7 17 false (3),
.cycle 12 9 false (0),
.cycle 11 9 false (1),
.last 19 (1,true)
])
theorem kid05_part733_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part733) = true := by rfl

def kid05_part734 : Audit := .cycle 12 4 false (0)
theorem kid05_part734_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part734) = true := by rfl

def kid05_part735 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 8 6 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 69 1 false (7),
.cycle 30 1 false (6),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.last 15 (1,true),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 22 1 false (0),
.cycle 6 12 true (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.last 15 (1,true)
])
theorem kid05_part735_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part735) = true := by rfl

def kid05_part736 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 29 (4,false),
.cycle 24 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 18 9 false (0),
.cycle 9 4 true (1),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 13 (4,false),
.cycle 14 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 1 15 true (1)
])
theorem kid05_part736_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part736) = true := by rfl

def kid05_part737 : Audit := .split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.last 19 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (-1),
.cycle 17 5 false (1),
.cycle 24 5 false (4),
.cycle 15 5 false (1),
.last 17 (4,false),
.cycle 16 5 false (0),
.cycle 15 5 false (2),
.cycle 19 5 false (-1),
.cycle 15 5 false (0),
.cycle 19 5 false (1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (-1),
.last 20 (4,false),
.cycle 1 16 true (0),
.cycle 15 5 false (1),
.last 17 (4,false),
.cycle 0 19 true (0),
.cycle 11 4 true (0)
])
theorem kid05_part737_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part737) = true := by rfl

def kid05_part738 : Audit := .cycle 0 13 true (0)
theorem kid05_part738_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part738) = true := by rfl

def kid05_part739 : Audit := .split 14 (1,true) (byMove [
.cycle 9 7 false (2),
.cycle 0 18 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (-1),
.last 16 (4,false),
.cycle 22 5 false (4),
.cycle 16 5 false (0),
.cycle 0 16 true (0),
.cycle 15 5 false (1),
.last 16 (4,false),
.cycle 18 5 false (0),
.cycle 15 5 false (0),
.last 18 (4,false),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 5 false (-1),
.last 16 (4,false),
.cycle 1 15 true (0),
.cycle 15 5 false (1),
.cycle 0 16 true (0),
.last 17 (4,false),
.last 16 (4,false)
])
theorem kid05_part739_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part739) = true := by rfl

def kid05_part740 : Audit := .cycle 8 5 true (1)
theorem kid05_part740_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part740) = true := by rfl

def kid05_part741 : Audit := .split 19 (1,true) (byMove [
.last 21 (4,false),
.cycle 12 14 false (1),
.cycle 14 7 false (0),
.cycle 9 16 true (-2),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.last 21 (4,false),
.cycle 21 14 true (0),
.cycle 14 10 false (0),
.cycle 0 35 true (-2),
.cycle 13 10 false (1),
.cycle 8 26 false (2),
.cycle 12 8 false (1),
.cycle 15 6 false (0),
.cycle 14 7 false (0),
.cycle 12 9 false (1),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.last 21 (4,false),
.cycle 19 8 true (-1),
.cycle 10 10 false (2),
.last 26 (4,false),
.cycle 11 10 false (1),
.cycle 11 14 false (1)
])
theorem kid05_part741_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part741) = true := by rfl

def kid05_part742 : Audit := .split 12 (1,true) (byMove [
.cycle 9 5 false (2),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 14 3 false (-1),
.cycle 16 3 false (1),
.cycle 23 3 false (4),
.cycle 15 3 false (0),
.last 15 (4,false),
.cycle 15 3 false (0),
.cycle 13 3 false (1),
.cycle 18 3 false (-1),
.cycle 13 3 false (0),
.cycle 18 3 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 14 3 false (-1),
.last 18 (4,false),
.cycle 1 14 true (0),
.cycle 13 3 false (1),
.last 15 (4,false),
.cycle 14 3 false (0),
.cycle 11 2 true (0)
])
theorem kid05_part742_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part742) = true := by rfl

def kid05_part743 : Audit := .split 28 (4,false) (byMove [
.cycle 9 21 false (2),
.cycle 30 15 true (0),
.cycle 30 1 false (0),
.cycle 29 1 false (-1),
.cycle 28 1 false (0),
.cycle 21 8 true (-3),
.cycle 0 39 true (-3),
.last 29 (1,true),
.cycle 64 1 false (4),
.cycle 32 1 false (4),
.cycle 46 1 true (2),
.cycle 29 8 true (0),
.last 30 (1,true),
.cycle 52 7 true (-1),
.cycle 0 43 true (-3),
.cycle 29 1 false (-1),
.cycle 28 1 false (0),
.cycle 13 16 true (-3),
.last 32 (1,true),
.last 29 (1,true),
.cycle 32 14 true (-1),
.cycle 29 4 true (1),
.last 34 (1,true),
.cycle 11 18 true (-3)
])
theorem kid05_part743_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part743) = true := by rfl

def kid05_part744 : Audit := .cycle 19 1 false (-1)
theorem kid05_part744_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part744) = true := by rfl

def kid05_part745 : Audit := .split 17 (4,false) (byMove [
.cycle 9 10 false (2),
.cycle 22 17 true (-1),
.cycle 19 1 false (-3),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.cycle 12 7 false (0),
.last 18 (1,true),
.cycle 13 6 false (-1),
.cycle 24 1 false (4),
.cycle 12 6 false (0),
.cycle 16 2 true (-3),
.last 19 (1,true),
.cycle 14 4 false (-1),
.cycle 12 9 false (0),
.cycle 18 1 false (-4),
.cycle 17 1 false (-3),
.cycle 13 5 false (-1),
.last 21 (1,true),
.last 18 (1,true),
.cycle 15 3 false (-1),
.cycle 21 4 true (1),
.cycle 16 3 false (-2),
.cycle 11 7 false (1)
])
theorem kid05_part745_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part745) = true := by rfl

def kid05_part746 : Audit := .cycle 12 4 false (0)
theorem kid05_part746_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part746) = true := by rfl

def kid05_part747 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 33 1 false (1),
.cycle 0 17 true (0),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.last 36 (1,true),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 8 6 true (1),
.last 15 (1,true),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 18 (1,true),
.last 15 (1,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.last 15 (1,true)
])
theorem kid05_part747_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part747) = true := by rfl

def kid05_part748 : Audit := .split 12 (1,true) (byMove [
.last 14 (4,false),
.cycle 13 13 false (1),
.cycle 13 6 false (1),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.cycle 1 13 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 13 (4,false),
.cycle 8 5 true (1),
.cycle 18 7 false (0),
.cycle 13 5 false (1),
.cycle 13 6 false (1),
.last 15 (4,false),
.cycle 9 6 true (0),
.cycle 11 2 true (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 1 15 true (1)
])
theorem kid05_part748_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part748) = true := by rfl

def kid05_part749 : Audit := .cycle 10 2 true (1)
theorem kid05_part749_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part749) = true := by rfl

def kid05_part750 : Audit := .cycle 0 13 true (0)
theorem kid05_part750_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part750) = true := by rfl

def kid05_part751 : Audit := .split 14 (4,false) (byMove [
.cycle 0 17 true (0),
.last 15 (1,true),
.cycle 15 8 false (1),
.cycle 0 16 true (0),
.cycle 15 8 false (1),
.cycle 13 2 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 14 1 true (2),
.cycle 8 7 true (1),
.last 18 (1,true),
.last 15 (1,true),
.cycle 15 8 false (1),
.cycle 33 1 false (1),
.cycle 15 8 false (1),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 14 4 true (2),
.cycle 14 1 true (2),
.last 16 (1,true)
])
theorem kid05_part751_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part751) = true := by rfl

def kid05_part752 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 15 15 false (1),
.cycle 11 14 false (3),
.cycle 0 19 true (0),
.last 19 (4,false),
.cycle 15 10 false (2),
.last 16 (4,false),
.cycle 1 15 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 2048, 128, 256, 8, 16, 4096, 2048, 4096],[16, 4, 2048, 1, 2048, 2048, 16, 4, 2048, 1, 2048, 2048, 4096],5648⟩,
.cycle 0 16 true (0),
.cycle 16 11 false (2),
.cycle 12 3 true (2),
.cycle 20 9 false (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 2048, 128, 256, 8, 16, 4096, 2048, 4096],[16, 2048, 2048, 1, 2048, 2048, 16, 2048, 2048, 1, 2048, 2048, 4096],5648⟩,
.cycle 11 7 true (0),
.cycle 5 10 true (1),
.last 19 (4,false),
.cycle 11 5 true (1),
.last 16 (4,false),
.cycle 1 15 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 12 4 true (2),
.cycle 12 3 true (2)
])
theorem kid05_part752_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part752) = true := by rfl

def kid05_part728 : Audit := .split 11 (5,true) (byMove [(kid05_part729),(kid05_part730),(kid05_part731),(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part751),(kid05_part752)])

theorem kid05_part728_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part728) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) 11 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part729),(kid05_part730),(kid05_part731),(kid05_part732),(kid05_part733),(kid05_part734),(kid05_part735),(kid05_part736),(kid05_part737),(kid05_part738),(kid05_part739),(kid05_part740),(kid05_part741),(kid05_part742),(kid05_part743),(kid05_part744),(kid05_part745),(kid05_part746),(kid05_part747),(kid05_part748),(kid05_part749),(kid05_part750),(kid05_part751),(kid05_part752)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part729_checked

  · exact kid05_part735_checked

  · exact kid05_part741_checked

  · exact kid05_part747_checked

  · exact kid05_part730_checked

  · exact kid05_part736_checked

  · exact kid05_part742_checked

  · exact kid05_part748_checked

  · exact kid05_part731_checked

  · exact kid05_part737_checked

  · exact kid05_part743_checked

  · exact kid05_part749_checked

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

def kid05_part753 : Audit := .cycle 0 11 true (0)
theorem kid05_part753_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part753) = true := by rfl

def kid05_part754 : Audit := .cycle 1 10 true (1)
theorem kid05_part754_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part754) = true := by rfl

def kid05_part755 : Audit := .cycle 2 9 true (1)
theorem kid05_part755_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part755) = true := by rfl

def kid05_part756 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 21 true (1),
.cycle 3 12 true (1),
.split 18 (5,true) (byMove [
.cycle 0 19 false (4),
.cycle 25 10 false (2),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 19 10 false (1),
.cycle 0 19 true (0),
.cycle 25 10 false (4),
.cycle 20 1 false (2),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 19 10 false (3),
.last 20 (1,true),
.cycle 19 10 false (2),
.cycle 0 21 true (-1),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.last 43 (1,true),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 24 10 false (3),
.cycle 22 1 false (2),
.cycle 19 10 false (1),
.last 20 (1,true)
]),
.cycle 8 7 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 37 true (1),
.cycle 4 28 true (1),
.cycle 14 1 true (4),
.cycle 8 7 true (1),
.split 16 (1,true) (byMove [
.cycle 13 4 true (3),
.cycle 1 17 true (1),
.cycle 10 7 true (2),
.cycle 0 18 true (0),
.cycle 19 16 false (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 4 23 true (1),
.cycle 3 14 true (1),
.cycle 14 3 true (3),
.cycle 8 9 true (1),
.cycle 6 11 true (1),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 12 5 true (2),
.last 48 (5,true),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 11 6 true (2),
.last 23 (5,true),
.last 19 (5,true)
]),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 4 19 true (1),
.split 18 (5,true) (byMove [
.last 36 (1,true),
.last 58 (1,true),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.cycle 84 44 false (-2),
.last 20 (1,true),
.cycle 12 9 true (0),
.cycle 4 46 true (0),
.cycle 19 1 false (1),
.cycle 19 1 false (1),
.cycle 5 17 true (0),
.last 20 (1,true),
.last 50 (1,true),
.last 22 (1,true),
.cycle 19 1 false (-1),
.cycle 19 1 false (-1),
.last 24 (1,true),
.last 20 (1,true),
.cycle 12 9 true (0),
.last 34 (1,true),
.cycle 4 29 true (0),
.far true 4 ⟨0,[0, 1, 2, 3, 2, 1, 2, 1],[131072, 131072, 2097152, 512, 1024, 128, 16777216, 131072, 16908416, 2097152, 4194304, 524288, 16908288, 21103616, 2097664, 512, 1024, 128, 16777216, 16908288, 4195456, 512, 1024, 128, 16777216],[4194304, 16777216, 4326400, 128, 32, 131072, 128, 16777216, 16908288, 4326400, 131072, 131072, 4195328, 16777216, 4326400, 16777344, 131072, 131072, 128, 16777216, 131072, 131072, 131072, 131072, 16777216],17578304⟩,
.last 20 (1,true)
]),
.cycle 0 19 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 4 true (2),
.cycle 14 1 true (4),
.split 16 (1,true) (byMove [
.cycle 9 9 true (1),
.cycle 0 20 true (0),
.cycle 4 30 true (1),
.last 29 (5,true),
.last 24 (5,true),
.cycle 4 16 true (1),
.cycle 13 4 true (3),
.cycle 1 17 true (1),
.cycle 10 7 true (2),
.cycle 0 18 true (0),
.cycle 7 10 true (1),
.last 17 (5,true),
.cycle 4 20 true (1),
.cycle 0 20 true (0),
.cycle 12 6 true (2),
.cycle 4 28 true (1),
.last 18 (5,true),
.cycle 12 8 true (2),
.cycle 13 4 true (3),
.cycle 1 17 true (1),
.cycle 10 7 true (2),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 17 (5,true)
])
])
theorem kid05_part756_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part756) = true := by rfl

def kid05_part758 : Audit := .cycle 0 14 true (0)
theorem kid05_part758_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part758) = true := by rfl

def kid05_part759 : Audit := .split 12 (1,true) (byMove [
.cycle 1 14 true (1),
.cycle 13 13 false (1),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 8 5 true (1),
.cycle 18 7 false (0),
.last 18 (5,true),
.last 15 (5,true),
.cycle 1 15 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 16 true (1),
.cycle 11 2 true (2),
.last 15 (5,true)
])
theorem kid05_part759_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part759) = true := by rfl

def kid05_part760 : Audit := .cycle 10 2 true (2)
theorem kid05_part760_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part760) = true := by rfl

def kid05_part761 : Audit := .cycle 0 13 true (0)
theorem kid05_part761_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part761) = true := by rfl

def kid05_part762 : Audit := .split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 24 1 false (-2),
.cycle 0 15 true (0),
.cycle 21 1 false (-3),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 23 1 false (-1),
.cycle 8 6 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 0 19 true (-1),
.cycle 16 1 false (2),
.cycle 21 1 false (-3),
.cycle 12 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 30 1 false (0),
.cycle 14 8 false (2),
.last 15 (1,true)
])
theorem kid05_part762_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part762) = true := by rfl

def kid05_part763 : Audit := .split 12 (5,true) (byMove [
.last 16 (1,true),
.last 13 (1,true),
.cycle 20 1 false (0),
.cycle 0 14 true (0),
.cycle 16 6 false (-1),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 15 (1,true),
.cycle 8 5 true (1),
.last 16 (1,true),
.last 13 (1,true),
.cycle 0 21 true (-1),
.cycle 8 8 true (1),
.cycle 16 6 false (-1),
.cycle 13 6 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.cycle 11 2 true (2),
.last 14 (1,true)
])
theorem kid05_part763_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part763) = true := by rfl

def kid05_part764 : Audit := .cycle 0 12 true (0)
theorem kid05_part764_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part764) = true := by rfl

def kid05_part765 : Audit := .cycle 1 11 true (1)
theorem kid05_part765_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part765) = true := by rfl

def kid05_part766 : Audit := .cycle 10 13 true (2)
theorem kid05_part766_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part766) = true := by rfl

def kid05_part767 : Audit := .cycle 3 9 true (1)
theorem kid05_part767_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part767) = true := by rfl

def kid05_part768 : Audit := .cycle 11 1 true (3)
theorem kid05_part768_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part768) = true := by rfl

def kid05_part769 : Audit := .cycle 8 4 true (1)
theorem kid05_part769_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part769) = true := by rfl

def kid05_part770 : Audit := .split 15 (1,true) (byMove [
.cycle 15 4 true (0),
.cycle 0 56 true (-2),
.cycle 29 1 false (-1),
.cycle 0 20 true (0),
.cycle 15 12 false (1),
.last 16 (5,true),
.cycle 0 20 true (0),
.cycle 1 16 true (1),
.cycle 6 12 true (1),
.cycle 0 17 true (0),
.cycle 16 9 false (2),
.last 16 (5,true),
.cycle 15 12 false (1),
.last 20 (5,true),
.last 18 (5,true),
.cycle 27 1 false (-1),
.cycle 15 12 false (1),
.last 16 (5,true),
.cycle 0 20 true (0),
.cycle 1 16 true (1),
.cycle 10 6 true (1),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part770_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part770) = true := by rfl

def kid05_part771 : Audit := .split 12 (1,true) (byMove [
.last 18 (5,true),
.cycle 13 13 false (1),
.cycle 20 1 false (0),
.cycle 0 17 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 9 6 true (1),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 15 9 false (2),
.last 13 (5,true),
.cycle 18 7 false (0),
.last 18 (5,true),
.last 15 (5,true),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 9 6 true (1),
.cycle 1 13 true (1),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part771_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part771) = true := by rfl

def kid05_part772 : Audit := .split 14 (5,true) (byMove [
.cycle 0 19 true (0),
.last 15 (1,true),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.cycle 0 20 true (-2),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.cycle 0 18 true (0),
.cycle 8 7 true (1),
.last 18 (1,true),
.last 15 (1,true),
.cycle 0 23 true (-1),
.cycle 0 20 true (0),
.cycle 0 28 true (-2),
.cycle 15 6 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 0 21 true (0),
.cycle 11 4 true (2),
.last 16 (1,true)
])
theorem kid05_part772_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part772) = true := by rfl

def kid05_part773 : Audit := .cycle 5 19 true (1)
theorem kid05_part773_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part773) = true := by rfl

def kid05_part774 : Audit := .split 13 (5,true) (byMove [
.cycle 15 1 false (1),
.last 14 (1,true),
.cycle 24 1 false (-2),
.cycle 9 7 true (0),
.cycle 21 1 false (-3),
.cycle 14 6 false (0),
.last 15 (1,true),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 23 1 false (-1),
.cycle 8 11 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 9 11 true (-1),
.cycle 16 1 false (2),
.cycle 21 1 false (-3),
.cycle 12 6 false (2),
.last 15 (1,true),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 14 8 false (2),
.last 15 (1,true)
])
theorem kid05_part774_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part774) = true := by rfl

def kid05_part775 : Audit := .split 12 (5,true) (byMove [
.last 16 (1,true),
.last 13 (1,true),
.cycle 20 1 false (0),
.last 15 (1,true),
.cycle 20 6 false (-2),
.cycle 13 6 false (1),
.cycle 0 20 true (0),
.last 13 (1,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.last 15 (1,true),
.cycle 8 6 true (1),
.last 16 (1,true),
.last 13 (1,true),
.cycle 9 13 true (-1),
.cycle 5 8 true (1),
.cycle 20 6 false (-2),
.cycle 13 6 false (1),
.last 16 (1,true),
.last 13 (1,true),
.cycle 10 3 true (2),
.cycle 0 14 true (0),
.cycle 11 4 true (2),
.last 15 (1,true)
])
theorem kid05_part775_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part775) = true := by rfl

def kid05_part776 : Audit := .cycle 0 12 true (0)
theorem kid05_part776_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part776) = true := by rfl

def kid05_part777 : Audit := .cycle 1 11 true (1)
theorem kid05_part777_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part777) = true := by rfl

def kid05_part778 : Audit := .cycle 2 10 true (1)
theorem kid05_part778_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part778) = true := by rfl

def kid05_part779 : Audit := .cycle 11 4 true (3)
theorem kid05_part779_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part779) = true := by rfl

def kid05_part780 : Audit := .cycle 11 1 true (3)
theorem kid05_part780_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part780) = true := by rfl

def kid05_part781 : Audit := .split 13 (1,true) (byMove [
.last 16 (5,true),
.cycle 14 15 false (2),
.last 16 (5,true),
.cycle 0 18 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 11 4 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.cycle 15 13 false (3),
.last 14 (5,true),
.last 24 (5,true),
.last 20 (5,true),
.last 16 (5,true),
.cycle 5 9 true (1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 11 4 true (3),
.cycle 1 14 true (1),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part781_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part781) = true := by rfl

def kid05_part757 : Audit := .split 11 (4,false) (byMove [(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774),(kid05_part775),(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781)])

theorem kid05_part757_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part757) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part758),(kid05_part759),(kid05_part760),(kid05_part761),(kid05_part762),(kid05_part763),(kid05_part764),(kid05_part765),(kid05_part766),(kid05_part767),(kid05_part768),(kid05_part769),(kid05_part770),(kid05_part771),(kid05_part772),(kid05_part773),(kid05_part774),(kid05_part775),(kid05_part776),(kid05_part777),(kid05_part778),(kid05_part779),(kid05_part780),(kid05_part781)] mv))) = true

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

def kid05_part783 : Audit := .split 14 (4,false) (byMove [
.cycle 9 7 true (1),
.cycle 0 18 true (0),
.cycle 29 1 false (1),
.cycle 19 1 false (1),
.cycle 23 1 false (-1),
.cycle 9 9 false (3),
.cycle 0 17 true (0),
.cycle 0 16 true (0),
.cycle 9 10 true (1),
.cycle 0 16 true (0),
.cycle 7 8 true (1),
.last 15 (5,true),
.cycle 12 4 true (1),
.last 17 (5,true),
.cycle 0 21 true (0),
.cycle 26 1 false (0),
.cycle 23 1 false (-1),
.last 20 (5,true),
.cycle 0 17 true (0),
.cycle 1 17 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid05_part783_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part783) = true := by rfl

def kid05_part784 : Audit := .cycle 13 13 false (1)
theorem kid05_part784_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part784) = true := by rfl

def kid05_part785 : Audit := .cycle 20 1 false (0)
theorem kid05_part785_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part785) = true := by rfl

def kid05_part786 : Audit := .cycle 0 17 true (0)
theorem kid05_part786_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part786) = true := by rfl

def kid05_part787 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 6 false (0),
.cycle 9 7 true (0),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 15 6 false (2),
.cycle 16 6 false (0),
.cycle 15 6 false (1),
.cycle 9 9 true (-1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 6 false (0),
.cycle 9 7 true (0),
.cycle 0 18 true (0),
.cycle 20 6 false (2),
.last 18 (4,false),
.last 15 (4,false),
.last 17 (4,false)
])
theorem kid05_part787_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part787) = true := by rfl

def kid05_part788 : Audit := .split 13 (5,true) (byMove [
.last 15 (4,false),
.cycle 15 13 false (0),
.cycle 24 1 false (-2),
.cycle 9 7 true (0),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 14 (4,false),
.cycle 8 10 true (1),
.cycle 20 3 false (0),
.cycle 16 5 false (0),
.cycle 13 2 true (0),
.last 16 (4,false),
.last 21 (4,false),
.cycle 13 6 false (1),
.cycle 0 17 true (0),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 14 (4,false),
.cycle 14 8 false (2)
])
theorem kid05_part788_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part788) = true := by rfl

def kid05_part789 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 21 true (1),
.cycle 3 12 true (1),
.last 18 (5,true),
.cycle 8 7 true (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 37 true (1),
.cycle 6 28 true (1),
.cycle 14 1 true (4),
.cycle 8 7 true (1),
.cycle 0 17 true (0),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 6 19 true (1),
.last 18 (5,true),
.last 18 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 13 4 true (3),
.cycle 14 1 true (4),
.cycle 11 4 true (2)
])
theorem kid05_part789_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part789) = true := by rfl

def kid05_part790 : Audit := .cycle 1 13 true (1)
theorem kid05_part790_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part790) = true := by rfl

def kid05_part791 : Audit := .cycle 10 3 true (2)
theorem kid05_part791_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part791) = true := by rfl

def kid05_part792 : Audit := .cycle 0 14 true (0)
theorem kid05_part792_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part792) = true := by rfl

def kid05_part793 : Audit := .cycle 14 9 false (2)
theorem kid05_part793_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part793) = true := by rfl

def kid05_part794 : Audit := .split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 14 9 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 27 37 true (3),
.cycle 0 27 true (0),
.last 14 (4,false),
.cycle 8 6 true (1),
.cycle 8 8 true (1),
.cycle 9 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.last 14 (4,false),
.cycle 19 6 false (1),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 11 3 true (2)
])
theorem kid05_part794_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part794) = true := by rfl

def kid05_part795 : Audit := .cycle 18 7 false (0)
theorem kid05_part795_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part795) = true := by rfl

def kid05_part796 : Audit := .split 17 (5,true) (byMove [
.last 19 (4,false),
.cycle 13 5 false (1),
.cycle 13 7 false (1),
.cycle 0 33 true (-1),
.last 20 (4,false),
.cycle 13 11 false (1),
.cycle 12 13 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2306, 4096, 2048, 128, 256, 8, 16, 4096, 2050, 4096],[16, 2048, 2048, 1, 2306, 2, 16, 2050, 2048, 1, 256, 2, 4096],5648⟩,
.cycle 13 18 true (-1),
.last 20 (4,false),
.cycle 13 7 false (2),
.cycle 18 10 true (2),
.cycle 14 7 false (1),
.cycle 13 5 false (1),
.cycle 16 2 true (0),
.cycle 5 13 false (3),
.last 20 (4,false),
.cycle 15 6 false (1),
.cycle 11 9 false (3),
.cycle 12 7 false (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 2304, 262144, 2048, 128, 256, 32768, 16, 262144, 2304, 128, 256, 8, 2304, 262144, 2048, 262144],[16, 2048, 2048, 1, 2304, 256, 65536, 2304, 2048, 4096, 32768, 256, 16, 2048, 2048, 1, 35072, 256, 262144],329232⟩,
.last 20 (4,false),
.last 20 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2048, 4096, 2048, 128, 256, 8, 16, 4096, 2048, 4096],[16, 2048, 2048, 1, 2048, 2048, 16, 2048, 2048, 1, 2048, 2048, 4096],5648⟩
])
theorem kid05_part796_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part796) = true := by rfl

def kid05_part797 : Audit := .split 14 (5,true) (byMove [
.last 16 (4,false),
.cycle 9 13 true (-1),
.cycle 15 14 true (-1),
.cycle 0 21 true (0),
.last 17 (4,false),
.cycle 15 8 false (1),
.last 16 (4,false),
.cycle 0 18 true (0),
.last 21 (4,false),
.cycle 0 16 true (0),
.last 26 (4,false),
.cycle 8 8 true (1),
.last 22 (4,false),
.cycle 15 12 true (-1),
.cycle 13 2 true (1),
.cycle 5 10 true (1),
.last 17 (4,false),
.cycle 13 6 false (2),
.last 16 (4,false),
.cycle 1 17 true (1),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 11 5 true (1)
])
theorem kid05_part797_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part797) = true := by rfl

def kid05_part798 : Audit := .cycle 5 8 true (1)
theorem kid05_part798_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part798) = true := by rfl

def kid05_part799 : Audit := .split 14 (5,true) (byMove [
.last 20 (4,false),
.cycle 21 6 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 6 false (0),
.cycle 16 6 false (2),
.cycle 31 6 false (3),
.last 18 (4,false),
.cycle 15 1 false (1),
.last 15 (4,false),
.cycle 26 6 false (2),
.cycle 16 6 false (0),
.cycle 15 6 false (1),
.cycle 18 6 false (2),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 14 6 false (0),
.cycle 12 4 true (0),
.cycle 1 17 true (0),
.last 18 (4,false),
.cycle 18 6 false (2),
.last 15 (4,false),
.last 17 (4,false)
])
theorem kid05_part799_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part799) = true := by rfl

def kid05_part800 : Audit := .split 13 (5,true) (byMove [
.last 15 (4,false),
.cycle 28 23 false (2),
.cycle 26 1 false (-2),
.cycle 18 1 false (0),
.last 21 (4,false),
.cycle 14 6 false (0),
.cycle 6 8 true (1),
.cycle 16 9 false (1),
.cycle 13 40 true (1),
.last 16 (4,false),
.cycle 22 7 false (0),
.cycle 8 8 true (1),
.cycle 20 3 false (0),
.cycle 16 5 false (0),
.cycle 13 2 true (0),
.cycle 23 1 false (-1),
.last 21 (4,false),
.cycle 13 6 false (1),
.last 28 (4,false),
.cycle 12 2 true (1),
.cycle 2 14 true (1),
.last 16 (4,false),
.last 16 (4,false),
.cycle 11 5 true (1)
])
theorem kid05_part800_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part800) = true := by rfl

def kid05_part801 : Audit := .split 14 (4,false) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 3 16 true (1),
.last 17 (5,true),
.cycle 11 4 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 10 24 true (2),
.cycle 11 17 true (2),
.cycle 14 1 true (4),
.cycle 8 7 true (1),
.cycle 0 17 true (0),
.cycle 9 6 true (1),
.cycle 0 17 true (0),
.cycle 4 11 true (1),
.last 17 (5,true),
.cycle 11 8 true (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 13 4 true (3),
.cycle 14 1 true (4),
.cycle 11 4 true (2)
])
theorem kid05_part801_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part801) = true := by rfl

def kid05_part802 : Audit := .cycle 1 13 true (1)
theorem kid05_part802_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part802) = true := by rfl

def kid05_part803 : Audit := .cycle 10 3 true (2)
theorem kid05_part803_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part803) = true := by rfl

def kid05_part804 : Audit := .cycle 0 14 true (0)
theorem kid05_part804_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part804) = true := by rfl

def kid05_part805 : Audit := .split 14 (5,true) (byMove [
.last 16 (4,false),
.last 16 (4,false),
.cycle 26 1 false (0),
.cycle 0 16 true (0),
.last 17 (4,false),
.cycle 15 8 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 0 31 true (0),
.cycle 3 12 true (1),
.last 15 (4,false),
.cycle 8 7 true (1),
.last 23 (4,false),
.cycle 15 9 false (2),
.cycle 14 2 true (1),
.last 17 (4,false),
.last 17 (4,false),
.cycle 14 6 false (2),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.last 18 (4,false),
.last 15 (4,false),
.cycle 11 4 true (2)
])
theorem kid05_part805_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part805) = true := by rfl

def kid05_part806 : Audit := .split 13 (5,true) (byMove [
.last 15 (4,false),
.cycle 11 4 true (2),
.cycle 10 4 true (2),
.cycle 0 15 true (0),
.last 25 (4,false),
.cycle 14 8 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 10 17 true (2),
.cycle 3 11 true (1),
.last 14 (4,false),
.cycle 8 6 true (1),
.cycle 16 13 false (2),
.cycle 12 2 true (2),
.cycle 13 2 true (2),
.last 16 (4,false),
.last 25 (4,false),
.cycle 14 6 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.last 17 (4,false),
.last 14 (4,false),
.cycle 11 3 true (2)
])
theorem kid05_part806_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part806) = true := by rfl

def kid05_part782 : Audit := .split 12 (1,true) (byMove [(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799),(kid05_part800),(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806)])

theorem kid05_part782_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part782) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (1,true) (some mv)) (byMove [(kid05_part783),(kid05_part784),(kid05_part785),(kid05_part786),(kid05_part787),(kid05_part788),(kid05_part789),(kid05_part790),(kid05_part791),(kid05_part792),(kid05_part793),(kid05_part794),(kid05_part795),(kid05_part796),(kid05_part797),(kid05_part798),(kid05_part799),(kid05_part800),(kid05_part801),(kid05_part802),(kid05_part803),(kid05_part804),(kid05_part805),(kid05_part806)] mv))) = true

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

def kid05_part566 : Audit := .split 10 (2,true) (byMove [(kid05_part567),(kid05_part568),(kid05_part593),(kid05_part594),(kid05_part595),(kid05_part620),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650),(kid05_part651),(kid05_part676),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part728),(kid05_part753),(kid05_part754),(kid05_part755),(kid05_part756),(kid05_part757),(kid05_part782)])

theorem kid05_part566_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (kid05_part566) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part567),(kid05_part568),(kid05_part593),(kid05_part594),(kid05_part595),(kid05_part620),(kid05_part645),(kid05_part646),(kid05_part647),(kid05_part648),(kid05_part649),(kid05_part650),(kid05_part651),(kid05_part676),(kid05_part701),(kid05_part702),(kid05_part703),(kid05_part728),(kid05_part753),(kid05_part754),(kid05_part755),(kid05_part756),(kid05_part757),(kid05_part782)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part567_checked

  · exact kid05_part645_checked

  · exact kid05_part651_checked

  · exact kid05_part753_checked

  · exact kid05_part568_checked

  · exact kid05_part646_checked

  · exact kid05_part676_checked

  · exact kid05_part754_checked

  · exact kid05_part593_checked

  · exact kid05_part647_checked

  · exact kid05_part701_checked

  · exact kid05_part755_checked

  · exact kid05_part594_checked

  · exact kid05_part648_checked

  · exact kid05_part702_checked

  · exact kid05_part756_checked

  · exact kid05_part595_checked

  · exact kid05_part649_checked

  · exact kid05_part703_checked

  · exact kid05_part757_checked

  · exact kid05_part620_checked

  · exact kid05_part650_checked

  · exact kid05_part728_checked

  · exact kid05_part782_checked

def kid05_part807 : Audit := .cycle 0 11 true (0)
theorem kid05_part807_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,2⟩)) (kid05_part807) = true := by rfl

def kid05_part808 : Audit := .cycle 14 1 false (0)
theorem kid05_part808_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,3⟩)) (kid05_part808) = true := by rfl

def kid05_part811 : Audit := .cycle 0 17 true (0)
theorem kid05_part811_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part811) = true := by rfl

def kid05_part812 : Audit := .split 15 (1,true) (byMove [
.cycle 0 18 true (0),
.cycle 11 14 false (2),
.cycle 11 14 false (2),
.cycle 0 17 true (0),
.cycle 11 7 false (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 11 13 true (0),
.cycle 11 13 false (3),
.cycle 11 11 false (2),
.cycle 0 17 true (0),
.cycle 8 8 true (0),
.cycle 11 8 false (2),
.cycle 16 3 false (0),
.cycle 0 20 true (-1),
.cycle 0 19 true (0),
.cycle 11 7 false (2),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.last 18 (5,true)
])
theorem kid05_part812_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part812) = true := by rfl

def kid05_part813 : Audit := .cycle 18 1 false (0)
theorem kid05_part813_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part813) = true := by rfl

def kid05_part814 : Audit := .cycle 0 16 true (0)
theorem kid05_part814_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part814) = true := by rfl

def kid05_part815 : Audit := .split 16 (5,true) (byMove [
.cycle 0 17 false (3),
.cycle 11 14 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 false (3),
.cycle 11 7 false (2),
.cycle 0 17 true (0),
.cycle 11 14 true (0),
.cycle 18 1 false (2),
.cycle 17 1 false (1),
.cycle 0 18 true (0),
.cycle 11 7 false (2),
.last 18 (1,true),
.cycle 11 10 false (2),
.cycle 0 19 true (-1),
.cycle 17 1 false (-1),
.cycle 11 6 false (2),
.cycle 11 7 false (2),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 11 13 false (2),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 11 9 false (2)
])
theorem kid05_part815_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part815) = true := by rfl

def kid05_part816 : Audit := .split 15 (5,true) (byMove [
.cycle 0 18 true (0),
.last 16 (1,true),
.cycle 11 7 false (2),
.cycle 0 17 true (0),
.cycle 11 7 false (2),
.cycle 11 7 false (2),
.cycle 0 16 true (0),
.cycle 11 13 true (0),
.cycle 11 13 false (3),
.cycle 11 11 false (2),
.cycle 0 17 true (0),
.cycle 8 8 true (0),
.cycle 11 8 false (2),
.last 16 (1,true),
.cycle 11 7 false (2),
.cycle 0 19 true (0),
.cycle 11 7 false (2),
.cycle 11 7 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.cycle 11 11 false (2)
])
theorem kid05_part816_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part816) = true := by rfl

def kid05_part817 : Audit := .cycle 0 15 true (0)
theorem kid05_part817_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part817) = true := by rfl

def kid05_part818 : Audit := .cycle 11 12 true (0)
theorem kid05_part818_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part818) = true := by rfl

def kid05_part819 : Audit := .cycle 0 31 true (0)
theorem kid05_part819_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part819) = true := by rfl

def kid05_part820 : Audit := .cycle 3 12 true (0)
theorem kid05_part820_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part820) = true := by rfl

def kid05_part821 : Audit := .cycle 0 16 true (0)
theorem kid05_part821_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part821) = true := by rfl

def kid05_part822 : Audit := .cycle 8 7 true (0)
theorem kid05_part822_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part822) = true := by rfl

def kid05_part823 : Audit := .cycle 11 9 false (2)
theorem kid05_part823_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part823) = true := by rfl

def kid05_part824 : Audit := .split 15 (1,true) (byMove [
.cycle 10 6 true (0),
.cycle 11 14 false (2),
.cycle 21 1 false (-1),
.cycle 0 20 true (0),
.cycle 11 7 false (2),
.last 16 (5,true),
.cycle 0 18 true (0),
.cycle 11 14 true (0),
.cycle 13 4 true (1),
.cycle 0 17 true (0),
.cycle 11 9 false (2),
.last 16 (5,true),
.cycle 11 8 false (2),
.cycle 16 3 false (0),
.cycle 11 14 false (2),
.cycle 11 9 false (2),
.cycle 11 7 false (2),
.last 16 (5,true),
.cycle 0 18 true (0),
.cycle 1 16 true (0),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part824_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part824) = true := by rfl

def kid05_part825 : Audit := .cycle 11 11 false (2)
theorem kid05_part825_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part825) = true := by rfl

def kid05_part826 : Audit := .cycle 0 18 true (0)
theorem kid05_part826_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part826) = true := by rfl

def kid05_part827 : Audit := .split 16 (5,true) (byMove [
.cycle 0 21 true (-1),
.cycle 11 14 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 18 false (3),
.cycle 11 7 false (2),
.last 18 (1,true),
.cycle 11 10 false (2),
.cycle 0 19 true (0),
.cycle 17 1 false (1),
.cycle 11 6 true (0),
.cycle 11 7 false (2),
.last 18 (1,true),
.cycle 11 10 false (2),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 11 6 false (2),
.cycle 11 7 false (2),
.last 18 (1,true),
.cycle 13 4 true (0),
.cycle 0 19 true (0),
.cycle 11 11 false (2),
.cycle 9 8 true (0),
.cycle 11 9 false (2)
])
theorem kid05_part827_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part827) = true := by rfl

def kid05_part828 : Audit := .split 15 (5,true) (byMove [
.cycle 10 6 true (0),
.last 16 (1,true),
.cycle 11 7 false (2),
.last 18 (1,true),
.cycle 11 7 false (2),
.cycle 11 7 false (2),
.cycle 0 18 true (0),
.last 16 (1,true),
.cycle 11 9 false (2),
.cycle 0 17 true (0),
.cycle 11 9 false (2),
.cycle 11 7 true (0),
.cycle 11 8 false (2),
.last 16 (1,true),
.cycle 11 7 false (2),
.cycle 11 9 false (2),
.cycle 11 7 false (2),
.cycle 11 7 false (2),
.cycle 0 18 true (0),
.last 16 (1,true),
.cycle 14 2 true (1),
.cycle 0 17 true (0),
.cycle 0 21 true (0),
.cycle 11 15 false (3)
])
theorem kid05_part828_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part828) = true := by rfl

def kid05_part829 : Audit := .cycle 0 15 true (0)
theorem kid05_part829_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part829) = true := by rfl

def kid05_part830 : Audit := .cycle 1 14 true (0)
theorem kid05_part830_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part830) = true := by rfl

def kid05_part831 : Audit := .cycle 2 13 true (0)
theorem kid05_part831_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part831) = true := by rfl

def kid05_part832 : Audit := .cycle 0 19 true (0)
theorem kid05_part832_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part832) = true := by rfl

def kid05_part833 : Audit := .cycle 0 18 true (0)
theorem kid05_part833_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part833) = true := by rfl

def kid05_part834 : Audit := .split 17 (5,true) (byMove [
.cycle 0 24 true (0),
.last 18 (1,true),
.cycle 11 11 false (3),
.cycle 12 7 true (0),
.cycle 11 9 false (3),
.cycle 11 9 false (3),
.last 19 (1,true),
.cycle 13 5 true (1),
.cycle 0 20 true (0),
.cycle 11 13 false (3),
.cycle 11 7 true (0),
.cycle 8 18 true (0),
.cycle 11 10 false (3),
.last 18 (1,true),
.cycle 17 2 true (0),
.cycle 10 9 true (0),
.cycle 11 9 false (3),
.cycle 17 9 false (1),
.last 19 (1,true),
.cycle 13 5 true (1),
.cycle 0 20 true (0),
.cycle 4 14 true (0),
.cycle 9 9 true (0),
.cycle 11 13 false (3)
])
theorem kid05_part834_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part834) = true := by rfl

def kid05_part810 : Audit := .split 14 (2,true) (byMove [(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832),(kid05_part833),(kid05_part834)])

theorem kid05_part810_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part810) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) 14 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid05_part811),(kid05_part812),(kid05_part813),(kid05_part814),(kid05_part815),(kid05_part816),(kid05_part817),(kid05_part818),(kid05_part819),(kid05_part820),(kid05_part821),(kid05_part822),(kid05_part823),(kid05_part824),(kid05_part825),(kid05_part826),(kid05_part827),(kid05_part828),(kid05_part829),(kid05_part830),(kid05_part831),(kid05_part832),(kid05_part833),(kid05_part834)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part815_checked

  · exact kid05_part821_checked

  · exact kid05_part827_checked

  · exact kid05_part833_checked

  · exact kid05_part816_checked

  · exact kid05_part822_checked

  · exact kid05_part828_checked

  · exact kid05_part834_checked

def kid05_part836 : Audit := .cycle 0 15 true (-1)
theorem kid05_part836_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part836) = true := by rfl

def kid05_part837 : Audit := .cycle 0 38 true (-2)
theorem kid05_part837_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part837) = true := by rfl

def kid05_part838 : Audit := .cycle 12 1 false (0)
theorem kid05_part838_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part838) = true := by rfl

def kid05_part839 : Audit := .cycle 11 1 false (-1)
theorem kid05_part839_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part839) = true := by rfl

def kid05_part840 : Audit := .split 26 (2,true) (byMove [
.cycle 1 39 false (3),
.cycle 7 21 false (3),
.cycle 7 36 false (3),
.cycle 1 41 false (5),
.last 28 (5,true),
.last 27 (5,true),
.cycle 7 33 false (6),
.last 62 (5,true),
.cycle 1 37 false (4),
.cycle 1 35 false (3),
.cycle 7 31 false (4),
.cycle 7 23 false (3),
.cycle 7 23 false (3),
.cycle 7 21 false (3),
.cycle 56 78 false (2),
.proven (BB6.Agent11Raw39B0REPumps.M169.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M169.never m hm),
.last 28 (5,true),
.last 27 (5,true),
.last 39 (5,true),
.last 38 (5,true),
.cycle 7 29 false (4),
.last 66 (5,true),
.last 30 (5,true),
.last 29 (5,true)
])
theorem kid05_part840_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part840) = true := by rfl

def kid05_part841 : Audit := .split 18 (2,true) (byMove [
.cycle 8 23 false (3),
.last 20 (5,true),
.last 35 (5,true),
.last 67 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 32 (5,true),
.last 45 (5,true),
.cycle 8 21 false (4),
.cycle 8 19 false (3),
.last 30 (5,true),
.last 22 (5,true),
.cycle 7 15 false (3),
.last 20 (5,true),
.last 53 (5,true),
.last 48 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 30 (5,true),
.last 29 (5,true),
.last 28 (5,true),
.last 49 (5,true),
.last 21 (5,true),
.last 21 (5,true)
])
theorem kid05_part841_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part841) = true := by rfl

def kid05_part842 : Audit := .cycle 0 13 true (0)
theorem kid05_part842_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part842) = true := by rfl

def kid05_part843 : Audit := .split 12 (2,true) (byMove [
.cycle 0 27 true (0),
.cycle 0 26 true (0),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 0 19 true (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 0 25 true (0),
.cycle 0 39 true (0),
.cycle 0 23 true (0),
.cycle 1 13 true (0),
.cycle 8 5 true (0),
.cycle 0 20 true (-1),
.cycle 0 27 true (0),
.cycle 0 30 true (0),
.cycle 0 28 true (0),
.cycle 0 33 true (-2),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 29 true (0),
.cycle 0 27 true (0),
.last 15 (5,true)
])
theorem kid05_part843_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part843) = true := by rfl

def kid05_part844 : Audit := .cycle 0 13 true (0)
theorem kid05_part844_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part844) = true := by rfl

def kid05_part845 : Audit := .cycle 11 1 false (1)
theorem kid05_part845_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part845) = true := by rfl

def kid05_part846 : Audit := .cycle 0 15 true (0)
theorem kid05_part846_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part846) = true := by rfl

def kid05_part847 : Audit := .cycle 0 30 true (-1)
theorem kid05_part847_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part847) = true := by rfl

def kid05_part848 : Audit := .split 22 (2,true) (byMove [
.cycle 6 31 false (3),
.cycle 12 36 false (4),
.cycle 12 51 false (3),
.proven (BB6.Agent11Raw39B0REPumps.M170.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M170.never m hm),
.last 24 (5,true),
.last 23 (5,true),
.last 40 (5,true),
.last 125 (5,true),
.cycle 6 29 false (4),
.cycle 6 27 false (3),
.cycle 12 21 true (-3),
.cycle 12 13 true (-3),
.cycle 7 19 false (3),
.last 122 (5,true),
.last 114 (5,true),
.proven (BB6.Agent11Raw39B0REPumps.M171.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M171.never m hm),
.last 24 (5,true),
.last 23 (5,true),
.last 38 (5,true),
.last 79 (5,true),
.cycle 12 19 true (-3),
.last 181 (5,true),
.cycle 7 21 false (3),
.last 25 (5,true)
])
theorem kid05_part848_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part848) = true := by rfl

def kid05_part849 : Audit := .split 12 (2,true) (byMove [
.cycle 0 37 true (-2),
.cycle 10 3 false (0),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.last 39 (5,true),
.last 13 (5,true),
.cycle 0 32 true (-1),
.cycle 0 27 true (-1),
.cycle 0 15 true (-1),
.cycle 0 29 true (-2),
.cycle 0 17 true (-1),
.cycle 8 5 false (2),
.cycle 7 19 false (3),
.cycle 10 3 false (0),
.cycle 0 21 true (-2),
.cycle 0 19 true (-1),
.cycle 13 13 false (0),
.last 13 (5,true),
.last 24 (5,true),
.cycle 25 5 false (1),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 19 (5,true),
.last 15 (5,true)
])
theorem kid05_part849_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part849) = true := by rfl

def kid05_part850 : Audit := .split 15 (2,true) (byMove [
.cycle 1 20 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 1 32 false (3),
.cycle 8 16 false (2),
.cycle 0 30 true (-1),
.cycle 0 19 true (-1),
.cycle 18 1 false (4),
.cycle 0 17 true (-1),
.cycle 0 22 true (-1),
.last 16 (5,true),
.cycle 13 3 false (2),
.cycle 0 28 true (-1),
.cycle 0 32 true (-1),
.cycle 16 1 false (0),
.cycle 0 34 true (-1),
.cycle 0 28 true (-2),
.cycle 1 17 true (-1),
.cycle 14 2 true (1),
.cycle 2 15 true (-1),
.cycle 0 17 true (-1),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part850_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part850) = true := by rfl

def kid05_part851 : Audit := .cycle 11 1 false (-1)
theorem kid05_part851_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part851) = true := by rfl

def kid05_part852 : Audit := .cycle 7 10 false (3)
theorem kid05_part852_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part852) = true := by rfl

def kid05_part853 : Audit := .proven (BB6.Agent11Raw39B0REPumps.M172.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M172.never m hm)
theorem kid05_part853_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part853) = true := by rfl

def kid05_part854 : Audit := .cycle 0 13 true (0)
theorem kid05_part854_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part854) = true := by rfl

def kid05_part855 : Audit := .split 12 (2,true) (byMove [
.cycle 1 14 true (0),
.cycle 1 13 true (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 0 25 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 1 13 true (0),
.cycle 8 5 true (0),
.last 40 (5,true),
.cycle 1 14 true (0),
.cycle 0 24 true (-1),
.cycle 0 28 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 0 29 true (0),
.cycle 1 14 true (0),
.last 15 (5,true)
])
theorem kid05_part855_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part855) = true := by rfl

def kid05_part856 : Audit := .cycle 0 13 true (0)
theorem kid05_part856_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part856) = true := by rfl

def kid05_part857 : Audit := .cycle 0 20 true (-1)
theorem kid05_part857_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part857) = true := by rfl

def kid05_part858 : Audit := .cycle 9 2 true (0)
theorem kid05_part858_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part858) = true := by rfl

def kid05_part859 : Audit := .split 20 (5,true) (byMove [
.cycle 7 27 false (3),
.cycle 21 17 true (-2),
.last 21 (2,true),
.last 53 (2,true),
.cycle 1 23 false (3),
.cycle 8 15 false (2),
.cycle 18 63 true (0),
.last 53 (2,true),
.cycle 74 104 true (0),
.cycle 7 23 false (3),
.cycle 85 46 true (-1),
.last 72 (2,true),
.cycle 7 17 false (3),
.cycle 19 2 true (1),
.last 21 (2,true),
.cycle 51 15 false (2),
.cycle 21 9 true (-2),
.cycle 8 15 false (2),
.cycle 18 17 true (0),
.last 35 (2,true),
.cycle 81 42 true (-1),
.proven (BB6.Agent11Raw39B0REPumps.M173.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M173.never m hm),
.cycle 7 27 false (3),
.cycle 7 21 false (3)
])
theorem kid05_part859_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part859) = true := by rfl

def kid05_part835 : Audit := .split 10 (1,true) (byMove [(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851),(kid05_part852),(kid05_part853),(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857),(kid05_part858),(kid05_part859)])

theorem kid05_part835_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part835) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part836),(kid05_part837),(kid05_part838),(kid05_part839),(kid05_part840),(kid05_part841),(kid05_part842),(kid05_part843),(kid05_part844),(kid05_part845),(kid05_part846),(kid05_part847),(kid05_part848),(kid05_part849),(kid05_part850),(kid05_part851),(kid05_part852),(kid05_part853),(kid05_part854),(kid05_part855),(kid05_part856),(kid05_part857),(kid05_part858),(kid05_part859)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part840_checked

  · exact kid05_part846_checked

  · exact kid05_part852_checked

  · exact kid05_part858_checked

  · exact kid05_part841_checked

  · exact kid05_part847_checked

  · exact kid05_part853_checked

  · exact kid05_part859_checked

def kid05_part860 : Audit := .split 10 (2,true) (byMove [
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 12 1 false (0),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.split 12 (1,true) (byMove [
.cycle 16 1 false (2),
.cycle 24 1 false (0),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 31 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 23 1 false (1),
.cycle 8 5 true (0),
.cycle 18 1 false (0),
.cycle 28 1 false (0),
.cycle 17 1 false (3),
.cycle 17 1 false (3),
.cycle 17 1 false (-1),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 27 1 false (1),
.cycle 0 15 true (0),
.last 15 (5,true)
]),
.cycle 31 1 false (1),
.cycle 0 13 true (0),
.cycle 11 1 false (1),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.split 12 (1,true) (byMove [
.cycle 16 1 false (0),
.cycle 24 1 false (-2),
.cycle 10 3 false (0),
.cycle 24 1 false (-2),
.cycle 17 1 false (-3),
.last 13 (5,true),
.cycle 0 15 true (-1),
.cycle 6 9 false (3),
.cycle 0 15 true (-1),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.cycle 8 5 false (2),
.cycle 18 1 false (-2),
.cycle 21 1 false (-3),
.cycle 10 3 false (0),
.cycle 17 1 false (1),
.cycle 17 1 false (-3),
.last 13 (5,true),
.last 30 (5,true),
.last 19 (5,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.cycle 20 1 false (-2),
.last 15 (5,true)
]),
.split 13 (1,true) (byMove [
.cycle 21 1 false (-1),
.cycle 38 1 false (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.cycle 17 1 false (1),
.cycle 29 1 false (3),
.cycle 10 4 true (-1),
.cycle 25 1 false (1),
.cycle 18 1 false (-2),
.last 14 (5,true),
.cycle 21 1 false (-3),
.cycle 11 3 false (0),
.cycle 19 1 false (1),
.cycle 14 1 false (-2),
.cycle 16 1 false (-2),
.cycle 17 1 false (-3),
.cycle 25 1 false (-1),
.cycle 12 16 true (-1),
.cycle 12 2 true (-1),
.cycle 39 1 false (-1),
.last 15 (5,true),
.last 14 (5,true)
]),
.split 14 (1,true) (byMove [
.cycle 18 1 false (2),
.cycle 26 1 false (0),
.cycle 0 18 true (-1),
.cycle 0 16 true (-1),
.cycle 19 1 false (-1),
.last 15 (5,true),
.cycle 0 15 true (-1),
.cycle 33 1 false (1),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 25 1 false (1),
.cycle 8 7 true (-1),
.cycle 20 1 false (0),
.cycle 26 1 false (0),
.cycle 21 1 false (3),
.cycle 19 1 false (3),
.cycle 19 1 false (-1),
.last 15 (5,true),
.cycle 35 1 false (1),
.cycle 31 1 false (3),
.cycle 2 13 true (-1),
.cycle 29 1 false (1),
.cycle 23 1 false (3),
.last 17 (5,true)
]),
.cycle 11 1 false (-1),
.cycle 13 1 false (-1),
.cycle 14 1 false (-2),
.split 12 (1,true) (byMove [
.cycle 24 1 false (0),
.cycle 25 1 false (-1),
.cycle 0 14 true (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 0 35 true (0),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 2 12 true (0),
.cycle 8 5 true (0),
.cycle 20 1 false (-2),
.last 21 (5,true),
.cycle 2 14 true (0),
.cycle 26 1 false (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 4 25 true (0),
.cycle 0 15 true (0),
.last 15 (5,true)
]),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (0),
.cycle 16 1 false (-2)
])
theorem kid05_part860_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part860) = true := by rfl

def kid05_part861 : Audit := .split 12 (1,true) (byMove [
.cycle 15 1 false (1),
.cycle 23 1 false (-1),
.split 13 (2,true) (byMove [
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 11 3 false (2),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (2),
.cycle 0 16 true (0),
.cycle 18 1 false (-2)
]),
.cycle 0 14 true (0),
.cycle 16 1 false (-2),
.split 13 (5,true) (byMove [
.cycle 0 14 true (0),
.cycle 23 1 false (-1),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 23 1 false (1),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 15 1 false (1),
.cycle 16 1 false (0),
.cycle 11 3 false (2),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 22 1 false (0),
.cycle 18 1 false (2),
.cycle 0 16 true (0),
.cycle 18 1 false (-2)
]),
.cycle 0 13 true (0),
.cycle 26 1 false (2),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (2),
.cycle 8 5 true (0),
.cycle 17 1 false (-1),
.split 15 (2,true) (byMove [
.cycle 18 1 false (0),
.cycle 13 3 false (1),
.cycle 18 1 false (0),
.cycle 10 6 true (0),
.cycle 19 1 false (-3),
.last 16 (5,true),
.cycle 25 1 false (-1),
.cycle 39 1 false (-1),
.cycle 27 1 false (-1),
.cycle 0 17 true (0),
.cycle 21 1 false (-3),
.last 16 (5,true),
.cycle 20 1 false (-2),
.cycle 13 3 false (1),
.cycle 23 1 false (-1),
.cycle 21 1 false (-1),
.cycle 19 1 false (-3),
.last 16 (5,true),
.cycle 29 1 false (-1),
.cycle 12 5 false (2),
.cycle 2 15 true (0),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
]),
.split 13 (2,true) (byMove [
.cycle 23 1 false (1),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 1 false (2),
.cycle 0 17 true (0),
.cycle 16 1 false (4),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.last 14 (5,true),
.cycle 11 3 false (2),
.cycle 23 1 false (-1),
.cycle 18 1 false (2),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 20 1 false (2),
.cycle 12 2 true (1),
.cycle 2 13 true (0),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 16 1 false (2),
.cycle 16 1 false (-2),
.split 13 (5,true) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 16 1 false (2),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 1 false (-1),
.cycle 17 1 false (1),
.cycle 11 3 false (2),
.last 15 (2,true),
.cycle 18 1 false (2),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 16 1 false (-2),
.cycle 20 1 false (2),
.cycle 12 2 true (1),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 0 18 true (0),
.cycle 22 1 false (-2)
]),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 24 1 false (0),
.cycle 0 15 true (0),
.split 15 (5,true) (byMove [
.cycle 0 20 true (0),
.cycle 25 1 false (-1),
.cycle 17 1 false (1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 5 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 17 1 false (1),
.cycle 18 1 false (0),
.cycle 11 5 false (3),
.last 17 (2,true),
.cycle 10 7 true (0),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 11 5 true (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 22 1 false (0),
.cycle 9 7 true (0),
.cycle 20 1 false (-2)
])
])
theorem kid05_part861_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part861) = true := by rfl

def kid05_part862 : Audit := .cycle 12 1 false (-2)
theorem kid05_part862_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part862) = true := by rfl

def kid05_part864 : Audit := .cycle 0 15 true (-1)
theorem kid05_part864_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part864) = true := by rfl

def kid05_part865 : Audit := .cycle 18 2 false (0)
theorem kid05_part865_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part865) = true := by rfl

def kid05_part866 : Audit := .cycle 12 1 false (0)
theorem kid05_part866_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part866) = true := by rfl

def kid05_part867 : Audit := .cycle 11 1 false (-1)
theorem kid05_part867_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part867) = true := by rfl

def kid05_part868 : Audit := .cycle 11 2 false (-1)
theorem kid05_part868_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part868) = true := by rfl

def kid05_part869 : Audit := .cycle 11 2 false (-1)
theorem kid05_part869_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part869) = true := by rfl

def kid05_part870 : Audit := .split 12 (1,true) (byMove [
.cycle 14 2 false (2),
.cycle 21 2 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 2 false (0),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.cycle 24 2 false (0),
.cycle 20 2 false (2),
.cycle 18 2 false (2),
.cycle 16 2 false (0),
.cycle 8 5 true (0),
.cycle 15 2 false (1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 15 2 false (3),
.cycle 14 2 false (0),
.cycle 15 2 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 8 9 true (0),
.cycle 0 15 true (0),
.cycle 10 5 true (0)
])
theorem kid05_part870_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part870) = true := by rfl

def kid05_part871 : Audit := .split 12 (2,true) (byMove [
.cycle 14 2 false (2),
.last 13 (1,true),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 14 2 false (0),
.cycle 21 2 false (3),
.cycle 0 13 true (0),
.cycle 24 2 false (0),
.cycle 20 2 false (2),
.cycle 18 2 false (2),
.cycle 16 2 false (0),
.cycle 8 5 true (0),
.cycle 15 2 false (1),
.last 13 (1,true),
.cycle 17 2 false (3),
.cycle 15 2 false (3),
.cycle 14 2 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 8 9 true (0),
.cycle 26 2 false (0),
.cycle 10 5 true (0)
])
theorem kid05_part871_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part871) = true := by rfl

def kid05_part872 : Audit := .cycle 0 13 true (0)
theorem kid05_part872_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part872) = true := by rfl

def kid05_part873 : Audit := .cycle 11 1 false (1)
theorem kid05_part873_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part873) = true := by rfl

def kid05_part874 : Audit := .cycle 11 2 false (1)
theorem kid05_part874_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part874) = true := by rfl

def kid05_part875 : Audit := .cycle 11 2 false (1)
theorem kid05_part875_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part875) = true := by rfl

def kid05_part876 : Audit := .split 12 (1,true) (byMove [
.cycle 14 2 false (0),
.cycle 21 2 false (-1),
.last 13 (2,true),
.last 16 (2,true),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 0 15 true (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 16 2 false (-2),
.cycle 8 5 false (2),
.cycle 15 2 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 15 2 false (1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 33 2 false (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.cycle 17 2 false (-1),
.cycle 10 5 false (1)
])
theorem kid05_part876_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part876) = true := by rfl

def kid05_part877 : Audit := .split 12 (2,true) (byMove [
.cycle 14 2 false (0),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 0 18 true (-1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 14 (1,true),
.cycle 28 2 false (-2),
.cycle 0 15 true (-1),
.cycle 18 2 false (0),
.cycle 16 2 false (-2),
.cycle 8 5 false (2),
.cycle 15 2 false (-1),
.last 13 (1,true),
.cycle 17 2 false (1),
.cycle 15 2 false (1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 14 (1,true),
.last 25 (1,true),
.cycle 0 15 true (-1),
.cycle 4 9 false (3),
.last 15 (1,true),
.cycle 10 5 false (1)
])
theorem kid05_part877_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part877) = true := by rfl

def kid05_part878 : Audit := .split 14 (1,true) (byMove [
.cycle 16 2 false (2),
.cycle 23 2 false (1),
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 16 2 false (0),
.cycle 0 18 true (-1),
.cycle 0 15 true (-1),
.cycle 26 2 false (0),
.cycle 22 2 false (2),
.cycle 20 2 false (2),
.cycle 18 2 false (0),
.cycle 8 7 true (-1),
.cycle 17 2 false (1),
.last 17 (2,true),
.last 15 (2,true),
.cycle 17 2 false (3),
.cycle 16 2 false (0),
.cycle 19 2 false (3),
.last 26 (2,true),
.last 25 (2,true),
.cycle 2 13 true (-1),
.cycle 8 11 true (-1),
.last 17 (2,true),
.cycle 10 7 true (-1)
])
theorem kid05_part878_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part878) = true := by rfl

def kid05_part879 : Audit := .cycle 11 1 false (-1)
theorem kid05_part879_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part879) = true := by rfl

def kid05_part880 : Audit := .cycle 11 2 false (-1)
theorem kid05_part880_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part880) = true := by rfl

def kid05_part881 : Audit := .cycle 11 2 false (-1)
theorem kid05_part881_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part881) = true := by rfl

def kid05_part882 : Audit := .split 12 (1,true) (byMove [
.cycle 17 2 false (-1),
.cycle 22 2 false (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 0 15 true (0),
.cycle 0 14 true (0),
.cycle 0 13 true (0),
.last 28 (2,true),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 10 6 true (0),
.cycle 8 5 true (0),
.cycle 17 2 false (-1),
.last 16 (2,true),
.last 13 (2,true),
.cycle 8 8 true (0),
.cycle 10 4 true (0),
.cycle 10 8 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 8 9 true (0),
.cycle 0 15 true (0),
.cycle 10 5 true (0)
])
theorem kid05_part882_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part882) = true := by rfl

def kid05_part883 : Audit := .split 12 (2,true) (byMove [
.cycle 17 2 false (-1),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.far false 3 ⟨0,[0, 1, 0, 2, 1, 2],[128, 256, 8, 278656, 16384, 128, 8192, 16384, 8, 16400, 16384, 128, 8192, 16384, 512, 16, 16384, 128, 262144],[16, 262144, 2, 1, 16384, 128, 16, 262144, 2, 1, 16384, 8192, 1024, 262144, 128, 64, 16384, 8192, 262144],262414⟩,
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.cycle 10 6 true (0),
.cycle 8 5 true (0),
.cycle 17 2 false (-1),
.last 13 (1,true),
.cycle 19 2 false (1),
.cycle 8 8 true (0),
.cycle 10 4 true (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.cycle 8 9 true (0),
.cycle 1 14 true (0),
.cycle 10 5 true (0)
])
theorem kid05_part883_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part883) = true := by rfl

def kid05_part884 : Audit := .cycle 0 13 true (0)
theorem kid05_part884_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part884) = true := by rfl

def kid05_part885 : Audit := .cycle 15 2 false (1)
theorem kid05_part885_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part885) = true := by rfl

def kid05_part886 : Audit := .cycle 9 2 true (0)
theorem kid05_part886_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part886) = true := by rfl

def kid05_part887 : Audit := .cycle 13 2 false (-1)
theorem kid05_part887_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part887) = true := by rfl

def kid05_part863 : Audit := .split 10 (5,true) (byMove [(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887)])

theorem kid05_part863_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part863) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part864),(kid05_part865),(kid05_part866),(kid05_part867),(kid05_part868),(kid05_part869),(kid05_part870),(kid05_part871),(kid05_part872),(kid05_part873),(kid05_part874),(kid05_part875),(kid05_part876),(kid05_part877),(kid05_part878),(kid05_part879),(kid05_part880),(kid05_part881),(kid05_part882),(kid05_part883),(kid05_part884),(kid05_part885),(kid05_part886),(kid05_part887)] mv))) = true

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

def kid05_part888 : Audit := .cycle 0 12 true (0)
theorem kid05_part888_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part888) = true := by rfl

def kid05_part889 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 25 1 false (3),
.cycle 1 11 true (1),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 37 1 false (9),
.cycle 20 1 false (2),
.cycle 1 11 true (1),
.cycle 8 3 true (1),
.cycle 16 7 false (0),
.split 12 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 8 5 true (1),
.cycle 16 7 false (0),
.cycle 14 3 false (0),
.cycle 16 17 true (-1),
.cycle 1 15 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 16 true (1),
.cycle 1 13 true (1),
.last 15 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 14 true (1),
.cycle 1 11 true (1),
.cycle 13 5 false (1)
])
theorem kid05_part889_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part889) = true := by rfl

def kid05_part890 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 16 1 false (4),
.cycle 24 1 false (2),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 27 1 false (7),
.cycle 20 1 false (2),
.cycle 34 1 false (8),
.cycle 8 3 true (1),
.split 12 (1,true) (byMove [
.cycle 35 1 false (7),
.cycle 13 13 false (1),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 36 (5,true),
.cycle 8 5 true (1),
.cycle 16 7 false (0),
.cycle 13 10 false (1),
.cycle 18 3 false (0),
.cycle 54 1 false (8),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 45 true (1),
.cycle 9 17 true (1),
.last 15 (5,true)
]),
.split 13 (1,true) (byMove [
.cycle 11 10 true (0),
.cycle 0 50 true (-2),
.cycle 19 1 false (-1),
.cycle 0 18 true (0),
.cycle 11 14 true (-3),
.last 14 (5,true),
.cycle 54 1 false (8),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 16 7 false (0),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 3 false (0),
.cycle 41 1 false (5),
.cycle 23 1 false (-1),
.cycle 16 5 false (-1),
.last 14 (5,true),
.last 42 (5,true),
.cycle 1 14 true (1),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 61 1 false (9),
.cycle 9 13 true (1),
.cycle 13 5 false (1)
])
theorem kid05_part890_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part890) = true := by rfl

def kid05_part891 : Audit := .cycle 0 11 true (0)
theorem kid05_part891_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part891) = true := by rfl

def kid05_part892 : Audit := .cycle 12 3 false (0)
theorem kid05_part892_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part892) = true := by rfl

def kid05_part893 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 18 1 false (2),
.cycle 8 4 true (1),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 30 1 false (8),
.cycle 20 1 false (2),
.cycle 8 4 true (1),
.cycle 8 3 true (1),
.split 12 (1,true) (byMove [
.cycle 8 7 true (1),
.cycle 13 13 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 6 true (1),
.cycle 8 5 true (1),
.cycle 16 7 false (0),
.last 16 (2,true),
.last 13 (2,true),
.cycle 8 8 true (1),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.cycle 8 6 true (1),
.cycle 20 5 false (1)
]),
.split 12 (2,true) (byMove [
.cycle 8 7 true (1),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 14 6 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 8 6 true (1),
.cycle 8 5 true (1),
.cycle 16 7 false (0),
.last 13 (1,true),
.cycle 19 10 true (-1),
.cycle 8 8 true (1),
.cycle 14 6 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.cycle 8 6 true (1),
.last 16 (1,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 9 2 true (1),
.cycle 13 3 false (-1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 7 true (1),
.cycle 8 4 true (1),
.cycle 13 5 false (1)
])
theorem kid05_part893_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part893) = true := by rfl

def kid05_part895 : Audit := .cycle 13 4 true (-2)
theorem kid05_part895_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part895) = true := by rfl

def kid05_part896 : Audit := .cycle 10 12 false (1)
theorem kid05_part896_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part896) = true := by rfl

def kid05_part897 : Audit := .split 16 (2,true) (byMove [
.cycle 11 30 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.proven (BB6.Agent11Raw39B0REPumps.M175.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M175.never m hm),
.cycle 18 14 true (0),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.cycle 21 1 false (-3),
.cycle 0 45 true (-3),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.last 37 (5,true),
.last 34 (5,true),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.cycle 11 7 false (1)
])
theorem kid05_part897_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part897) = true := by rfl

def kid05_part898 : Audit := .split 22 (2,true) (byMove [
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 128, 128, 8192, 16384, 8, 16, 16384, 128, 33554432, 67108864, 2097152, 16, 16384, 1073741824, 33554432, 67108864, 2097152, 16512, 1600405632, 1600405632, 33554432, 67108864, 134217728, 1600405632, 1600405632, 1600405632, 1073741824],[16, 2113664, 67125248, 1, 16384, 1073741824, 16, 128, 128, 1, 1073741824, 1073741824, 4194304, 128, 128, 262144, 1073741824, 1073741824, 4194304, 2113664, 67108864, 262144, 1600405632, 1073741824, 268435456, 1600405632, 1600405632, 16777216, 1600405632, 1073741824, 1073741824],2144219200⟩,
.cycle 0 25 true (-2),
.cycle 26 1 false (0),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 128, 128, 8192, 16384, 8, 16, 16384, 128, 33554432, 67108864, 2097152, 16, 16384, 1073741824, 33554432, 67108864, 2097152, 16512, 1600405632, 1600405632, 33554432, 67108864, 134217728, 1600405632, 1600405632, 1600405632, 1073741824],[16, 2113664, 2113664, 1, 16384, 1073741824, 16, 128, 128, 1, 1073741824, 1073741824, 4194304, 128, 128, 262144, 1073741824, 1073741824, 4194304, 2113664, 2113664, 262144, 1600405632, 1073741824, 268435456, 1600405632, 1600405632, 16777216, 1600405632, 1073741824, 1073741824],2144219200⟩,
.last 24 (5,true),
.last 23 (5,true),
.proven (BB6.Agent11Raw39B0REPumps.M178.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M178.never m hm),
.cycle 0 38 true (-2),
.cycle 0 47 true (-2),
.cycle 3 20 true (-2),
.proven (BB6.Agent11Raw39B0REPumps.M179.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M179.never m hm),
.cycle 11 17 false (3),
.cycle 11 15 false (2),
.cycle 0 28 true (-2),
.cycle 0 37 true (-2),
.cycle 0 29 true (-2),
.last 24 (5,true),
.last 23 (5,true),
.last 37 (5,true),
.last 36 (5,true),
.last 89 (5,true),
.cycle 0 30 true (-2),
.last 28 (5,true),
.last 25 (5,true)
])
theorem kid05_part898_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part898) = true := by rfl

def kid05_part899 : Audit := .cycle 11 5 false (1)
theorem kid05_part899_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part899) = true := by rfl

def kid05_part900 : Audit := .split 16 (5,true) (byMove [
.cycle 11 30 false (3),
.cycle 10 12 false (1),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.last 22 (2,true),
.last 18 (2,true),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 13 4 true (-2),
.cycle 12 5 false (0),
.cycle 14 3 false (-1),
.last 18 (2,true),
.last 26 (2,true),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.last 22 (2,true),
.last 18 (2,true),
.cycle 0 35 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.cycle 11 7 false (1)
])
theorem kid05_part900_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part900) = true := by rfl

def kid05_part901 : Audit := .far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 4096, 268435456, 524288, 1048576, 32768, 70368744177680, 4096, 268435456, 128, 256, 134217728, 18295942205673472, 1073741824, 268435456, 137438953472, 274877906944, 8589934592, 268435456, 4096, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 22519097916915712, 4096, 70368744177664, 137438953472, 274877906944, 35184372088832, 4096, 68719476736, 268435456, 562949953421312, 1125899906842624, 549755813888, 22871010357284864, 18295942205673472, 22519097916915712, 8796093022208, 17592186044416, 549755813888, 18297041985736704, 18295942205673472, 22519097916915712, 137438953472, 274877906944, 2251799813685248, 22800641613107200, 18295942205673472, 22519097916915712, 18014398509481984],[16, 1, 18014398509481984, 1, 4096, 18014398509481984, 65536, 4096, 18014398509481984, 4096, 18014398509481984, 18014398509481984, 268435456, 16777216, 18014398509481984, 16777216, 4096, 18014398509481984, 17179869184, 1073741824, 18014398509481984, 1073741824, 18014398509481984, 18014398509481984, 70368744177664, 4398046511104, 18014398509481984, 4398046511104, 4096, 18014398509481984, 70368744177664, 4398046511104, 18014398509481984, 4398046511104, 18014398509481984, 18014398509481984, 1099511627776, 68719476736, 18014398509481984, 68719476736, 18295942205673472, 18014398509481984, 1099511627776, 68719476736, 18014398509481984, 68719476736, 18295942205673472, 18014398509481984, 4503599627370496, 281474976710656, 18014398509481984, 281474976710656, 18295942205673472, 18014398509481984, 18014398509481984],36028753793377090⟩
theorem kid05_part901_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part901) = true := by rfl

def kid05_part902 : Audit := .split 18 (2,true) (byMove [
.cycle 22 12 true (2),
.cycle 19 12 true (1),
.cycle 10 15 false (2),
.cycle 0 20 true (-2),
.cycle 7 12 false (3),
.last 19 (5,true),
.cycle 43 12 true (5),
.cycle 19 12 true (2),
.cycle 10 14 true (-2),
.cycle 19 12 true (0),
.cycle 21 12 true (3),
.cycle 8 11 true (-2),
.cycle 19 12 true (-1),
.cycle 19 12 true (1),
.cycle 25 12 true (3),
.cycle 23 12 true (3),
.cycle 7 12 false (3),
.last 19 (5,true),
.last 33 (5,true),
.last 60 (5,true),
.cycle 2 17 true (-2),
.cycle 24 12 true (4),
.cycle 7 16 false (3),
.last 21 (5,true)
])
theorem kid05_part902_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part902) = true := by rfl

def kid05_part903 : Audit := .split 16 (2,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 0 25 true (-2),
.cycle 9 8 false (1),
.cycle 11 7 false (1),
.cycle 10 14 true (-2),
.cycle 18 12 true (2),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.cycle 10 19 true (-2),
.last 22 (5,true),
.cycle 0 21 true (-2),
.cycle 15 4 true (-1),
.cycle 10 16 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.cycle 11 7 false (1),
.cycle 10 40 true (-4),
.last 32 (5,true),
.cycle 0 19 true (-2),
.cycle 10 27 true (-2),
.cycle 6 12 false (3),
.cycle 11 9 false (1)
])
theorem kid05_part903_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part903) = true := by rfl

def kid05_part904 : Audit := .cycle 0 29 true (-2)
theorem kid05_part904_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part904) = true := by rfl

def kid05_part905 : Audit := .cycle 11 7 false (1)
theorem kid05_part905_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part905) = true := by rfl

def kid05_part906 : Audit := .split 16 (5,true) (byMove [
.cycle 0 21 true (-2),
.cycle 1 16 false (3),
.cycle 10 11 false (1),
.cycle 8 15 false (2),
.cycle 9 8 false (1),
.cycle 11 7 false (1),
.cycle 8 11 true (-2),
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 10 11 false (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 48, 32, 16, 64],[16, 32, 64, 1, 32, 16, 64],64⟩,
.cycle 22 5 true (1),
.cycle 11 13 false (1),
.last 18 (2,true),
.cycle 8 13 true (-2),
.cycle 10 9 false (1),
.cycle 9 8 false (1),
.cycle 11 7 false (1),
.cycle 11 15 false (3),
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 8 24 true (-2),
.cycle 6 12 false (3),
.cycle 11 9 false (1)
])
theorem kid05_part906_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part906) = true := by rfl

def kid05_part907 : Audit := .cycle 10 6 false (1)
theorem kid05_part907_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part907) = true := by rfl

def kid05_part908 : Audit := .split 18 (2,true) (byMove [
.cycle 13 7 false (-1),
.cycle 16 3 false (-2),
.cycle 21 1 false (-3),
.cycle 14 6 true (-3),
.cycle 11 8 false (1),
.last 19 (5,true),
.cycle 6 13 false (3),
.far true 2 ⟨0,[0, 1, 0, 1],[1152, 192, 512, 512, 64, 1024, 128, 128, 128, 512, 64, 1024, 4096],[128, 128, 128, 192, 32, 4096, 1024, 128, 128, 192, 32, 4096, 4096],4096⟩,
.cycle 0 23 true (-3),
.cycle 75 11 false (0),
.cycle 11 10 false (1),
.last 19 (5,true),
.cycle 10 9 false (1),
.cycle 16 3 false (-2),
.cycle 10 12 false (1),
.cycle 10 10 false (1),
.cycle 11 8 false (1),
.last 19 (5,true),
.last 23 (5,true),
.cycle 15 5 false (-1),
.far true 8 ⟨0,[0, 6, 3, 2, 7, 2, 7, 3, 7, 3, 3, 1, 5, 4, 3, 7],[1024, 16777216, 134217728, 549755813888, 68719476736, 1099511627776, 8192, 8192, 4194304, 32768, 4096, 65536, 8192, 8192, 505775362158592, 32768, 4096, 65536, 501377315381248, 505775362158592, 540959734280192, 2097152, 262144, 4194304, 524288, 8388608, 4194304, 2097152, 262144, 4194304, 8388608, 8192, 2097152, 512, 64, 1024, 33554432, 1024, 8192, 134217728, 16777216, 268435456, 501377315381248, 505775362158592, 505775364288512, 35184372088832, 4398046511104, 70368744177664, 281474976710656],[33554432, 137438953472, 16777216, 4096, 32, 281474976710656, 4194304, 8192, 8192, 505775362158592, 8388608, 281474976710656, 70368748371968, 8192, 8192, 4398046773248, 140737488355328, 281474976710656, 501377315381248, 524288, 505775362158592, 505775362158592, 140737488355328, 281474976710656, 1024, 524288, 8388608, 16777216, 140737488355328, 281474976710656, 524288, 128, 8192, 8388608, 8388608, 281474976710656, 1099511627776, 33554432, 1024, 8388608, 34359738368, 281474976710656, 501377315381248, 8796093022208, 505775362158592, 505775362158592, 8388608, 281474976710656, 281474976710656],526736800104754⟩,
.last 54 (5,true),
.last 20 (5,true),
.last 19 (5,true)
])
theorem kid05_part908_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part908) = true := by rfl

def kid05_part909 : Audit := .split 16 (2,true) (byMove [
.cycle 13 13 false (-1),
.cycle 14 42 true (-3),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 10 7 false (1),
.cycle 0 36 true (-2),
.cycle 0 21 true (-2),
.cycle 0 30 true (-2),
.cycle 11 6 false (1),
.last 17 (5,true),
.cycle 14 3 false (-1),
.cycle 10 12 false (1),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 11 9 false (1),
.cycle 15 2 true (-2),
.cycle 0 21 true (-2),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 4096, 268435456, 524288, 1048576, 32768, 70368744177680, 4096, 268435456, 128, 256, 134217728, 18295942205673472, 1073741824, 268435456, 137438953472, 274877906944, 8589934592, 268435456, 4096, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 22519097916915712, 4096, 70368744177664, 137438953472, 274877906944, 35184372088832, 4096, 68719476736, 268435456, 562949953421312, 1125899906842624, 549755813888, 22871010357284864, 18295942205673472, 22519097916915712, 8796093022208, 17592186044416, 549755813888, 18297041985736704, 18295942205673472, 22519097916915712, 137438953472, 274877906944, 2251799813685248, 22800641613107200, 18295942205673472, 22519097916915712, 18014398509481984],[16, 1, 512, 1, 4096, 18014398509481984, 65536, 4096, 2097152, 4096, 18014398509481984, 18014398509481984, 268435456, 16777216, 512, 16777216, 4096, 18014398509481984, 17179869184, 1073741824, 549755813888, 1073741824, 18014398509481984, 18014398509481984, 70368744177664, 4398046511104, 35184372088832, 4398046511104, 4096, 18014398509481984, 70368744177664, 4398046511104, 549755813888, 4398046511104, 18014398509481984, 18014398509481984, 1099511627776, 68719476736, 2251799813685248, 68719476736, 18295942205673472, 18014398509481984, 1099511627776, 68719476736, 35184372088832, 68719476736, 18295942205673472, 18014398509481984, 4503599627370496, 281474976710656, 549755813888, 281474976710656, 18295942205673472, 18014398509481984, 18014398509481984],36028753793377090⟩,
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part909_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part909) = true := by rfl

def kid05_part910 : Audit := .cycle 10 7 false (1)
theorem kid05_part910_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part910) = true := by rfl

def kid05_part911 : Audit := .cycle 11 5 false (1)
theorem kid05_part911_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part911) = true := by rfl

def kid05_part912 : Audit := .split 16 (5,true) (byMove [
.last 19 (2,true),
.cycle 46 36 false (5),
.cycle 18 1 false (-2),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 10 7 false (1),
.cycle 12 6 false (0),
.last 17 (2,true),
.cycle 0 30 true (-2),
.cycle 11 6 false (1),
.cycle 24 7 true (0),
.cycle 14 3 false (-1),
.last 18 (2,true),
.cycle 10 9 false (1),
.cycle 17 1 false (-3),
.cycle 13 4 false (-1),
.cycle 12 5 false (0),
.cycle 11 9 false (1),
.cycle 15 2 true (-2),
.last 17 (2,true),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 4096, 268435456, 524288, 1048576, 32768, 70368744177680, 4096, 268435456, 128, 256, 134217728, 26843417020469376, 1073741824, 268435456, 137438953472, 274877906944, 8589934592, 268435456, 4096, 26843417020469376, 8796093022208, 17592186044416, 35184372088832, 26843417020469376, 4096, 70368744177664, 137438953472, 274877906944, 35184372088832, 4096, 26843417020469376, 268435456, 562949953421312, 1125899906842624, 549755813888, 26843417020469376, 26843417020469376, 26843417020469376, 8796093022208, 17592186044416, 549755813888, 26843417020469376, 26843417020469376, 26843417020469376, 137438953472, 274877906944, 2251799813685248, 26843417020469376, 26843417020469376, 26843417020469376, 18014398509481984],[16, 4096, 18014398509481984, 1, 4096, 512, 65536, 4096, 18014398509481984, 4096, 70368744177680, 2097152, 268435456, 4096, 18014398509481984, 16777216, 4096, 512, 17179869184, 1073741824, 18014398509481984, 1073741824, 268435456, 549755813888, 70368744177664, 4096, 18014398509481984, 4398046511104, 4096, 35184372088832, 70368744177664, 26843417020469376, 18014398509481984, 4398046511104, 26843417020469376, 549755813888, 1099511627776, 26843417020469376, 18014398509481984, 68719476736, 26843417020469376, 2251799813685248, 1099511627776, 26843417020469376, 18014398509481984, 68719476736, 26843417020469376, 35184372088832, 4503599627370496, 26843417020469376, 18014398509481984, 281474976710656, 26843417020469376, 549755813888, 18014398509481984],36028753793377090⟩,
.cycle 9 10 false (1),
.cycle 11 15 false (1)
])
theorem kid05_part912_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part912) = true := by rfl

def kid05_part913 : Audit := .split 38 (5,true) (byMove [
.cycle 22 23 true (1),
.last 42 (2,true),
.last 39 (2,true),
.last 42 (2,true),
.last 66 (2,true),
.last 84 (2,true),
.cycle 22 19 true (2),
.last 40 (2,true),
.cycle 22 19 true (2),
.cycle 51 1 false (-1),
.cycle 13 26 true (-2),
.cycle 34 47 false (5),
.last 58 (2,true),
.cycle 13 28 true (-2),
.last 39 (2,true),
.cycle 13 28 true (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 17, 1, 16, 64],[16, 1, 64, 1, 1, 16, 64],64⟩,
.cycle 42 9 false (-2),
.cycle 22 19 true (2),
.last 40 (2,true),
.cycle 22 19 true (2),
.last 74 (2,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 17, 1, 16, 64],[16, 1, 64, 1, 1, 16, 64],64⟩,
.cycle 42 21 false (2)
])
theorem kid05_part913_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part913) = true := by rfl

def kid05_part914 : Audit := .split 18 (2,true) (byMove [
.last 36 (5,true),
.last 33 (5,true),
.cycle 24 1 false (-2),
.last 38 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 37 (5,true),
.last 44 (5,true),
.last 32 (5,true),
.last 30 (5,true),
.last 35 (5,true),
.last 25 (5,true),
.last 23 (5,true),
.last 34 (5,true),
.cycle 10 15 false (2),
.last 39 (5,true),
.last 20 (5,true),
.last 19 (5,true),
.last 33 (5,true),
.last 32 (5,true),
.last 31 (5,true),
.last 40 (5,true),
.last 24 (5,true),
.last 21 (5,true)
])
theorem kid05_part914_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part914) = true := by rfl

def kid05_part915 : Audit := .split 16 (2,true) (byMove [
.cycle 0 23 true (-2),
.cycle 2 16 false (3),
.cycle 20 1 false (-2),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 1048576, 128, 524288, 1048576, 32768, 70368744177680, 1048576, 128, 128, 256, 134217728, 26843416752029824, 274877906944, 128, 137438953472, 274877906944, 8589934592, 268435456, 1048576, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 26843416752029824, 1048576, 26843416752029824, 137438953472, 274877906944, 35184372088832, 1048576, 1125899906842624, 128, 562949953421312, 1125899906842624, 549755813888, 26843416752029824, 26843416752029824, 26843416752029824, 8796093022208, 17592186044416, 549755813888, 26843416752029824, 26843416752029824, 26843416752029824, 137438953472, 274877906944, 2251799813685248, 26843416752029824, 26843416752029824, 26843416752029824, 18014398509481984],[16, 256, 0, 1, 1048576, 18014398509481984, 65536, 1048576, 8796093022336, 4096, 18014398509481984, 18014398509481984, 268435456, 256, 26843416752029824, 16777216, 1048576, 18014398509481984, 17179869184, 274877906944, 128, 1073741824, 18014398509481984, 18014398509481984, 70368744177664, 17592186044416, 26843416752029824, 4398046511104, 1048576, 18014398509481984, 70368744177664, 274877906944, 1048576, 4398046511104, 18014398509481984, 18014398509481984, 1099511627776, 1125899906842624, 26843416752029824, 68719476736, 26843416752029824, 18014398509481984, 1099511627776, 17592186044416, 26843416752029824, 68719476736, 26843416752029824, 18014398509481984, 4503599627370496, 274877906944, 26843416752029824, 281474976710656, 26843416752029824, 18014398509481984, 18014398509481984],36028753793377090⟩,
.last 18 (5,true),
.last 17 (5,true),
.last 79 (5,true),
.cycle 18 12 true (2),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.last 36 (5,true),
.cycle 11 11 false (1),
.cycle 11 9 false (1),
.cycle 15 2 true (-1),
.cycle 10 11 false (1),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 3, 2, 2],[268436480, 4160, 512, 512, 64, 1024, 268436480, 4160, 268436480, 512, 64, 1024, 268436480, 1082527808, 402654720, 134217728, 16777216, 268435456, 1346372608, 1082527808, 1348502528, 2097152, 262144, 4194304, 1346372608, 4160, 1346372608, 32768, 4096, 65536, 1073741824],[268436480, 4160, 512, 4160, 32, 1073741824, 268436480, 4160, 512, 4160, 131072, 1073741824, 268436480, 1082527808, 134217728, 1074008128, 8388608, 1073741824, 1346372608, 1082527808, 2097152, 1074008128, 8388608, 1073741824, 4194304, 4160, 32768, 4160, 131072, 1073741824, 1073741824],1708990464⟩,
.last 18 (5,true),
.last 17 (5,true),
.last 31 (5,true),
.last 32 (5,true),
.cycle 0 19 true (-2),
.cycle 11 15 false (2),
.last 22 (5,true),
.last 19 (5,true)
])
theorem kid05_part915_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part915) = true := by rfl

def kid05_part916 : Audit := .cycle 17 6 true (1)
theorem kid05_part916_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part916) = true := by rfl

def kid05_part917 : Audit := .split 17 (5,true) (byMove [
.cycle 11 15 false (1),
.cycle 9 10 false (1),
.last 18 (2,true),
.cycle 0 23 true (-2),
.cycle 11 7 false (1),
.cycle 12 7 false (0),
.last 20 (2,true),
.cycle 0 21 true (-2),
.cycle 10 13 false (1),
.cycle 10 11 false (1),
.cycle 13 14 true (-2),
.cycle 8 10 false (2),
.cycle 10 8 false (1),
.last 22 (2,true),
.last 18 (2,true),
.cycle 11 16 false (1),
.cycle 11 7 false (1),
.cycle 12 7 false (0),
.last 20 (2,true),
.cycle 0 21 true (-2),
.cycle 2 16 false (3),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 16, 16, 16, 64],[16, 16, 64, 1, 16, 8, 64],64⟩,
.cycle 11 11 false (1),
.cycle 11 11 false (1)
])
theorem kid05_part917_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part917) = true := by rfl

def kid05_part918 : Audit := .split 16 (5,true) (byMove [
.cycle 16 39 false (2),
.cycle 10 16 false (1),
.last 17 (2,true),
.last 20 (2,true),
.cycle 17 6 false (-1),
.cycle 12 7 false (0),
.cycle 16 5 true (0),
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 3 14 false (3),
.cycle 16 10 true (0),
.cycle 11 11 false (1),
.cycle 11 9 false (1),
.cycle 15 2 true (-1),
.last 17 (2,true),
.cycle 4 44 false (4),
.cycle 13 6 false (0),
.cycle 12 7 false (0),
.cycle 16 5 true (0),
.last 18 (2,true),
.cycle 0 19 true (-2),
.cycle 11 15 false (2),
.cycle 9 14 false (1),
.cycle 11 13 false (1)
])
theorem kid05_part918_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part918) = true := by rfl

def kid05_part894 : Audit := .split 15 (1,true) (byMove [(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904),(kid05_part905),(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917),(kid05_part918)])

theorem kid05_part894_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part894) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) 15 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part895),(kid05_part896),(kid05_part897),(kid05_part898),(kid05_part899),(kid05_part900),(kid05_part901),(kid05_part902),(kid05_part903),(kid05_part904),(kid05_part905),(kid05_part906),(kid05_part907),(kid05_part908),(kid05_part909),(kid05_part910),(kid05_part911),(kid05_part912),(kid05_part913),(kid05_part914),(kid05_part915),(kid05_part916),(kid05_part917),(kid05_part918)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part900_checked

  · exact kid05_part906_checked

  · exact kid05_part912_checked

  · exact kid05_part918_checked

def kid05_part920 : Audit := .split 13 (2,true) (byMove [
.cycle 12 4 true (0),
.cycle 0 20 false (3),
.cycle 17 1 false (-1),
.cycle 0 22 true (-1),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 18 true (-1),
.cycle 12 31 true (0),
.cycle 0 50 true (-2),
.cycle 0 15 true (-1),
.last 17 (5,true),
.last 14 (5,true),
.cycle 17 6 false (-1),
.cycle 10 9 false (1),
.cycle 14 9 false (1),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true),
.last 37 (5,true),
.cycle 12 24 true (0),
.cycle 13 15 true (0),
.cycle 0 15 true (-1),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part920_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part920) = true := by rfl

def kid05_part921 : Audit := .split 17 (2,true) (byMove [
.cycle 14 4 true (2),
.cycle 31 12 false (0),
.cycle 32 1 false (-2),
.cycle 0 19 true (-1),
.cycle 7 11 false (3),
.last 18 (5,true),
.cycle 0 18 true (-1),
.cycle 98 95 false (4),
.cycle 0 32 true (-1),
.cycle 0 28 true (-1),
.cycle 15 3 true (2),
.cycle 8 10 true (-1),
.cycle 27 6 false (-1),
.cycle 0 22 true (-1),
.cycle 12 7 true (0),
.cycle 13 5 true (1),
.cycle 7 11 false (3),
.last 18 (5,true),
.cycle 137 94 false (5),
.cycle 41 14 false (1),
.cycle 2 16 true (-1),
.cycle 13 6 true (1),
.last 33 (5,true),
.last 20 (5,true)
])
theorem kid05_part921_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part921) = true := by rfl

def kid05_part922 : Audit := .cycle 12 1 false (0)
theorem kid05_part922_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part922) = true := by rfl

def kid05_part923 : Audit := .cycle 11 1 false (-1)
theorem kid05_part923_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part923) = true := by rfl

def kid05_part924 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 23 8 false (-1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 109 (5,true),
.cycle 42 77 false (0),
.cycle 0 34 true (-2),
.cycle 7 19 false (3),
.last 20 (5,true),
.cycle 8 6 false (2),
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 18 9 false (1),
.cycle 16 7 false (1),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 17 (5,true),
.last 18 (5,true),
.cycle 2 18 true (-2),
.cycle 4 10 false (3),
.last 22 (5,true),
.last 16 (5,true)
])
theorem kid05_part924_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part924) = true := by rfl

def kid05_part925 : Audit := .split 14 (2,true) (byMove [
.cycle 12 4 true (-3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.last 18 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 4, 3, 2, 2, 1],[131072, 301990016, 512, 512, 128, 1024, 1073741824, 131072, 1073873024, 512, 128, 1024, 1073741824, 1073872896, 1073742464, 134217728, 33554432, 268435456, 1073872896, 1375862912, 134218240, 32768, 8192, 65536, 1073741824, 1073872896, 1073741952, 512, 128, 1024, 1073741824],[131072, 32, 268435456, 268435456, 32, 1073741824, 268436480, 131072, 301990016, 301990016, 131072, 1073741824, 196608, 8388608, 1342177280, 1342177280, 8388608, 1073741824, 1073872896, 8388608, 1342177280, 1342177280, 8388608, 1073741824, 65536, 131072, 301989888, 301989888, 131072, 1073741824, 1073741824],1204646210⟩,
.cycle 11 7 false (-1),
.cycle 0 36 true (-3),
.last 18 (5,true),
.cycle 11 7 false (-1),
.last 15 (5,true),
.cycle 11 6 false (-1),
.cycle 10 5 false (0),
.cycle 11 9 false (-1),
.cycle 11 7 false (-1),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 23 (5,true),
.last 16 (5,true),
.last 34 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid05_part925_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part925) = true := by rfl

def kid05_part926 : Audit := .split 16 (2,true) (byMove [
.cycle 14 4 true (-1),
.cycle 0 20 true (-1),
.cycle 19 1 false (-1),
.cycle 0 20 true (-1),
.cycle 12 5 false (2),
.last 17 (5,true),
.cycle 0 21 true (-1),
.cycle 0 18 true (-1),
.cycle 0 51 true (-2),
.cycle 0 18 true (-1),
.cycle 12 7 false (2),
.last 17 (5,true),
.cycle 11 6 false (2),
.cycle 10 7 false (2),
.cycle 11 9 false (2),
.cycle 11 7 false (2),
.cycle 12 5 false (2),
.last 17 (5,true),
.cycle 6 41 false (6),
.cycle 0 18 true (-1),
.cycle 6 21 false (3),
.cycle 0 18 true (-1),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part926_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part926) = true := by rfl

def kid05_part927 : Audit := .split 23 (2,true) (byMove [
.cycle 21 4 true (2),
.cycle 12 15 true (2),
.cycle 26 1 false (2),
.cycle 12 14 true (2),
.cycle 19 5 false (5),
.last 24 (5,true),
.cycle 0 28 true (0),
.cycle 12 12 true (2),
.cycle 0 58 true (0),
.cycle 0 25 true (0),
.cycle 19 7 false (5),
.last 24 (5,true),
.cycle 18 6 false (5),
.cycle 10 14 true (0),
.cycle 17 9 false (5),
.cycle 17 7 false (5),
.cycle 19 5 false (5),
.last 24 (5,true),
.cycle 0 28 true (0),
.cycle 12 12 true (2),
.cycle 2 23 true (0),
.cycle 0 25 true (0),
.last 25 (5,true),
.last 24 (5,true)
])
theorem kid05_part927_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part927) = true := by rfl

def kid05_part928 : Audit := .split 11 (2,true) (byMove [
.cycle 13 4 true (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 5 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 14 1 false (4),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 12 7 false (2),
.last 12 (5,true),
.cycle 0 35 true (0),
.cycle 10 4 true (0),
.cycle 11 7 true (0),
.cycle 12 1 false (0),
.cycle 12 5 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 0 27 true (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part928_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part928) = true := by rfl

def kid05_part929 : Audit := .split 15 (2,true) (byMove [
.cycle 12 4 true (2),
.cycle 17 1 false (3),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 13 5 false (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 39 11 false (7),
.cycle 0 30 true (0),
.cycle 0 26 true (0),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 13 6 false (3),
.cycle 0 18 true (0),
.cycle 11 7 true (1),
.cycle 11 5 true (1),
.cycle 13 5 false (3),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.cycle 0 19 true (0),
.last 18 (5,true)
])
theorem kid05_part929_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part929) = true := by rfl

def kid05_part930 : Audit := .split 15 (2,true) (byMove [
.cycle 13 4 true (-2),
.cycle 13 4 true (-2),
.cycle 18 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 144, 128, 16, 8192, 16384, 8, 16, 128, 16, 33554432, 67108864, 2097152, 16, 128, 1073741824, 33554432, 67108864, 2097152, 144, 1600405648, 1600405648, 33554432, 67108864, 134217728, 1600405648, 1600405648, 1600405648, 1073741824],[16, 16, 16512, 1, 128, 1073741824, 16, 16, 128, 1, 1073741824, 1073741824, 4194304, 4194304, 128, 262144, 1073741824, 1073741824, 4194304, 4194304, 16512, 262144, 1600405648, 1073741824, 268435456, 268435456, 1600405648, 16777216, 1600405648, 1073741824, 1073741824],2144219200⟩,
.cycle 11 5 false (1),
.last 16 (5,true),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 4096, 268435456, 524288, 1048576, 32768, 70368744177680, 4096, 268435456, 128, 256, 134217728, 18295942205673472, 1073741824, 268435456, 137438953472, 274877906944, 8589934592, 268435456, 4096, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 22519097916915712, 4096, 70368744177664, 137438953472, 274877906944, 35184372088832, 4096, 68719476736, 268435456, 562949953421312, 1125899906842624, 549755813888, 22871010357284864, 18295942205673472, 22519097916915712, 8796093022208, 17592186044416, 549755813888, 18297041985736704, 18295942205673472, 22519097916915712, 137438953472, 274877906944, 2251799813685248, 22800641613107200, 18295942205673472, 22519097916915712, 18014398509481984],[16, 16, 1, 1, 4096, 18014398509481984, 65536, 65536, 4096, 4096, 18014398509481984, 18014398509481984, 268435456, 268435456, 16777216, 16777216, 4096, 18014398509481984, 17179869184, 17179869184, 1073741824, 1073741824, 18014398509481984, 18014398509481984, 70368744177664, 70368744177664, 4398046511104, 4398046511104, 4096, 18014398509481984, 70368744177664, 70368744177664, 4398046511104, 4398046511104, 18014398509481984, 18014398509481984, 1099511627776, 1099511627776, 68719476736, 68719476736, 18295942205673472, 18014398509481984, 1099511627776, 1099511627776, 68719476736, 68719476736, 18295942205673472, 18014398509481984, 4503599627370496, 4503599627370496, 281474976710656, 281474976710656, 18295942205673472, 18014398509481984, 18014398509481984],36028753793377090⟩,
.cycle 17 15 true (0),
.cycle 0 19 true (-2),
.cycle 3 19 true (-2),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 11 6 false (1),
.cycle 10 6 false (1),
.cycle 11 9 false (1),
.cycle 11 7 false (1),
.cycle 11 5 false (1),
.last 16 (5,true),
.last 38 (5,true),
.last 37 (5,true),
.cycle 0 19 true (-2),
.cycle 19 6 true (2),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part930_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part930) = true := by rfl

def kid05_part931 : Audit := .split 11 (5,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 14 (2,true),
.last 15 (2,true),
.last 15 (2,true),
.last 16 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.last 16 (2,true),
.last 16 (2,true),
.cycle 8 9 true (0),
.last 13 (2,true),
.last 17 (2,true),
.cycle 12 1 false (0),
.last 14 (2,true),
.last 15 (2,true),
.last 15 (2,true),
.cycle 8 5 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 3 true (1),
.last 21 (2,true)
])
theorem kid05_part931_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part931) = true := by rfl

def kid05_part932 : Audit := .split 18 (2,true) (byMove [
.cycle 16 4 true (-3),
.cycle 10 9 false (0),
.cycle 21 1 false (-3),
.cycle 11 9 false (0),
.cycle 14 5 false (0),
.last 19 (5,true),
.far true 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 2, 4, 3],[8519744, 74880, 512, 512, 128, 1024, 66560, 8519744, 1082328256, 512, 128, 1024, 1086522432, 1082328128, 1082328768, 512, 128, 1024, 1086522432, 1082336448, 1082328768, 32768, 8192, 65536, 1082328128, 1082336448, 33280, 2097152, 524288, 4194304, 1073741824],[8519744, 64, 66560, 66560, 32, 1073741824, 66560, 64, 74880, 74880, 131072, 1073741824, 12714048, 64, 74880, 74880, 8388608, 1073741824, 12714048, 4096, 1082336448, 1082336448, 536870912, 1073741824, 1082336448, 262144, 1073816704, 1073816704, 536870912, 1073741824, 1073741824],1935438082⟩,
.cycle 14 11 false (0),
.cycle 0 40 true (-3),
.last 118 (5,true),
.cycle 14 7 false (0),
.last 19 (5,true),
.cycle 13 6 false (0),
.cycle 10 9 false (0),
.cycle 13 9 false (0),
.cycle 13 7 false (0),
.cycle 14 5 false (0),
.last 19 (5,true),
.last 27 (5,true),
.cycle 14 9 false (0),
.last 97 (5,true),
.cycle 12 14 false (1),
.last 20 (5,true),
.last 19 (5,true)
])
theorem kid05_part932_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part932) = true := by rfl

def kid05_part933 : Audit := .split 12 (2,true) (byMove [
.cycle 11 4 true (-1),
.cycle 10 3 false (0),
.cycle 15 1 false (-1),
.cycle 10 6 true (-1),
.cycle 11 5 false (0),
.last 13 (5,true),
.cycle 6 7 false (3),
.cycle 14 14 true (0),
.cycle 0 71 true (-2),
.cycle 0 28 true (-1),
.cycle 11 7 false (1),
.last 13 (5,true),
.cycle 11 6 false (0),
.cycle 10 3 false (0),
.cycle 11 9 false (1),
.cycle 11 7 false (1),
.cycle 11 5 false (0),
.last 13 (5,true),
.last 17 (5,true),
.cycle 10 5 false (1),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[18, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 13 6 true (1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part933_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part933) = true := by rfl

def kid05_part934 : Audit := .split 18 (2,true) (byMove [
.cycle 16 4 true (-1),
.cycle 0 28 true (-2),
.cycle 21 1 false (-1),
.cycle 23 1 false (-1),
.cycle 14 5 false (2),
.last 19 (5,true),
.cycle 0 23 true (-1),
.cycle 0 22 true (-1),
.cycle 0 53 true (-2),
.cycle 0 20 true (-1),
.cycle 14 7 false (2),
.last 19 (5,true),
.cycle 13 6 false (2),
.cycle 10 9 false (2),
.cycle 11 9 false (2),
.cycle 12 7 false (2),
.cycle 14 5 false (2),
.last 19 (5,true),
.last 39 (5,true),
.cycle 18 2 true (0),
.cycle 18 13 true (-1),
.cycle 0 20 true (-1),
.last 20 (5,true),
.last 19 (5,true)
])
theorem kid05_part934_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part934) = true := by rfl

def kid05_part935 : Audit := .cycle 11 1 false (-1)
theorem kid05_part935_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part935) = true := by rfl

def kid05_part936 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.cycle 10 4 false (0),
.cycle 16 1 false (-2),
.cycle 11 8 false (0),
.cycle 11 5 false (-1),
.last 14 (5,true),
.cycle 6 8 false (3),
.cycle 9 6 false (1),
.cycle 0 43 true (-3),
.cycle 0 22 true (-2),
.cycle 11 7 false (0),
.last 14 (5,true),
.cycle 11 6 false (-1),
.cycle 10 4 false (0),
.cycle 11 9 false (0),
.cycle 11 7 false (0),
.cycle 11 5 false (-1),
.last 14 (5,true),
.last 18 (5,true),
.last 16 (5,true),
.last 27 (5,true),
.last 31 (5,true),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part936_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part936) = true := by rfl

def kid05_part937 : Audit := .split 14 (2,true) (byMove [
.cycle 12 4 true (-3),
.cycle 10 5 false (0),
.cycle 17 1 false (-3),
.last 18 (5,true),
.cycle 11 5 false (-1),
.last 15 (5,true),
.cycle 6 9 false (3),
.cycle 11 7 false (-1),
.cycle 0 64 true (-4),
.last 25 (5,true),
.cycle 11 7 false (-1),
.last 15 (5,true),
.cycle 11 6 false (-1),
.cycle 10 5 false (0),
.cycle 11 9 false (-1),
.cycle 11 7 false (-1),
.cycle 11 5 false (-1),
.last 15 (5,true),
.last 19 (5,true),
.last 16 (5,true),
.last 28 (5,true),
.last 21 (5,true),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid05_part937_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part937) = true := by rfl

def kid05_part938 : Audit := .split 18 (2,true) (byMove [
.cycle 16 4 true (-3),
.last 39 (5,true),
.cycle 21 1 false (-3),
.last 39 (5,true),
.cycle 14 5 false (0),
.last 19 (5,true),
.far false 9 ⟨0,[0, 1, 2, 3, 4, 1, 5, 6, 7, 7, 7, 6, 6, 8, 6, 7, 8, 6],[128, 256, 8, 0, 4096, 268435456, 524288, 1048576, 32768, 70368744177680, 65536, 268435456, 128, 256, 134217728, 18015566740590592, 1073741824, 4096, 137438953472, 274877906944, 8589934592, 268435456, 17179869184, 18014398509481984, 8796093022208, 17592186044416, 35184372088832, 26843435274342528, 4096, 70368744177664, 137438953472, 274877906944, 35184372088832, 128, 68719476736, 18014398509481984, 562949953421312, 1125899906842624, 549755813888, 26843435274342528, 282643207815168, 26843435274342528, 8796093022208, 17592186044416, 549755813888, 26843435274342528, 1168231104512, 26843435274342528, 137438953472, 274877906944, 2251799813685248, 26843435274342528, 4503668346847232, 26843435274342528, 18014398509481984],[16, 64, 1, 1, 4096, 18014398509481984, 65536, 262144, 4096, 4096, 18014398509481984, 18014398509481984, 268435456, 64, 16777216, 16777216, 4096, 18014398509481984, 17179869184, 68719476736, 1073741824, 1073741824, 18014398509481984, 18014398509481984, 70368744177664, 4398046511104, 4398046511104, 4398046511104, 128, 18014398509481984, 70368744177664, 68719476736, 4398046511104, 4398046511104, 18014398509481984, 18014398509481984, 1099511627776, 281474976710656, 68719476736, 68719476736, 26843435274342528, 18014398509481984, 1099511627776, 4398046511104, 68719476736, 68719476736, 18015566740586496, 18014398509481984, 4503599627370496, 68719476736, 281474976710656, 281474976710656, 26843435274342528, 18014398509481984, 18014398509481984],36028788157310786⟩,
.last 37 (5,true),
.cycle 0 22 true (-3),
.last 37 (5,true),
.cycle 12 7 false (2),
.last 19 (5,true),
.cycle 14 6 false (0),
.cycle 10 9 false (2),
.cycle 14 9 false (0),
.cycle 14 7 false (0),
.cycle 14 5 false (0),
.last 19 (5,true),
.last 42 (5,true),
.last 37 (5,true),
.last 44 (5,true),
.last 37 (5,true),
.last 20 (5,true),
.last 19 (5,true)
])
theorem kid05_part938_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part938) = true := by rfl

def kid05_part939 : Audit := .cycle 1 12 true (0)
theorem kid05_part939_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part939) = true := by rfl

def kid05_part940 : Audit := .split 11 (2,true) (byMove [
.cycle 11 4 true (0),
.cycle 0 15 true (0),
.cycle 14 1 false (0),
.cycle 2 13 true (0),
.cycle 11 5 false (1),
.last 12 (5,true),
.cycle 0 16 true (0),
.cycle 11 11 true (1),
.cycle 0 46 true (-1),
.cycle 0 13 true (0),
.cycle 11 7 false (2),
.last 12 (5,true),
.cycle 11 6 false (1),
.cycle 10 2 true (0),
.cycle 11 9 false (2),
.cycle 11 7 false (2),
.cycle 11 5 false (1),
.last 12 (5,true),
.cycle 0 16 true (0),
.cycle 2 11 true (0),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part940_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part940) = true := by rfl

def kid05_part941 : Audit := .split 15 (2,true) (byMove [
.cycle 12 4 true (2),
.cycle 11 7 true (1),
.cycle 29 1 false (-1),
.cycle 0 17 true (0),
.cycle 18 5 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 11 18 true (1),
.cycle 0 30 true (0),
.cycle 0 26 true (0),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 6 10 true (0),
.cycle 0 18 true (0),
.cycle 11 7 true (1),
.cycle 11 5 true (1),
.cycle 18 5 false (0),
.last 16 (5,true),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.cycle 0 19 true (0),
.last 18 (5,true)
])
theorem kid05_part941_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part941) = true := by rfl

def kid05_part942 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.last 23 (2,true),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 19 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 15 (2,true),
.last 16 (2,true),
.last 24 (2,true),
.last 14 (2,true),
.last 21 (2,true),
.cycle 13 1 false (-1),
.last 15 (2,true),
.last 16 (2,true),
.cycle 0 19 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.last 20 (2,true),
.cycle 9 4 true (0),
.last 18 (2,true)
])
theorem kid05_part942_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part942) = true := by rfl

def kid05_part943 : Audit := .split 11 (5,true) (byMove [
.last 15 (2,true),
.last 18 (2,true),
.last 12 (2,true),
.cycle 18 1 false (0),
.last 16 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.last 20 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.last 18 (2,true),
.last 16 (2,true),
.last 17 (2,true),
.cycle 10 2 true (0),
.last 12 (2,true),
.last 18 (2,true),
.last 16 (2,true),
.last 16 (2,true),
.last 15 (2,true),
.last 17 (2,true),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 3 true (1),
.last 24 (2,true)
])
theorem kid05_part943_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part943) = true := by rfl

def kid05_part919 : Audit := .split 10 (1,true) (byMove [(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929),(kid05_part930),(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943)])

theorem kid05_part919_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part919) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part920),(kid05_part921),(kid05_part922),(kid05_part923),(kid05_part924),(kid05_part925),(kid05_part926),(kid05_part927),(kid05_part928),(kid05_part929),(kid05_part930),(kid05_part931),(kid05_part932),(kid05_part933),(kid05_part934),(kid05_part935),(kid05_part936),(kid05_part937),(kid05_part938),(kid05_part939),(kid05_part940),(kid05_part941),(kid05_part942),(kid05_part943)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part920_checked

  · exact kid05_part926_checked

  · exact kid05_part932_checked

  · exact kid05_part938_checked

  · exact kid05_part921_checked

  · exact kid05_part927_checked

  · exact kid05_part933_checked

  · exact kid05_part939_checked

  · exact kid05_part922_checked

  · exact kid05_part928_checked

  · exact kid05_part934_checked

  · exact kid05_part940_checked

  · exact kid05_part923_checked

  · exact kid05_part929_checked

  · exact kid05_part935_checked

  · exact kid05_part941_checked

  · exact kid05_part924_checked

  · exact kid05_part930_checked

  · exact kid05_part936_checked

  · exact kid05_part942_checked

  · exact kid05_part925_checked

  · exact kid05_part931_checked

  · exact kid05_part937_checked

  · exact kid05_part943_checked

def kid05_part945 : Audit := .cycle 0 22 true (-1)
theorem kid05_part945_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part945) = true := by rfl

def kid05_part946 : Audit := .cycle 0 18 true (-1)
theorem kid05_part946_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part946) = true := by rfl

def kid05_part947 : Audit := .cycle 12 1 false (0)
theorem kid05_part947_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part947) = true := by rfl

def kid05_part948 : Audit := .cycle 11 1 false (-1)
theorem kid05_part948_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part948) = true := by rfl

def kid05_part949 : Audit := .split 15 (1,true) (byMove [
.cycle 0 24 true (-2),
.cycle 0 36 true (-2),
.last 24 (5,true),
.cycle 0 20 true (-2),
.cycle 0 36 true (-3),
.last 16 (5,true),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.cycle 0 43 true (-2),
.cycle 0 17 true (-2),
.cycle 0 31 true (-3),
.last 16 (5,true),
.cycle 0 30 true (-2),
.cycle 11 14 true (-4),
.cycle 10 6 true (-2),
.cycle 0 27 true (-2),
.cycle 0 35 true (-3),
.last 16 (5,true),
.cycle 0 20 true (-2),
.last 28 (5,true),
.last 18 (5,true),
.cycle 0 62 true (-3),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part949_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part949) = true := by rfl

def kid05_part950 : Audit := .cycle 0 29 true (-3)
theorem kid05_part950_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part950) = true := by rfl

def kid05_part951 : Audit := .cycle 0 21 true (-1)
theorem kid05_part951_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part951) = true := by rfl

def kid05_part952 : Audit := .split 11 (1,true) (byMove [
.cycle 0 30 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 0 26 true (-2),
.cycle 0 24 true (-2),
.cycle 0 16 true (0),
.cycle 0 28 true (0),
.cycle 0 28 true (0),
.cycle 0 13 true (0),
.cycle 0 21 true (-1),
.last 12 (5,true),
.cycle 0 28 true (-2),
.cycle 0 32 true (0),
.cycle 0 18 true (0),
.cycle 12 1 false (0),
.cycle 0 25 true (-1),
.cycle 0 30 true (-2),
.cycle 0 16 true (0),
.cycle 1 12 true (0),
.cycle 0 28 true (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part952_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part952) = true := by rfl

def kid05_part953 : Audit := .cycle 14 1 false (4)
theorem kid05_part953_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part953) = true := by rfl

def kid05_part954 : Audit := .cycle 0 16 true (0)
theorem kid05_part954_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part954) = true := by rfl

def kid05_part955 : Audit := .cycle 0 24 true (-2)
theorem kid05_part955_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part955) = true := by rfl

def kid05_part956 : Audit := .split 11 (5,true) (byMove [
.cycle 8 7 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.last 16 (1,true),
.cycle 0 24 true (-2),
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 0 21 true (0),
.cycle 0 13 true (0),
.cycle 0 21 true (-1),
.cycle 0 21 true (0),
.last 13 (1,true),
.cycle 8 9 true (0),
.cycle 0 18 true (0),
.cycle 12 1 false (0),
.cycle 0 25 true (-1),
.cycle 0 30 true (-2),
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 8 5 true (0),
.cycle 0 13 true (0),
.cycle 13 3 true (1),
.cycle 0 36 true (-2)
])
theorem kid05_part956_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part956) = true := by rfl

def kid05_part957 : Audit := .split 12 (1,true) (byMove [
.cycle 0 27 true (-1),
.cycle 0 39 true (-3),
.cycle 10 3 false (0),
.cycle 0 20 true (-1),
.cycle 0 44 true (-4),
.last 13 (5,true),
.cycle 6 7 false (3),
.cycle 0 30 true (-1),
.cycle 0 70 true (-3),
.cycle 0 18 true (-1),
.cycle 0 32 true (-4),
.last 13 (5,true),
.cycle 0 33 true (-3),
.cycle 0 40 true (-4),
.cycle 10 3 false (0),
.cycle 0 28 true (-2),
.cycle 0 36 true (-4),
.last 13 (5,true),
.last 17 (5,true),
.last 29 (5,true),
.cycle 0 34 true (-4),
.cycle 0 18 true (-1),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part957_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part957) = true := by rfl

def kid05_part958 : Audit := .split 13 (1,true) (byMove [
.cycle 0 36 true (-2),
.cycle 0 27 true (-2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.cycle 0 50 true (-4),
.cycle 0 36 true (-4),
.cycle 0 28 true (-2),
.cycle 0 32 true (-1),
.cycle 10 4 true (-1),
.cycle 0 25 true (-1),
.cycle 0 33 true (-3),
.last 14 (5,true),
.cycle 0 40 true (-4),
.cycle 11 3 false (0),
.cycle 0 30 true (-2),
.cycle 14 1 false (-2),
.cycle 0 37 true (-3),
.cycle 0 42 true (-4),
.cycle 0 34 true (-4),
.cycle 12 14 true (-1),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part958_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part958) = true := by rfl

def kid05_part959 : Audit := .cycle 0 23 true (-1)
theorem kid05_part959_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part959) = true := by rfl

def kid05_part960 : Audit := .cycle 11 1 false (-1)
theorem kid05_part960_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part960) = true := by rfl

def kid05_part961 : Audit := .cycle 0 28 true (-2)
theorem kid05_part961_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part961) = true := by rfl

def kid05_part962 : Audit := .cycle 0 35 true (-3)
theorem kid05_part962_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part962) = true := by rfl

def kid05_part963 : Audit := .cycle 0 27 true (-3)
theorem kid05_part963_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part963) = true := by rfl

def kid05_part964 : Audit := .split 11 (1,true) (byMove [
.cycle 0 20 true (0),
.cycle 0 32 true (-2),
.cycle 1 14 true (0),
.cycle 0 16 true (0),
.cycle 0 32 true (-3),
.last 12 (5,true),
.cycle 0 16 true (0),
.cycle 0 28 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.cycle 0 27 true (-3),
.last 12 (5,true),
.cycle 0 26 true (-2),
.cycle 11 5 false (1),
.cycle 10 2 true (0),
.cycle 0 23 true (-1),
.cycle 0 31 true (-3),
.last 12 (5,true),
.cycle 0 16 true (0),
.cycle 1 12 true (0),
.cycle 1 12 true (0),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part964_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part964) = true := by rfl

def kid05_part965 : Audit := .cycle 2 11 true (0)
theorem kid05_part965_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part965) = true := by rfl

def kid05_part966 : Audit := .cycle 0 16 true (0)
theorem kid05_part966_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part966) = true := by rfl

def kid05_part967 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 0 32 true (-2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 28 true (-2),
.last 22 (1,true),
.last 14 (1,true),
.cycle 0 34 true (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 0 20 true (0),
.cycle 0 27 true (-1),
.last 14 (1,true),
.last 19 (1,true),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 0 24 true (-2),
.last 28 (1,true),
.last 14 (1,true),
.cycle 1 18 true (0),
.cycle 0 15 true (0),
.cycle 0 25 true (-1),
.cycle 9 4 true (0),
.cycle 0 33 true (-3)
])
theorem kid05_part967_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part967) = true := by rfl

def kid05_part968 : Audit := .split 11 (5,true) (byMove [
.cycle 0 20 true (0),
.last 12 (1,true),
.cycle 0 33 true (-3),
.last 14 (1,true),
.last 22 (1,true),
.last 22 (1,true),
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 0 33 true (-3),
.cycle 0 13 true (0),
.cycle 0 27 true (-3),
.cycle 0 21 true (0),
.cycle 0 26 true (-2),
.last 12 (1,true),
.cycle 10 2 true (0),
.cycle 0 23 true (-1),
.cycle 0 31 true (-3),
.cycle 0 37 true (-3),
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 0 18 true (0),
.cycle 0 13 true (0),
.cycle 13 3 true (1),
.cycle 0 43 true (-3)
])
theorem kid05_part968_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part968) = true := by rfl

def kid05_part944 : Audit := .split 10 (2,true) (byMove [(kid05_part945),(kid05_part946),(kid05_part947),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part966),(kid05_part967),(kid05_part968)])

theorem kid05_part944_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part944) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part945),(kid05_part946),(kid05_part947),(kid05_part948),(kid05_part949),(kid05_part950),(kid05_part951),(kid05_part952),(kid05_part953),(kid05_part954),(kid05_part955),(kid05_part956),(kid05_part957),(kid05_part958),(kid05_part959),(kid05_part960),(kid05_part961),(kid05_part962),(kid05_part963),(kid05_part964),(kid05_part965),(kid05_part966),(kid05_part967),(kid05_part968)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part945_checked

  · exact kid05_part951_checked

  · exact kid05_part957_checked

  · exact kid05_part963_checked

  · exact kid05_part946_checked

  · exact kid05_part952_checked

  · exact kid05_part958_checked

  · exact kid05_part964_checked

  · exact kid05_part947_checked

  · exact kid05_part953_checked

  · exact kid05_part959_checked

  · exact kid05_part965_checked

  · exact kid05_part948_checked

  · exact kid05_part954_checked

  · exact kid05_part960_checked

  · exact kid05_part966_checked

  · exact kid05_part949_checked

  · exact kid05_part955_checked

  · exact kid05_part961_checked

  · exact kid05_part967_checked

  · exact kid05_part950_checked

  · exact kid05_part956_checked

  · exact kid05_part962_checked

  · exact kid05_part968_checked

def kid05_part969 : Audit := .cycle 15 1 false (-1)
theorem kid05_part969_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part969) = true := by rfl

def kid05_part970 : Audit := .cycle 12 1 false (-2)
theorem kid05_part970_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part970) = true := by rfl

def kid05_part972 : Audit := .split 13 (2,true) (byMove [
.cycle 18 2 false (-2),
.last 14 (1,true),
.cycle 17 1 false (-1),
.last 16 (1,true),
.cycle 0 16 false (3),
.cycle 16 2 false (0),
.cycle 20 2 false (0),
.last 14 (1,true),
.cycle 36 11 false (2),
.cycle 0 15 true (-1),
.cycle 0 22 true (-2),
.cycle 30 2 false (-2),
.cycle 18 2 false (-2),
.last 14 (1,true),
.cycle 20 2 false (0),
.cycle 5 9 false (3),
.cycle 22 11 false (2),
.cycle 16 2 false (0),
.cycle 20 2 false (0),
.last 14 (1,true),
.cycle 28 2 false (-2),
.cycle 0 15 true (-1),
.cycle 20 2 false (-2),
.cycle 26 11 false (2)
])
theorem kid05_part972_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part972) = true := by rfl

def kid05_part973 : Audit := .cycle 20 2 false (-2)
theorem kid05_part973_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part973) = true := by rfl

def kid05_part974 : Audit := .cycle 12 1 false (0)
theorem kid05_part974_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part974) = true := by rfl

def kid05_part975 : Audit := .cycle 11 1 false (-1)
theorem kid05_part975_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part975) = true := by rfl

def kid05_part976 : Audit := .cycle 11 2 false (-1)
theorem kid05_part976_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part976) = true := by rfl

def kid05_part977 : Audit := .cycle 11 2 false (-1)
theorem kid05_part977_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part977) = true := by rfl

def kid05_part978 : Audit := .cycle 13 2 false (1)
theorem kid05_part978_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part978) = true := by rfl

def kid05_part979 : Audit := .split 11 (1,true) (byMove [
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 13 2 false (3),
.cycle 20 2 false (4),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 13 2 false (1),
.cycle 20 2 false (4),
.cycle 16 2 false (0),
.last 13 (2,true),
.cycle 15 2 false (3),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 16 2 false (0),
.cycle 1 12 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 21 2 false (3),
.cycle 24 2 false (0)
])
theorem kid05_part979_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part979) = true := by rfl

def kid05_part980 : Audit := .split 11 (2,true) (byMove [
.cycle 19 2 false (-1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 13 2 false (3),
.last 12 (1,true),
.cycle 14 1 false (4),
.cycle 0 13 true (0),
.cycle 13 2 false (1),
.cycle 14 1 false (4),
.last 13 (1,true),
.last 14 (1,true),
.cycle 15 2 false (3),
.cycle 12 1 false (0),
.cycle 12 2 false (0),
.cycle 12 2 false (0),
.cycle 16 2 false (0),
.last 12 (1,true),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 15 1 false (3),
.cycle 20 2 false (2)
])
theorem kid05_part980_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part980) = true := by rfl

def kid05_part981 : Audit := .cycle 13 2 false (3)
theorem kid05_part981_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part981) = true := by rfl

def kid05_part982 : Audit := .cycle 12 2 false (0)
theorem kid05_part982_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part982) = true := by rfl

def kid05_part983 : Audit := .cycle 13 2 false (3)
theorem kid05_part983_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part983) = true := by rfl

def kid05_part984 : Audit := .split 12 (1,true) (byMove [
.cycle 14 2 false (0),
.cycle 21 2 false (-1),
.last 13 (2,true),
.cycle 0 20 true (-1),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.cycle 28 2 false (-2),
.last 13 (2,true),
.cycle 20 2 false (-2),
.cycle 16 2 false (-2),
.cycle 26 2 false (-2),
.cycle 15 2 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 16 2 false (0),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 40 2 false (-2),
.last 33 (2,true),
.last 13 (2,true),
.cycle 21 2 false (-1),
.cycle 17 2 false (-1),
.cycle 18 2 false (-2)
])
theorem kid05_part984_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part984) = true := by rfl

def kid05_part985 : Audit := .split 12 (2,true) (byMove [
.cycle 14 2 false (0),
.last 13 (1,true),
.cycle 15 1 false (-1),
.last 15 (1,true),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.last 13 (1,true),
.cycle 24 2 false (0),
.cycle 20 2 false (-2),
.cycle 16 2 false (-2),
.last 22 (1,true),
.cycle 15 2 false (-1),
.last 13 (1,true),
.cycle 18 2 false (0),
.cycle 16 2 false (0),
.cycle 14 2 false (-2),
.cycle 10 3 false (0),
.last 21 (1,true),
.last 13 (1,true),
.last 24 (1,true),
.last 19 (1,true),
.last 15 (1,true),
.last 14 (1,true)
])
theorem kid05_part985_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part985) = true := by rfl

def kid05_part986 : Audit := .cycle 15 2 false (1)
theorem kid05_part986_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part986) = true := by rfl

def kid05_part987 : Audit := .cycle 11 1 false (-1)
theorem kid05_part987_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part987) = true := by rfl

def kid05_part988 : Audit := .cycle 11 2 false (-1)
theorem kid05_part988_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part988) = true := by rfl

def kid05_part989 : Audit := .cycle 11 2 false (-1)
theorem kid05_part989_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part989) = true := by rfl

def kid05_part990 : Audit := .cycle 15 2 false (-1)
theorem kid05_part990_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part990) = true := by rfl

def kid05_part991 : Audit := .split 11 (1,true) (byMove [
.cycle 13 2 false (1),
.cycle 20 2 false (0),
.last 12 (2,true),
.cycle 0 16 true (0),
.cycle 13 2 false (-1),
.last 14 (2,true),
.cycle 6 12 true (0),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 0, 0, 8192, 16384, 512, 16, 128, 128, 33554432, 67108864, 2097152, 1024, 524288, 1073741824, 33554432, 67108864, 134217728, 16384, 1073741824, 33554432, 33554432, 67108864, 134217728, 1409286144, 1107296256, 1107296256, 1073741824],[16, 2, 1073741824, 1, 0, 128, 1024, 128, 1073741824, 64, 16384, 8192, 4194304, 524288, 1073741824, 262144, 67108864, 33554432, 268435456, 33554432, 1073741824, 16777216, 1073741824, 33554432, 268435456, 33554432, 1073741824, 16777216, 1140850688, 33554432, 1073741824],2145333312⟩,
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 15 2 false (-1),
.cycle 1 12 true (0),
.cycle 14 2 false (0),
.last 14 (2,true),
.last 12 (2,true),
.cycle 15 2 false (1),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.last 18 (2,true),
.cycle 1 12 true (0),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 1 13 true (0),
.cycle 1 12 true (0)
])
theorem kid05_part991_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part991) = true := by rfl

def kid05_part992 : Audit := .split 11 (2,true) (byMove [
.cycle 13 2 false (1),
.last 12 (1,true),
.cycle 14 1 false (0),
.last 14 (1,true),
.cycle 13 2 false (-1),
.cycle 0 15 true (0),
.cycle 6 12 true (0),
.last 12 (1,true),
.cycle 21 2 false (1),
.cycle 0 13 true (0),
.cycle 15 2 false (-1),
.cycle 23 2 false (-1),
.cycle 14 2 false (0),
.last 12 (1,true),
.cycle 17 2 false (1),
.cycle 15 2 false (1),
.cycle 13 2 false (-1),
.cycle 10 2 true (0),
.cycle 25 2 false (-1),
.last 12 (1,true),
.cycle 2 11 true (0),
.cycle 0 13 true (0),
.cycle 2 12 true (0),
.cycle 2 11 true (0)
])
theorem kid05_part992_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part992) = true := by rfl

def kid05_part993 : Audit := .cycle 5 12 true (0)
theorem kid05_part993_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part993) = true := by rfl

def kid05_part994 : Audit := .cycle 9 4 true (0)
theorem kid05_part994_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part994) = true := by rfl

def kid05_part995 : Audit := .cycle 21 2 false (-1)
theorem kid05_part995_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part995) = true := by rfl

def kid05_part971 : Audit := .split 10 (5,true) (byMove [(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977),(kid05_part978),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995)])

theorem kid05_part971_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part971) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part972),(kid05_part973),(kid05_part974),(kid05_part975),(kid05_part976),(kid05_part977),(kid05_part978),(kid05_part979),(kid05_part980),(kid05_part981),(kid05_part982),(kid05_part983),(kid05_part984),(kid05_part985),(kid05_part986),(kid05_part987),(kid05_part988),(kid05_part989),(kid05_part990),(kid05_part991),(kid05_part992),(kid05_part993),(kid05_part994),(kid05_part995)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part972_checked

  · exact kid05_part978_checked

  · exact kid05_part984_checked

  · exact kid05_part990_checked

  · exact kid05_part973_checked

  · exact kid05_part979_checked

  · exact kid05_part985_checked

  · exact kid05_part991_checked

  · exact kid05_part974_checked

  · exact kid05_part980_checked

  · exact kid05_part986_checked

  · exact kid05_part992_checked

  · exact kid05_part975_checked

  · exact kid05_part981_checked

  · exact kid05_part987_checked

  · exact kid05_part993_checked

  · exact kid05_part976_checked

  · exact kid05_part982_checked

  · exact kid05_part988_checked

  · exact kid05_part994_checked

  · exact kid05_part977_checked

  · exact kid05_part983_checked

  · exact kid05_part989_checked

  · exact kid05_part995_checked

def kid05_part996 : Audit := .cycle 0 12 true (0)
theorem kid05_part996_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part996) = true := by rfl

def kid05_part998 : Audit := .cycle 1 12 true (1)
theorem kid05_part998_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part998) = true := by rfl

def kid05_part999 : Audit := .cycle 11 11 false (1)
theorem kid05_part999_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part999) = true := by rfl

def kid05_part1000 : Audit := .split 11 (2,true) (byMove [
.cycle 1 13 true (0),
.cycle 14 1 false (0),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 1 17 false (3),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 8 4 true (1),
.cycle 16 3 false (0),
.cycle 14 1 false (0),
.cycle 1 16 true (-1),
.cycle 1 14 true (0),
.cycle 14 3 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 15 true (1),
.cycle 1 12 true (1),
.last 14 (5,true)
])
theorem kid05_part1000_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part1000) = true := by rfl

def kid05_part1001 : Audit := .cycle 0 12 true (0)
theorem kid05_part1001_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part1001) = true := by rfl

def kid05_part1002 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 1 13 false (3),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 1 13 true (0),
.cycle 13 4 false (1),
.cycle 14 4 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 1 16 true (0),
.cycle 1 13 true (0),
.cycle 14 4 false (0)
])
theorem kid05_part1002_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part1002) = true := by rfl

def kid05_part1003 : Audit := .split 11 (5,true) (byMove [
.cycle 1 13 true (0),
.cycle 13 11 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 1 17 false (3),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 12 true (1),
.cycle 8 4 true (1),
.cycle 16 3 false (0),
.last 18 (2,true),
.last 12 (2,true),
.cycle 1 14 true (0),
.cycle 14 3 false (-1),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 15 true (1),
.cycle 1 12 true (1),
.cycle 14 6 false (1)
])
theorem kid05_part1003_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part1003) = true := by rfl

def kid05_part1004 : Audit := .cycle 0 11 true (0)
theorem kid05_part1004_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part1004) = true := by rfl

def kid05_part1005 : Audit := .cycle 1 10 true (1)
theorem kid05_part1005_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part1005) = true := by rfl

def kid05_part1006 : Audit := .cycle 0 23 true (0)
theorem kid05_part1006_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part1006) = true := by rfl

def kid05_part1007 : Audit := .cycle 3 8 true (1)
theorem kid05_part1007_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part1007) = true := by rfl

def kid05_part1008 : Audit := .cycle 1 11 true (1)
theorem kid05_part1008_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part1008) = true := by rfl

def kid05_part1009 : Audit := .cycle 8 3 true (1)
theorem kid05_part1009_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part1009) = true := by rfl

def kid05_part1010 : Audit := .cycle 14 5 false (0)
theorem kid05_part1010_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part1010) = true := by rfl

def kid05_part1011 : Audit := .split 14 (2,true) (byMove [
.cycle 11 6 true (-1),
.cycle 12 3 false (0),
.cycle 17 1 false (-1),
.cycle 11 6 true (-1),
.cycle 11 7 false (1),
.last 15 (5,true),
.cycle 6 9 false (3),
.cycle 15 16 true (0),
.cycle 1 62 true (-2),
.cycle 1 17 true (-1),
.cycle 11 9 false (1),
.last 15 (5,true),
.cycle 11 8 false (1),
.cycle 12 3 false (0),
.cycle 11 11 false (1),
.cycle 11 9 false (1),
.cycle 11 7 false (1),
.last 15 (5,true),
.last 19 (5,true),
.cycle 10 5 false (2),
.far true 1 ⟨0,[0, 0],[2, 2, 10, 8, 2, 16, 64],[18, 2, 2, 2, 32, 64, 64],64⟩,
.cycle 1 17 true (-1),
.last 16 (5,true),
.last 15 (5,true)
])
theorem kid05_part1011_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part1011) = true := by rfl

def kid05_part1012 : Audit := .split 11 (2,true) (byMove [
.cycle 1 20 true (0),
.cycle 0 21 true (-1),
.cycle 14 1 false (0),
.cycle 16 1 false (0),
.last 21 (5,true),
.last 12 (5,true),
.cycle 1 13 true (1),
.cycle 0 15 true (0),
.cycle 1 29 true (0),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.last 12 (5,true),
.cycle 16 3 false (0),
.cycle 11 11 false (2),
.cycle 1 24 true (-1),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.last 12 (5,true),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part1012_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part1012) = true := by rfl

def kid05_part1013 : Audit := .cycle 1 13 true (1)
theorem kid05_part1013_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part1013) = true := by rfl

def kid05_part1014 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 17 true (-1),
.cycle 13 4 false (-1),
.cycle 14 4 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (2),
.cycle 13 4 false (1),
.cycle 14 4 false (0),
.last 14 (2,true),
.cycle 16 4 false (2),
.cycle 13 1 false (-1),
.cycle 13 4 false (0),
.cycle 13 4 false (-1),
.cycle 10 4 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 9 4 true (0),
.cycle 14 4 false (0)
])
theorem kid05_part1014_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part1014) = true := by rfl

def kid05_part1015 : Audit := .split 11 (5,true) (byMove [
.last 18 (2,true),
.proven (BB6.Agent11Raw39B0REPumps.M199.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M199.never m hm),
.last 12 (2,true),
.cycle 16 1 false (0),
.last 19 (2,true),
.cycle 12 4 false (0),
.cycle 1 13 true (1),
.cycle 15 5 false (-1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.cycle 8 5 true (1),
.cycle 16 3 false (0),
.last 18 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.cycle 12 4 false (0),
.cycle 1 13 true (1),
.cycle 10 2 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 1 14 true (1),
.cycle 15 10 false (2)
])
theorem kid05_part1015_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part1015) = true := by rfl

def kid05_part1016 : Audit := .cycle 0 11 true (0)
theorem kid05_part1016_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part1016) = true := by rfl

def kid05_part1017 : Audit := .cycle 1 10 true (1)
theorem kid05_part1017_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part1017) = true := by rfl

def kid05_part1018 : Audit := .cycle 2 9 true (1)
theorem kid05_part1018_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part1018) = true := by rfl

def kid05_part1019 : Audit := .cycle 1 14 true (1)
theorem kid05_part1019_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part1019) = true := by rfl

def kid05_part1020 : Audit := .cycle 1 11 true (1)
theorem kid05_part1020_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part1020) = true := by rfl

def kid05_part1021 : Audit := .split 13 (5,true) (byMove [
.last 17 (2,true),
.cycle 16 13 false (0),
.last 14 (2,true),
.last 17 (2,true),
.last 27 (2,true),
.cycle 14 6 false (0),
.cycle 10 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 9 5 true (1),
.cycle 8 10 true (1),
.cycle 18 5 false (1),
.cycle 13 2 true (0),
.last 14 (2,true),
.cycle 21 1 false (1),
.cycle 16 5 false (0),
.cycle 13 6 false (1),
.cycle 10 5 true (1),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 9 5 true (1),
.cycle 14 8 false (2)
])
theorem kid05_part1021_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part1021) = true := by rfl

def kid05_part997 : Audit := .split 10 (1,true) (byMove [(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019),(kid05_part1020),(kid05_part1021)])

theorem kid05_part997_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part997) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid05_part998),(kid05_part999),(kid05_part1000),(kid05_part1001),(kid05_part1002),(kid05_part1003),(kid05_part1004),(kid05_part1005),(kid05_part1006),(kid05_part1007),(kid05_part1008),(kid05_part1009),(kid05_part1010),(kid05_part1011),(kid05_part1012),(kid05_part1013),(kid05_part1014),(kid05_part1015),(kid05_part1016),(kid05_part1017),(kid05_part1018),(kid05_part1019),(kid05_part1020),(kid05_part1021)] mv))) = true

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

def kid05_part1023 : Audit := .cycle 2 11 true (1)
theorem kid05_part1023_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1023) = true := by rfl

def kid05_part1024 : Audit := .split 11 (1,true) (byMove [
.cycle 0 24 true (0),
.cycle 12 11 false (1),
.cycle 25 1 false (-1),
.cycle 0 13 true (0),
.cycle 12 11 false (0),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.cycle 12 3 false (0),
.cycle 0 16 true (-1),
.cycle 25 1 false (1),
.cycle 14 3 false (-1),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 14 true (1),
.cycle 2 11 true (1),
.last 14 (5,true)
])
theorem kid05_part1024_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1024) = true := by rfl

def kid05_part1025 : Audit := .cycle 14 1 false (0)
theorem kid05_part1025_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1025) = true := by rfl

def kid05_part1026 : Audit := .cycle 0 12 true (0)
theorem kid05_part1026_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1026) = true := by rfl

def kid05_part1027 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 false (3),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 19 4 false (1),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 19 4 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 19 4 false (3),
.cycle 13 4 false (1),
.last 14 (1,true),
.cycle 14 4 false (0),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 4 false (0),
.cycle 13 4 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 18 4 false (2),
.cycle 22 4 false (4),
.cycle 2 12 true (0),
.cycle 14 4 false (0)
])
theorem kid05_part1027_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1027) = true := by rfl

def kid05_part1028 : Audit := .split 11 (5,true) (byMove [
.cycle 0 24 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 12 11 false (0),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 2 11 true (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 10 11 false (2),
.cycle 25 1 false (1),
.cycle 14 3 false (-1),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 14 true (1),
.cycle 2 11 true (1),
.cycle 14 6 false (1)
])
theorem kid05_part1028_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1028) = true := by rfl

def kid05_part1029 : Audit := .cycle 0 11 true (0)
theorem kid05_part1029_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1029) = true := by rfl

def kid05_part1030 : Audit := .cycle 1 10 true (1)
theorem kid05_part1030_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1030) = true := by rfl

def kid05_part1031 : Audit := .cycle 0 23 true (0)
theorem kid05_part1031_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1031) = true := by rfl

def kid05_part1032 : Audit := .cycle 3 8 true (1)
theorem kid05_part1032_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1032) = true := by rfl

def kid05_part1033 : Audit := .cycle 2 10 true (1)
theorem kid05_part1033_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1033) = true := by rfl

def kid05_part1034 : Audit := .cycle 8 3 true (1)
theorem kid05_part1034_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1034) = true := by rfl

def kid05_part1035 : Audit := .cycle 14 5 false (0)
theorem kid05_part1035_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1035) = true := by rfl

def kid05_part1036 : Audit := .split 11 (1,true) (byMove [
.cycle 10 8 true (0),
.cycle 0 44 true (-2),
.cycle 17 1 false (-1),
.cycle 0 16 true (0),
.cycle 7 17 false (3),
.last 12 (5,true),
.cycle 2 12 true (1),
.cycle 1 12 true (1),
.cycle 10 4 true (1),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.last 12 (5,true),
.cycle 11 8 false (1),
.cycle 12 3 false (0),
.cycle 27 14 true (0),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.last 12 (5,true),
.cycle 2 12 true (1),
.cycle 1 12 true (1),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.last 13 (5,true),
.last 12 (5,true)
])
theorem kid05_part1036_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1036) = true := by rfl

def kid05_part1037 : Audit := .cycle 14 14 true (-1)
theorem kid05_part1037_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1037) = true := by rfl

def kid05_part1038 : Audit := .cycle 2 12 true (1)
theorem kid05_part1038_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1038) = true := by rfl

def kid05_part1039 : Audit := .split 12 (5,true) (byMove [
.cycle 0 17 true (-1),
.cycle 19 4 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 19 4 false (1),
.cycle 13 4 false (-1),
.last 14 (1,true),
.cycle 14 4 false (2),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 13 4 false (2),
.cycle 13 4 false (1),
.last 14 (1,true),
.cycle 14 4 false (0),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 13 4 false (0),
.cycle 13 4 false (-1),
.last 14 (1,true),
.cycle 10 4 true (0),
.cycle 0 15 true (0),
.cycle 16 4 false (2),
.cycle 9 4 true (0),
.cycle 14 4 false (0)
])
theorem kid05_part1039_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1039) = true := by rfl

def kid05_part1040 : Audit := .split 11 (5,true) (byMove [
.cycle 10 8 true (0),
.last 12 (1,true),
.cycle 18 1 false (-2),
.last 14 (1,true),
.cycle 7 17 false (3),
.cycle 12 4 false (0),
.cycle 2 12 true (1),
.last 12 (1,true),
.cycle 15 5 false (-1),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.cycle 8 5 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 32 14 true (-1),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.cycle 12 4 false (0),
.cycle 2 12 true (1),
.last 12 (1,true),
.cycle 10 2 true (1),
.cycle 0 13 true (0),
.cycle 2 13 true (1),
.cycle 15 10 false (2)
])
theorem kid05_part1040_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1040) = true := by rfl

def kid05_part1041 : Audit := .cycle 0 11 true (0)
theorem kid05_part1041_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1041) = true := by rfl

def kid05_part1042 : Audit := .cycle 1 10 true (1)
theorem kid05_part1042_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1042) = true := by rfl

def kid05_part1043 : Audit := .cycle 2 9 true (1)
theorem kid05_part1043_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1043) = true := by rfl

def kid05_part1044 : Audit := .cycle 2 13 true (1)
theorem kid05_part1044_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1044) = true := by rfl

def kid05_part1045 : Audit := .cycle 2 10 true (1)
theorem kid05_part1045_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1045) = true := by rfl

def kid05_part1046 : Audit := .split 13 (5,true) (byMove [
.cycle 0 18 true (0),
.last 14 (1,true),
.cycle 24 1 false (-2),
.cycle 10 7 true (0),
.cycle 14 13 false (0),
.cycle 14 6 false (0),
.last 15 (1,true),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 9 5 true (1),
.cycle 8 10 true (1),
.last 23 (1,true),
.last 14 (1,true),
.cycle 13 2 true (0),
.cycle 21 1 false (1),
.cycle 16 5 false (0),
.cycle 13 6 false (1),
.last 15 (1,true),
.cycle 10 5 true (1),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 9 5 true (1),
.cycle 14 8 false (2)
])
theorem kid05_part1046_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1046) = true := by rfl

def kid05_part1022 : Audit := .split 10 (2,true) (byMove [(kid05_part1023),(kid05_part1024),(kid05_part1025),(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046)])

theorem kid05_part1022_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1022) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part1023),(kid05_part1024),(kid05_part1025),(kid05_part1026),(kid05_part1027),(kid05_part1028),(kid05_part1029),(kid05_part1030),(kid05_part1031),(kid05_part1032),(kid05_part1033),(kid05_part1034),(kid05_part1035),(kid05_part1036),(kid05_part1037),(kid05_part1038),(kid05_part1039),(kid05_part1040),(kid05_part1041),(kid05_part1042),(kid05_part1043),(kid05_part1044),(kid05_part1045),(kid05_part1046)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1023_checked

  · exact kid05_part1029_checked

  · exact kid05_part1035_checked

  · exact kid05_part1041_checked

  · exact kid05_part1024_checked

  · exact kid05_part1030_checked

  · exact kid05_part1036_checked

  · exact kid05_part1042_checked

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

def kid05_part1047 : Audit := .cycle 0 11 true (0)
theorem kid05_part1047_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1047) = true := by rfl

def kid05_part1048 : Audit := .split 11 (5,true) (byMove [
.cycle 13 1 true (1),
.split 12 (1,true) (byMove [
.cycle 0 13 false (3),
.cycle 13 11 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 true (-1),
.cycle 13 11 false (-1),
.cycle 0 13 true (0),
.cycle 13 11 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 true (1),
.cycle 13 11 false (1),
.cycle 15 11 false (0),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 13 11 false (0),
.cycle 13 11 false (-1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 11 false (2),
.cycle 16 1 true (2),
.cycle 13 1 true (1),
.cycle 14 11 false (0)
]),
.split 12 (2,true) (byMove [
.cycle 0 13 false (3),
.cycle 25 1 false (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 13 1 true (-1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 25 1 false (1),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.cycle 13 1 true (1),
.cycle 18 1 false (0),
.last 14 (1,true),
.last 15 (1,true),
.cycle 0 15 true (-1),
.cycle 13 1 false (-1),
.cycle 17 1 false (-1),
.cycle 18 1 false (-2),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 24 1 false (0),
.cycle 16 1 true (2),
.cycle 13 1 true (1),
.cycle 20 1 false (-2)
]),
.cycle 0 13 true (0),
.cycle 17 1 true (-3),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 12 1 true (2),
.cycle 8 4 true (1),
.split 19 (1,true) (byMove [
.cycle 21 1 true (-1),
.cycle 12 14 false (1),
.last 20 (2,true),
.cycle 0 21 false (3),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.cycle 6 26 false (3),
.cycle 12 13 true (-2),
.cycle 12 13 false (1),
.cycle 12 11 false (1),
.cycle 20 1 true (0),
.cycle 8 12 false (2),
.cycle 12 8 false (1),
.last 22 (2,true),
.last 20 (2,true),
.cycle 22 1 true (0),
.cycle 13 7 false (1),
.cycle 17 3 false (-1),
.last 70 (2,true),
.last 95 (2,true),
.cycle 2 18 false (3),
.cycle 23 1 true (1),
.cycle 20 1 true (0),
.cycle 16 5 false (0)
]),
.split 12 (1,true) (byMove [
.last 15 (2,true),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.last 18 (2,true),
.cycle 14 1 true (2),
.last 26 (2,true),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 19 (2,true),
.last 15 (2,true),
.last 22 (2,true),
.last 14 (2,true),
.cycle 16 1 true (2),
.cycle 13 1 false (-1),
.last 17 (2,true),
.last 18 (2,true),
.cycle 14 1 true (2),
.cycle 1 13 true (0),
.last 13 (2,true),
.cycle 0 14 true (0),
.last 16 (2,true),
.cycle 11 2 true (0)
]),
.split 12 (2,true) (byMove [
.cycle 17 1 true (1),
.cycle 0 16 true (-1),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 9 5 false (2),
.cycle 11 11 false (1),
.cycle 14 1 true (2),
.last 13 (1,true),
.cycle 15 1 false (3),
.cycle 0 14 true (0),
.cycle 0 20 true (-2),
.cycle 0 16 true (0),
.last 14 (1,true),
.last 15 (1,true),
.cycle 16 1 true (2),
.cycle 13 1 false (-1),
.last 19 (1,true),
.last 20 (1,true),
.cycle 14 1 true (2),
.last 13 (1,true),
.cycle 2 12 true (0),
.cycle 0 14 true (0),
.cycle 0 17 true (-1),
.cycle 11 2 true (0)
]),
.cycle 14 1 true (2),
.cycle 14 3 false (-1),
.cycle 12 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 15 1 true (3),
.cycle 12 1 true (2),
.cycle 13 6 false (1)
])
theorem kid05_part1048_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1048) = true := by rfl

def kid05_part1049 : Audit := .split 10 (5,true) (byMove [
.cycle 15 7 false (1),
.split 11 (1,true) (byMove [
.cycle 0 20 false (3),
.cycle 12 11 false (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 12 7 false (0),
.cycle 20 4 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 7 false (1),
.cycle 8 4 true (1),
.cycle 11 8 false (1),
.last 14 (2,true),
.last 12 (2,true),
.cycle 21 1 false (-1),
.cycle 14 3 false (-1),
.cycle 0 16 true (-1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 9 16 true (1),
.cycle 15 15 false (2),
.cycle 21 6 false (1)
]),
.split 11 (2,true) (byMove [
.cycle 0 20 false (3),
.last 12 (1,true),
.cycle 14 1 false (0),
.cycle 0 13 true (0),
.cycle 12 7 false (0),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 15 7 false (1),
.cycle 8 4 true (1),
.last 19 (1,true),
.last 12 (1,true),
.cycle 0 40 true (-1),
.cycle 21 1 false (-1),
.cycle 14 3 false (-1),
.cycle 14 1 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 9 16 true (1),
.cycle 22 1 false (0),
.cycle 16 1 false (0)
]),
.cycle 0 12 true (0),
.cycle 15 4 false (-1),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 0 23 true (0),
.cycle 3 8 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 48, 32, 16, 64],[16, 64, 64, 1, 32, 16, 64],64⟩,
.cycle 8 3 true (1),
.cycle 14 5 false (0),
.split 11 (1,true) (byMove [
.last 18 (2,true),
.cycle 0 44 true (-2),
.last 12 (2,true),
.cycle 0 16 true (0),
.cycle 12 7 false (0),
.last 14 (2,true),
.cycle 9 12 true (1),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.last 14 (2,true),
.cycle 11 8 false (1),
.last 14 (2,true),
.last 12 (2,true),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.last 14 (2,true),
.last 20 (2,true),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.last 18 (2,true),
.cycle 10 2 true (1)
]),
.split 11 (2,true) (byMove [
.cycle 13 13 false (3),
.last 12 (1,true),
.cycle 14 1 false (0),
.last 14 (1,true),
.cycle 12 7 false (0),
.last 16 (1,true),
.cycle 9 12 true (1),
.last 12 (1,true),
.cycle 0 39 true (0),
.cycle 0 13 true (0),
.cycle 14 5 false (0),
.cycle 0 15 true (0),
.last 19 (1,true),
.last 12 (1,true),
.cycle 18 16 true (-1),
.cycle 19 1 false (-1),
.cycle 14 3 false (-1),
.cycle 17 4 false (1),
.last 22 (1,true),
.last 12 (1,true),
.cycle 2 11 true (1),
.cycle 0 13 true (0),
.cycle 0 19 true (-1),
.cycle 10 2 true (1)
]),
.cycle 9 12 true (1),
.cycle 13 4 false (0),
.cycle 11 4 false (1),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 4 16 true (1),
.cycle 9 6 true (1),
.cycle 13 8 false (2)
])
theorem kid05_part1049_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1049) = true := by rfl

def kid05_part809 : Audit := .split 9 (4,false) (byMove [(kid05_part810),(kid05_part835),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part894),(kid05_part919),(kid05_part944),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part996),(kid05_part997),(kid05_part1022),(kid05_part1047),(kid05_part1048),(kid05_part1049)])

theorem kid05_part809_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (kid05_part809) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part810),(kid05_part835),(kid05_part860),(kid05_part861),(kid05_part862),(kid05_part863),(kid05_part888),(kid05_part889),(kid05_part890),(kid05_part891),(kid05_part892),(kid05_part893),(kid05_part894),(kid05_part919),(kid05_part944),(kid05_part969),(kid05_part970),(kid05_part971),(kid05_part996),(kid05_part997),(kid05_part1022),(kid05_part1047),(kid05_part1048),(kid05_part1049)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part810_checked

  · exact kid05_part888_checked

  · exact kid05_part894_checked

  · exact kid05_part996_checked

  · exact kid05_part835_checked

  · exact kid05_part889_checked

  · exact kid05_part919_checked

  · exact kid05_part997_checked

  · exact kid05_part860_checked

  · exact kid05_part890_checked

  · exact kid05_part944_checked

  · exact kid05_part1022_checked

  · exact kid05_part861_checked

  · exact kid05_part891_checked

  · exact kid05_part969_checked

  · exact kid05_part1047_checked

  · exact kid05_part862_checked

  · exact kid05_part892_checked

  · exact kid05_part970_checked

  · exact kid05_part1048_checked

  · exact kid05_part863_checked

  · exact kid05_part893_checked

  · exact kid05_part971_checked

  · exact kid05_part1049_checked

def kid05_part1052 : Audit := .split 15 (4,false) (byMove [
.cycle 11 23 true (-1),
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (-2),
.cycle 9 7 false (1),
.cycle 0 18 true (-1),
.last 16 (1,true),
.cycle 0 17 true (-1),
.cycle 0 17 true (-1),
.cycle 7 9 false (3),
.cycle 0 17 true (-1),
.last 17 (1,true),
.cycle 12 4 true (0),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 18 1 false (-2),
.cycle 9 7 false (1),
.cycle 16 22 true (2),
.last 16 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 4, 4, 64],[16, 64, 4, 1, 8, 4, 64],64⟩,
.cycle 0 17 true (-1),
.cycle 0 37 true (-1),
.cycle 17 7 true (1)
])
theorem kid05_part1052_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1052) = true := by rfl

def kid05_part1053 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 23 1 false (-1),
.cycle 23 1 false (-1),
.cycle 0 21 true (-1),
.cycle 16 1 false (-2),
.cycle 0 16 false (3),
.cycle 0 17 true (-1),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 0, 8192, 16384, 512, 16, 1073741824, 16384, 33554432, 67108864, 2097152, 1024, 1073741824, 1275068416, 33554432, 67108864, 134217728, 2097152, 1073741824, 1291845632, 33554432, 67108864, 134217728, 1593835520, 1073741824, 1593835520, 1073741824],[16, 2, 512, 1, 0, 16384, 1024, 128, 2097408, 64, 2097152, 1140850688, 4194304, 524288, 16384, 262144, 1207959552, 1073741824, 268435456, 33554432, 134217728, 16777216, 1593835520, 67108864, 268435456, 33554432, 201326592, 16777216, 1593835520, 1140850688, 1073741824],2145367890⟩,
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.last 15 (4,false),
.cycle 8 7 false (2),
.cycle 17 1 false (-1),
.cycle 15 3 false (-1),
.cycle 0 25 true (-2),
.last 17 (4,false),
.cycle 16 1 false (-2),
.cycle 10 5 false (1),
.last 29 (4,false),
.last 29 (4,false),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 15 (4,false),
.last 18 (4,false)
])
theorem kid05_part1053_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1053) = true := by rfl

def kid05_part1054 : Audit := .cycle 17 1 false (-1)
theorem kid05_part1054_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1054) = true := by rfl

def kid05_part1055 : Audit := .split 16 (1,true) (byMove [
.last 18 (4,false),
.cycle 1 17 false (3),
.last 21 (4,false),
.cycle 0 18 true (-1),
.last 45 (4,false),
.last 30 (4,false),
.cycle 0 17 true (-1),
.far true 6 ⟨0,[0, 3, 5, 2, 5, 2, 5, 1, 4, 4, 4, 4],[1073741824, 2048, 512, 2097152, 68719476736, 8388608, 1073741824, 0, 68719476736, 32768, 68719476736, 131072, 1073741824, 0, 537001984, 32768, 68719476736, 131072, 1073741824, 0, 0, 512, 68719476736, 2048, 69273124864, 69273124864, 69407342592, 134217728, 68719476736, 536870912, 0, 69809995776, 32768, 134217728, 68719476736, 536870912, 68719476736],[68719476736, 131072, 8, 0, 32, 1, 536870912, 131072, 8589934592, 2048, 34359738368, 1073741824, 536870912, 131072, 8589934592, 536870912, 34359738368, 1073741824, 8388608, 131072, 8589934592, 68719476736, 34359738368, 1073741824, 69256347648, 69273124864, 134217728, 69273124864, 536870912, 16777216, 68719476736, 0, 134217728, 0, 536870912, 16777216, 68719476736],88436966672⟩,
.last 38 (4,false),
.cycle 0 33 true (-2),
.last 17 (4,false),
.cycle 8 9 true (-1),
.cycle 6 11 false (3),
.cycle 12 6 true (0),
.last 21 (4,false),
.last 19 (4,false),
.last 49 (4,false),
.cycle 0 22 true (-1),
.last 29 (4,false),
.last 28 (4,false),
.cycle 2 15 true (-1),
.last 20 (4,false),
.last 17 (4,false),
.last 20 (4,false)
])
theorem kid05_part1055_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1055) = true := by rfl

def kid05_part1056 : Audit := .cycle 0 16 false (3)
theorem kid05_part1056_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1056) = true := by rfl

def kid05_part1057 : Audit := .split 16 (4,false) (byMove [
.cycle 0 21 true (-1),
.cycle 24 1 false (0),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 18 (1,true),
.cycle 0 20 true (-1),
.cycle 0 19 true (-1),
.cycle 17 1 false (1),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.last 18 (1,true),
.cycle 0 20 false (3),
.last 20 (1,true),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.last 18 (1,true),
.cycle 1 21 true (-1),
.cycle 0 19 true (-1),
.cycle 21 1 false (1),
.cycle 21 1 true (1),
.cycle 9 8 true (-1)
])
theorem kid05_part1057_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1057) = true := by rfl

def kid05_part1058 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.last 205 (1,true),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 0 20 false (3),
.cycle 21 1 false (-1),
.cycle 0 16 true (-1),
.last 31 (1,true),
.cycle 47 1 false (1),
.cycle 66 1 false (0),
.cycle 15 1 true (3),
.cycle 0 38 true (-1),
.last 17 (1,true),
.cycle 0 18 true (-1),
.cycle 0 18 true (-1),
.cycle 3 13 false (3),
.cycle 31 1 false (-1),
.cycle 21 1 false (-1),
.cycle 0 36 true (-1),
.cycle 1 15 true (-1),
.cycle 0 41 true (-1),
.cycle 14 4 true (2),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1058_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1058) = true := by rfl

def kid05_part1059 : Audit := .split 14 (1,true) (byMove [
.last 27 (4,false),
.last 26 (4,false),
.cycle 2 13 false (3),
.last 18 (4,false),
.last 15 (4,false),
.last 18 (4,false),
.cycle 0 15 true (-1),
.last 28 (4,false),
.last 33 (4,false),
.cycle 3 13 false (3),
.last 15 (4,false),
.last 20 (4,false),
.last 22 (4,false),
.last 29 (4,false),
.cycle 0 17 true (-1),
.cycle 4 11 false (3),
.last 15 (4,false),
.last 18 (4,false),
.last 27 (4,false),
.cycle 1 14 true (-1),
.last 26 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 32 (4,false)
])
theorem kid05_part1059_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1059) = true := by rfl

def kid05_part1060 : Audit := .split 33 (4,false) (byMove [
.cycle 0 34 true (-2),
.cycle 38 27 false (6),
.cycle 64 1 false (-2),
.cycle 61 1 false (-3),
.cycle 0 41 false (5),
.cycle 42 1 false (-2),
.cycle 0 34 true (-2),
.last 52 (1,true),
.cycle 74 1 false (6),
.cycle 66 1 false (0),
.cycle 33 1 true (5),
.cycle 34 61 true (-2),
.last 35 (1,true),
.cycle 0 62 true (-2),
.cycle 0 36 true (-2),
.cycle 61 1 false (-3),
.cycle 52 1 false (-2),
.cycle 42 1 false (-2),
.cycle 0 70 true (-2),
.cycle 1 33 true (-2),
.cycle 70 1 false (0),
.cycle 31 4 true (3),
.cycle 33 1 true (5),
.cycle 0 55 true (-2)
])
theorem kid05_part1060_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1060) = true := by rfl

def kid05_part1061 : Audit := .cycle 0 15 true (-1)
theorem kid05_part1061_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1061) = true := by rfl

def kid05_part1062 : Audit := .split 18 (4,false) (byMove [
.cycle 11 25 true (-1),
.cycle 0 22 true (-1),
.cycle 20 1 false (0),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 0 21 true (-1),
.last 19 (1,true),
.cycle 22 1 false (4),
.cycle 0 20 true (-1),
.cycle 20 1 false (0),
.cycle 0 20 true (-1),
.last 20 (1,true),
.cycle 25 3 true (-1),
.cycle 0 25 true (-1),
.cycle 19 1 false (-1),
.cycle 18 1 false (0),
.cycle 19 1 false (-1),
.cycle 20 21 true (2),
.last 19 (1,true),
.cycle 18 22 true (-1),
.cycle 0 20 true (-1),
.cycle 0 21 false (3),
.cycle 21 6 true (0)
])
theorem kid05_part1062_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1062) = true := by rfl

def kid05_part1063 : Audit := .split 27 (4,false) (byMove [
.cycle 11 17 true (-1),
.cycle 63 181 true (-4),
.cycle 34 1 false (0),
.cycle 32 1 false (0),
.cycle 30 1 false (-2),
.cycle 38 1 false (-2),
.cycle 56 1 false (0),
.last 28 (1,true),
.cycle 0 30 true (-1),
.cycle 40 1 false (0),
.cycle 0 40 true (-2),
.cycle 23 9 true (0),
.last 29 (1,true),
.cycle 23 11 true (0),
.cycle 62 1 false (0),
.cycle 32 1 false (0),
.cycle 30 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 61, 36, 36, 64],[16, 64, 32, 1, 44, 36, 64],64⟩,
.cycle 23 12 true (0),
.last 28 (1,true),
.cycle 13 15 true (0),
.cycle 28 4 true (2),
.cycle 0 34 true (-1),
.cycle 23 16 true (0)
])
theorem kid05_part1063_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1063) = true := by rfl

def kid05_part1064 : Audit := .cycle 9 7 false (1)
theorem kid05_part1064_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1064) = true := by rfl

def kid05_part1065 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 23 1 false (-1),
.cycle 20 1 false (-2),
.cycle 0 22 true (-1),
.cycle 16 1 false (-2),
.last 21 (4,false),
.cycle 6 9 false (3),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 0, 8192, 16384, 512, 16, 1073741824, 128, 33554432, 67108864, 2097152, 1024, 1073741824, 1107296256, 33554432, 67108864, 134217728, 2113536, 1073741824, 1107296256, 33554432, 67108864, 134217728, 1593835648, 1073741824, 1107296256, 1073741824],[16, 2, 130, 1, 0, 16384, 1024, 128, 130, 64, 2113536, 1140850688, 4194304, 524288, 128, 262144, 1207959552, 1073741824, 268435456, 33554432, 33554432, 16777216, 1140850688, 67108864, 268435456, 33554432, 33554432, 16777216, 1275068416, 1140850688, 1073741824],2145367890⟩,
.cycle 12 4 true (0),
.last 17 (4,false),
.cycle 9 7 false (1),
.last 33 (4,false),
.cycle 17 1 false (-1),
.cycle 15 3 false (-1),
.cycle 23 1 false (-1),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 10 5 false (1),
.last 20 (4,false),
.last 28 (4,false),
.cycle 13 2 true (0),
.last 17 (4,false),
.last 18 (4,false),
.last 17 (4,false)
])
theorem kid05_part1065_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1065) = true := by rfl

def kid05_part1066 : Audit := .cycle 20 1 false (0)
theorem kid05_part1066_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1066) = true := by rfl

def kid05_part1067 : Audit := .cycle 5 9 false (3)
theorem kid05_part1067_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1067) = true := by rfl

def kid05_part1068 : Audit := .split 21 (4,false) (byMove [
.cycle 0 22 true (-2),
.cycle 30 26 false (2),
.cycle 3 22 false (3),
.cycle 3 20 false (3),
.cycle 0 27 false (3),
.cycle 28 1 false (-2),
.cycle 0 22 true (-2),
.last 38 (1,true),
.cycle 45 2 true (1),
.cycle 59 1 false (-1),
.cycle 21 1 true (3),
.cycle 0 61 true (-2),
.last 23 (1,true),
.cycle 33 1 false (-3),
.cycle 0 24 true (-2),
.cycle 3 20 false (3),
.cycle 38 1 false (-2),
.cycle 28 1 false (-2),
.cycle 0 48 true (-2),
.cycle 1 21 true (-2),
.cycle 38 1 false (-2),
.cycle 19 4 true (1),
.cycle 21 1 true (3),
.cycle 0 33 true (-2)
])
theorem kid05_part1068_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1068) = true := by rfl

def kid05_part1069 : Audit := .split 16 (4,false) (byMove [
.cycle 11 6 true (-1),
.cycle 30 15 false (2),
.cycle 18 1 false (0),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.last 17 (1,true),
.cycle 18 1 false (0),
.cycle 20 1 false (4),
.cycle 18 1 false (0),
.cycle 0 25 true (-1),
.last 18 (1,true),
.cycle 10 9 false (1),
.cycle 21 1 false (1),
.cycle 17 1 false (-1),
.cycle 16 1 false (0),
.cycle 17 1 false (-1),
.cycle 14 25 true (-1),
.last 17 (1,true),
.cycle 10 8 true (-1),
.cycle 17 4 true (1),
.cycle 0 23 true (-1),
.cycle 17 11 true (0)
])
theorem kid05_part1069_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1069) = true := by rfl

def kid05_part1070 : Audit := .split 15 (4,false) (byMove [
.cycle 11 18 true (-1),
.cycle 0 139 true (-2),
.cycle 28 1 false (0),
.cycle 3 17 false (3),
.cycle 20 1 false (0),
.last 26 (1,true),
.cycle 0 16 true (-1),
.last 30 (1,true),
.last 59 (1,true),
.cycle 0 31 true (-1),
.cycle 15 1 true (3),
.cycle 10 12 true (-1),
.last 17 (1,true),
.cycle 12 27 true (0),
.cycle 0 18 true (-1),
.cycle 25 1 false (-1),
.cycle 20 1 false (0),
.cycle 16 11 false (2),
.cycle 16 20 true (3),
.cycle 1 15 true (-1),
.cycle 13 36 true (0),
.cycle 14 4 true (2),
.cycle 15 1 true (3),
.cycle 14 24 true (2)
])
theorem kid05_part1070_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1070) = true := by rfl

def kid05_part1071 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 25 1 false (-1),
.last 27 (4,false),
.cycle 0 16 true (-1),
.last 18 (4,false),
.last 17 (4,false),
.cycle 0 15 true (-1),
.last 27 (4,false),
.last 26 (4,false),
.last 24 (4,false),
.last 15 (4,false),
.last 19 (4,false),
.last 20 (4,false),
.cycle 15 5 false (1),
.cycle 13 2 true (1),
.last 17 (4,false),
.last 18 (4,false),
.last 17 (4,false),
.last 27 (4,false),
.last 26 (4,false),
.last 25 (4,false),
.last 18 (4,false),
.last 15 (4,false),
.last 18 (4,false)
])
theorem kid05_part1071_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1071) = true := by rfl

def kid05_part1072 : Audit := .split 25 (4,false) (byMove [
.cycle 11 15 true (-1),
.cycle 0 61 true (-2),
.cycle 32 1 false (0),
.cycle 30 1 false (0),
.cycle 28 1 false (-2),
.cycle 35 15 false (3),
.cycle 58 1 false (0),
.last 26 (1,true),
.cycle 2 26 true (-1),
.cycle 38 1 false (0),
.cycle 0 36 true (-2),
.cycle 14 15 true (0),
.last 27 (1,true),
.cycle 13 15 true (0),
.cycle 64 1 false (0),
.cycle 30 1 false (0),
.cycle 28 1 false (-2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 4, 4, 64],[16, 64, 4, 1, 8, 4, 64],64⟩,
.cycle 14 18 true (0),
.last 26 (1,true),
.cycle 13 13 true (0),
.cycle 26 4 true (2),
.cycle 0 32 true (-1),
.cycle 14 22 true (0)
])
theorem kid05_part1072_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1072) = true := by rfl

def kid05_part1073 : Audit := .cycle 0 15 true (-1)
theorem kid05_part1073_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1073) = true := by rfl

def kid05_part1074 : Audit := .split 17 (4,false) (byMove [
.cycle 11 20 true (-1),
.cycle 1 17 false (3),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 15 9 false (1),
.cycle 0 18 true (-1),
.proven (BB6.Agent11Raw39B0REPumps.M207.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M207.never m hm),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 17 1 true (1),
.cycle 8 11 false (2),
.last 19 (1,true),
.last 21 (1,true),
.cycle 0 20 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 9 9 false (2),
.cycle 17 21 true (1),
.cycle 1 17 true (-1),
.cycle 0 37 true (-2),
.cycle 16 4 true (0),
.cycle 17 1 true (1),
.cycle 15 13 true (0)
])
theorem kid05_part1074_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1074) = true := by rfl

def kid05_part1075 : Audit := .split 16 (4,false) (byMove [
.cycle 11 19 true (-1),
.proven (BB6.Agent11Raw39B0REPumps.M208.table) (fun m hm => BB6.Agent11Raw39B0REPumps.M208.never m hm),
.cycle 2 15 false (3),
.cycle 26 1 false (0),
.cycle 0 20 false (3),
.cycle 21 1 false (-1),
.cycle 0 17 true (-1),
.last 31 (1,true),
.cycle 9 123 true (-3),
.cycle 3 15 false (3),
.cycle 16 1 true (2),
.cycle 10 13 true (-1),
.last 18 (1,true),
.cycle 12 11 true (0),
.cycle 0 19 true (-1),
.cycle 4 13 false (3),
.cycle 42 1 false (-2),
.cycle 21 1 false (-1),
.cycle 15 26 true (1),
.cycle 1 16 true (-1),
.cycle 30 5 true (1),
.cycle 15 4 true (1),
.cycle 16 1 true (2),
.cycle 14 12 true (1)
])
theorem kid05_part1075_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1075) = true := by rfl

def kid05_part1051 : Audit := .split 13 (2,true) (byMove [(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073),(kid05_part1074),(kid05_part1075)])

theorem kid05_part1051_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part1051) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) 13 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (2,true) (some mv)) (byMove [(kid05_part1052),(kid05_part1053),(kid05_part1054),(kid05_part1055),(kid05_part1056),(kid05_part1057),(kid05_part1058),(kid05_part1059),(kid05_part1060),(kid05_part1061),(kid05_part1062),(kid05_part1063),(kid05_part1064),(kid05_part1065),(kid05_part1066),(kid05_part1067),(kid05_part1068),(kid05_part1069),(kid05_part1070),(kid05_part1071),(kid05_part1072),(kid05_part1073),(kid05_part1074),(kid05_part1075)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part1056_checked

  · exact kid05_part1062_checked

  · exact kid05_part1068_checked

  · exact kid05_part1074_checked

  · exact kid05_part1057_checked

  · exact kid05_part1063_checked

  · exact kid05_part1069_checked

  · exact kid05_part1075_checked

def kid05_part1076 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 24 9 false (2),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.cycle 0 16 true (-1),
.cycle 26 9 false (2),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 18 9 false (2),
.split 17 (1,true) (byMove [
.cycle 14 4 true (2),
.cycle 23 9 false (3),
.last 18 (2,true),
.cycle 0 19 true (-1),
.cycle 7 11 false (3),
.cycle 23 9 false (3),
.cycle 0 18 true (-1),
.last 49 (2,true),
.cycle 26 9 false (2),
.cycle 24 9 false (2),
.cycle 15 3 true (2),
.cycle 8 10 true (-1),
.cycle 18 9 false (3),
.last 20 (2,true),
.last 18 (2,true),
.cycle 13 5 true (1),
.cycle 7 11 false (3),
.cycle 0 22 true (-1),
.cycle 14 18 true (2),
.last 30 (2,true),
.cycle 2 16 true (-1),
.cycle 13 6 true (1),
.cycle 0 26 true (-1),
.cycle 9 12 true (-1)
]),
.split 17 (2,true) (byMove [
.cycle 14 4 true (2),
.last 18 (1,true),
.cycle 26 1 false (0),
.cycle 0 19 true (-1),
.cycle 7 11 false (3),
.cycle 23 9 false (3),
.cycle 0 18 true (-1),
.last 47 (1,true),
.cycle 26 9 false (2),
.cycle 24 9 false (2),
.cycle 15 3 true (2),
.cycle 8 10 true (-1),
.cycle 18 9 false (3),
.last 18 (1,true),
.cycle 12 7 true (0),
.cycle 13 5 true (1),
.cycle 7 11 false (3),
.cycle 0 22 true (-1),
.last 29 (1,true),
.last 28 (1,true),
.cycle 2 16 true (-1),
.cycle 13 6 true (1),
.last 19 (1,true),
.last 20 (1,true)
]),
.cycle 0 18 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.split 27 (1,true) (byMove [
.cycle 11 18 true (-1),
.cycle 36 9 false (2),
.cycle 36 1 false (0),
.cycle 34 1 false (0),
.last 31 (2,true),
.cycle 28 9 false (2),
.cycle 14 16 true (2),
.last 29 (2,true),
.cycle 12 16 true (0),
.cycle 36 1 false (0),
.cycle 0 36 true (-1),
.cycle 30 9 false (2),
.cycle 30 9 false (3),
.last 29 (2,true),
.last 32 (2,true),
.cycle 34 1 false (0),
.cycle 0 38 true (-1),
.cycle 28 9 false (2),
.cycle 14 16 true (2),
.last 29 (2,true),
.cycle 12 16 true (0),
.cycle 34 9 false (2),
.cycle 14 21 true (2),
.cycle 58 9 false (2)
]),
.cycle 1 15 true (-1),
.cycle 24 9 false (2),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1076_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part1076) = true := by rfl

def kid05_part1077 : Audit := .cycle 12 1 false (0)
theorem kid05_part1077_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part1077) = true := by rfl

def kid05_part1078 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1078_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part1078) = true := by rfl

def kid05_part1080 : Audit := .cycle 0 18 true (-2)
theorem kid05_part1080_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1080) = true := by rfl

def kid05_part1081 : Audit := .cycle 19 1 false (-1)
theorem kid05_part1081_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1081) = true := by rfl

def kid05_part1082 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1082_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1082) = true := by rfl

def kid05_part1083 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1083_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1083) = true := by rfl

def kid05_part1084 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1084_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1084) = true := by rfl

def kid05_part1085 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1085_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1085) = true := by rfl

def kid05_part1086 : Audit := .split 13 (1,true) (byMove [
.cycle 0 18 true (-1),
.cycle 22 1 false (0),
.last 14 (2,true),
.cycle 0 18 true (-1),
.cycle 15 1 false (-1),
.last 18 (2,true),
.cycle 0 16 true (-1),
.far false 4 ⟨0,[0, 1, 1, 2, 3, 3, 0, 3],[128, 256, 8, 20473819, 1, 20473819, 8192, 16384, 512, 20473819, 64, 128, 524288, 1048576, 2097152, 1024, 262144, 20473819, 524288, 1048576, 8, 16400, 1, 20473819, 16777216],[16, 2, 16777216, 1, 20473819, 128, 1024, 128, 16777216, 64, 16384, 20473819, 4194304, 524288, 16777216, 262144, 20473819, 2097152, 16, 2, 16777216, 1, 20473819, 20473819, 16777216],27244398⟩,
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 0 21 true (-1),
.cycle 0 16 true (-1),
.cycle 16 1 false (0),
.last 16 (2,true),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 0 16 true (-1),
.cycle 0 34 true (-1),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 17 1 false (-1),
.cycle 0 18 true (-1)
])
theorem kid05_part1086_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1086) = true := by rfl

def kid05_part1087 : Audit := .split 13 (2,true) (byMove [
.last 16 (1,true),
.last 14 (1,true),
.cycle 16 1 false (0),
.last 16 (1,true),
.cycle 15 1 false (-1),
.cycle 0 19 true (-1),
.last 42 (1,true),
.last 14 (1,true),
.cycle 23 1 false (1),
.cycle 0 15 true (-1),
.last 43 (1,true),
.cycle 8 26 true (-1),
.cycle 16 1 false (0),
.last 14 (1,true),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 29 1 false (-1),
.last 14 (1,true),
.cycle 25 1 false (-1),
.cycle 0 15 true (-1),
.cycle 17 1 false (-1),
.cycle 25 1 false (1)
])
theorem kid05_part1087_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1087) = true := by rfl

def kid05_part1088 : Audit := .cycle 17 1 false (5)
theorem kid05_part1088_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1088) = true := by rfl

def kid05_part1089 : Audit := .cycle 12 1 false (0)
theorem kid05_part1089_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1089) = true := by rfl

def kid05_part1090 : Audit := .cycle 14 1 false (0)
theorem kid05_part1090_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1090) = true := by rfl

def kid05_part1091 : Audit := .cycle 12 1 false (0)
theorem kid05_part1091_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1091) = true := by rfl

def kid05_part1092 : Audit := .split 13 (1,true) (byMove [
.cycle 11 4 true (-2),
.cycle 22 1 false (-2),
.last 14 (2,true),
.last 17 (2,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 40 1 false (-2),
.last 15 (2,true),
.cycle 28 12 false (2),
.cycle 19 1 false (-1),
.cycle 21 1 false (-3),
.cycle 8 6 false (2),
.cycle 16 1 false (-2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 22 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 61 24 true (0),
.last 15 (2,true),
.cycle 2 18 true (-2),
.cycle 4 10 false (3),
.cycle 9 8 false (1),
.cycle 17 1 false (-3)
])
theorem kid05_part1092_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1092) = true := by rfl

def kid05_part1093 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 20 (1,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 15 (1,true),
.last 16 (1,true),
.cycle 28 12 false (2),
.cycle 19 1 false (-1),
.cycle 21 1 false (-3),
.cycle 8 6 false (2),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 26 1 false (0),
.cycle 22 1 false (0),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.last 15 (1,true),
.last 16 (1,true),
.cycle 2 18 true (-2),
.cycle 4 10 false (3),
.last 15 (1,true),
.cycle 17 1 false (-3)
])
theorem kid05_part1093_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1093) = true := by rfl

def kid05_part1094 : Audit := .split 15 (1,true) (byMove [
.cycle 0 24 true (-2),
.cycle 24 1 false (0),
.last 16 (2,true),
.cycle 0 20 true (-2),
.cycle 17 1 false (-1),
.last 22 (2,true),
.cycle 0 20 true (-2),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 3, 4, 3, 0, 3],[128, 256, 8, 1530423251, 1, 1530423251, 8192, 16384, 512, 1530423251, 1073741888, 128, 524288, 1048576, 2097152, 1024, 1073741824, 1530423251, 524288, 1048576, 134217728, 268451856, 1090519040, 1530423251, 524288, 1048576, 8, 1530423251, 1, 1530423251, 1073741824],[16, 2, 1073741824, 1, 1530423251, 128, 1024, 128, 1073741824, 64, 16384, 1530423251, 4194304, 524288, 1073741824, 262144, 1530423251, 2097152, 268435456, 33554432, 1073741824, 16777216, 1530423251, 1530423251, 16, 2, 1073741824, 1, 1530423251, 1074266112, 1073741824],1876932462⟩,
.last 16 (2,true),
.cycle 0 17 true (-2),
.cycle 0 27 true (-2),
.last 18 (2,true),
.cycle 18 1 false (0),
.last 18 (2,true),
.last 16 (2,true),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 10 6 true (-2),
.cycle 0 20 true (-2),
.cycle 0 40 true (-2),
.last 16 (2,true),
.last 29 (2,true),
.cycle 19 1 false (-1),
.cycle 0 22 true (-2)
])
theorem kid05_part1094_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1094) = true := by rfl

def kid05_part1095 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1095_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1095) = true := by rfl

def kid05_part1096 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1096_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1096) = true := by rfl

def kid05_part1097 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1097_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1097) = true := by rfl

def kid05_part1098 : Audit := .split 13 (1,true) (byMove [
.last 39 (2,true),
.cycle 23 1 false (-1),
.last 14 (2,true),
.cycle 0 18 true (-1),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.cycle 32 1 false (-2),
.cycle 28 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 18 1 false (-2),
.cycle 30 1 false (-2),
.cycle 9 7 false (1),
.last 17 (2,true),
.last 14 (2,true),
.cycle 5 9 false (3),
.last 19 (2,true),
.cycle 16 1 false (-2),
.last 39 (2,true),
.cycle 28 1 false (-2),
.last 14 (2,true),
.cycle 0 15 true (-1),
.cycle 31 1 false (-3),
.cycle 18 1 false (-2)
])
theorem kid05_part1098_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1098) = true := by rfl

def kid05_part1099 : Audit := .split 13 (2,true) (byMove [
.last 16 (1,true),
.last 14 (1,true),
.cycle 17 1 false (-1),
.last 16 (1,true),
.cycle 1 16 false (3),
.cycle 16 1 false (-2),
.cycle 1 15 true (-1),
.last 14 (1,true),
.cycle 1 33 true (-2),
.cycle 0 15 true (-1),
.cycle 18 1 false (-2),
.cycle 1 48 true (-3),
.cycle 9 7 false (1),
.last 14 (1,true),
.cycle 20 1 false (0),
.cycle 5 9 false (3),
.cycle 1 21 true (-2),
.cycle 16 1 false (-2),
.cycle 1 15 true (-1),
.last 14 (1,true),
.cycle 1 44 true (-3),
.cycle 0 15 true (-1),
.cycle 1 18 false (3),
.cycle 18 1 false (-2)
])
theorem kid05_part1099_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1099) = true := by rfl

def kid05_part1100 : Audit := .cycle 24 9 false (2)
theorem kid05_part1100_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1100) = true := by rfl

def kid05_part1101 : Audit := .cycle 16 1 false (0)
theorem kid05_part1101_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1101) = true := by rfl

def kid05_part1102 : Audit := .cycle 16 1 false (-2)
theorem kid05_part1102_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1102) = true := by rfl

def kid05_part1103 : Audit := .cycle 9 3 false (1)
theorem kid05_part1103_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1103) = true := by rfl

def kid05_part1079 : Audit := .split 11 (4,false) (byMove [(kid05_part1080),(kid05_part1081),(kid05_part1082),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103)])

theorem kid05_part1079_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part1079) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part1080),(kid05_part1081),(kid05_part1082),(kid05_part1083),(kid05_part1084),(kid05_part1085),(kid05_part1086),(kid05_part1087),(kid05_part1088),(kid05_part1089),(kid05_part1090),(kid05_part1091),(kid05_part1092),(kid05_part1093),(kid05_part1094),(kid05_part1095),(kid05_part1096),(kid05_part1097),(kid05_part1098),(kid05_part1099),(kid05_part1100),(kid05_part1101),(kid05_part1102),(kid05_part1103)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1080_checked

  · exact kid05_part1086_checked

  · exact kid05_part1092_checked

  · exact kid05_part1098_checked

  · exact kid05_part1081_checked

  · exact kid05_part1087_checked

  · exact kid05_part1093_checked

  · exact kid05_part1099_checked

  · exact kid05_part1082_checked

  · exact kid05_part1088_checked

  · exact kid05_part1094_checked

  · exact kid05_part1100_checked

  · exact kid05_part1083_checked

  · exact kid05_part1089_checked

  · exact kid05_part1095_checked

  · exact kid05_part1101_checked

  · exact kid05_part1084_checked

  · exact kid05_part1090_checked

  · exact kid05_part1096_checked

  · exact kid05_part1102_checked

  · exact kid05_part1085_checked

  · exact kid05_part1091_checked

  · exact kid05_part1097_checked

  · exact kid05_part1103_checked

def kid05_part1104 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1104_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part1104) = true := by rfl

def kid05_part1105 : Audit := .cycle 13 1 false (1)
theorem kid05_part1105_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part1105) = true := by rfl

def kid05_part1107 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.last 17 (4,false),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 24 1 false (2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 256, 128, 256, 8, 32768, 262144, 256, 262144],[16, 256, 32768, 1, 32768, 2, 65536, 262144, 256, 4096, 256, 8192, 16, 256, 32768, 1, 32768, 2, 262144],345628⟩,
.cycle 0 15 true (0),
.cycle 0 31 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 0 20 true (0),
.last 17 (4,false),
.cycle 21 1 false (1),
.last 17 (4,false),
.cycle 20 1 false (0),
.cycle 0 17 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 18 true (0)
])
theorem kid05_part1107_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part1107) = true := by rfl

def kid05_part1108 : Audit := .cycle 0 15 true (0)
theorem kid05_part1108_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part1108) = true := by rfl

def kid05_part1109 : Audit := .cycle 13 1 false (1)
theorem kid05_part1109_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part1109) = true := by rfl

def kid05_part1110 : Audit := .cycle 12 1 false (0)
theorem kid05_part1110_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part1110) = true := by rfl

def kid05_part1111 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 16 1 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 18 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 24 1 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 33 (2,true),
.cycle 9 4 true (0)
])
theorem kid05_part1111_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part1111) = true := by rfl

def kid05_part1112 : Audit := .cycle 12 1 false (0)
theorem kid05_part1112_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part1112) = true := by rfl

def kid05_part1113 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 14 1 false (4),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1113_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part1113) = true := by rfl

def kid05_part1114 : Audit := .cycle 20 1 false (4)
theorem kid05_part1114_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part1114) = true := by rfl

def kid05_part1115 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.last 13 (4,false),
.cycle 13 1 false (3),
.cycle 22 1 false (2),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.last 16 (4,false),
.last 13 (4,false),
.cycle 17 1 false (5)
])
theorem kid05_part1115_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part1115) = true := by rfl

def kid05_part1116 : Audit := .cycle 0 13 true (0)
theorem kid05_part1116_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part1116) = true := by rfl

def kid05_part1117 : Audit := .cycle 13 1 false (1)
theorem kid05_part1117_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part1117) = true := by rfl

def kid05_part1118 : Audit := .cycle 20 1 false (4)
theorem kid05_part1118_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part1118) = true := by rfl

def kid05_part1119 : Audit := .cycle 16 1 false (0)
theorem kid05_part1119_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part1119) = true := by rfl

def kid05_part1120 : Audit := .split 13 (2,true) (byMove [
.last 15 (4,false),
.cycle 11 3 false (1),
.cycle 16 1 false (0),
.cycle 11 6 true (0),
.cycle 15 1 false (-1),
.cycle 25 1 false (3),
.last 15 (4,false),
.cycle 11 20 true (0),
.cycle 23 1 false (1),
.cycle 0 15 true (0),
.last 20 (4,false),
.cycle 10 20 true (0),
.cycle 16 1 false (0),
.cycle 11 3 false (1),
.cycle 19 1 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.last 15 (4,false),
.cycle 11 5 false (2),
.cycle 2 13 true (0),
.cycle 0 15 true (0),
.last 34 (4,false),
.cycle 29 5 true (3)
])
theorem kid05_part1120_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part1120) = true := by rfl

def kid05_part1121 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 23 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.cycle 0 16 true (0),
.cycle 23 1 false (5),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.cycle 15 1 true (3),
.cycle 16 1 false (4),
.last 18 (2,true),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 22 1 false (4),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (0)
])
theorem kid05_part1121_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part1121) = true := by rfl

def kid05_part1122 : Audit := .cycle 12 1 false (0)
theorem kid05_part1122_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part1122) = true := by rfl

def kid05_part1123 : Audit := .split 12 (4,false) (byMove [
.last 15 (2,true),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 11 2 true (0),
.last 13 (2,true),
.cycle 16 1 false (4),
.cycle 14 1 false (0),
.cycle 24 1 false (4),
.cycle 16 1 false (-2),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 21 true (0),
.cycle 15 1 false (-1),
.last 13 (2,true),
.cycle 13 4 true (1),
.last 16 (2,true),
.cycle 10 20 true (0)
])
theorem kid05_part1123_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part1123) = true := by rfl

def kid05_part1124 : Audit := .cycle 12 1 false (0)
theorem kid05_part1124_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part1124) = true := by rfl

def kid05_part1125 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 16 1 false (0),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 0 34 true (0),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 13 1 true (3),
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 18 1 false (2),
.cycle 16 1 false (0),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 30 true (0),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1125_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part1125) = true := by rfl

def kid05_part1126 : Audit := .cycle 1 12 true (0)
theorem kid05_part1126_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part1126) = true := by rfl

def kid05_part1127 : Audit := .split 12 (2,true) (byMove [
.last 14 (4,false),
.cycle 20 1 false (2),
.cycle 15 1 false (1),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 21 1 false (3),
.cycle 0 13 true (0),
.cycle 14 13 true (1),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (0),
.cycle 15 1 false (1),
.cycle 11 2 true (1),
.last 17 (4,false),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 21 1 false (3),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 16 14 true (1)
])
theorem kid05_part1127_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part1127) = true := by rfl

def kid05_part1128 : Audit := .cycle 0 13 true (0)
theorem kid05_part1128_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part1128) = true := by rfl

def kid05_part1129 : Audit := .cycle 21 1 false (3)
theorem kid05_part1129_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part1129) = true := by rfl

def kid05_part1130 : Audit := .cycle 25 3 true (3)
theorem kid05_part1130_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part1130) = true := by rfl

def kid05_part1106 : Audit := .split 11 (1,true) (byMove [(kid05_part1107),(kid05_part1108),(kid05_part1109),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118),(kid05_part1119),(kid05_part1120),(kid05_part1121),(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130)])

theorem kid05_part1106_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part1106) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (1,true) (some mv)) (byMove [(kid05_part1107),(kid05_part1108),(kid05_part1109),(kid05_part1110),(kid05_part1111),(kid05_part1112),(kid05_part1113),(kid05_part1114),(kid05_part1115),(kid05_part1116),(kid05_part1117),(kid05_part1118),(kid05_part1119),(kid05_part1120),(kid05_part1121),(kid05_part1122),(kid05_part1123),(kid05_part1124),(kid05_part1125),(kid05_part1126),(kid05_part1127),(kid05_part1128),(kid05_part1129),(kid05_part1130)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1107_checked

  · exact kid05_part1113_checked

  · exact kid05_part1119_checked

  · exact kid05_part1125_checked

  · exact kid05_part1108_checked

  · exact kid05_part1114_checked

  · exact kid05_part1120_checked

  · exact kid05_part1126_checked

  · exact kid05_part1109_checked

  · exact kid05_part1115_checked

  · exact kid05_part1121_checked

  · exact kid05_part1127_checked

  · exact kid05_part1110_checked

  · exact kid05_part1116_checked

  · exact kid05_part1122_checked

  · exact kid05_part1128_checked

  · exact kid05_part1111_checked

  · exact kid05_part1117_checked

  · exact kid05_part1123_checked

  · exact kid05_part1129_checked

  · exact kid05_part1112_checked

  · exact kid05_part1118_checked

  · exact kid05_part1124_checked

  · exact kid05_part1130_checked

def kid05_part1132 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 0 20 true (0),
.cycle 0 17 true (0),
.last 35 (1,true),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 true (2),
.cycle 37 1 false (1),
.last 18 (1,true),
.cycle 13 4 true (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 9 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 25, 4, 4, 64],[16, 64, 4, 1, 8, 4, 64],64⟩,
.cycle 15 4 true (1),
.cycle 16 1 true (2),
.cycle 0 20 true (0)
])
theorem kid05_part1132_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1132) = true := by rfl

def kid05_part1133 : Audit := .cycle 0 15 true (0)
theorem kid05_part1133_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1133) = true := by rfl

def kid05_part1134 : Audit := .cycle 13 1 false (1)
theorem kid05_part1134_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1134) = true := by rfl

def kid05_part1135 : Audit := .cycle 12 1 false (0)
theorem kid05_part1135_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1135) = true := by rfl

def kid05_part1136 : Audit := .split 12 (4,false) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 16 1 false (0),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.cycle 15 1 false (1),
.cycle 13 1 false (1),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.last 14 (1,true),
.cycle 18 1 false (2),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.cycle 23 1 false (1),
.cycle 9 4 true (0)
])
theorem kid05_part1136_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1136) = true := by rfl

def kid05_part1137 : Audit := .cycle 12 1 false (0)
theorem kid05_part1137_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1137) = true := by rfl

def kid05_part1138 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 14 1 false (4),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1138_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1138) = true := by rfl

def kid05_part1139 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 20 1 false (2),
.cycle 14 1 false (2),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 20 1 false (4),
.cycle 14 1 false (4),
.cycle 13 1 false (3),
.last 13 (4,false),
.cycle 13 1 false (3),
.cycle 17 1 false (1),
.cycle 11 18 true (1),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (3),
.last 16 (4,false),
.last 13 (4,false),
.cycle 23 1 false (5)
])
theorem kid05_part1139_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1139) = true := by rfl

def kid05_part1140 : Audit := .cycle 14 1 false (4)
theorem kid05_part1140_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1140) = true := by rfl

def kid05_part1141 : Audit := .cycle 0 13 true (0)
theorem kid05_part1141_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1141) = true := by rfl

def kid05_part1142 : Audit := .cycle 13 1 false (1)
theorem kid05_part1142_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1142) = true := by rfl

def kid05_part1143 : Audit := .cycle 14 1 false (4)
theorem kid05_part1143_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1143) = true := by rfl

def kid05_part1144 : Audit := .split 13 (1,true) (byMove [
.last 15 (4,false),
.cycle 22 1 false (0),
.cycle 11 3 false (1),
.cycle 0 18 true (0),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 15 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 256, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2, 1, 256, 4, 16, 2, 256, 1, 8, 4, 4096],5648⟩,
.cycle 0 35 true (0),
.cycle 0 15 true (0),
.last 20 (4,false),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 19 1 false (-1),
.cycle 11 3 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (0),
.last 15 (4,false),
.cycle 1 14 true (0),
.cycle 2 20 true (0),
.cycle 0 15 true (0),
.cycle 23 1 false (1),
.cycle 0 31 true (0)
])
theorem kid05_part1144_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1144) = true := by rfl

def kid05_part1145 : Audit := .split 14 (1,true) (byMove [
.last 20 (4,false),
.last 19 (4,false),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 24 1 false (4),
.cycle 11 4 true (0),
.last 17 (4,false),
.cycle 16 1 false (0),
.cycle 22 1 false (4),
.cycle 19 1 false (-1),
.cycle 12 3 false (1),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.last 15 (4,false),
.cycle 15 1 false (-1),
.last 24 (4,false),
.cycle 1 16 true (0),
.cycle 13 2 true (0),
.last 17 (4,false),
.cycle 0 19 true (0),
.cycle 0 43 true (0)
])
theorem kid05_part1145_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1145) = true := by rfl

def kid05_part1146 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (0),
.cycle 23 1 false (3),
.cycle 17 1 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.cycle 0 16 true (0),
.cycle 23 1 false (5),
.cycle 17 1 false (5),
.cycle 16 1 false (4),
.cycle 15 1 true (3),
.cycle 16 1 false (4),
.last 17 (1,true),
.cycle 11 7 true (0),
.cycle 0 18 true (0),
.cycle 16 1 false (2),
.cycle 15 1 false (3),
.cycle 16 1 false (2),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 22 1 false (4),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (0)
])
theorem kid05_part1146_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1146) = true := by rfl

def kid05_part1147 : Audit := .cycle 12 1 false (0)
theorem kid05_part1147_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1147) = true := by rfl

def kid05_part1148 : Audit := .split 12 (4,false) (byMove [
.cycle 0 22 true (-1),
.cycle 26 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 11 2 true (0),
.cycle 16 1 false (4),
.cycle 14 1 false (0),
.cycle 18 1 false (4),
.last 14 (1,true),
.cycle 16 1 false (-2),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 12 1 false (0),
.cycle 13 1 false (-1),
.cycle 0 21 true (0),
.last 13 (1,true),
.cycle 15 1 false (-1),
.cycle 13 4 true (1),
.cycle 0 17 true (0),
.cycle 0 35 true (0)
])
theorem kid05_part1148_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1148) = true := by rfl

def kid05_part1149 : Audit := .cycle 12 1 false (0)
theorem kid05_part1149_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1149) = true := by rfl

def kid05_part1150 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.cycle 16 1 false (0),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 33 (1,true),
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.cycle 13 1 true (3),
.cycle 0 24 true (0),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 18 1 false (2),
.cycle 16 1 false (0),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 30 true (0),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1150_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1150) = true := by rfl

def kid05_part1151 : Audit := .split 12 (1,true) (byMove [
.last 14 (4,false),
.cycle 21 1 false (1),
.cycle 1 13 true (0),
.cycle 0 14 true (0),
.cycle 14 1 false (0),
.cycle 15 1 false (3),
.cycle 0 13 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 386, 4096, 2, 128, 256, 8, 16, 4096, 128, 4096],[16, 2, 128, 1, 256, 4, 16, 2, 128, 1, 8, 4, 4096],5648⟩,
.cycle 20 1 false (2),
.cycle 18 1 false (2),
.last 13 (4,false),
.cycle 8 5 true (0),
.cycle 15 1 false (1),
.cycle 12 5 false (2),
.cycle 11 2 true (1),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 1 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 1 15 true (0)
])
theorem kid05_part1151_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1151) = true := by rfl

def kid05_part1152 : Audit := .cycle 2 11 true (0)
theorem kid05_part1152_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1152) = true := by rfl

def kid05_part1153 : Audit := .cycle 0 13 true (0)
theorem kid05_part1153_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1153) = true := by rfl

def kid05_part1154 : Audit := .cycle 15 1 false (3)
theorem kid05_part1154_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1154) = true := by rfl

def kid05_part1155 : Audit := .cycle 20 1 false (2)
theorem kid05_part1155_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1155) = true := by rfl

def kid05_part1131 : Audit := .split 11 (2,true) (byMove [(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144),(kid05_part1145),(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152),(kid05_part1153),(kid05_part1154),(kid05_part1155)])

theorem kid05_part1131_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part1131) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part1132),(kid05_part1133),(kid05_part1134),(kid05_part1135),(kid05_part1136),(kid05_part1137),(kid05_part1138),(kid05_part1139),(kid05_part1140),(kid05_part1141),(kid05_part1142),(kid05_part1143),(kid05_part1144),(kid05_part1145),(kid05_part1146),(kid05_part1147),(kid05_part1148),(kid05_part1149),(kid05_part1150),(kid05_part1151),(kid05_part1152),(kid05_part1153),(kid05_part1154),(kid05_part1155)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1132_checked

  · exact kid05_part1138_checked

  · exact kid05_part1144_checked

  · exact kid05_part1150_checked

  · exact kid05_part1133_checked

  · exact kid05_part1139_checked

  · exact kid05_part1145_checked

  · exact kid05_part1151_checked

  · exact kid05_part1134_checked

  · exact kid05_part1140_checked

  · exact kid05_part1146_checked

  · exact kid05_part1152_checked

  · exact kid05_part1135_checked

  · exact kid05_part1141_checked

  · exact kid05_part1147_checked

  · exact kid05_part1153_checked

  · exact kid05_part1136_checked

  · exact kid05_part1142_checked

  · exact kid05_part1148_checked

  · exact kid05_part1154_checked

  · exact kid05_part1137_checked

  · exact kid05_part1143_checked

  · exact kid05_part1149_checked

  · exact kid05_part1155_checked

def kid05_part1156 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 21 1 false (3),
.cycle 15 1 false (3),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 21 1 false (5),
.cycle 15 1 false (5),
.cycle 14 1 false (4),
.cycle 13 1 true (3),
.cycle 14 1 false (4),
.split 15 (1,true) (byMove [
.cycle 12 4 true (2),
.cycle 24 1 false (2),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (3),
.cycle 0 16 true (0),
.cycle 30 1 false (4),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 18 1 false (2),
.last 18 (2,true),
.last 16 (2,true),
.cycle 11 5 true (1),
.cycle 17 1 false (1),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.cycle 0 22 true (0),
.cycle 0 19 true (0)
]),
.split 15 (2,true) (byMove [
.cycle 12 4 true (2),
.last 16 (1,true),
.cycle 18 1 false (2),
.cycle 0 17 true (0),
.cycle 17 1 false (1),
.cycle 17 1 false (3),
.cycle 0 16 true (0),
.cycle 30 1 false (4),
.cycle 23 1 false (3),
.cycle 21 1 false (3),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 18 1 false (2),
.last 16 (1,true),
.cycle 11 7 true (1),
.cycle 11 5 true (1),
.cycle 17 1 false (1),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.last 17 (1,true),
.cycle 0 19 true (0)
]),
.cycle 0 16 true (0),
.cycle 14 1 false (2),
.cycle 13 1 false (3),
.cycle 14 1 false (2),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 20 1 false (4),
.cycle 11 4 true (1),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1156_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part1156) = true := by rfl

def kid05_part1157 : Audit := .cycle 12 1 false (0)
theorem kid05_part1157_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part1157) = true := by rfl

def kid05_part1158 : Audit := .cycle 13 1 false (3)
theorem kid05_part1158_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part1158) = true := by rfl

def kid05_part1160 : Audit := .split 14 (4,false) (byMove [
.last 17 (2,true),
.cycle 28 13 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.last 18 (2,true),
.last 15 (2,true),
.cycle 18 1 false (4),
.cycle 16 1 false (0),
.cycle 25 1 false (3),
.cycle 11 4 true (-1),
.last 16 (2,true),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 19 36 true (-1),
.cycle 1 20 true (-1),
.last 15 (2,true),
.cycle 15 4 true (1),
.cycle 26 1 false (0),
.cycle 18 1 false (0)
])
theorem kid05_part1160_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part1160) = true := by rfl

def kid05_part1161 : Audit := .cycle 21 1 false (-1)
theorem kid05_part1161_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part1161) = true := by rfl

def kid05_part1162 : Audit := .split 13 (2,true) (byMove [
.last 19 (4,false),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 0 20 true (-1),
.cycle 23 1 false (1),
.last 17 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 11 3 false (0),
.cycle 18 1 false (-2),
.cycle 0 26 true (-2),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 37 1 false (-1),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 0, 128, 256, 32768, 4194320, 1073741824, 128, 524288, 1048576, 2097152, 32768, 1073741824, 256, 33554432, 67108864, 134217728, 268697600, 1073741824, 128, 33554432, 67108864, 134217728, 1594130816, 1073741824, 1594130816, 1073741824],[16, 0, 128, 1, 0, 256, 65536, 256, 128, 4096, 32768, 256, 4194304, 32768, 524288, 262144, 256, 256, 268435456, 335806464, 33554432, 16777216, 32768, 335839232, 268435456, 1594130816, 33554432, 16777216, 1594130816, 1594130816, 1073741824],2138928656⟩,
.last 17 (4,false),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid05_part1162_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part1162) = true := by rfl

def kid05_part1163 : Audit := .cycle 0 20 true (-1)
theorem kid05_part1163_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part1163) = true := by rfl

def kid05_part1164 : Audit := .cycle 14 1 false (-2)
theorem kid05_part1164_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part1164) = true := by rfl

def kid05_part1165 : Audit := .cycle 10 3 false (0)
theorem kid05_part1165_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part1165) = true := by rfl

def kid05_part1166 : Audit := .cycle 6 7 false (3)
theorem kid05_part1166_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part1166) = true := by rfl

def kid05_part1167 : Audit := .far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 0, 8192, 16384, 512, 16, 1073741824, 128, 33554432, 67108864, 2097152, 1024, 1073741824, 33554432, 33554432, 67108864, 134217728, 16384, 1073741824, 33554432, 33554432, 67108864, 134217728, 1595949056, 1073741824, 1595949056, 1073741824],[16, 2, 1073741824, 1, 0, 128, 1024, 128, 1073741824, 64, 16384, 524288, 4194304, 524288, 1073741824, 262144, 67108864, 16384, 268435456, 33554432, 1073741824, 16777216, 67108864, 33554432, 268435456, 33554432, 1073741824, 16777216, 1595949056, 1595949056, 1073741824],2145367890⟩
theorem kid05_part1167_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part1167) = true := by rfl

def kid05_part1168 : Audit := .split 13 (2,true) (byMove [
.last 18 (4,false),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.last 17 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1),
.last 15 (4,false),
.cycle 24 1 false (0),
.cycle 24 1 false (0),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 10 32 true (-2),
.cycle 31 1 false (-1),
.cycle 12 4 true (0),
.last 17 (4,false),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 9 5 false (1),
.last 15 (4,false),
.last 80 (4,false),
.cycle 2 13 true (-1),
.cycle 0 15 true (-1),
.cycle 3 17 false (3),
.cycle 6 9 false (3)
])
theorem kid05_part1168_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part1168) = true := by rfl

def kid05_part1169 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 24 9 false (2),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.cycle 0 16 true (-1),
.cycle 26 9 false (2),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 18 9 false (2),
.cycle 24 9 false (2),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.cycle 30 9 false (2),
.cycle 1 15 true (-1),
.cycle 24 9 false (2),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1169_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part1169) = true := by rfl

def kid05_part1170 : Audit := .cycle 9 5 false (1)
theorem kid05_part1170_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part1170) = true := by rfl

def kid05_part1171 : Audit := .cycle 36 1 false (-2)
theorem kid05_part1171_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part1171) = true := by rfl

def kid05_part1172 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1172_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part1172) = true := by rfl

def kid05_part1173 : Audit := .split 15 (2,true) (byMove [
.last 17 (4,false),
.cycle 13 3 false (-1),
.cycle 18 1 false (-2),
.cycle 11 6 true (-2),
.cycle 17 1 false (-3),
.cycle 10 6 false (0),
.cycle 6 10 false (3),
.cycle 42 1 false (-2),
.cycle 29 1 false (-1),
.cycle 8 12 false (2),
.cycle 9 8 false (1),
.cycle 12 7 false (0),
.cycle 18 1 false (-2),
.cycle 13 3 false (-1),
.cycle 21 1 false (-1),
.cycle 19 1 false (-1),
.cycle 17 1 false (-3),
.cycle 10 6 false (0),
.cycle 22 1 false (-2),
.cycle 12 5 false (0),
.cycle 34 1 false (-2),
.cycle 24 1 false (-2),
.cycle 20 1 false (-2),
.cycle 9 10 false (1)
])
theorem kid05_part1173_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part1173) = true := by rfl

def kid05_part1174 : Audit := .split 13 (2,true) (byMove [
.last 18 (4,false),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 19 1 false (1),
.cycle 18 1 false (4),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 11 3 false (0),
.cycle 21 1 false (-1),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 9 7 false (1),
.cycle 12 2 true (-1),
.last 38 (4,false),
.cycle 5 9 false (3),
.cycle 10 5 false (0),
.cycle 17 1 false (-1)
])
theorem kid05_part1174_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part1174) = true := by rfl

def kid05_part1175 : Audit := .cycle 16 1 false (0)
theorem kid05_part1175_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part1175) = true := by rfl

def kid05_part1176 : Audit := .cycle 14 1 false (-2)
theorem kid05_part1176_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part1176) = true := by rfl

def kid05_part1177 : Audit := .cycle 10 3 false (0)
theorem kid05_part1177_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part1177) = true := by rfl

def kid05_part1178 : Audit := .cycle 19 1 false (-1)
theorem kid05_part1178_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part1178) = true := by rfl

def kid05_part1179 : Audit := .cycle 31 1 false (-1)
theorem kid05_part1179_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part1179) = true := by rfl

def kid05_part1180 : Audit := .split 13 (2,true) (byMove [
.last 15 (4,false),
.cycle 0 17 true (-1),
.cycle 17 1 false (-1),
.cycle 2 15 true (-1),
.cycle 2 16 false (3),
.cycle 17 1 false (-1),
.last 15 (4,false),
.cycle 27 1 false (-1),
.last 33 (4,false),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 38 1 false (-2),
.cycle 9 7 false (1),
.cycle 12 2 true (0),
.cycle 20 1 false (0),
.cycle 5 9 false (3),
.last 21 (4,false),
.cycle 17 1 false (-1),
.last 15 (4,false),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 1073741824, 0, 128, 256, 32768, 4194320, 1073741824, 128, 524288, 1048576, 2097152, 32768, 1073741824, 256, 33554432, 67108864, 134217728, 268697600, 1073741824, 128, 33554432, 67108864, 134217728, 1594130816, 1073741824, 1594130816, 1073741824],[16, 256, 128, 1, 0, 256, 65536, 256, 128, 4096, 32768, 256, 4194304, 1048576, 524288, 262144, 256, 256, 268435456, 67108864, 33554432, 16777216, 32768, 67141632, 268435456, 67108864, 33554432, 16777216, 1594130816, 1594130816, 1073741824],2138928656⟩,
.last 34 (4,false),
.cycle 0 15 true (-1),
.last 23 (4,false),
.cycle 21 1 false (-1)
])
theorem kid05_part1180_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part1180) = true := by rfl

def kid05_part1181 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 29 1 false (-1),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 29 1 false (-3),
.cycle 21 1 false (-1),
.cycle 0 16 true (-1),
.cycle 31 1 false (-1),
.last 33 (2,true),
.cycle 63 1 false (-3),
.cycle 15 1 true (3),
.cycle 23 1 false (-1),
.cycle 13 6 true (1),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 3 13 false (3),
.cycle 4 18 false (3),
.cycle 21 1 false (-1),
.cycle 35 1 false (-1),
.cycle 1 15 true (-1),
.cycle 29 1 false (-1),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1181_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part1181) = true := by rfl

def kid05_part1182 : Audit := .cycle 17 1 false (-1)
theorem kid05_part1182_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part1182) = true := by rfl

def kid05_part1183 : Audit := .cycle 9 7 false (1)
theorem kid05_part1183_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part1183) = true := by rfl

def kid05_part1159 : Audit := .split 12 (1,true) (byMove [(kid05_part1160),(kid05_part1161),(kid05_part1162),(kid05_part1163),(kid05_part1164),(kid05_part1165),(kid05_part1166),(kid05_part1167),(kid05_part1168),(kid05_part1169),(kid05_part1170),(kid05_part1171),(kid05_part1172),(kid05_part1173),(kid05_part1174),(kid05_part1175),(kid05_part1176),(kid05_part1177),(kid05_part1178),(kid05_part1179),(kid05_part1180),(kid05_part1181),(kid05_part1182),(kid05_part1183)])

theorem kid05_part1159_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part1159) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) 12 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (1,true) (some mv)) (byMove [(kid05_part1160),(kid05_part1161),(kid05_part1162),(kid05_part1163),(kid05_part1164),(kid05_part1165),(kid05_part1166),(kid05_part1167),(kid05_part1168),(kid05_part1169),(kid05_part1170),(kid05_part1171),(kid05_part1172),(kid05_part1173),(kid05_part1174),(kid05_part1175),(kid05_part1176),(kid05_part1177),(kid05_part1178),(kid05_part1179),(kid05_part1180),(kid05_part1181),(kid05_part1182),(kid05_part1183)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1160_checked

  · exact kid05_part1166_checked

  · exact kid05_part1172_checked

  · exact kid05_part1178_checked

  · exact kid05_part1161_checked

  · exact kid05_part1167_checked

  · exact kid05_part1173_checked

  · exact kid05_part1179_checked

  · exact kid05_part1162_checked

  · exact kid05_part1168_checked

  · exact kid05_part1174_checked

  · exact kid05_part1180_checked

  · exact kid05_part1163_checked

  · exact kid05_part1169_checked

  · exact kid05_part1175_checked

  · exact kid05_part1181_checked

  · exact kid05_part1164_checked

  · exact kid05_part1170_checked

  · exact kid05_part1176_checked

  · exact kid05_part1182_checked

  · exact kid05_part1165_checked

  · exact kid05_part1171_checked

  · exact kid05_part1177_checked

  · exact kid05_part1183_checked

def kid05_part1185 : Audit := .split 14 (4,false) (byMove [
.last 36 (1,true),
.cycle 28 13 false (2),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.last 15 (1,true),
.cycle 29 1 false (1),
.cycle 18 1 false (4),
.cycle 16 1 false (0),
.cycle 25 1 false (3),
.last 16 (1,true),
.cycle 11 4 true (-1),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.cycle 14 1 false (0),
.cycle 15 1 false (-1),
.last 36 (1,true),
.last 15 (1,true),
.cycle 27 1 false (3),
.cycle 15 4 true (1),
.last 24 (1,true),
.last 16 (1,true)
])
theorem kid05_part1185_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1185) = true := by rfl

def kid05_part1186 : Audit := .split 13 (1,true) (byMove [
.last 19 (4,false),
.cycle 21 1 false (-1),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 17 (4,false),
.cycle 27 1 false (3),
.last 17 (4,false),
.cycle 14 1 false (0),
.last 14 (4,false),
.cycle 14 1 false (0),
.cycle 18 1 false (-2),
.cycle 11 3 false (0),
.last 23 (4,false),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.last 17 (4,false),
.cycle 19 14 true (0),
.last 17 (4,false),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 9 5 false (1)
])
theorem kid05_part1186_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1186) = true := by rfl

def kid05_part1187 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1187_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1187) = true := by rfl

def kid05_part1188 : Audit := .split 15 (1,true) (byMove [
.last 17 (4,false),
.cycle 24 1 false (0),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 17 1 false (-1),
.cycle 0 24 true (-1),
.last 17 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 386, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 4360, 1, 256, 128, 16, 2, 128, 1, 256, 2, 4096],5648⟩,
.last 20 (4,false),
.cycle 0 17 true (-1),
.last 24 (4,false),
.cycle 0 20 true (-1),
.cycle 18 1 false (0),
.cycle 11 6 true (-1),
.cycle 17 1 false (-1),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 10 6 true (-1),
.last 17 (4,false),
.cycle 15 14 true (1),
.cycle 0 18 true (-1),
.cycle 0 17 true (-1),
.cycle 0 24 true (-1),
.cycle 15 2 true (1)
])
theorem kid05_part1188_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1188) = true := by rfl

def kid05_part1189 : Audit := .cycle 14 1 false (-2)
theorem kid05_part1189_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1189) = true := by rfl

def kid05_part1190 : Audit := .cycle 10 3 false (0)
theorem kid05_part1190_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1190) = true := by rfl

def kid05_part1191 : Audit := .cycle 6 7 false (3)
theorem kid05_part1191_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1191) = true := by rfl

def kid05_part1192 : Audit := .split 13 (1,true) (byMove [
.last 30 (4,false),
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.last 17 (4,false),
.last 14 (4,false),
.cycle 9 5 false (1),
.last 15 (4,false),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 258, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2, 1, 256, 2, 16, 2, 2, 1, 256, 2, 4096],5648⟩,
.cycle 47 1 false (-1),
.cycle 0 15 true (-1),
.cycle 7 7 false (3),
.cycle 24 11 true (0),
.cycle 9 9 false (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 258, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2, 1, 256, 2, 16, 2, 2, 1, 256, 2, 4096],5648⟩,
.last 17 (4,false),
.cycle 18 1 false (0),
.last 14 (4,false),
.cycle 9 5 false (1),
.last 15 (4,false),
.cycle 13 14 true (1),
.cycle 16 15 true (0),
.cycle 0 15 true (-1),
.cycle 11 23 true (-2),
.cycle 13 2 true (1)
])
theorem kid05_part1192_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1192) = true := by rfl

def kid05_part1193 : Audit := .cycle 24 1 false (0)
theorem kid05_part1193_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1193) = true := by rfl

def kid05_part1194 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.cycle 24 9 false (2),
.cycle 24 1 false (0),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.cycle 0 16 true (-1),
.cycle 26 9 false (2),
.cycle 26 1 false (0),
.cycle 24 1 false (0),
.cycle 15 1 true (3),
.cycle 18 9 false (2),
.last 17 (1,true),
.cycle 24 9 false (2),
.cycle 0 18 true (-1),
.cycle 22 1 false (0),
.cycle 20 1 false (-2),
.cycle 16 9 false (2),
.last 27 (1,true),
.cycle 1 15 true (-1),
.cycle 24 9 false (2),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1194_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1194) = true := by rfl

def kid05_part1195 : Audit := .cycle 9 5 false (1)
theorem kid05_part1195_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1195) = true := by rfl

def kid05_part1196 : Audit := .split 22 (1,true) (byMove [
.last 24 (4,false),
.cycle 31 1 false (-1),
.cycle 24 1 false (0),
.cycle 0 33 true (-1),
.cycle 24 1 false (-2),
.cycle 54 1 false (-4),
.cycle 6 17 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 290, 4096, 34, 128, 256, 8, 16, 4096, 34, 4096],[16, 2, 32, 1, 290, 32, 16, 2, 32, 1, 290, 2, 4096],5648⟩,
.cycle 12 11 true (0),
.cycle 56 1 false (0),
.cycle 36 1 false (-2),
.cycle 10 13 true (-1),
.cycle 25 1 false (-1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 32, 128, 256, 8, 16, 4096, 32, 4096],[16, 32, 32, 1, 32, 32, 16, 32, 32, 1, 32, 32, 4096],5648⟩,
.cycle 10 17 true (-1),
.cycle 26 1 false (0),
.cycle 24 1 false (-2),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 32, 4096, 32, 128, 256, 8, 16, 4096, 32, 4096],[16, 32, 32, 1, 32, 32, 16, 32, 32, 1, 32, 32, 4096],5648⟩,
.cycle 25 13 false (1),
.cycle 19 14 true (0),
.cycle 12 11 true (0),
.cycle 5 25 false (3),
.cycle 8 22 false (3),
.cycle 21 2 true (0)
])
theorem kid05_part1196_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1196) = true := by rfl

def kid05_part1197 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1197_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1197) = true := by rfl

def kid05_part1198 : Audit := .split 13 (1,true) (byMove [
.last 19 (4,false),
.cycle 8 12 false (2),
.cycle 15 1 false (-1),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 16 1 false (0),
.cycle 24 1 false (4),
.cycle 11 4 true (-1),
.cycle 17 1 false (1),
.cycle 15 1 false (-1),
.cycle 10 4 true (-1),
.cycle 18 1 false (-2),
.cycle 11 3 false (0),
.cycle 18 1 false (0),
.cycle 14 1 false (-2),
.last 14 (4,false),
.cycle 14 1 false (-2),
.cycle 9 7 false (1),
.cycle 13 14 true (-1),
.cycle 12 2 true (-1),
.cycle 5 9 false (3),
.cycle 10 5 false (0),
.cycle 13 2 true (-1)
])
theorem kid05_part1198_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1198) = true := by rfl

def kid05_part1199 : Audit := .cycle 18 1 false (0)
theorem kid05_part1199_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1199) = true := by rfl

def kid05_part1200 : Audit := .cycle 16 1 false (0)
theorem kid05_part1200_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1200) = true := by rfl

def kid05_part1201 : Audit := .cycle 14 1 false (-2)
theorem kid05_part1201_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1201) = true := by rfl

def kid05_part1202 : Audit := .cycle 10 3 false (0)
theorem kid05_part1202_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1202) = true := by rfl

def kid05_part1203 : Audit := .split 17 (1,true) (byMove [
.last 22 (4,false),
.last 22 (4,false),
.cycle 19 1 false (-1),
.cycle 18 1 false (-2),
.last 18 (4,false),
.cycle 18 1 false (-2),
.cycle 20 1 false (0),
.cycle 27 1 false (3),
.last 20 (4,false),
.last 20 (4,false),
.cycle 19 1 false (-1),
.last 22 (4,false),
.cycle 22 1 false (-2),
.cycle 11 7 false (2),
.cycle 22 1 false (0),
.cycle 18 1 false (-2),
.last 18 (4,false),
.cycle 18 1 false (-2),
.last 25 (4,false),
.cycle 17 14 true (-1),
.last 20 (4,false),
.last 20 (4,false),
.last 24 (4,false),
.cycle 16 2 true (-1)
])
theorem kid05_part1203_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1203) = true := by rfl

def kid05_part1204 : Audit := .split 13 (1,true) (byMove [
.last 15 (4,false),
.cycle 23 1 false (-1),
.cycle 11 18 true (-1),
.cycle 0 18 true (-1),
.cycle 0 21 true (-2),
.cycle 16 1 false (-2),
.last 15 (4,false),
.cycle 40 1 false (6),
.cycle 1 14 true (-1),
.cycle 0 15 true (-1),
.cycle 19 1 false (-1),
.cycle 10 18 true (-1),
.cycle 9 7 false (1),
.cycle 11 5 false (1),
.cycle 12 2 true (0),
.cycle 5 9 false (3),
.cycle 25 1 false (-3),
.cycle 16 1 false (-2),
.last 15 (4,false),
.cycle 13 14 true (1),
.cycle 12 14 true (0),
.cycle 0 15 true (-1),
.last 42 (4,false),
.cycle 13 2 true (1)
])
theorem kid05_part1204_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1204) = true := by rfl

def kid05_part1205 : Audit := .split 24 (1,true) (byMove [
.last 26 (4,false),
.cycle 33 1 false (-1),
.cycle 60 1 false (-2),
.cycle 0 35 true (-1),
.cycle 26 1 false (-2),
.cycle 37 1 false (-3),
.cycle 0 36 true (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 33041, 262144, 258, 128, 256, 32768, 16, 262144, 258, 2, 4, 8, 33024, 262144, 258, 262144],[16, 2, 256, 1, 33024, 258, 65536, 8192, 256, 4096, 33024, 2, 16, 2, 4, 1, 33024, 256, 262144],353820⟩,
.cycle 12 13 true (0),
.cycle 58 1 false (0),
.last 34 (4,false),
.cycle 10 15 true (-1),
.cycle 27 1 false (-1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 256, 2, 4, 8, 32768, 262144, 256, 262144],[16, 256, 256, 1, 32768, 256, 65536, 256, 256, 4096, 32768, 256, 16, 256, 4, 1, 32768, 256, 262144],353820⟩,
.cycle 12 15 true (-1),
.cycle 28 1 false (0),
.cycle 26 1 false (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 256, 2, 4, 8, 32768, 262144, 256, 262144],[16, 256, 256, 1, 32768, 256, 65536, 256, 256, 4096, 32768, 256, 16, 256, 4, 1, 32768, 256, 262144],353820⟩,
.cycle 15 45 true (-3),
.cycle 15 14 true (0),
.cycle 12 13 true (0),
.cycle 5 27 false (4),
.last 48 (4,false),
.cycle 23 2 true (0)
])
theorem kid05_part1205_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1205) = true := by rfl

def kid05_part1206 : Audit := .split 15 (4,false) (byMove [
.cycle 0 16 true (-1),
.last 27 (1,true),
.cycle 3 15 false (3),
.cycle 3 13 false (3),
.cycle 29 1 false (-3),
.last 19 (1,true),
.cycle 0 16 true (-1),
.last 29 (1,true),
.last 52 (1,true),
.last 61 (1,true),
.cycle 15 1 true (3),
.last 21 (1,true),
.last 17 (1,true),
.cycle 13 6 true (1),
.cycle 0 18 true (-1),
.cycle 3 13 false (3),
.cycle 4 18 false (3),
.last 19 (1,true),
.last 27 (1,true),
.cycle 1 15 true (-1),
.last 27 (1,true),
.cycle 13 4 true (1),
.cycle 15 1 true (3),
.cycle 0 21 true (-1)
])
theorem kid05_part1206_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1206) = true := by rfl

def kid05_part1207 : Audit := .split 15 (1,true) (byMove [
.last 19 (4,false),
.cycle 8 22 false (2),
.cycle 17 1 false (-1),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.last 17 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.cycle 24 1 false (2),
.cycle 17 1 false (-1),
.last 19 (4,false),
.cycle 20 1 false (-2),
.cycle 11 5 false (1),
.last 19 (4,false),
.cycle 16 1 false (-2),
.last 16 (4,false),
.cycle 16 1 false (-2),
.last 17 (4,false),
.last 19 (4,false),
.last 17 (4,false),
.last 22 (4,false),
.last 20 (4,false),
.cycle 14 2 true (-1)
])
theorem kid05_part1207_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1207) = true := by rfl

def kid05_part1208 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 23 1 false (-1),
.cycle 9 7 false (1),
.cycle 0 22 true (-1),
.cycle 16 1 false (-2),
.cycle 21 1 false (-3),
.cycle 6 9 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 2306, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2048, 1, 256, 2048, 16, 2, 2048, 1, 258, 2, 4096],5648⟩,
.cycle 15 7 true (1),
.last 17 (4,false),
.cycle 9 7 false (1),
.cycle 13 11 true (0),
.cycle 17 1 false (-1),
.cycle 11 5 false (1),
.cycle 22 1 false (0),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 10 5 false (1),
.last 29 (4,false),
.cycle 14 14 true (0),
.cycle 13 7 true (0),
.last 17 (4,false),
.cycle 16 7 false (0),
.cycle 13 2 true (0)
])
theorem kid05_part1208_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1208) = true := by rfl

def kid05_part1184 : Audit := .split 12 (2,true) (byMove [(kid05_part1185),(kid05_part1186),(kid05_part1187),(kid05_part1188),(kid05_part1189),(kid05_part1190),(kid05_part1191),(kid05_part1192),(kid05_part1193),(kid05_part1194),(kid05_part1195),(kid05_part1196),(kid05_part1197),(kid05_part1198),(kid05_part1199),(kid05_part1200),(kid05_part1201),(kid05_part1202),(kid05_part1203),(kid05_part1204),(kid05_part1205),(kid05_part1206),(kid05_part1207),(kid05_part1208)])

theorem kid05_part1184_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part1184) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) 12 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (2,true) (some mv)) (byMove [(kid05_part1185),(kid05_part1186),(kid05_part1187),(kid05_part1188),(kid05_part1189),(kid05_part1190),(kid05_part1191),(kid05_part1192),(kid05_part1193),(kid05_part1194),(kid05_part1195),(kid05_part1196),(kid05_part1197),(kid05_part1198),(kid05_part1199),(kid05_part1200),(kid05_part1201),(kid05_part1202),(kid05_part1203),(kid05_part1204),(kid05_part1205),(kid05_part1206),(kid05_part1207),(kid05_part1208)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

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

  · exact kid05_part1188_checked

  · exact kid05_part1194_checked

  · exact kid05_part1200_checked

  · exact kid05_part1206_checked

  · exact kid05_part1189_checked

  · exact kid05_part1195_checked

  · exact kid05_part1201_checked

  · exact kid05_part1207_checked

  · exact kid05_part1190_checked

  · exact kid05_part1196_checked

  · exact kid05_part1202_checked

  · exact kid05_part1208_checked

def kid05_part1209 : Audit := .cycle 15 1 false (1)
theorem kid05_part1209_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part1209) = true := by rfl

def kid05_part1210 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1210_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part1210) = true := by rfl

def kid05_part1212 : Audit := .split 14 (2,true) (byMove [
.cycle 41 1 false (-3),
.last 15 (1,true),
.cycle 18 1 false (-2),
.last 17 (1,true),
.cycle 10 6 false (0),
.cycle 17 1 false (-3),
.cycle 21 1 false (-3),
.last 15 (1,true),
.cycle 47 1 false (-5),
.cycle 0 18 true (-2),
.cycle 19 1 false (-3),
.cycle 35 1 false (-3),
.cycle 9 8 false (1),
.last 15 (1,true),
.cycle 21 1 false (-1),
.cycle 5 10 false (3),
.cycle 10 6 false (0),
.cycle 17 1 false (-3),
.last 26 (1,true),
.last 15 (1,true),
.cycle 29 1 false (-3),
.cycle 11 20 true (-2),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 4, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 256, 524288, 1048576, 2097152, 256, 256, 1024, 33554432, 67108864, 134217728, 268436480, 67108864, 256, 33554432, 67108864, 134217728, 1594131712, 67108864, 1594131712, 1073741824],[16, 1073741824, 1024, 1, 0, 1024, 65536, 1073741824, 1024, 4096, 256, 1024, 4194304, 1073741824, 4194304, 262144, 32768, 1024, 268435456, 1073741824, 268435456, 16777216, 256, 263168, 268435456, 1073741824, 268435456, 16777216, 1594131712, 1594131712, 1073741824],2138862080⟩,
.cycle 19 1 false (-3)
])
theorem kid05_part1212_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1212) = true := by rfl

def kid05_part1213 : Audit := .cycle 8 10 false (2)
theorem kid05_part1213_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1213) = true := by rfl

def kid05_part1214 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1214_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1214) = true := by rfl

def kid05_part1215 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1215_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1215) = true := by rfl

def kid05_part1216 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1216_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1216) = true := by rfl

def kid05_part1217 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1217_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1217) = true := by rfl

def kid05_part1218 : Audit := .cycle 14 1 false (0)
theorem kid05_part1218_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1218) = true := by rfl

def kid05_part1219 : Audit := .split 12 (1,true) (byMove [
.last 15 (2,true),
.cycle 28 11 false (2),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 15 (2,true),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 22 1 false (4),
.last 13 (2,true),
.cycle 23 1 false (5),
.cycle 14 1 false (0),
.cycle 19 1 false (3),
.cycle 17 1 false (-1),
.last 14 (2,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 13 1 false (-1),
.cycle 17 25 true (-1),
.last 30 (2,true),
.last 13 (2,true),
.cycle 0 44 true (-1),
.cycle 17 24 true (1),
.cycle 15 1 false (-1)
])
theorem kid05_part1219_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1219) = true := by rfl

def kid05_part1220 : Audit := .split 12 (2,true) (byMove [
.cycle 0 19 true (-1),
.cycle 28 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.cycle 19 1 false (5),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.last 13 (1,true),
.cycle 16 1 false (4),
.cycle 17 1 false (5),
.cycle 14 1 false (0),
.cycle 19 1 false (3),
.last 14 (1,true),
.last 15 (1,true),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.cycle 11 2 true (-1),
.cycle 13 1 false (-1),
.cycle 29 1 false (1),
.last 13 (1,true),
.cycle 25 1 false (-1),
.cycle 25 1 false (1),
.cycle 0 46 true (-1),
.cycle 15 1 false (-1)
])
theorem kid05_part1220_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1220) = true := by rfl

def kid05_part1221 : Audit := .cycle 15 1 false (1)
theorem kid05_part1221_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1221) = true := by rfl

def kid05_part1222 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1222_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1222) = true := by rfl

def kid05_part1223 : Audit := .cycle 10 2 true (-1)
theorem kid05_part1223_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1223) = true := by rfl

def kid05_part1224 : Audit := .split 13 (1,true) (byMove [
.cycle 11 4 true (-2),
.cycle 22 1 false (-2),
.last 14 (2,true),
.cycle 0 24 true (-2),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 0, 8192, 16384, 512, 16, 524288, 128, 33554432, 67108864, 2097152, 1024, 16384, 33554432, 33554432, 67108864, 134217728, 16384, 33554432, 33554432, 33554432, 67108864, 134217728, 1409286144, 1174405120, 1107296256, 1073741824],[16, 2, 1073741824, 1, 0, 128, 1024, 128, 1073741824, 64, 16384, 33554432, 4194304, 524288, 1073741824, 262144, 67108864, 1073741824, 268435456, 33554432, 1073741824, 16777216, 67108864, 1073741824, 268435456, 33554432, 1073741824, 16777216, 1140850688, 1107296256, 1073741824],2145301568⟩,
.last 14 (2,true),
.cycle 8 10 false (2),
.cycle 9 6 false (1),
.cycle 18 1 false (-2),
.cycle 16 1 false (-2),
.last 16 (2,true),
.last 14 (2,true),
.cycle 17 1 false (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 19 1 false (-3),
.last 36 (2,true),
.last 14 (2,true),
.cycle 21 1 false (-3),
.cycle 17 1 false (-3),
.cycle 10 6 false (0)
])
theorem kid05_part1224_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1224) = true := by rfl

def kid05_part1225 : Audit := .split 13 (2,true) (byMove [
.cycle 11 4 true (-2),
.last 14 (1,true),
.cycle 16 1 false (-2),
.last 16 (1,true),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 6 8 false (3),
.last 14 (1,true),
.cycle 27 1 false (-1),
.cycle 8 10 false (2),
.cycle 9 6 false (1),
.last 16 (1,true),
.cycle 16 1 false (-2),
.last 14 (1,true),
.cycle 19 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-3),
.cycle 10 4 false (0),
.cycle 19 1 false (-3),
.last 14 (1,true),
.cycle 29 1 false (-3),
.cycle 21 1 false (-3),
.cycle 17 1 false (-3),
.cycle 10 6 false (0)
])
theorem kid05_part1225_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1225) = true := by rfl

def kid05_part1226 : Audit := .cycle 16 1 false (0)
theorem kid05_part1226_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1226) = true := by rfl

def kid05_part1227 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1227_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1227) = true := by rfl

def kid05_part1228 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1228_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1228) = true := by rfl

def kid05_part1229 : Audit := .cycle 12 1 false (-2)
theorem kid05_part1229_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1229) = true := by rfl

def kid05_part1230 : Audit := .cycle 9 5 false (1)
theorem kid05_part1230_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1230) = true := by rfl

def kid05_part1231 : Audit := .split 12 (1,true) (byMove [
.cycle 1 20 true (-1),
.cycle 21 1 false (-1),
.last 13 (2,true),
.cycle 0 20 true (-1),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.far false 5 ⟨0,[0, 1, 1, 2, 3, 4, 4, 4, 4, 4],[128, 256, 8, 0, 128, 0, 8192, 16384, 512, 16, 8192, 128, 33554432, 67108864, 2097152, 1024, 33554432, 33554432, 33554432, 67108864, 134217728, 16384, 33554432, 33554432, 33554432, 67108864, 134217728, 1409286144, 33554432, 1107296256, 1073741824],[16, 2, 1073741824, 1, 0, 128, 1024, 128, 1073741824, 64, 16384, 524288, 4194304, 524288, 1073741824, 262144, 67108864, 1073741824, 268435456, 33554432, 1073741824, 16777216, 67108864, 33554432, 268435456, 33554432, 1073741824, 16777216, 1140850688, 1107296256, 1073741824],2145367104⟩,
.last 13 (2,true),
.cycle 1 15 true (-1),
.cycle 9 5 false (1),
.cycle 54 1 false (-4),
.cycle 15 1 false (-1),
.last 15 (2,true),
.last 13 (2,true),
.cycle 16 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (-2),
.cycle 28 1 false (-2),
.last 13 (2,true),
.cycle 1 15 true (-1),
.cycle 16 1 false (-2),
.cycle 21 1 false (-3)
])
theorem kid05_part1231_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1231) = true := by rfl

def kid05_part1232 : Audit := .split 12 (2,true) (byMove [
.cycle 27 1 false (3),
.last 13 (1,true),
.cycle 15 1 false (-1),
.last 15 (1,true),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 6 7 false (3),
.last 13 (1,true),
.cycle 24 1 false (0),
.cycle 24 9 false (2),
.cycle 9 5 false (1),
.cycle 54 1 false (-4),
.cycle 15 1 false (-1),
.last 13 (1,true),
.cycle 18 1 false (0),
.cycle 16 1 false (0),
.cycle 14 1 false (-2),
.cycle 10 3 false (0),
.cycle 18 1 false (-2),
.last 13 (1,true),
.cycle 37 1 false (-3),
.cycle 28 1 false (-2),
.cycle 16 1 false (-2),
.cycle 21 1 false (-3)
])
theorem kid05_part1232_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1232) = true := by rfl

def kid05_part1233 : Audit := .cycle 5 7 false (3)
theorem kid05_part1233_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1233) = true := by rfl

def kid05_part1234 : Audit := .cycle 10 3 false (0)
theorem kid05_part1234_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1234) = true := by rfl

def kid05_part1235 : Audit := .cycle 14 1 false (-2)
theorem kid05_part1235_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1235) = true := by rfl

def kid05_part1211 : Audit := .split 11 (4,false) (byMove [(kid05_part1212),(kid05_part1213),(kid05_part1214),(kid05_part1215),(kid05_part1216),(kid05_part1217),(kid05_part1218),(kid05_part1219),(kid05_part1220),(kid05_part1221),(kid05_part1222),(kid05_part1223),(kid05_part1224),(kid05_part1225),(kid05_part1226),(kid05_part1227),(kid05_part1228),(kid05_part1229),(kid05_part1230),(kid05_part1231),(kid05_part1232),(kid05_part1233),(kid05_part1234),(kid05_part1235)])

theorem kid05_part1211_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part1211) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) 11 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (4,false) (some mv)) (byMove [(kid05_part1212),(kid05_part1213),(kid05_part1214),(kid05_part1215),(kid05_part1216),(kid05_part1217),(kid05_part1218),(kid05_part1219),(kid05_part1220),(kid05_part1221),(kid05_part1222),(kid05_part1223),(kid05_part1224),(kid05_part1225),(kid05_part1226),(kid05_part1227),(kid05_part1228),(kid05_part1229),(kid05_part1230),(kid05_part1231),(kid05_part1232),(kid05_part1233),(kid05_part1234),(kid05_part1235)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1212_checked

  · exact kid05_part1218_checked

  · exact kid05_part1224_checked

  · exact kid05_part1230_checked

  · exact kid05_part1213_checked

  · exact kid05_part1219_checked

  · exact kid05_part1225_checked

  · exact kid05_part1231_checked

  · exact kid05_part1214_checked

  · exact kid05_part1220_checked

  · exact kid05_part1226_checked

  · exact kid05_part1232_checked

  · exact kid05_part1215_checked

  · exact kid05_part1221_checked

  · exact kid05_part1227_checked

  · exact kid05_part1233_checked

  · exact kid05_part1216_checked

  · exact kid05_part1222_checked

  · exact kid05_part1228_checked

  · exact kid05_part1234_checked

  · exact kid05_part1217_checked

  · exact kid05_part1223_checked

  · exact kid05_part1229_checked

  · exact kid05_part1235_checked

def kid05_part1236 : Audit := .cycle 11 1 false (-1)
theorem kid05_part1236_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part1236) = true := by rfl

def kid05_part1237 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 13 4 true (0),
.cycle 0 17 true (0),
.split 35 (1,true) (byMove [
.last 38 (2,true),
.cycle 0 39 true (0),
.cycle 43 1 false (1),
.cycle 41 1 false (1),
.last 38 (2,true),
.last 46 (2,true),
.proven (BB6.Agent11Raw39B0RECounter231.M231.table) (fun m hm => BB6.Agent11Raw39B0RECounter231.M231.never m hm),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 2, 128, 256, 32768, 16, 8192, 65536, 128, 256, 8, 256, 2, 2, 262144],[16, 2, 262144, 1, 256, 64, 65536, 8192, 262144, 4096, 128, 64, 16, 2, 262144, 1, 2, 64, 262144],278540⟩,
.last 36 (2,true),
.cycle 0 37 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 2, 0, 128, 256, 32768, 272629776, 8192, 65536, 128, 256, 2097152, 524544, 524288, 524288, 128, 256, 134217728, 1342177280, 33554432, 268435456, 128, 256, 2097152, 1074266112, 524288, 524288, 1073741824],[16, 16, 1073741824, 1, 0, 64, 65536, 65536, 1073741824, 4096, 128, 64, 4194304, 4194304, 1073741824, 262144, 524288, 64, 268435456, 268435456, 1073741824, 16777216, 256, 64, 4194304, 4194304, 1073741824, 262144, 524288, 64, 1073741824],1278230528⟩,
.cycle 0 37 true (0),
.last 50 (2,true),
.last 37 (2,true),
.proven (BB6.Agent11Raw39B0RECounter234.M234.table) (fun m hm => BB6.Agent11Raw39B0RECounter234.M234.never m hm),
.cycle 41 1 false (1),
.cycle 34 2 true (2),
.cycle 26 10 true (0),
.cycle 15 21 true (0),
.cycle 1 36 true (0),
.last 36 (2,true),
.cycle 0 37 true (0),
.cycle 0 38 true (0),
.cycle 0 37 true (0)
]),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 true (2),
.cycle 0 28 true (0),
.split 18 (1,true) (byMove [
.cycle 15 4 true (1),
.cycle 28 1 false (0),
.last 19 (2,true),
.cycle 0 20 true (0),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 8192, 2, 128, 256, 32768, 16, 8448, 65536, 128, 256, 8, 256, 8192, 8192, 262144],[16, 2, 262144, 1, 256, 64, 65536, 8192, 262144, 4096, 128, 64, 16, 2, 262144, 1, 8192, 64, 262144],278540⟩,
.cycle 0 39 true (0),
.cycle 3 16 true (0),
.cycle 16 3 true (1),
.cycle 8 11 true (0),
.cycle 11 8 true (0),
.last 22 (2,true),
.last 19 (2,true),
.cycle 15 5 true (1),
.cycle 17 4 true (0),
.cycle 14 5 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 15 6 true (1),
.cycle 11 9 true (0),
.cycle 13 6 true (0)
]),
.split 18 (2,true) (byMove [
.cycle 15 4 true (1),
.last 19 (1,true),
.cycle 22 1 false (0),
.cycle 0 20 true (0),
.cycle 0 21 true (0),
.cycle 0 20 true (0),
.cycle 0 19 true (0),
.last 38 (1,true),
.cycle 0 39 true (0),
.cycle 3 16 true (0),
.cycle 16 3 true (1),
.cycle 8 11 true (0),
.cycle 11 8 true (0),
.last 19 (1,true),
.cycle 25 1 false (1),
.cycle 15 5 true (1),
.last 22 (1,true),
.cycle 14 5 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 15 6 true (1),
.last 20 (1,true),
.cycle 13 6 true (0)
]),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 9 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.split 33 (2,true) (byMove [
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 256, 256, 128, 256, 32768, 16, 256, 65536, 128, 256, 8, 32768, 256, 256, 262144],[16, 262144, 256, 1, 32768, 64, 65536, 262144, 256, 4096, 128, 64, 16, 262144, 256, 1, 256, 64, 262144],262144⟩,
.last 34 (1,true),
.cycle 41 1 false (1),
.cycle 0 35 true (0),
.cycle 12 22 true (0),
.cycle 0 35 true (0),
.cycle 0 34 true (0),
.cycle 17 18 true (0),
.cycle 0 54 true (0),
.cycle 18 16 true (0),
.cycle 16 18 true (0),
.cycle 8 26 true (0),
.cycle 6 28 true (0),
.last 34 (1,true),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 65536, 33554432, 67108864, 2097152, 67207168, 67108864, 67108864, 128, 256, 32768, 67436544, 256, 65536, 128, 256, 32768, 65536, 256, 65536, 1073741824],[16, 1073741824, 1, 1, 0, 64, 65536, 1073741824, 71663632, 4096, 128, 64, 4194304, 1073741824, 262144, 262144, 67108864, 16777216, 65536, 1073741824, 4096, 4096, 32768, 64, 65536, 1073741824, 65536, 4096, 128, 64, 1073741824],1073741824⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 2, 1],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 65536, 33554432, 67108864, 2097152, 67207168, 67108864, 67108864, 128, 256, 32768, 67436544, 256, 65536, 128, 256, 32768, 65536, 256, 65536, 1073741824],[16, 1073741824, 0, 1, 0, 64, 65536, 1073741824, 4194320, 4096, 128, 64, 4194304, 1073741824, 67207168, 262144, 67108864, 16777216, 65536, 1073741824, 67436544, 4096, 32768, 64, 65536, 1073741824, 65536, 4096, 128, 64, 1073741824],1073741824⟩,
.cycle 28 6 true (0),
.cycle 14 20 true (0),
.cycle 0 34 true (0),
.cycle 1 33 true (0),
.cycle 2 32 true (0),
.cycle 0 57 true (0),
.cycle 2 33 true (0),
.cycle 13 21 true (0)
]),
.cycle 15 4 true (1),
.cycle 16 1 true (2),
.cycle 13 4 true (0)
])
theorem kid05_part1237_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part1237) = true := by rfl

def kid05_part1239 : Audit := .split 13 (4,false) (byMove [
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 16 true (0),
.cycle 0 15 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 15 1 false (1),
.cycle 1 14 true (0),
.cycle 11 4 true (0),
.last 15 (2,true),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 1 15 true (0),
.cycle 1 14 true (0)
])
theorem kid05_part1239_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part1239) = true := by rfl

def kid05_part1240 : Audit := .cycle 20 1 false (0)
theorem kid05_part1240_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part1240) = true := by rfl

def kid05_part1241 : Audit := .split 12 (2,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.cycle 37 1 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 11 3 false (1),
.cycle 17 1 false (-1),
.cycle 0 20 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 16 true (0),
.cycle 1 14 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid05_part1241_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part1241) = true := by rfl

def kid05_part1242 : Audit := .cycle 0 16 true (0)
theorem kid05_part1242_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part1242) = true := by rfl

def kid05_part1243 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1243_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part1243) = true := by rfl

def kid05_part1244 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.cycle 1 16 true (0),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 1 16 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 1 34 true (0),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 1 20 true (0),
.cycle 11 4 true (0),
.cycle 21 1 false (1),
.last 17 (4,false),
.cycle 12 4 true (0),
.cycle 1 17 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 1 18 true (0)
])
theorem kid05_part1244_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part1244) = true := by rfl

def kid05_part1245 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 6 20 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 8 6 true (0),
.cycle 0 14 true (0),
.far false 4 ⟨0,[0, 1, 2, 0, 3, 1, 1, 0],[128, 256, 8, 4264064, 2, 21870047, 2, 4, 32768, 21042320, 8192, 4096, 128, 256, 2097152, 21606798, 524288, 4194304, 2, 4, 512, 21237953, 128, 128, 16777216],[16, 1, 16777216, 1, 21606798, 128, 65536, 4096, 16777216, 4096, 4, 2, 4194304, 262144, 16777216, 262144, 128, 128, 1024, 64, 16777216, 64, 128, 2, 16777216],20244338⟩,
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 13 1 true (3),
.cycle 1 28 true (0),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 6 12 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.last 34 (2,true),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1245_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part1245) = true := by rfl

def kid05_part1246 : Audit := .far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 262416, 262144, 2, 128, 256, 32768, 16, 262144, 8192, 2, 4, 8, 256, 262144, 2, 262144],[16, 2, 262144, 1, 256, 128, 65536, 8192, 262144, 4096, 256, 128, 16, 2, 262144, 1, 4, 2, 262144],355868⟩
theorem kid05_part1246_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part1246) = true := by rfl

def kid05_part1247 : Audit := .split 12 (2,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 23 1 false (1),
.cycle 0 13 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 3, 4, 1, 3, 3],[128, 256, 8, 0, 1073741824, 0, 128, 256, 32768, 4194320, 1073741824, 16384, 524288, 1048576, 2097152, 256, 1073741824, 524288, 128, 256, 134217728, 319824128, 1073741824, 67108864, 524288, 1048576, 2097152, 40902656, 1073741824, 524288, 1073741824],[16, 4, 2, 1, 0, 128, 65536, 16384, 8192, 4096, 256, 128, 4194304, 1048576, 524288, 262144, 2097152, 524288, 268435456, 67108864, 33554432, 16777216, 256, 128, 4194304, 1048576, 524288, 262144, 2097152, 524288, 1073741824],1592880656⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 13 (4,false),
.cycle 1 19 true (0),
.cycle 0 31 true (0),
.cycle 11 4 true (1),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 13 (4,false),
.cycle 9 4 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 24 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 9 38 true (0)
])
theorem kid05_part1247_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part1247) = true := by rfl

def kid05_part1248 : Audit := .cycle 0 13 true (0)
theorem kid05_part1248_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part1248) = true := by rfl

def kid05_part1249 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 13 4 true (0),
.cycle 0 17 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 2, 0, 128, 256, 32768, 272629776, 8192, 65536, 128, 256, 2097152, 524544, 524288, 524288, 128, 256, 134217728, 1342177280, 33554432, 268435456, 128, 256, 2097152, 1074266112, 524288, 524288, 1073741824],[16, 16, 1073741824, 1, 0, 128, 65536, 65536, 1073741824, 4096, 256, 128, 4194304, 4194304, 1073741824, 262144, 524288, 128, 268435456, 268435456, 1073741824, 16777216, 256, 128, 4194304, 4194304, 1073741824, 262144, 524288, 128, 1073741824],1278230528⟩,
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 true (2),
.cycle 1 27 true (0),
.cycle 15 3 true (1),
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 9 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.last 33 (2,true),
.cycle 16 4 true (2),
.cycle 16 1 true (2),
.cycle 13 4 true (0)
])
theorem kid05_part1249_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part1249) = true := by rfl

def kid05_part1250 : Audit := .cycle 1 12 true (0)
theorem kid05_part1250_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part1250) = true := by rfl

def kid05_part1251 : Audit := .cycle 14 1 false (0)
theorem kid05_part1251_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part1251) = true := by rfl

def kid05_part1252 : Audit := .split 14 (2,true) (byMove [
.last 16 (4,false),
.cycle 12 3 false (0),
.cycle 17 1 false (-1),
.cycle 11 6 true (-1),
.cycle 16 1 false (-2),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 32785, 262144, 256, 128, 256, 32768, 16, 262144, 256, 128, 256, 8, 32768, 262144, 256, 262144],[16, 256, 32768, 1, 32768, 128, 65536, 256, 256, 4096, 256, 128, 16, 256, 32768, 1, 32768, 128, 262144],345628⟩,
.cycle 6 9 false (3),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 258, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2, 1, 256, 128, 16, 2, 2, 1, 256, 128, 4096],5648⟩,
.cycle 26 1 false (0),
.last 17 (4,false),
.cycle 9 7 false (1),
.cycle 1 20 true (-1),
.cycle 17 1 false (-1),
.cycle 12 3 false (0),
.cycle 20 1 false (0),
.cycle 18 1 false (0),
.cycle 16 1 false (-2),
.cycle 10 5 false (1),
.cycle 11 9 false (2),
.cycle 11 5 false (1),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 0],[128, 256, 8, 33041, 262144, 256, 128, 256, 32768, 16, 262144, 256, 2, 4, 8, 33024, 262144, 256, 262144],[16, 256, 256, 1, 33024, 128, 65536, 256, 256, 4096, 256, 128, 16, 256, 4, 1, 32768, 2, 262144],353820⟩,
.last 17 (4,false),
.last 19 (4,false),
.cycle 11 7 false (2)
])
theorem kid05_part1252_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part1252) = true := by rfl

def kid05_part1253 : Audit := .split 12 (2,true) (byMove [
.last 17 (4,false),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.last 17 (4,false),
.cycle 16 1 false (4),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 1 16 true (0),
.cycle 11 3 false (1),
.cycle 20 1 false (0),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.last 20 (4,false),
.cycle 11 2 true (0),
.cycle 2 13 true (0),
.last 15 (4,false),
.last 17 (4,false),
.cycle 1 16 true (0)
])
theorem kid05_part1253_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part1253) = true := by rfl

def kid05_part1254 : Audit := .cycle 15 1 false (1)
theorem kid05_part1254_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part1254) = true := by rfl

def kid05_part1255 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1255_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part1255) = true := by rfl

def kid05_part1256 : Audit := .cycle 10 2 true (0)
theorem kid05_part1256_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part1256) = true := by rfl

def kid05_part1257 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 23 1 false (1),
.cycle 1 16 true (0),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.cycle 0 34 true (0),
.last 28 (2,true),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 0 24 true (0),
.cycle 0 16 true (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.last 18 (2,true),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 30 true (0),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1257_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part1257) = true := by rfl

def kid05_part1258 : Audit := .cycle 1 12 true (0)
theorem kid05_part1258_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part1258) = true := by rfl

def kid05_part1259 : Audit := .split 12 (2,true) (byMove [
.last 14 (4,false),
.cycle 2 12 true (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 1 14 true (0),
.cycle 1 13 true (0),
.cycle 0 13 true (0),
.cycle 14 13 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 13 (4,false),
.cycle 8 5 true (0),
.cycle 2 16 true (0),
.cycle 11 2 true (1),
.cycle 19 1 false (1),
.last 15 (4,false),
.cycle 12 4 true (0),
.cycle 2 13 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 2 14 true (0)
])
theorem kid05_part1259_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part1259) = true := by rfl

def kid05_part1260 : Audit := .cycle 0 13 true (0)
theorem kid05_part1260_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part1260) = true := by rfl

def kid05_part1261 : Audit := .cycle 1 13 true (0)
theorem kid05_part1261_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part1261) = true := by rfl

def kid05_part1262 : Audit := .cycle 1 12 true (0)
theorem kid05_part1262_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part1262) = true := by rfl

def kid05_part1238 : Audit := .split 11 (1,true) (byMove [(kid05_part1239),(kid05_part1240),(kid05_part1241),(kid05_part1242),(kid05_part1243),(kid05_part1244),(kid05_part1245),(kid05_part1246),(kid05_part1247),(kid05_part1248),(kid05_part1249),(kid05_part1250),(kid05_part1251),(kid05_part1252),(kid05_part1253),(kid05_part1254),(kid05_part1255),(kid05_part1256),(kid05_part1257),(kid05_part1258),(kid05_part1259),(kid05_part1260),(kid05_part1261),(kid05_part1262)])

theorem kid05_part1238_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part1238) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) 11 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (1,true) (some mv)) (byMove [(kid05_part1239),(kid05_part1240),(kid05_part1241),(kid05_part1242),(kid05_part1243),(kid05_part1244),(kid05_part1245),(kid05_part1246),(kid05_part1247),(kid05_part1248),(kid05_part1249),(kid05_part1250),(kid05_part1251),(kid05_part1252),(kid05_part1253),(kid05_part1254),(kid05_part1255),(kid05_part1256),(kid05_part1257),(kid05_part1258),(kid05_part1259),(kid05_part1260),(kid05_part1261),(kid05_part1262)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1239_checked

  · exact kid05_part1245_checked

  · exact kid05_part1251_checked

  · exact kid05_part1257_checked

  · exact kid05_part1240_checked

  · exact kid05_part1246_checked

  · exact kid05_part1252_checked

  · exact kid05_part1258_checked

  · exact kid05_part1241_checked

  · exact kid05_part1247_checked

  · exact kid05_part1253_checked

  · exact kid05_part1259_checked

  · exact kid05_part1242_checked

  · exact kid05_part1248_checked

  · exact kid05_part1254_checked

  · exact kid05_part1260_checked

  · exact kid05_part1243_checked

  · exact kid05_part1249_checked

  · exact kid05_part1255_checked

  · exact kid05_part1261_checked

  · exact kid05_part1244_checked

  · exact kid05_part1250_checked

  · exact kid05_part1256_checked

  · exact kid05_part1262_checked

def kid05_part1264 : Audit := .split 13 (4,false) (byMove [
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 0 15 true (0),
.cycle 0 15 true (0),
.cycle 15 1 false (1),
.cycle 21 1 false (3),
.last 15 (1,true),
.cycle 11 4 true (0),
.cycle 0 20 true (0),
.cycle 14 1 false (0),
.cycle 13 1 false (1),
.cycle 14 1 false (0),
.cycle 0 16 true (0),
.last 14 (1,true),
.cycle 23 1 false (3),
.cycle 0 15 true (0),
.cycle 22 1 false (2),
.cycle 2 13 true (0)
])
theorem kid05_part1264_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1264) = true := by rfl

def kid05_part1265 : Audit := .split 12 (1,true) (byMove [
.cycle 0 17 true (-1),
.cycle 20 1 false (0),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 15 true (0),
.cycle 23 1 false (3),
.cycle 0 15 true (0),
.cycle 13 1 false (1),
.last 13 (4,false),
.cycle 13 1 false (1),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 0 21 true (-1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 0 15 true (0),
.cycle 1 15 true (0),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 13 (4,false),
.cycle 9 4 true (0)
])
theorem kid05_part1265_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1265) = true := by rfl

def kid05_part1266 : Audit := .cycle 14 1 false (0)
theorem kid05_part1266_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1266) = true := by rfl

def kid05_part1267 : Audit := .split 14 (1,true) (byMove [
.last 16 (4,false),
.cycle 23 1 false (1),
.cycle 16 1 false (0),
.cycle 0 16 true (0),
.cycle 16 1 false (0),
.cycle 22 1 false (2),
.cycle 0 15 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 386, 4096, 2, 128, 256, 8, 16, 4096, 128, 4096],[16, 2, 4360, 1, 256, 256, 16, 2, 128, 1, 8, 256, 4096],5648⟩,
.cycle 22 1 false (2),
.cycle 20 1 false (2),
.last 15 (4,false),
.cycle 8 7 true (0),
.cycle 17 1 false (1),
.cycle 11 6 true (0),
.cycle 16 1 false (0),
.last 17 (4,false),
.cycle 16 1 false (0),
.cycle 0 18 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.last 18 (4,false),
.last 15 (4,false),
.cycle 0 19 true (0)
])
theorem kid05_part1267_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1267) = true := by rfl

def kid05_part1268 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1268_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1268) = true := by rfl

def kid05_part1269 : Audit := .cycle 0 15 true (0)
theorem kid05_part1269_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1269) = true := by rfl

def kid05_part1270 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 6 20 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 8 6 true (0),
.cycle 0 14 true (0),
.last 36 (1,true),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 13 1 true (3),
.cycle 0 52 true (0),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 6 12 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 35 true (0),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1270_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1270) = true := by rfl

def kid05_part1271 : Audit := .split 12 (1,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 19 1 false (1),
.last 16 (4,false),
.last 13 (4,false),
.cycle 15 18 true (0),
.cycle 0 13 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 258, 4096, 2, 128, 256, 8, 16, 4096, 2, 4096],[16, 2, 2, 1, 256, 256, 16, 2, 2, 1, 8, 256, 4096],5648⟩,
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.last 13 (4,false),
.cycle 13 29 true (0),
.cycle 19 22 true (0),
.cycle 11 18 true (1),
.cycle 0 15 true (0),
.cycle 17 1 false (1),
.last 13 (4,false),
.cycle 9 4 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 13 14 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 2 28 true (0)
])
theorem kid05_part1271_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1271) = true := by rfl

def kid05_part1272 : Audit := .cycle 21 1 false (1)
theorem kid05_part1272_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1272) = true := by rfl

def kid05_part1273 : Audit := .cycle 0 13 true (0)
theorem kid05_part1273_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1273) = true := by rfl

def kid05_part1274 : Audit := .split 16 (4,false) (byMove [
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 13 4 true (0),
.cycle 0 17 true (0),
.last 35 (1,true),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 16 1 true (2),
.cycle 14 31 true (0),
.last 18 (1,true),
.cycle 15 3 true (1),
.cycle 0 19 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (-1),
.cycle 9 8 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 15 18 true (0),
.cycle 16 4 true (2),
.cycle 16 1 true (2),
.cycle 13 4 true (0)
])
theorem kid05_part1274_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1274) = true := by rfl

def kid05_part1275 : Audit := .cycle 8 18 true (0)
theorem kid05_part1275_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1275) = true := by rfl

def kid05_part1276 : Audit := .cycle 14 1 false (0)
theorem kid05_part1276_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1276) = true := by rfl

def kid05_part1277 : Audit := .split 12 (1,true) (byMove [
.last 18 (4,false),
.last 17 (4,false),
.cycle 14 1 false (0),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.cycle 15 1 false (1),
.cycle 22 1 false (4),
.cycle 11 4 true (0),
.last 15 (4,false),
.cycle 14 1 false (0),
.cycle 23 1 false (3),
.cycle 17 1 false (-1),
.cycle 11 3 false (1),
.cycle 17 1 false (1),
.cycle 13 1 false (-1),
.last 13 (4,false),
.cycle 13 1 false (-1),
.last 20 (4,false),
.cycle 1 14 true (0),
.cycle 11 2 true (0),
.last 15 (4,false),
.cycle 0 17 true (0),
.cycle 2 15 true (0)
])
theorem kid05_part1277_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1277) = true := by rfl

def kid05_part1278 : Audit := .cycle 17 1 false (1)
theorem kid05_part1278_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1278) = true := by rfl

def kid05_part1279 : Audit := .cycle 15 1 false (1)
theorem kid05_part1279_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1279) = true := by rfl

def kid05_part1280 : Audit := .cycle 13 1 false (-1)
theorem kid05_part1280_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1280) = true := by rfl

def kid05_part1281 : Audit := .cycle 10 2 true (0)
theorem kid05_part1281_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1281) = true := by rfl

def kid05_part1282 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 2 12 true (0),
.cycle 23 1 false (1),
.cycle 23 1 false (1),
.cycle 0 17 true (0),
.cycle 0 14 true (0),
.last 33 (1,true),
.last 51 (1,true),
.cycle 0 27 true (0),
.cycle 13 1 true (3),
.cycle 0 24 true (0),
.last 15 (1,true),
.cycle 0 16 true (0),
.cycle 0 16 true (0),
.cycle 4 10 true (0),
.cycle 25 1 false (-1),
.cycle 9 5 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.cycle 0 30 true (0),
.cycle 12 4 true (2),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1282_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1282) = true := by rfl

def kid05_part1283 : Audit := .split 12 (1,true) (byMove [
.last 14 (4,false),
.cycle 22 1 false (0),
.cycle 1 13 true (0),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 2 12 true (0),
.cycle 0 13 true (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 386, 4096, 2, 128, 256, 8, 16, 4096, 128, 4096],[16, 2, 128, 1, 256, 256, 16, 2, 128, 1, 8, 256, 4096],5648⟩,
.cycle 0 27 true (0),
.cycle 3 10 true (0),
.last 13 (4,false),
.cycle 8 5 true (0),
.cycle 1 17 true (0),
.cycle 11 5 false (2),
.cycle 11 2 true (1),
.last 15 (4,false),
.cycle 0 17 true (0),
.cycle 1 14 true (0),
.cycle 0 13 true (0),
.cycle 1 12 true (0),
.cycle 2 11 true (0),
.last 16 (4,false),
.last 13 (4,false),
.cycle 1 15 true (0)
])
theorem kid05_part1283_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1283) = true := by rfl

def kid05_part1284 : Audit := .cycle 2 11 true (0)
theorem kid05_part1284_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1284) = true := by rfl

def kid05_part1285 : Audit := .cycle 0 13 true (0)
theorem kid05_part1285_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1285) = true := by rfl

def kid05_part1286 : Audit := .cycle 2 12 true (0)
theorem kid05_part1286_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1286) = true := by rfl

def kid05_part1287 : Audit := .cycle 2 11 true (0)
theorem kid05_part1287_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1287) = true := by rfl

def kid05_part1263 : Audit := .split 11 (2,true) (byMove [(kid05_part1264),(kid05_part1265),(kid05_part1266),(kid05_part1267),(kid05_part1268),(kid05_part1269),(kid05_part1270),(kid05_part1271),(kid05_part1272),(kid05_part1273),(kid05_part1274),(kid05_part1275),(kid05_part1276),(kid05_part1277),(kid05_part1278),(kid05_part1279),(kid05_part1280),(kid05_part1281),(kid05_part1282),(kid05_part1283),(kid05_part1284),(kid05_part1285),(kid05_part1286),(kid05_part1287)])

theorem kid05_part1263_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part1263) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) 11 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (2,true) (some mv)) (byMove [(kid05_part1264),(kid05_part1265),(kid05_part1266),(kid05_part1267),(kid05_part1268),(kid05_part1269),(kid05_part1270),(kid05_part1271),(kid05_part1272),(kid05_part1273),(kid05_part1274),(kid05_part1275),(kid05_part1276),(kid05_part1277),(kid05_part1278),(kid05_part1279),(kid05_part1280),(kid05_part1281),(kid05_part1282),(kid05_part1283),(kid05_part1284),(kid05_part1285),(kid05_part1286),(kid05_part1287)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1264_checked

  · exact kid05_part1270_checked

  · exact kid05_part1276_checked

  · exact kid05_part1282_checked

  · exact kid05_part1265_checked

  · exact kid05_part1271_checked

  · exact kid05_part1277_checked

  · exact kid05_part1283_checked

  · exact kid05_part1266_checked

  · exact kid05_part1272_checked

  · exact kid05_part1278_checked

  · exact kid05_part1284_checked

  · exact kid05_part1267_checked

  · exact kid05_part1273_checked

  · exact kid05_part1279_checked

  · exact kid05_part1285_checked

  · exact kid05_part1268_checked

  · exact kid05_part1274_checked

  · exact kid05_part1280_checked

  · exact kid05_part1286_checked

  · exact kid05_part1269_checked

  · exact kid05_part1275_checked

  · exact kid05_part1281_checked

  · exact kid05_part1287_checked

def kid05_part1288 : Audit := .split 13 (4,false) (byMove [
.cycle 0 14 true (0),
.cycle 5 20 true (0),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 8 6 true (0),
.cycle 0 14 true (0),
.split 36 (1,true) (byMove [
.last 39 (2,true),
.cycle 0 40 true (0),
.cycle 45 1 false (1),
.cycle 43 1 false (1),
.last 39 (2,true),
.last 51 (2,true),
.far false 4 ⟨0,[0, 1, 2, 0, 3, 1, 1, 0],[128, 256, 8, 4264064, 2, 21870047, 2, 4, 32768, 21870047, 8192, 4096, 128, 256, 2097152, 21870047, 524288, 4194304, 2, 4, 512, 21870047, 128, 128, 16777216],[16, 1, 16777216, 1, 21870047, 512, 65536, 4096, 16777216, 4096, 21870047, 8, 4194304, 262144, 16777216, 262144, 128, 512, 1024, 64, 16777216, 64, 128, 8, 16777216],20244338⟩,
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 16777218, 2, 2, 128, 256, 32768, 4194320, 8192, 4096, 128, 256, 2097152, 258, 524288, 4194304, 128, 256, 8, 16777218, 2, 2, 16777216],[16, 2, 16777216, 1, 256, 512, 65536, 8192, 16777216, 4096, 4194320, 512, 4194304, 524288, 16777216, 262144, 128, 512, 16, 2, 16777216, 1, 2, 512, 16777216],19939340⟩,
.last 37 (2,true),
.cycle 0 38 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 1, 4, 1, 3, 1],[128, 256, 8, 0, 2, 0, 128, 256, 32768, 272629776, 8192, 4096, 128, 256, 2097152, 33554688, 524288, 4194304, 128, 256, 134217728, 1077936128, 33554432, 33554432, 128, 256, 2097152, 1107296256, 524288, 4194304, 1073741824],[16, 16, 1073741824, 1, 0, 512, 65536, 65536, 1073741824, 4096, 272629776, 512, 4194304, 4194304, 1073741824, 262144, 128, 512, 268435456, 268435456, 1073741824, 16777216, 33554432, 512, 4194304, 4194304, 1073741824, 262144, 256, 512, 1073741824],1278230528⟩,
.cycle 21 59 true (0),
.last 55 (2,true),
.last 38 (2,true),
.far false 5 ⟨0,[0, 1, 2, 0, 3, 1, 4, 1, 2, 0],[128, 256, 8, 37752832, 2, 1380233631, 2, 4, 32768, 268501008, 8192, 4096, 128, 256, 2097152, 1111536014, 524288, 4194304, 128, 256, 134217728, 1111756801, 33554432, 33554432, 2, 4, 32768, 1379930128, 8192, 4096, 1073741824],[16, 1073741825, 1073741824, 1, 1111536014, 512, 65536, 1073741824, 1073741824, 4096, 268501008, 8, 4194304, 262144, 1073741824, 262144, 128, 512, 268435456, 16777216, 1073741824, 16777216, 33554432, 512, 65536, 4096, 1073741824, 4096, 4, 8, 1073741824],1564075890⟩,
.cycle 43 1 false (1),
.cycle 35 2 true (3),
.cycle 23 14 true (0),
.cycle 0 61 true (0),
.cycle 1 37 true (0),
.last 37 (2,true),
.cycle 0 38 true (0),
.far false 6 ⟨0,[0, 1, 2, 1, 3, 4, 4, 4, 5, 1, 3, 4],[128, 256, 8, 0, 2, 0, 128, 256, 32768, 4194320, 8192, 4096, 33554432, 67108864, 2097152, 33554434, 524288, 4194304, 33554432, 67108864, 134217728, 86205539602, 33554432, 33554434, 128, 256, 8589934592, 86205539602, 2147483648, 1073742848, 33554432, 67108864, 2097152, 86205539602, 524288, 4194320, 68719476736],[16, 1024, 68719476736, 1, 0, 512, 65536, 1024, 68719476736, 4096, 4194320, 512, 4194304, 268435456, 68719476736, 262144, 33554432, 134217728, 268435456, 268435456, 68719476736, 16777216, 33554434, 134217728, 17179869184, 1024, 68719476736, 1073741824, 86205539602, 512, 4194304, 268435456, 68719476736, 262144, 33562624, 134217728, 68719476736],101942125568⟩,
.cycle 11 28 true (0)
]),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 13 1 true (3),
.cycle 5 46 true (0),
.split 15 (1,true) (byMove [
.cycle 12 4 true (2),
.cycle 1 16 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 0 20 true (0),
.cycle 11 7 true (1),
.cycle 0 16 true (0),
.cycle 5 22 true (0),
.cycle 0 40 true (0),
.cycle 5 20 true (0),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 6 10 true (0),
.last 18 (2,true),
.last 16 (2,true),
.cycle 11 5 true (1),
.cycle 14 6 true (0),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.cycle 0 22 true (0),
.cycle 0 19 true (0)
]),
.split 15 (2,true) (byMove [
.cycle 12 4 true (2),
.last 16 (1,true),
.cycle 23 1 false (1),
.cycle 0 17 true (0),
.cycle 0 20 true (0),
.cycle 11 7 true (1),
.cycle 0 16 true (0),
.cycle 5 22 true (0),
.cycle 0 40 true (0),
.cycle 5 20 true (0),
.cycle 13 3 true (2),
.cycle 8 8 true (0),
.cycle 6 10 true (0),
.last 16 (1,true),
.cycle 11 7 true (1),
.cycle 11 5 true (1),
.last 21 (1,true),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (0),
.cycle 2 14 true (0),
.cycle 11 6 true (1),
.last 17 (1,true),
.cycle 0 19 true (0)
]),
.cycle 0 16 true (0),
.cycle 19 1 false (1),
.cycle 17 1 false (-1),
.cycle 5 12 true (0),
.cycle 0 14 true (0),
.cycle 1 13 true (0),
.split 34 (2,true) (byMove [
.far false 4 ⟨0,[0, 1, 2, 1, 3, 1, 0, 1],[128, 256, 8, 295184, 256, 256, 128, 256, 32768, 4194320, 256, 4096, 128, 256, 2097152, 33024, 256, 4194304, 128, 256, 8, 262400, 256, 256, 16777216],[16, 16777216, 256, 1, 32768, 512, 65536, 16777216, 256, 4096, 4194320, 512, 4194304, 16777216, 256, 262144, 128, 512, 16, 16777216, 256, 1, 256, 512, 16777216],16777216⟩,
.last 35 (1,true),
.cycle 43 1 false (1),
.cycle 0 36 true (0),
.cycle 7 28 true (0),
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 4096, 33554432, 67108864, 2097152, 256, 67108864, 4194320, 128, 256, 32768, 4194320, 256, 256, 33554432, 67108864, 134217728, 1598390672, 67108864, 1598390672, 1073741824],[16, 1073741824, 0, 1, 0, 512, 65536, 1073741824, 4194320, 4096, 4194320, 512, 4194304, 1073741824, 33587200, 262144, 33587200, 134217728, 65536, 1073741824, 256, 4096, 256, 512, 268435456, 1073741824, 1598390672, 16777216, 1598390672, 134217728, 1073741824],2130786304⟩,
.cycle 0 35 true (0),
.cycle 5 41 true (0),
.cycle 0 59 true (0),
.cycle 15 20 true (0),
.cycle 5 41 true (0),
.cycle 8 27 true (0),
.cycle 5 36 true (0),
.last 35 (1,true),
.far false 7 ⟨0,[0, 5, 3, 1, 2, 4, 6, 4, 2, 4, 3, 1, 3, 5],[2147483648, 4294967296, 8, 0, 4294967296, 0, 128, 256, 2097152, 1099511627776, 256, 262144, 33554432, 67108864, 32768, 5572827123984, 67108864, 5572827123984, 33554432, 67108864, 549755813888, 4294967296, 67108864, 1099511627792, 33554432, 67108864, 32768, 4259840, 67108864, 4096, 128, 256, 2097152, 1099511627792, 256, 262144, 2147483648, 4294967296, 2097152, 1099511627792, 4294967296, 4294967296, 4398046511104],[16, 4398046511104, 1, 1, 0, 8589934592, 4194304, 4398046511104, 1103806595088, 262144, 1099511627776, 512, 65536, 4398046511104, 4096, 4096, 5572827123984, 134217728, 1099511627776, 4398046511104, 68719476736, 68719476736, 35651584, 134217728, 65536, 4398046511104, 5572827123984, 4096, 4259840, 134217728, 4194304, 4398046511104, 1099511627792, 262144, 1099511627792, 512, 4194304, 4398046511104, 262144, 262144, 4294967296, 8589934592, 4398046511104],4433468454912⟩,
.far false 5 ⟨0,[0, 1, 2, 1, 3, 4, 2, 1, 4, 4],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 4096, 33554432, 67108864, 2097152, 256, 67108864, 4194320, 128, 256, 32768, 4194320, 256, 256, 33554432, 67108864, 134217728, 1598390672, 67108864, 1598390672, 1073741824],[16, 1073741824, 0, 1, 0, 512, 65536, 1073741824, 4194320, 4096, 4194320, 512, 4194304, 1073741824, 256, 262144, 33587200, 134217728, 65536, 1073741824, 4194320, 4096, 256, 512, 268435456, 1073741824, 1598390672, 16777216, 1598390672, 134217728, 1073741824],2130786304⟩,
.cycle 27 8 true (0),
.cycle 0 37 true (0),
.cycle 0 35 true (0),
.cycle 1 34 true (0),
.cycle 2 33 true (0),
.cycle 11 25 true (0),
.cycle 2 34 true (0),
.cycle 0 38 true (0)
]),
.cycle 11 4 true (1),
.cycle 13 1 true (3),
.cycle 0 17 true (0)
])
theorem kid05_part1288_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part1288) = true := by rfl

def kid05_part1290 : Audit := .split 18 (2,true) (byMove [
.cycle 0 21 true (0),
.last 19 (1,true),
.cycle 22 1 false (0),
.cycle 0 20 true (0),
.cycle 0 24 true (0),
.cycle 0 23 true (0),
.cycle 0 19 true (0),
.last 38 (1,true),
.cycle 0 39 true (0),
.cycle 3 16 true (0),
.cycle 0 20 true (0),
.cycle 8 11 true (0),
.cycle 0 28 true (0),
.last 19 (1,true),
.cycle 25 1 false (1),
.cycle 0 22 true (0),
.cycle 11 8 true (0),
.cycle 0 25 true (0),
.cycle 0 19 true (0),
.cycle 1 18 true (0),
.cycle 2 17 true (0),
.cycle 0 23 true (0),
.cycle 0 22 true (0),
.cycle 0 26 true (0)
])
theorem kid05_part1290_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1290) = true := by rfl

def kid05_part1291 : Audit := .split 14 (1,true) (byMove [
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 23 1 false (-1),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 0 19 true (0),
.cycle 15 1 false (1),
.cycle 19 1 false (-1),
.last 16 (2,true),
.last 19 (2,true),
.cycle 15 1 false (-1),
.cycle 7 14 false (3),
.cycle 15 1 false (-1),
.cycle 0 17 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.cycle 13 2 true (0),
.cycle 9 6 true (0)
])
theorem kid05_part1291_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1291) = true := by rfl

def kid05_part1292 : Audit := .split 14 (2,true) (byMove [
.cycle 0 19 true (-1),
.cycle 22 1 false (0),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 16 (1,true),
.last 34 (1,true),
.cycle 0 17 true (0),
.cycle 15 1 false (1),
.cycle 17 1 false (1),
.cycle 15 1 false (1),
.last 16 (1,true),
.last 17 (1,true),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 1 false (-1),
.last 16 (1,true),
.cycle 1 16 true (0),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.cycle 13 2 true (0),
.cycle 9 6 true (0)
])
theorem kid05_part1292_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1292) = true := by rfl

def kid05_part1293 : Audit := .split 16 (1,true) (byMove [
.cycle 19 1 false (1),
.cycle 25 1 false (1),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 18 1 false (0),
.cycle 0 20 true (0),
.cycle 0 17 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 294912, 2, 128, 256, 32768, 16, 128, 128, 128, 256, 8, 256, 294912, 8192, 262144],[16, 2, 262144, 1, 256, 1024, 65536, 8192, 262144, 4096, 128, 1024, 16, 2, 262144, 1, 256, 1024, 262144],344604⟩,
.cycle 24 1 false (2),
.cycle 22 1 false (2),
.cycle 22 1 false (2),
.cycle 8 9 true (0),
.cycle 19 1 false (1),
.last 19 (2,true),
.last 17 (2,true),
.cycle 20 1 false (2),
.cycle 18 1 false (0),
.cycle 0 22 true (0),
.cycle 0 17 true (0),
.cycle 1 16 true (0),
.cycle 2 15 true (0),
.cycle 26 1 false (2),
.cycle 0 19 true (0),
.cycle 0 23 true (0)
])
theorem kid05_part1293_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1293) = true := by rfl

def kid05_part1294 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1294_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1294) = true := by rfl

def kid05_part1295 : Audit := .cycle 12 2 true (0)
theorem kid05_part1295_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1295) = true := by rfl

def kid05_part1296 : Audit := .cycle 0 16 true (0)
theorem kid05_part1296_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1296) = true := by rfl

def kid05_part1297 : Audit := .split 14 (1,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (1),
.cycle 26 1 false (4),
.last 33 (2,true),
.last 41 (2,true),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 2, 2, 128, 256, 32768, 16, 8192, 8192, 128, 256, 8, 256, 2, 2, 262144],[16, 2, 262144, 1, 256, 1024, 65536, 8192, 262144, 4096, 8192, 1024, 16, 2, 262144, 1, 256, 1024, 262144],278540⟩,
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.far false 5 ⟨0,[0, 1, 2, 0, 1, 3, 4, 0, 1, 1],[128, 256, 8, 9216, 2, 1209116127, 2, 4, 32768, 1209116127, 8192, 8192, 524288, 1048576, 512, 1209116127, 128, 1024, 2, 4, 134217728, 65536, 33554432, 33554432, 128, 256, 512, 1048576, 128, 1024, 1073741824],[16, 16, 1073741824, 1, 1209116127, 1024, 65536, 65536, 1073741824, 4096, 8192, 16, 1024, 1024, 1073741824, 64, 1048576, 4194304, 268435456, 268435456, 1073741824, 16777216, 33554432, 16, 1024, 1024, 1073741824, 64, 256, 1024, 1073741824],1187300210⟩,
.cycle 15 17 true (0),
.last 49 (2,true),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.cycle 13 2 true (1),
.cycle 9 6 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.last 29 (2,true),
.cycle 0 60 true (0),
.cycle 15 18 true (2),
.cycle 18 17 true (2)
])
theorem kid05_part1297_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1297) = true := by rfl

def kid05_part1298 : Audit := .split 14 (2,true) (byMove [
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 1 false (1),
.cycle 20 1 false (4),
.cycle 23 1 false (1),
.cycle 27 1 false (1),
.cycle 0 15 true (0),
.last 31 (1,true),
.cycle 23 1 false (1),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 0 47 true (0),
.last 16 (1,true),
.last 17 (1,true),
.cycle 0 17 true (0),
.cycle 19 1 false (1),
.cycle 13 2 true (1),
.cycle 9 6 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 28 true (0),
.cycle 29 1 false (1),
.cycle 0 36 true (0),
.cycle 12 23 true (0)
])
theorem kid05_part1298_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1298) = true := by rfl

def kid05_part1299 : Audit := .cycle 0 15 true (0)
theorem kid05_part1299_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1299) = true := by rfl

def kid05_part1300 : Audit := .cycle 19 1 true (1)
theorem kid05_part1300_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1300) = true := by rfl

def kid05_part1301 : Audit := .cycle 8 8 true (0)
theorem kid05_part1301_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1301) = true := by rfl

def kid05_part1302 : Audit := .cycle 16 1 false (0)
theorem kid05_part1302_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1302) = true := by rfl

def kid05_part1303 : Audit := .split 14 (1,true) (byMove [
.last 17 (2,true),
.last 21 (2,true),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 17 (2,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.cycle 24 1 false (4),
.last 15 (2,true),
.last 19 (2,true),
.cycle 16 1 false (0),
.cycle 17 3 true (1),
.cycle 19 1 false (-1),
.last 16 (2,true),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.last 17 (2,true),
.cycle 15 1 false (-1),
.last 26 (2,true),
.cycle 1 16 true (0),
.last 15 (2,true),
.last 19 (2,true),
.cycle 11 4 true (0),
.cycle 17 3 true (1)
])
theorem kid05_part1303_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1303) = true := by rfl

def kid05_part1304 : Audit := .split 14 (2,true) (byMove [
.cycle 0 26 true (-1),
.cycle 0 22 true (-1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 19 (1,true),
.cycle 15 1 false (-1),
.cycle 17 1 false (1),
.last 15 (1,true),
.cycle 18 1 false (4),
.cycle 0 20 true (0),
.cycle 16 1 false (0),
.cycle 17 3 true (1),
.last 16 (1,true),
.last 17 (1,true),
.cycle 19 1 false (1),
.cycle 15 1 false (-1),
.cycle 20 1 false (0),
.cycle 15 1 false (-1),
.cycle 0 27 true (0),
.last 15 (1,true),
.cycle 2 15 true (0),
.cycle 0 20 true (0),
.cycle 11 4 true (0),
.cycle 17 3 true (1)
])
theorem kid05_part1304_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1304) = true := by rfl

def kid05_part1305 : Audit := .cycle 17 1 false (1)
theorem kid05_part1305_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1305) = true := by rfl

def kid05_part1306 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1306_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1306) = true := by rfl

def kid05_part1307 : Audit := .cycle 10 4 true (0)
theorem kid05_part1307_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1307) = true := by rfl

def kid05_part1308 : Audit := .cycle 0 16 true (0)
theorem kid05_part1308_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1308) = true := by rfl

def kid05_part1309 : Audit := .split 14 (1,true) (byMove [
.cycle 1 16 true (0),
.cycle 24 1 false (0),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 1 17 true (0),
.cycle 1 16 true (0),
.cycle 0 15 true (0),
.far false 3 ⟨0,[0, 1, 2, 1, 0, 1],[128, 256, 8, 262144, 128, 2, 128, 256, 32768, 16, 128, 128, 128, 256, 8, 256, 128, 8192, 262144],[16, 2, 262144, 1, 256, 1024, 65536, 8192, 262144, 4096, 128, 1024, 16, 2, 262144, 1, 256, 1024, 262144],278540⟩,
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 1 15 true (0),
.cycle 8 7 true (0),
.cycle 1 21 true (0),
.last 18 (2,true),
.last 15 (2,true),
.cycle 1 17 true (0),
.cycle 11 4 true (0),
.cycle 1 18 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 1 18 true (0),
.cycle 1 15 true (0),
.cycle 1 19 true (0)
])
theorem kid05_part1309_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1309) = true := by rfl

def kid05_part1310 : Audit := .split 14 (2,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 25, 256, 256, 128, 256, 8, 16, 256, 256, 4096],[16, 4096, 256, 1, 8, 1024, 16, 4096, 256, 1, 256, 1024, 4096],4096⟩,
.last 15 (1,true),
.cycle 18 1 false (0),
.cycle 0 16 true (0),
.cycle 2 16 true (0),
.cycle 2 15 true (0),
.cycle 0 15 true (0),
.last 30 (1,true),
.cycle 0 31 true (0),
.cycle 3 12 true (0),
.cycle 2 34 true (0),
.cycle 8 7 true (0),
.cycle 2 20 true (0),
.last 15 (1,true),
.cycle 21 1 false (1),
.far false 4 ⟨0,[0, 1, 2, 1, 3, 3, 2, 1],[128, 256, 8, 0, 256, 0, 128, 256, 32768, 4194320, 256, 256, 524288, 1048576, 2097152, 360704, 1048576, 4194320, 128, 256, 32768, 4554768, 256, 256, 16777216],[16, 16777216, 0, 1, 0, 1024, 65536, 16777216, 4194320, 4096, 256, 1024, 4194304, 16777216, 360704, 262144, 32768, 4194304, 65536, 16777216, 4554768, 4096, 256, 1024, 16777216],16777216⟩,
.cycle 11 4 true (0),
.cycle 2 17 true (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 2 13 true (0),
.cycle 16 18 true (1),
.cycle 2 14 true (0),
.cycle 2 18 true (0)
])
theorem kid05_part1310_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1310) = true := by rfl

def kid05_part1311 : Audit := .cycle 0 15 true (0)
theorem kid05_part1311_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1311) = true := by rfl

def kid05_part1312 : Audit := .cycle 16 1 true (2)
theorem kid05_part1312_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1312) = true := by rfl

def kid05_part1313 : Audit := .cycle 14 5 true (2)
theorem kid05_part1313_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1313) = true := by rfl

def kid05_part1289 : Audit := .split 13 (4,false) (byMove [(kid05_part1290),(kid05_part1291),(kid05_part1292),(kid05_part1293),(kid05_part1294),(kid05_part1295),(kid05_part1296),(kid05_part1297),(kid05_part1298),(kid05_part1299),(kid05_part1300),(kid05_part1301),(kid05_part1302),(kid05_part1303),(kid05_part1304),(kid05_part1305),(kid05_part1306),(kid05_part1307),(kid05_part1308),(kid05_part1309),(kid05_part1310),(kid05_part1311),(kid05_part1312),(kid05_part1313)])

theorem kid05_part1289_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part1289) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) 13 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part1290),(kid05_part1291),(kid05_part1292),(kid05_part1293),(kid05_part1294),(kid05_part1295),(kid05_part1296),(kid05_part1297),(kid05_part1298),(kid05_part1299),(kid05_part1300),(kid05_part1301),(kid05_part1302),(kid05_part1303),(kid05_part1304),(kid05_part1305),(kid05_part1306),(kid05_part1307),(kid05_part1308),(kid05_part1309),(kid05_part1310),(kid05_part1311),(kid05_part1312),(kid05_part1313)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1290_checked

  · exact kid05_part1296_checked

  · exact kid05_part1302_checked

  · exact kid05_part1308_checked

  · exact kid05_part1291_checked

  · exact kid05_part1297_checked

  · exact kid05_part1303_checked

  · exact kid05_part1309_checked

  · exact kid05_part1292_checked

  · exact kid05_part1298_checked

  · exact kid05_part1304_checked

  · exact kid05_part1310_checked

  · exact kid05_part1293_checked

  · exact kid05_part1299_checked

  · exact kid05_part1305_checked

  · exact kid05_part1311_checked

  · exact kid05_part1294_checked

  · exact kid05_part1300_checked

  · exact kid05_part1306_checked

  · exact kid05_part1312_checked

  · exact kid05_part1295_checked

  · exact kid05_part1301_checked

  · exact kid05_part1307_checked

  · exact kid05_part1313_checked

def kid05_part1314 : Audit := .cycle 11 3 true (1)
theorem kid05_part1314_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part1314) = true := by rfl

def kid05_part1050 : Audit := .split 10 (5,true) (byMove [(kid05_part1051),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1131),(kid05_part1156),(kid05_part1157),(kid05_part1158),(kid05_part1159),(kid05_part1184),(kid05_part1209),(kid05_part1210),(kid05_part1211),(kid05_part1236),(kid05_part1237),(kid05_part1238),(kid05_part1263),(kid05_part1288),(kid05_part1289),(kid05_part1314)])

theorem kid05_part1050_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (kid05_part1050) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part1051),(kid05_part1076),(kid05_part1077),(kid05_part1078),(kid05_part1079),(kid05_part1104),(kid05_part1105),(kid05_part1106),(kid05_part1131),(kid05_part1156),(kid05_part1157),(kid05_part1158),(kid05_part1159),(kid05_part1184),(kid05_part1209),(kid05_part1210),(kid05_part1211),(kid05_part1236),(kid05_part1237),(kid05_part1238),(kid05_part1263),(kid05_part1288),(kid05_part1289),(kid05_part1314)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1051_checked

  · exact kid05_part1105_checked

  · exact kid05_part1159_checked

  · exact kid05_part1237_checked

  · exact kid05_part1076_checked

  · exact kid05_part1106_checked

  · exact kid05_part1184_checked

  · exact kid05_part1238_checked

  · exact kid05_part1077_checked

  · exact kid05_part1131_checked

  · exact kid05_part1209_checked

  · exact kid05_part1263_checked

  · exact kid05_part1078_checked

  · exact kid05_part1156_checked

  · exact kid05_part1210_checked

  · exact kid05_part1288_checked

  · exact kid05_part1079_checked

  · exact kid05_part1157_checked

  · exact kid05_part1211_checked

  · exact kid05_part1289_checked

  · exact kid05_part1104_checked

  · exact kid05_part1158_checked

  · exact kid05_part1236_checked

  · exact kid05_part1314_checked

def kid05_part1315 : Audit := .cycle 0 9 true (0)
theorem kid05_part1315_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (kid05_part1315) = true := by rfl

def kid05_part1316 : Audit := .cycle 1 8 true (1)
theorem kid05_part1316_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,1⟩)) (kid05_part1316) = true := by rfl

def kid05_part1317 : Audit := .cycle 2 7 true (1)
theorem kid05_part1317_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,2⟩)) (kid05_part1317) = true := by rfl

def kid05_part1319 : Audit := .cycle 0 13 true (0)
theorem kid05_part1319_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1319) = true := by rfl

def kid05_part1320 : Audit := .cycle 1 12 true (1)
theorem kid05_part1320_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1320) = true := by rfl

def kid05_part1321 : Audit := .cycle 37 1 false (5)
theorem kid05_part1321_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1321) = true := by rfl

def kid05_part1322 : Audit := .cycle 29 1 false (3)
theorem kid05_part1322_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1322) = true := by rfl

def kid05_part1323 : Audit := .cycle 21 1 false (1)
theorem kid05_part1323_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1323) = true := by rfl

def kid05_part1324 : Audit := .cycle 8 5 true (2)
theorem kid05_part1324_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1324) = true := by rfl

def kid05_part1325 : Audit := .cycle 0 13 true (0)
theorem kid05_part1325_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1325) = true := by rfl

def kid05_part1326 : Audit := .cycle 1 12 true (1)
theorem kid05_part1326_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1326) = true := by rfl

def kid05_part1327 : Audit := .cycle 49 1 false (9)
theorem kid05_part1327_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1327) = true := by rfl

def kid05_part1328 : Audit := .cycle 41 1 false (7)
theorem kid05_part1328_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1328) = true := by rfl

def kid05_part1329 : Audit := .cycle 12 1 true (4)
theorem kid05_part1329_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1329) = true := by rfl

def kid05_part1330 : Audit := .cycle 8 5 true (2)
theorem kid05_part1330_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1330) = true := by rfl

def kid05_part1331 : Audit := .split 14 (1,true) (byMove [
.cycle 11 4 true (3),
.cycle 1 15 true (1),
.split 15 (2,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 37 1 false (3),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 49 1 false (7),
.cycle 41 1 false (5),
.cycle 12 4 true (3),
.cycle 8 8 true (2),
.cycle 29 3 false (2),
.cycle 42 1 false (2),
.cycle 0 18 true (0),
.cycle 34 1 false (2),
.cycle 30 4 false (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 9 7 true (2),
.cycle 6 11 true (2),
.cycle 8 8 true (2)
]),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 37 1 false (3),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 49 1 false (7),
.cycle 41 1 false (5),
.cycle 12 4 true (3),
.cycle 8 8 true (2),
.cycle 29 3 false (2),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 34 1 false (2),
.cycle 30 4 false (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 9 7 true (2),
.cycle 6 11 true (2),
.cycle 8 8 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 19 true (1),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.split 17 (2,true) (byMove [
.cycle 29 7 false (1),
.cycle 22 3 false (0),
.cycle 37 1 false (1),
.cycle 13 6 true (2),
.last 30 (5,true),
.last 18 (5,true),
.cycle 11 7 true (2),
.cycle 1 20 true (1),
.cycle 4 29 true (1),
.cycle 0 19 true (0),
.cycle 7 11 true (2),
.last 18 (5,true),
.cycle 4 17 true (1),
.cycle 22 3 false (0),
.cycle 5 15 true (1),
.cycle 5 13 true (1),
.cycle 4 21 true (1),
.last 18 (5,true),
.cycle 4 26 true (1),
.cycle 24 5 false (2),
.cycle 2 17 true (1),
.cycle 0 19 true (0),
.last 19 (5,true),
.last 18 (5,true)
]),
.split 15 (2,true) (byMove [
.cycle 36 13 false (2),
.cycle 0 19 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 4 13 true (1),
.cycle 11 5 true (3),
.cycle 0 19 true (0),
.cycle 57 1 false (9),
.cycle 0 17 true (0),
.cycle 7 9 true (2),
.last 16 (5,true),
.cycle 44 3 false (5),
.cycle 5 15 true (1),
.cycle 10 7 true (2),
.cycle 39 1 false (3),
.cycle 45 4 false (5),
.cycle 10 7 true (2),
.cycle 11 5 true (3),
.cycle 14 2 true (3),
.cycle 2 15 true (1),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
]),
.cycle 10 5 true (2),
.cycle 4 13 true (1),
.split 15 (5,true) (byMove [
.last 18 (2,true),
.cycle 0 19 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 4 13 true (1),
.cycle 11 5 true (3),
.cycle 0 19 true (0),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 7 9 true (2),
.cycle 8 9 true (2),
.cycle 44 3 false (5),
.last 17 (2,true),
.cycle 10 7 true (2),
.cycle 39 1 false (3),
.cycle 45 4 false (5),
.cycle 10 7 true (2),
.cycle 11 5 true (3),
.cycle 14 2 true (3),
.last 16 (2,true),
.cycle 0 17 true (0),
.cycle 6 13 true (2),
.cycle 8 9 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 9 6 true (2),
.cycle 6 10 true (2),
.cycle 8 7 true (2)
])
theorem kid05_part1331_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1331) = true := by rfl

def kid05_part1332 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (3),
.split 15 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 37 1 false (3),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 49 1 false (7),
.cycle 41 1 false (5),
.cycle 12 4 true (3),
.cycle 8 8 true (2),
.cycle 6 12 true (2),
.cycle 22 3 false (0),
.cycle 0 18 true (0),
.cycle 34 1 false (2),
.cycle 30 4 false (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 9 7 true (2),
.last 19 (5,true),
.cycle 8 8 true (2)
]),
.cycle 37 1 false (3),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.split 15 (5,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 37 1 false (3),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 8 8 true (2),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 49 1 false (7),
.cycle 41 1 false (5),
.cycle 12 4 true (3),
.cycle 8 8 true (2),
.last 17 (1,true),
.last 22 (1,true),
.cycle 0 18 true (0),
.cycle 34 1 false (2),
.cycle 30 4 false (2),
.cycle 0 18 true (0),
.cycle 0 16 true (0),
.cycle 1 15 true (1),
.cycle 2 14 true (1),
.cycle 9 7 true (2),
.last 17 (1,true),
.cycle 8 8 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 4 19 true (1),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.split 15 (1,true) (byMove [
.cycle 31 9 false (2),
.cycle 0 19 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 4 13 true (1),
.cycle 11 5 true (3),
.cycle 1 16 true (1),
.cycle 13 4 true (3),
.cycle 0 17 true (0),
.cycle 7 9 true (2),
.last 16 (5,true),
.cycle 4 17 true (1),
.cycle 22 3 false (0),
.cycle 10 7 true (2),
.cycle 39 1 false (3),
.cycle 45 4 false (5),
.cycle 10 7 true (2),
.cycle 11 5 true (3),
.cycle 1 16 true (1),
.cycle 14 2 true (3),
.cycle 0 17 true (0),
.last 17 (5,true),
.last 16 (5,true)
]),
.cycle 10 7 true (2),
.cycle 10 5 true (2),
.cycle 4 13 true (1),
.split 15 (5,true) (byMove [
.cycle 31 9 false (2),
.cycle 0 19 true (0),
.cycle 42 1 false (4),
.cycle 29 1 false (1),
.cycle 25 4 false (1),
.cycle 4 13 true (1),
.cycle 11 5 true (3),
.last 16 (1,true),
.cycle 0 19 true (0),
.cycle 0 17 true (0),
.cycle 7 9 true (2),
.cycle 8 9 true (2),
.last 17 (1,true),
.last 22 (1,true),
.cycle 10 7 true (2),
.cycle 39 1 false (3),
.cycle 45 4 false (5),
.cycle 10 7 true (2),
.cycle 11 5 true (3),
.last 16 (1,true),
.cycle 14 2 true (3),
.cycle 0 17 true (0),
.last 19 (1,true),
.cycle 8 9 true (2)
]),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 9 6 true (2),
.split 16 (1,true) (byMove [
.last 22 (5,true),
.cycle 4 22 true (1),
.cycle 55 1 false (5),
.cycle 0 21 true (0),
.last 26 (5,true),
.last 17 (5,true),
.cycle 11 6 true (3),
.cycle 1 17 true (1),
.cycle 14 3 true (4),
.cycle 0 18 true (0),
.cycle 7 10 true (2),
.last 17 (5,true),
.cycle 4 16 true (1),
.last 21 (5,true),
.last 19 (5,true),
.cycle 5 12 true (1),
.cycle 4 20 true (1),
.last 17 (5,true),
.cycle 11 6 true (3),
.cycle 1 17 true (1),
.cycle 14 3 true (4),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 17 (5,true)
]),
.cycle 8 7 true (2)
])
theorem kid05_part1332_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1332) = true := by rfl

def kid05_part1333 : Audit := .cycle 0 15 true (0)
theorem kid05_part1333_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1333) = true := by rfl

def kid05_part1334 : Audit := .cycle 34 1 false (4)
theorem kid05_part1334_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1334) = true := by rfl

def kid05_part1335 : Audit := .cycle 41 1 false (5)
theorem kid05_part1335_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1335) = true := by rfl

def kid05_part1336 : Audit := .cycle 0 15 true (0)
theorem kid05_part1336_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1336) = true := by rfl

def kid05_part1337 : Audit := .cycle 0 13 true (0)
theorem kid05_part1337_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1337) = true := by rfl

def kid05_part1338 : Audit := .cycle 1 12 true (1)
theorem kid05_part1338_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1338) = true := by rfl

def kid05_part1339 : Audit := .cycle 2 11 true (1)
theorem kid05_part1339_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1339) = true := by rfl

def kid05_part1340 : Audit := .cycle 9 4 true (2)
theorem kid05_part1340_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1340) = true := by rfl

def kid05_part1341 : Audit := .cycle 12 1 true (4)
theorem kid05_part1341_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1341) = true := by rfl

def kid05_part1342 : Audit := .cycle 8 5 true (2)
theorem kid05_part1342_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1342) = true := by rfl

def kid05_part1318 : Audit := .split 12 (4,false) (byMove [(kid05_part1319),(kid05_part1320),(kid05_part1321),(kid05_part1322),(kid05_part1323),(kid05_part1324),(kid05_part1325),(kid05_part1326),(kid05_part1327),(kid05_part1328),(kid05_part1329),(kid05_part1330),(kid05_part1331),(kid05_part1332),(kid05_part1333),(kid05_part1334),(kid05_part1335),(kid05_part1336),(kid05_part1337),(kid05_part1338),(kid05_part1339),(kid05_part1340),(kid05_part1341),(kid05_part1342)])

theorem kid05_part1318_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (kid05_part1318) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) 12 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) (4,false) (some mv)) (byMove [(kid05_part1319),(kid05_part1320),(kid05_part1321),(kid05_part1322),(kid05_part1323),(kid05_part1324),(kid05_part1325),(kid05_part1326),(kid05_part1327),(kid05_part1328),(kid05_part1329),(kid05_part1330),(kid05_part1331),(kid05_part1332),(kid05_part1333),(kid05_part1334),(kid05_part1335),(kid05_part1336),(kid05_part1337),(kid05_part1338),(kid05_part1339),(kid05_part1340),(kid05_part1341),(kid05_part1342)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1319_checked

  · exact kid05_part1325_checked

  · exact kid05_part1331_checked

  · exact kid05_part1337_checked

  · exact kid05_part1320_checked

  · exact kid05_part1326_checked

  · exact kid05_part1332_checked

  · exact kid05_part1338_checked

  · exact kid05_part1321_checked

  · exact kid05_part1327_checked

  · exact kid05_part1333_checked

  · exact kid05_part1339_checked

  · exact kid05_part1322_checked

  · exact kid05_part1328_checked

  · exact kid05_part1334_checked

  · exact kid05_part1340_checked

  · exact kid05_part1323_checked

  · exact kid05_part1329_checked

  · exact kid05_part1335_checked

  · exact kid05_part1341_checked

  · exact kid05_part1324_checked

  · exact kid05_part1330_checked

  · exact kid05_part1336_checked

  · exact kid05_part1342_checked

def kid05_part1344 : Audit := .cycle 0 12 true (0)
theorem kid05_part1344_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (kid05_part1344) = true := by rfl

def kid05_part1345 : Audit := .split 10 (1,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 25 1 false (1),
.cycle 11 11 false (1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 23 3 false (0),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 22 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 23 3 false (2),
.cycle 15 3 false (2),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 0 19 true (-2),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 26 3 false (3),
.cycle 15 3 false (1),
.cycle 11 4 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 37 1 false (7),
.cycle 20 1 false (2),
.cycle 1 11 true (1),
.cycle 8 3 true (2),
.cycle 17 7 false (1),
.split 12 (2,true) (byMove [
.cycle 1 14 true (1),
.cycle 14 3 false (0),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 1 13 true (1),
.cycle 8 5 true (1),
.cycle 18 7 false (0),
.cycle 14 3 false (0),
.cycle 16 17 true (-1),
.cycle 1 15 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 1 16 true (1),
.last 20 (5,true),
.last 21 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 7 12 false (3),
.split 13 (5,true) (byMove [
.cycle 0 29 false (3),
.cycle 14 13 false (0),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 14 14 false (0),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 1 14 true (1),
.cycle 8 6 true (1),
.cycle 21 3 false (-1),
.last 19 (2,true),
.last 14 (2,true),
.cycle 30 1 false (0),
.last 27 (2,true),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 1 17 true (1),
.cycle 17 5 false (1),
.cycle 13 5 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 1 14 true (1),
.cycle 9 2 true (2),
.cycle 8 3 true (2)
])
theorem kid05_part1345_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,1⟩)) (kid05_part1345) = true := by rfl

def kid05_part1346 : Audit := .split 10 (2,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 16 1 false (2),
.cycle 15 1 false (-1),
.split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 22 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 17 1 false (1),
.cycle 15 3 false (2),
.last 16 (1,true),
.cycle 13 3 false (1),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 17 1 false (-1),
.cycle 14 3 false (0),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 21 3 false (2),
.cycle 20 1 false (2),
.cycle 15 3 false (1),
.cycle 11 4 true (0)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 27 1 false (5),
.cycle 20 1 false (2),
.cycle 24 1 false (2),
.cycle 8 3 true (2),
.split 12 (1,true) (byMove [
.cycle 29 1 false (1),
.cycle 13 13 false (1),
.cycle 18 3 false (0),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 2 12 true (1),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.cycle 13 10 false (1),
.cycle 18 3 false (0),
.cycle 32 1 false (2),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 4 25 true (1),
.cycle 18 9 false (2),
.cycle 18 15 false (3)
]),
.split 13 (1,true) (byMove [
.cycle 17 1 false (1),
.cycle 0 50 true (-2),
.cycle 19 1 false (-1),
.cycle 0 18 true (0),
.cycle 23 1 false (-3),
.last 14 (5,true),
.cycle 32 1 false (2),
.cycle 1 14 true (1),
.cycle 10 4 true (1),
.cycle 0 15 true (0),
.cycle 17 7 false (1),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 3 false (0),
.cycle 33 1 false (1),
.cycle 23 1 false (-1),
.cycle 23 1 false (-3),
.last 14 (5,true),
.cycle 2 14 true (1),
.cycle 1 14 true (1),
.cycle 12 2 true (1),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 15 1 false (-1),
.split 13 (5,true) (byMove [
.cycle 17 1 false (1),
.last 14 (1,true),
.cycle 19 1 false (-1),
.cycle 0 15 true (0),
.cycle 23 1 false (-3),
.cycle 14 6 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 28 1 false (2),
.cycle 25 1 false (1),
.cycle 29 1 false (1),
.cycle 8 6 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 21 (1,true),
.cycle 18 1 false (2),
.cycle 23 1 false (-3),
.cycle 14 3 false (0),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 36 1 false (2),
.cycle 17 5 false (1),
.cycle 13 5 true (1)
]),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 45 1 false (5),
.cycle 9 2 true (2),
.cycle 8 3 true (2)
])
theorem kid05_part1346_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,2⟩)) (kid05_part1346) = true := by rfl

def kid05_part1347 : Audit := .cycle 0 11 true (0)
theorem kid05_part1347_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,3⟩)) (kid05_part1347) = true := by rfl

def kid05_part1348 : Audit := .split 14 (5,true) (byMove [
.cycle 0 15 false (3),
.cycle 21 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 15 3 false (0),
.cycle 0 15 true (0),
.cycle 21 3 false (3),
.cycle 16 1 false (2),
.cycle 15 1 false (1),
.cycle 15 1 false (1),
.cycle 15 3 false (2),
.split 16 (1,true) (byMove [
.cycle 18 1 false (0),
.cycle 24 3 false (0),
.last 17 (2,true),
.cycle 0 18 true (-1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 18 3 false (0),
.cycle 8 9 false (3),
.cycle 18 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.cycle 19 1 false (1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.cycle 10 23 false (4),
.cycle 32 3 false (0),
.cycle 2 15 false (3),
.cycle 22 3 false (0),
.cycle 12 5 false (2),
.cycle 22 3 false (0)
]),
.split 16 (2,true) (byMove [
.cycle 18 1 false (0),
.last 17 (1,true),
.cycle 19 1 false (-1),
.cycle 0 18 true (-1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.cycle 0 17 true (-1),
.cycle 7 19 false (3),
.cycle 23 3 false (1),
.cycle 21 3 false (1),
.cycle 18 3 false (0),
.cycle 8 9 false (3),
.cycle 18 3 false (0),
.last 17 (1,true),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.last 32 (1,true),
.last 31 (1,true),
.cycle 2 15 false (3),
.cycle 22 3 false (0),
.cycle 12 5 false (2),
.last 21 (1,true)
]),
.cycle 0 17 true (-1),
.cycle 15 1 false (-1),
.cycle 15 1 false (-1),
.cycle 13 3 false (1),
.cycle 0 15 true (0),
.cycle 1 14 true (0),
.cycle 20 3 false (2),
.cycle 18 1 false (2),
.cycle 15 3 false (1),
.cycle 11 4 true (0)
])
theorem kid05_part1348_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,4⟩)) (kid05_part1348) = true := by rfl

def kid05_part1349 : Audit := .split 10 (5,true) (byMove [
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 21 1 false (1),
.cycle 18 1 false (0),
.cycle 11 4 false (1),
.cycle 14 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 30 1 false (6),
.cycle 20 1 false (2),
.cycle 8 4 true (2),
.cycle 8 3 true (2),
.split 12 (1,true) (byMove [
.cycle 20 7 false (1),
.cycle 13 13 false (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.cycle 19 11 false (2),
.cycle 8 5 true (1),
.cycle 18 7 false (1),
.last 16 (2,true),
.last 13 (2,true),
.cycle 8 8 true (1),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.cycle 18 9 false (2),
.cycle 18 15 false (3)
]),
.split 12 (2,true) (byMove [
.last 18 (1,true),
.last 13 (1,true),
.cycle 16 1 false (0),
.cycle 0 14 true (0),
.cycle 14 6 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 27 true (0),
.cycle 3 10 true (1),
.last 17 (1,true),
.cycle 8 5 true (1),
.last 18 (1,true),
.last 13 (1,true),
.cycle 19 10 true (-1),
.cycle 8 8 true (1),
.cycle 14 6 false (0),
.last 14 (1,true),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 8 9 true (1),
.last 15 (1,true),
.last 16 (1,true)
]),
.cycle 0 13 true (0),
.cycle 18 1 false (0),
.cycle 11 4 false (1),
.cycle 14 3 false (0),
.cycle 0 11 true (0),
.cycle 1 10 true (1),
.cycle 2 9 true (1),
.cycle 8 7 true (2),
.cycle 9 2 true (2),
.cycle 8 3 true (2)
])
theorem kid05_part1349_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,false,5⟩)) (kid05_part1349) = true := by rfl

def kid05_part1350 : Audit := .cycle 0 10 true (0)
theorem kid05_part1350_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) (kid05_part1350) = true := by rfl

def kid05_part1351 : Audit := .cycle 1 9 true (1)
theorem kid05_part1351_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,1⟩)) (kid05_part1351) = true := by rfl

def kid05_part1352 : Audit := .split 19 (2,true) (byMove [
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 43 1 false (3),
.cycle 9 11 true (2),
.cycle 8 12 true (2),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 8, 16, 4, 1024, 4096],[16, 4096, 4, 1, 4, 4096, 16, 4096, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 11 9 true (2),
.cycle 16 17 true (3),
.cycle 8 12 true (2),
.split 21 (1,true) (byMove [
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 8, 16, 4, 1024, 4096],[16, 256, 4, 1, 4, 4096, 16, 4, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 1 23 true (1),
.cycle 6 17 true (2),
.cycle 0 23 true (0),
.last 23 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 10 12 true (2),
.cycle 3 19 true (1),
.cycle 7 29 true (2),
.cycle 8 14 true (2),
.cycle 6 16 true (2),
.cycle 44 11 false (2),
.cycle 15 8 true (3),
.cycle 14 25 true (2),
.last 23 (5,true),
.last 22 (5,true),
.cycle 0 22 true (0),
.cycle 1 21 true (1),
.cycle 2 20 true (1),
.cycle 23 17 true (4),
.cycle 9 13 true (2),
.cycle 8 14 true (2)
]),
.split 22 (1,true) (byMove [
.cycle 20 10 true (3),
.cycle 12 14 true (2),
.cycle 44 1 false (0),
.cycle 0 27 true (0),
.cycle 0 28 true (0),
.last 23 (5,true),
.cycle 15 25 true (3),
.cycle 1 23 true (1),
.cycle 19 4 true (4),
.cycle 0 24 true (0),
.cycle 7 16 true (2),
.last 23 (5,true),
.cycle 15 8 true (3),
.cycle 30 3 false (0),
.cycle 14 14 true (1),
.cycle 5 18 true (1),
.last 38 (5,true),
.last 23 (5,true),
.cycle 6 33 true (2),
.cycle 1 23 true (1),
.cycle 21 2 true (4),
.cycle 0 24 true (0),
.last 24 (5,true),
.last 23 (5,true)
]),
.cycle 0 22 true (0),
.cycle 4 16 true (1),
.cycle 18 2 true (4),
.split 22 (5,true) (byMove [
.cycle 65 1 false (9),
.last 23 (1,true),
.cycle 53 1 false (1),
.cycle 0 24 true (0),
.cycle 7 16 true (2),
.cycle 8 16 true (2),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 10 13 true (2),
.cycle 3 20 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[16, 64, 4, 1, 4, 16, 64],64⟩,
.cycle 8 15 true (2),
.cycle 6 17 true (2),
.last 23 (1,true),
.last 30 (1,true),
.cycle 50 1 false (2),
.cycle 37 5 false (1),
.cycle 30 3 false (0),
.cycle 0 23 true (0),
.cycle 1 22 true (1),
.cycle 2 21 true (1),
.cycle 13 29 true (2),
.cycle 9 14 true (2),
.cycle 8 15 true (2)
]),
.cycle 0 20 true (0),
.cycle 1 19 true (1),
.cycle 2 18 true (1),
.cycle 5 32 true (1),
.cycle 9 11 true (2),
.cycle 8 12 true (2)
])
theorem kid05_part1352_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,2⟩)) (kid05_part1352) = true := by rfl

def kid05_part1353 : Audit := .cycle 3 7 true (1)
theorem kid05_part1353_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,3⟩)) (kid05_part1353) = true := by rfl

def kid05_part1354 : Audit := .cycle 9 1 true (3)
theorem kid05_part1354_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,4⟩)) (kid05_part1354) = true := by rfl

def kid05_part1355 : Audit := .cycle 8 2 true (2)
theorem kid05_part1355_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,5⟩)) (kid05_part1355) = true := by rfl

def kid05_part1356 : Audit := .cycle 6 4 true (2)
theorem kid05_part1356_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,0⟩)) (kid05_part1356) = true := by rfl

def kid05_part1358 : Audit := .split 13 (2,true) (byMove [
.cycle 12 4 true (2),
.cycle 0 25 false (3),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 8, 16, 4, 1024, 4096],[16, 256, 4, 1, 4, 4096, 16, 4, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 3 11 true (1),
.cycle 12 3 true (2),
.cycle 8 6 true (1),
.cycle 21 17 false (2),
.cycle 17 9 false (2),
.cycle 14 12 true (-1),
.cycle 12 5 true (2),
.last 15 (5,true),
.last 14 (5,true),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 12 6 true (2),
.last 21 (5,true),
.last 21 (5,true)
])
theorem kid05_part1358_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (kid05_part1358) = true := by rfl

def kid05_part1359 : Audit := .cycle 0 14 true (0)
theorem kid05_part1359_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) (kid05_part1359) = true := by rfl

def kid05_part1360 : Audit := .cycle 21 1 false (1)
theorem kid05_part1360_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,2⟩)) (kid05_part1360) = true := by rfl

def kid05_part1361 : Audit := .split 16 (2,true) (byMove [
.cycle 13 4 true (1),
.cycle 18 1 false (0),
.cycle 19 1 false (1),
.cycle 0 21 true (0),
.cycle 21 1 false (-1),
.last 17 (5,true),
.cycle 0 21 true (0),
.cycle 42 1 false (2),
.cycle 29 1 false (1),
.cycle 0 18 true (0),
.cycle 0 25 true (0),
.last 17 (5,true),
.cycle 22 1 false (0),
.cycle 18 1 false (0),
.cycle 25 1 false (1),
.cycle 23 1 false (1),
.cycle 21 1 false (-1),
.last 17 (5,true),
.cycle 0 21 true (0),
.cycle 0 19 true (0),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.last 18 (5,true),
.last 17 (5,true)
])
theorem kid05_part1361_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,3⟩)) (kid05_part1361) = true := by rfl

def kid05_part1362 : Audit := .split 15 (2,true) (byMove [
.cycle 13 4 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 16512, 128, 1024, 8192, 16384, 8, 16, 128, 65536, 33554432, 67108864, 2097152, 16, 128, 268435456, 33554432, 67108864, 2097152, 16512, 1600405632, 268435456, 33554432, 67108864, 134217728, 1600405632, 1600405632, 268435456, 1073741824],[16, 16384, 2113664, 1, 128, 1073741824, 16, 16384, 128, 1, 1073741824, 1073741824, 4194304, 1073741824, 128, 262144, 1073741824, 1073741824, 4194304, 1600405632, 2113664, 262144, 1600405632, 1073741824, 268435456, 1600405632, 1600405632, 16777216, 1600405632, 1073741824, 1073741824],2144219200⟩,
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 11 13 false (1),
.cycle 16 15 true (0),
.cycle 0 29 true (-2),
.cycle 11 11 false (1),
.last 24 (5,true),
.last 18 (5,true),
.cycle 11 8 false (1),
.cycle 12 4 false (0),
.cycle 11 18 true (-3),
.cycle 11 14 true (-2),
.cycle 11 7 false (1),
.last 16 (5,true),
.last 19 (5,true),
.last 33 (5,true),
.cycle 11 17 false (3),
.cycle 4 12 false (3),
.cycle 11 9 false (1),
.last 18 (5,true)
])
theorem kid05_part1362_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,4⟩)) (kid05_part1362) = true := by rfl

def kid05_part1363 : Audit := .split 14 (5,true) (byMove [
.last 22 (2,true),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.last 17 (2,true),
.cycle 15 3 false (0),
.cycle 0 21 true (0),
.last 16 (2,true),
.last 20 (2,true),
.cycle 15 1 false (1),
.last 17 (2,true),
.cycle 21 3 false (4),
.cycle 13 3 false (1),
.last 16 (2,true),
.cycle 0 27 true (-1),
.cycle 15 1 false (-1),
.last 17 (2,true),
.cycle 14 3 false (0),
.cycle 0 21 true (0),
.last 16 (2,true),
.last 20 (2,true),
.cycle 19 3 false (2),
.cycle 15 3 false (1),
.cycle 17 7 true (1)
])
theorem kid05_part1363_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,5⟩)) (kid05_part1363) = true := by rfl

def kid05_part1364 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (3),
.cycle 0 16 true (0),
.cycle 37 1 false (3),
.cycle 0 16 true (0),
.cycle 7 8 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 19 true (2),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 11 7 true (2),
.cycle 11 5 true (3),
.cycle 6 13 true (2),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 6 true (3),
.cycle 9 6 true (2),
.cycle 8 7 true (2)
])
theorem kid05_part1364_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,0⟩)) (kid05_part1364) = true := by rfl

def kid05_part1365 : Audit := .cycle 1 11 true (1)
theorem kid05_part1365_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,1⟩)) (kid05_part1365) = true := by rfl

def kid05_part1366 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 16 (5,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 37 1 false (7),
.cycle 11 3 true (3),
.cycle 8 4 true (2),
.cycle 10 16 true (2),
.cycle 10 4 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 16 (5,true),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 11 6 true (3),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1366_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,2⟩)) (kid05_part1366) = true := by rfl

def kid05_part1367 : Audit := .cycle 0 12 true (0)
theorem kid05_part1367_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,3⟩)) (kid05_part1367) = true := by rfl

def kid05_part1368 : Audit := .cycle 7 4 true (2)
theorem kid05_part1368_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,4⟩)) (kid05_part1368) = true := by rfl

def kid05_part1369 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.last 14 (2,true),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.last 27 (2,true),
.last 14 (2,true),
.cycle 8 4 true (2),
.cycle 8 6 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 14 (2,true),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.last 17 (2,true),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1369_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,true,5⟩)) (kid05_part1369) = true := by rfl

def kid05_part1370 : Audit := .cycle 17 7 false (1)
theorem kid05_part1370_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (kid05_part1370) = true := by rfl

def kid05_part1371 : Audit := .split 12 (2,true) (byMove [
.cycle 11 4 true (1),
.cycle 14 3 false (0),
.cycle 16 1 false (0),
.cycle 10 6 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 1 15 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 8, 16, 4, 1024, 4096],[16, 4, 4, 1, 4, 4096, 16, 4, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 0 14 true (0),
.cycle 17 7 false (1),
.last 13 (5,true),
.cycle 18 7 false (0),
.cycle 14 3 false (0),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 14 5 false (2),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part1371_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,1⟩)) (kid05_part1371) = true := by rfl

def kid05_part1372 : Audit := .split 16 (2,true) (byMove [
.cycle 13 4 true (3),
.cycle 0 20 true (0),
.cycle 43 1 false (3),
.cycle 0 18 true (0),
.cycle 7 10 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 5 23 true (1),
.cycle 3 14 true (1),
.cycle 14 3 true (3),
.cycle 8 9 true (1),
.cycle 6 11 true (1),
.cycle 10 7 true (1),
.cycle 11 7 true (1),
.cycle 12 5 true (2),
.cycle 5 17 true (1),
.last 17 (5,true),
.cycle 0 17 true (0),
.cycle 1 16 true (1),
.cycle 2 15 true (1),
.cycle 12 6 true (2),
.last 21 (5,true),
.last 21 (5,true)
])
theorem kid05_part1372_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) (kid05_part1372) = true := by rfl

def kid05_part1373 : Audit := .cycle 18 1 false (0)
theorem kid05_part1373_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,3⟩)) (kid05_part1373) = true := by rfl

def kid05_part1374 : Audit := .split 15 (2,true) (byMove [
.cycle 13 4 true (-2),
.cycle 12 4 false (0),
.cycle 18 1 false (-2),
.cycle 11 10 false (1),
.cycle 11 7 false (1),
.last 16 (5,true),
.cycle 6 10 false (3),
.cycle 10 6 false (2),
.far true 4 ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],[1024, 128, 512, 512, 128, 1024, 131072, 128, 128, 512, 128, 16777216, 1024, 1024, 512, 2097152, 524288, 1024, 29492224, 30016640, 32113792, 2097152, 524288, 20971520, 16777216],[128, 1024, 512, 128, 32, 16777216, 1024, 1024, 512, 128, 131072, 16777216, 128, 4194304, 128, 1024, 8388608, 16777216, 30016640, 4194304, 32114304, 30016640, 8388608, 16777216, 16777216],31262720⟩,
.cycle 25 16 true (0),
.cycle 11 11 false (1),
.last 16 (5,true),
.cycle 11 8 false (1),
.cycle 12 4 false (0),
.cycle 11 11 false (1),
.cycle 11 9 false (1),
.cycle 11 7 false (1),
.last 16 (5,true),
.last 22 (5,true),
.last 18 (5,true),
.last 32 (5,true),
.cycle 11 15 false (2),
.last 17 (5,true),
.last 16 (5,true)
])
theorem kid05_part1374_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,4⟩)) (kid05_part1374) = true := by rfl

def kid05_part1375 : Audit := .split 13 (5,true) (byMove [
.last 17 (2,true),
.cycle 14 13 false (0),
.last 14 (2,true),
.last 17 (2,true),
.last 23 (2,true),
.cycle 14 6 false (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.last 16 (2,true),
.cycle 8 9 true (1),
.cycle 21 3 false (-1),
.last 19 (2,true),
.last 14 (2,true),
.last 18 (2,true),
.last 23 (2,true),
.cycle 14 3 false (0),
.last 20 (2,true),
.last 15 (2,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 5 false (1),
.cycle 16 6 true (2)
])
theorem kid05_part1375_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,5⟩)) (kid05_part1375) = true := by rfl

def kid05_part1376 : Audit := .split 14 (2,true) (byMove [
.cycle 11 4 true (3),
.cycle 0 16 true (0),
.cycle 33 1 false (1),
.cycle 0 16 true (0),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 6 19 true (2),
.cycle 3 12 true (1),
.cycle 12 3 true (3),
.cycle 8 7 true (2),
.cycle 6 9 true (2),
.cycle 10 5 true (2),
.cycle 5 13 true (1),
.cycle 11 5 true (3),
.last 16 (5,true),
.last 15 (5,true),
.cycle 0 15 true (0),
.cycle 1 14 true (1),
.cycle 2 13 true (1),
.cycle 11 6 true (3),
.cycle 9 6 true (2),
.cycle 8 7 true (2)
])
theorem kid05_part1376_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,0⟩)) (kid05_part1376) = true := by rfl

def kid05_part1377 : Audit := .cycle 1 11 true (1)
theorem kid05_part1377_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,1⟩)) (kid05_part1377) = true := by rfl

def kid05_part1378 : Audit := .split 11 (2,true) (byMove [
.cycle 11 4 true (2),
.cycle 2 11 true (1),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.last 18 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 4, 4, 1024, 128, 256, 8, 16, 4, 1024, 4096],[16, 256, 4, 1, 4, 4096, 16, 256, 4, 1, 4096, 4096, 4096],4096⟩,
.cycle 3 9 true (1),
.cycle 11 3 true (3),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.cycle 11 7 true (1),
.cycle 11 5 true (2),
.last 18 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 11 6 true (3),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1378_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,2⟩)) (kid05_part1378) = true := by rfl

def kid05_part1379 : Audit := .cycle 0 12 true (0)
theorem kid05_part1379_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,3⟩)) (kid05_part1379) = true := by rfl

def kid05_part1380 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.last 18 (2,true),
.last 19 (2,true),
.cycle 18 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.last 31 (2,true),
.cycle 24 1 false (2),
.last 15 (2,true),
.cycle 8 5 true (2),
.cycle 22 13 false (2),
.last 14 (2,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.last 19 (2,true),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.last 18 (2,true),
.cycle 9 4 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part1380_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,4⟩)) (kid05_part1380) = true := by rfl

def kid05_part1381 : Audit := .split 11 (5,true) (byMove [
.last 15 (2,true),
.cycle 8 5 true (2),
.last 12 (2,true),
.cycle 0 13 true (0),
.last 21 (2,true),
.cycle 17 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.last 14 (2,true),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 10 2 true (2),
.last 12 (2,true),
.last 16 (2,true),
.last 21 (2,true),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.last 17 (2,true),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1381_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,true,5⟩)) (kid05_part1381) = true := by rfl

def kid05_part1357 : Audit := .split 10 (1,true) (byMove [(kid05_part1358),(kid05_part1359),(kid05_part1360),(kid05_part1361),(kid05_part1362),(kid05_part1363),(kid05_part1364),(kid05_part1365),(kid05_part1366),(kid05_part1367),(kid05_part1368),(kid05_part1369),(kid05_part1370),(kid05_part1371),(kid05_part1372),(kid05_part1373),(kid05_part1374),(kid05_part1375),(kid05_part1376),(kid05_part1377),(kid05_part1378),(kid05_part1379),(kid05_part1380),(kid05_part1381)])

theorem kid05_part1357_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (kid05_part1357) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) 10 (1,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some mv)) (byMove [(kid05_part1358),(kid05_part1359),(kid05_part1360),(kid05_part1361),(kid05_part1362),(kid05_part1363),(kid05_part1364),(kid05_part1365),(kid05_part1366),(kid05_part1367),(kid05_part1368),(kid05_part1369),(kid05_part1370),(kid05_part1371),(kid05_part1372),(kid05_part1373),(kid05_part1374),(kid05_part1375),(kid05_part1376),(kid05_part1377),(kid05_part1378),(kid05_part1379),(kid05_part1380),(kid05_part1381)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1358_checked

  · exact kid05_part1364_checked

  · exact kid05_part1370_checked

  · exact kid05_part1376_checked

  · exact kid05_part1359_checked

  · exact kid05_part1365_checked

  · exact kid05_part1371_checked

  · exact kid05_part1377_checked

  · exact kid05_part1360_checked

  · exact kid05_part1366_checked

  · exact kid05_part1372_checked

  · exact kid05_part1378_checked

  · exact kid05_part1361_checked

  · exact kid05_part1367_checked

  · exact kid05_part1373_checked

  · exact kid05_part1379_checked

  · exact kid05_part1362_checked

  · exact kid05_part1368_checked

  · exact kid05_part1374_checked

  · exact kid05_part1380_checked

  · exact kid05_part1363_checked

  · exact kid05_part1369_checked

  · exact kid05_part1375_checked

  · exact kid05_part1381_checked

def kid05_part1383 : Audit := .cycle 0 18 true (0)
theorem kid05_part1383_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,0⟩)) (kid05_part1383) = true := by rfl

def kid05_part1384 : Audit := .cycle 0 14 true (0)
theorem kid05_part1384_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,1⟩)) (kid05_part1384) = true := by rfl

def kid05_part1385 : Audit := .cycle 21 1 false (1)
theorem kid05_part1385_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,2⟩)) (kid05_part1385) = true := by rfl

def kid05_part1386 : Audit := .cycle 0 21 true (0)
theorem kid05_part1386_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,3⟩)) (kid05_part1386) = true := by rfl

def kid05_part1387 : Audit := .split 17 (1,true) (byMove [
.cycle 0 28 true (-2),
.cycle 11 16 true (-2),
.cycle 0 26 true (-2),
.last 23 (5,true),
.cycle 11 9 false (1),
.last 18 (5,true),
.far false 5 ⟨0,[0, 1, 0, 2, 3, 4, 3, 4, 4, 4],[128, 256, 8, 17, 1, 1024, 8192, 16384, 8, 16, 1, 65536, 33554432, 67108864, 2097152, 16, 1, 268435456, 33554432, 67108864, 2097152, 17, 262144, 268435456, 33554432, 67108864, 134217728, 1363148817, 1090519041, 268435456, 1073741824],[16, 1, 128, 1, 1, 1073741824, 16, 1, 128, 1, 1073741824, 1073741824, 4194304, 262144, 1073741824, 262144, 1073741824, 1073741824, 4194304, 262144, 33554560, 262144, 1090519041, 1073741824, 268435456, 16777216, 1107296384, 16777216, 1090519041, 1073741824, 1073741824],2144219200⟩,
.cycle 11 15 false (3),
.cycle 0 20 true (-2),
.cycle 0 32 true (-2),
.cycle 0 25 true (-2),
.last 20 (5,true),
.cycle 11 10 true (-2),
.cycle 11 12 false (1),
.cycle 12 6 true (-2),
.cycle 0 27 true (-2),
.cycle 11 9 false (1),
.last 18 (5,true),
.last 34 (5,true),
.last 21 (5,true),
.cycle 0 20 true (-2),
.cycle 4 14 true (-2),
.cycle 11 11 false (2),
.last 20 (5,true)
])
theorem kid05_part1387_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,4⟩)) (kid05_part1387) = true := by rfl

def kid05_part1388 : Audit := .split 14 (5,true) (byMove [
.cycle 0 23 true (-1),
.cycle 22 3 false (1),
.cycle 16 1 false (0),
.cycle 15 1 false (-1),
.cycle 23 3 false (0),
.cycle 15 3 false (0),
.last 16 (1,true),
.cycle 28 3 false (5),
.cycle 0 21 true (0),
.cycle 15 1 false (1),
.cycle 20 3 false (3),
.cycle 21 3 false (4),
.last 16 (1,true),
.cycle 13 3 false (1),
.last 18 (1,true),
.cycle 15 1 false (-1),
.cycle 24 3 false (3),
.cycle 14 3 false (0),
.last 16 (1,true),
.cycle 1 20 true (0),
.cycle 0 21 true (0),
.cycle 19 3 false (2),
.cycle 15 3 false (1),
.cycle 17 7 true (1)
])
theorem kid05_part1388_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,false,5⟩)) (kid05_part1388) = true := by rfl

def kid05_part1389 : Audit := .cycle 0 15 true (0)
theorem kid05_part1389_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,0⟩)) (kid05_part1389) = true := by rfl

def kid05_part1390 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 40 1 false (10),
.cycle 0 28 true (0),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.cycle 1 13 true (1),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.last 14 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 18 true (0),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1390_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (kid05_part1390) = true := by rfl

def kid05_part1391 : Audit := .cycle 29 1 false (7)
theorem kid05_part1391_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,2⟩)) (kid05_part1391) = true := by rfl

def kid05_part1392 : Audit := .cycle 0 12 true (0)
theorem kid05_part1392_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,3⟩)) (kid05_part1392) = true := by rfl

def kid05_part1393 : Audit := .cycle 7 4 true (2)
theorem kid05_part1393_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,4⟩)) (kid05_part1393) = true := by rfl

def kid05_part1394 : Audit := .split 11 (5,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 33 1 false (9),
.cycle 0 28 true (0),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.last 13 (1,true),
.cycle 8 6 true (2),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 19 true (0),
.cycle 18 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 18 true (0),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1394_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,5⟩)) (kid05_part1394) = true := by rfl

def kid05_part1395 : Audit := .split 12 (1,true) (byMove [
.cycle 0 21 true (0),
.cycle 13 13 false (1),
.cycle 18 3 false (0),
.cycle 0 17 true (0),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.cycle 10 18 true (1),
.cycle 0 14 true (0),
.cycle 18 11 false (2),
.last 13 (5,true),
.cycle 18 7 false (1),
.cycle 13 10 false (1),
.cycle 18 3 false (0),
.cycle 5 8 true (1),
.last 14 (5,true),
.last 13 (5,true),
.cycle 0 17 true (0),
.cycle 1 13 true (1),
.cycle 18 13 false (2),
.cycle 0 14 true (0),
.last 14 (5,true),
.last 13 (5,true)
])
theorem kid05_part1395_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (kid05_part1395) = true := by rfl

def kid05_part1396 : Audit := .split 13 (1,true) (byMove [
.cycle 11 16 true (0),
.cycle 0 57 true (-2),
.cycle 19 1 false (-1),
.cycle 0 21 true (0),
.cycle 13 12 false (1),
.last 14 (5,true),
.cycle 6 8 true (1),
.cycle 1 15 true (1),
.cycle 10 4 true (1),
.cycle 0 19 true (0),
.cycle 17 7 false (1),
.last 14 (5,true),
.cycle 13 10 false (1),
.cycle 14 3 false (0),
.cycle 14 10 true (-2),
.cycle 23 1 false (-1),
.cycle 14 11 false (0),
.last 14 (5,true),
.cycle 12 6 true (1),
.cycle 1 15 true (1),
.cycle 12 2 true (1),
.cycle 0 19 true (0),
.last 15 (5,true),
.last 14 (5,true)
])
theorem kid05_part1396_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (kid05_part1396) = true := by rfl

def kid05_part1397 : Audit := .cycle 0 17 true (0)
theorem kid05_part1397_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,2⟩)) (kid05_part1397) = true := by rfl

def kid05_part1398 : Audit := .cycle 18 1 false (0)
theorem kid05_part1398_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,3⟩)) (kid05_part1398) = true := by rfl

def kid05_part1399 : Audit := .cycle 11 8 true (-2)
theorem kid05_part1399_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,4⟩)) (kid05_part1399) = true := by rfl

def kid05_part1400 : Audit := .split 13 (5,true) (byMove [
.last 19 (1,true),
.last 14 (1,true),
.cycle 19 1 false (-1),
.last 21 (1,true),
.cycle 13 14 false (1),
.cycle 14 6 false (0),
.last 15 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 25 1 false (1),
.cycle 0 21 true (0),
.cycle 8 9 true (1),
.last 23 (1,true),
.last 14 (1,true),
.last 21 (1,true),
.cycle 0 23 true (0),
.cycle 0 51 true (-4),
.cycle 14 3 false (0),
.last 15 (1,true),
.last 17 (1,true),
.cycle 0 16 true (0),
.cycle 4 10 true (1),
.cycle 17 5 false (1),
.cycle 16 6 true (2)
])
theorem kid05_part1400_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,5⟩)) (kid05_part1400) = true := by rfl

def kid05_part1401 : Audit := .cycle 0 15 true (0)
theorem kid05_part1401_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,0⟩)) (kid05_part1401) = true := by rfl

def kid05_part1402 : Audit := .split 11 (1,true) (byMove [
.cycle 0 16 true (0),
.cycle 1 12 true (1),
.cycle 1 12 true (1),
.cycle 0 13 true (0),
.last 18 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 1 23 true (1),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.cycle 16 5 false (2),
.cycle 10 2 true (2),
.cycle 0 17 true (0),
.last 18 (5,true),
.last 12 (5,true),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 18 true (0),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1402_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,1⟩)) (kid05_part1402) = true := by rfl

def kid05_part1403 : Audit := .cycle 2 10 true (1)
theorem kid05_part1403_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,2⟩)) (kid05_part1403) = true := by rfl

def kid05_part1404 : Audit := .cycle 0 12 true (0)
theorem kid05_part1404_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,3⟩)) (kid05_part1404) = true := by rfl

def kid05_part1405 : Audit := .split 12 (5,true) (byMove [
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 25 1 false (1),
.cycle 0 19 true (0),
.cycle 0 20 true (-2),
.cycle 18 5 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 0 32 true (0),
.cycle 24 1 false (2),
.cycle 0 16 true (0),
.cycle 8 5 true (2),
.last 14 (1,true),
.last 19 (1,true),
.cycle 0 15 true (0),
.cycle 22 1 false (0),
.cycle 0 28 true (-2),
.cycle 16 3 false (0),
.cycle 0 13 true (0),
.cycle 1 12 true (1),
.cycle 2 11 true (1),
.cycle 0 19 true (0),
.cycle 9 4 true (2),
.cycle 8 5 true (2)
])
theorem kid05_part1405_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,4⟩)) (kid05_part1405) = true := by rfl

def kid05_part1406 : Audit := .split 11 (5,true) (byMove [
.cycle 0 16 true (0),
.last 12 (1,true),
.cycle 8 5 true (2),
.cycle 0 13 true (0),
.cycle 0 22 true (-2),
.cycle 17 5 false (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 8 16 true (2),
.cycle 3 9 true (1),
.cycle 0 15 true (0),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 10 2 true (2),
.cycle 0 17 true (0),
.cycle 27 5 false (3),
.cycle 16 3 false (0),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 18 true (0),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1406_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,true,5⟩)) (kid05_part1406) = true := by rfl

def kid05_part1382 : Audit := .split 10 (2,true) (byMove [(kid05_part1383),(kid05_part1384),(kid05_part1385),(kid05_part1386),(kid05_part1387),(kid05_part1388),(kid05_part1389),(kid05_part1390),(kid05_part1391),(kid05_part1392),(kid05_part1393),(kid05_part1394),(kid05_part1395),(kid05_part1396),(kid05_part1397),(kid05_part1398),(kid05_part1399),(kid05_part1400),(kid05_part1401),(kid05_part1402),(kid05_part1403),(kid05_part1404),(kid05_part1405),(kid05_part1406)])

theorem kid05_part1382_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (kid05_part1382) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) 10 (2,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some mv)) (byMove [(kid05_part1383),(kid05_part1384),(kid05_part1385),(kid05_part1386),(kid05_part1387),(kid05_part1388),(kid05_part1389),(kid05_part1390),(kid05_part1391),(kid05_part1392),(kid05_part1393),(kid05_part1394),(kid05_part1395),(kid05_part1396),(kid05_part1397),(kid05_part1398),(kid05_part1399),(kid05_part1400),(kid05_part1401),(kid05_part1402),(kid05_part1403),(kid05_part1404),(kid05_part1405),(kid05_part1406)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1383_checked

  · exact kid05_part1389_checked

  · exact kid05_part1395_checked

  · exact kid05_part1401_checked

  · exact kid05_part1384_checked

  · exact kid05_part1390_checked

  · exact kid05_part1396_checked

  · exact kid05_part1402_checked

  · exact kid05_part1385_checked

  · exact kid05_part1391_checked

  · exact kid05_part1397_checked

  · exact kid05_part1403_checked

  · exact kid05_part1386_checked

  · exact kid05_part1392_checked

  · exact kid05_part1398_checked

  · exact kid05_part1404_checked

  · exact kid05_part1387_checked

  · exact kid05_part1393_checked

  · exact kid05_part1399_checked

  · exact kid05_part1405_checked

  · exact kid05_part1388_checked

  · exact kid05_part1394_checked

  · exact kid05_part1400_checked

  · exact kid05_part1406_checked

def kid05_part1407 : Audit := .cycle 34 1 false (4)
theorem kid05_part1407_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,3⟩)) (kid05_part1407) = true := by rfl

def kid05_part1409 : Audit := .cycle 43 1 false (-1)
theorem kid05_part1409_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part1409) = true := by rfl

def kid05_part1410 : Audit := .cycle 21 3 false (1)
theorem kid05_part1410_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part1410) = true := by rfl

def kid05_part1411 : Audit := .cycle 16 1 false (0)
theorem kid05_part1411_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part1411) = true := by rfl

def kid05_part1412 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1412_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part1412) = true := by rfl

def kid05_part1413 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1413_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part1413) = true := by rfl

def kid05_part1414 : Audit := .cycle 15 3 false (0)
theorem kid05_part1414_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part1414) = true := by rfl

def kid05_part1415 : Audit := .split 16 (1,true) (byMove [
.cycle 18 1 false (2),
.cycle 24 3 false (2),
.last 17 (2,true),
.cycle 0 21 true (0),
.cycle 17 3 false (1),
.cycle 0 21 true (0),
.cycle 20 3 false (2),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 2, 16, 64],[16, 2, 64, 1, 2, 1, 64],64⟩,
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 25 3 false (3),
.cycle 0 18 true (0),
.cycle 18 3 false (2),
.last 19 (2,true),
.last 17 (2,true),
.cycle 19 3 false (3),
.cycle 17 3 false (1),
.cycle 19 3 false (3),
.cycle 12 7 true (0),
.cycle 1 17 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.cycle 0 18 true (0)
])
theorem kid05_part1415_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part1415) = true := by rfl

def kid05_part1416 : Audit := .split 16 (2,true) (byMove [
.cycle 18 1 false (2),
.last 17 (1,true),
.cycle 19 1 false (1),
.last 19 (1,true),
.cycle 17 3 false (1),
.cycle 27 3 false (5),
.cycle 20 3 false (2),
.last 17 (1,true),
.cycle 25 3 false (3),
.cycle 0 18 true (0),
.cycle 25 3 false (3),
.last 41 (1,true),
.cycle 18 3 false (2),
.last 17 (1,true),
.cycle 21 3 false (3),
.cycle 19 3 false (3),
.cycle 17 3 false (1),
.last 18 (1,true),
.cycle 12 7 true (0),
.last 17 (1,true),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.cycle 38 5 true (3),
.last 38 (1,true)
])
theorem kid05_part1416_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part1416) = true := by rfl

def kid05_part1417 : Audit := .cycle 18 1 false (4)
theorem kid05_part1417_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part1417) = true := by rfl

def kid05_part1418 : Audit := .cycle 15 1 false (1)
theorem kid05_part1418_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part1418) = true := by rfl

def kid05_part1419 : Audit := .cycle 15 1 false (1)
theorem kid05_part1419_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part1419) = true := by rfl

def kid05_part1420 : Audit := .cycle 21 3 false (4)
theorem kid05_part1420_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part1420) = true := by rfl

def kid05_part1421 : Audit := .split 16 (1,true) (byMove [
.cycle 18 1 false (0),
.cycle 24 3 false (0),
.last 17 (2,true),
.last 20 (2,true),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.cycle 28 47 true (-3),
.last 18 (2,true),
.cycle 24 3 false (0),
.cycle 21 3 false (1),
.cycle 18 3 false (0),
.cycle 55 3 false (-1),
.cycle 18 3 false (0),
.last 19 (2,true),
.last 17 (2,true),
.cycle 19 1 false (1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.far false 2 ⟨0,[0, 1, 0, 1],[128, 256, 8, 80, 80, 1024, 128, 256, 8, 16, 80, 1024, 4096],[16, 64, 4096, 1, 80, 64, 16, 64, 4096, 1, 208, 80, 4096],4096⟩,
.last 18 (2,true),
.cycle 43 3 false (-1),
.cycle 4 13 false (3),
.cycle 12 5 false (2),
.cycle 10 11 false (2)
])
theorem kid05_part1421_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part1421) = true := by rfl

def kid05_part1422 : Audit := .split 16 (2,true) (byMove [
.cycle 18 1 false (0),
.last 17 (1,true),
.cycle 19 1 false (-1),
.last 23 (1,true),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.last 18 (1,true),
.last 19 (1,true),
.cycle 24 3 false (0),
.cycle 21 3 false (1),
.cycle 18 3 false (0),
.last 34 (1,true),
.cycle 18 3 false (0),
.last 17 (1,true),
.cycle 21 1 false (1),
.cycle 19 1 false (1),
.cycle 17 3 false (-1),
.cycle 14 3 false (0),
.last 18 (1,true),
.last 19 (1,true),
.last 42 (1,true),
.cycle 4 13 false (3),
.cycle 12 5 false (2),
.last 20 (1,true)
])
theorem kid05_part1422_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part1422) = true := by rfl

def kid05_part1423 : Audit := .split 18 (1,true) (byMove [
.cycle 20 1 false (2),
.cycle 26 3 false (2),
.last 19 (2,true),
.cycle 0 23 true (-1),
.cycle 19 3 false (1),
.cycle 0 27 true (-1),
.cycle 22 3 false (2),
.far false 4 ⟨0,[0, 1, 0, 2, 2, 3, 3, 3],[128, 256, 8, 2, 2, 1024, 8192, 16384, 8, 16, 2, 65536, 524288, 1048576, 32768, 18, 2, 4194304, 524288, 1048576, 2097152, 21561344, 17301504, 4194304, 16777216],[16, 2, 16777216, 1, 2, 1, 16, 2, 16777216, 1, 128, 16777216, 65536, 8192, 16777216, 4096, 17301504, 16781312, 4194304, 524288, 16777216, 262144, 17301504, 17039360, 16777216],33435712⟩,
.last 19 (2,true),
.cycle 0 20 true (-1),
.cycle 29 3 false (3),
.cycle 0 22 true (-1),
.cycle 20 3 false (2),
.last 21 (2,true),
.last 19 (2,true),
.cycle 21 3 false (3),
.cycle 19 3 false (1),
.cycle 23 3 false (3),
.cycle 12 9 true (-1),
.last 34 (2,true),
.last 19 (2,true),
.cycle 0 20 true (-1),
.last 21 (2,true),
.last 20 (2,true)
])
theorem kid05_part1423_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part1423) = true := by rfl

def kid05_part1424 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1424_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part1424) = true := by rfl

def kid05_part1425 : Audit := .cycle 15 1 false (-1)
theorem kid05_part1425_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part1425) = true := by rfl

def kid05_part1426 : Audit := .cycle 13 3 false (1)
theorem kid05_part1426_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part1426) = true := by rfl

def kid05_part1427 : Audit := .split 16 (1,true) (byMove [
.cycle 19 3 false (1),
.cycle 25 3 false (1),
.last 17 (2,true),
.cycle 0 21 true (0),
.last 21 (2,true),
.cycle 0 21 true (0),
.cycle 6 19 true (0),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 18, 2, 16, 64],[16, 2, 64, 1, 2, 1, 64],64⟩,
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 12 13 true (0),
.cycle 0 18 true (0),
.cycle 10 8 true (0),
.last 20 (2,true),
.last 17 (2,true),
.cycle 5 12 true (0),
.cycle 13 4 true (0),
.cycle 12 17 true (0),
.cycle 12 7 true (0),
.cycle 1 17 true (0),
.last 17 (2,true),
.cycle 0 18 true (0),
.cycle 0 19 true (0),
.cycle 0 18 true (0)
])
theorem kid05_part1427_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part1427) = true := by rfl

def kid05_part1428 : Audit := .split 16 (2,true) (byMove [
.cycle 19 3 false (1),
.last 17 (1,true),
.cycle 20 1 false (0),
.last 19 (1,true),
.cycle 0 22 true (0),
.cycle 1 20 true (0),
.cycle 6 19 true (0),
.last 17 (1,true),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 20, 4, 16, 64],[16, 64, 4, 1, 4, 2, 64],64⟩,
.cycle 0 18 true (0),
.cycle 12 13 true (0),
.cycle 1 17 true (0),
.cycle 10 8 true (0),
.last 17 (1,true),
.cycle 22 3 false (2),
.cycle 5 12 true (0),
.cycle 13 4 true (0),
.last 18 (1,true),
.cycle 12 7 true (0),
.last 17 (1,true),
.cycle 2 16 true (0),
.cycle 0 18 true (0),
.cycle 1 18 true (0),
.cycle 1 17 true (0)
])
theorem kid05_part1428_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part1428) = true := by rfl

def kid05_part1429 : Audit := .cycle 21 3 false (1)
theorem kid05_part1429_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part1429) = true := by rfl

def kid05_part1430 : Audit := .cycle 18 3 false (2)
theorem kid05_part1430_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part1430) = true := by rfl

def kid05_part1431 : Audit := .cycle 15 3 false (1)
theorem kid05_part1431_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part1431) = true := by rfl

def kid05_part1432 : Audit := .cycle 16 7 true (1)
theorem kid05_part1432_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part1432) = true := by rfl

def kid05_part1408 : Audit := .split 14 (5,true) (byMove [(kid05_part1409),(kid05_part1410),(kid05_part1411),(kid05_part1412),(kid05_part1413),(kid05_part1414),(kid05_part1415),(kid05_part1416),(kid05_part1417),(kid05_part1418),(kid05_part1419),(kid05_part1420),(kid05_part1421),(kid05_part1422),(kid05_part1423),(kid05_part1424),(kid05_part1425),(kid05_part1426),(kid05_part1427),(kid05_part1428),(kid05_part1429),(kid05_part1430),(kid05_part1431),(kid05_part1432)])

theorem kid05_part1408_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (kid05_part1408) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) 14 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,4⟩)) (5,true) (some mv)) (byMove [(kid05_part1409),(kid05_part1410),(kid05_part1411),(kid05_part1412),(kid05_part1413),(kid05_part1414),(kid05_part1415),(kid05_part1416),(kid05_part1417),(kid05_part1418),(kid05_part1419),(kid05_part1420),(kid05_part1421),(kid05_part1422),(kid05_part1423),(kid05_part1424),(kid05_part1425),(kid05_part1426),(kid05_part1427),(kid05_part1428),(kid05_part1429),(kid05_part1430),(kid05_part1431),(kid05_part1432)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1409_checked

  · exact kid05_part1415_checked

  · exact kid05_part1421_checked

  · exact kid05_part1427_checked

  · exact kid05_part1410_checked

  · exact kid05_part1416_checked

  · exact kid05_part1422_checked

  · exact kid05_part1428_checked

  · exact kid05_part1411_checked

  · exact kid05_part1417_checked

  · exact kid05_part1423_checked

  · exact kid05_part1429_checked

  · exact kid05_part1412_checked

  · exact kid05_part1418_checked

  · exact kid05_part1424_checked

  · exact kid05_part1430_checked

  · exact kid05_part1413_checked

  · exact kid05_part1419_checked

  · exact kid05_part1425_checked

  · exact kid05_part1431_checked

  · exact kid05_part1414_checked

  · exact kid05_part1420_checked

  · exact kid05_part1426_checked

  · exact kid05_part1432_checked

def kid05_part1434 : Audit := .split 13 (2,true) (byMove [
.cycle 0 29 false (3),
.last 14 (1,true),
.cycle 18 1 false (0),
.cycle 0 15 true (0),
.cycle 0 21 false (3),
.cycle 0 25 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 1, 0, 1],[128, 256, 8, 16388, 32776, 1024, 524288, 1048576, 32768, 16, 16388, 4194304, 128, 256, 8, 16388, 16388, 1024, 128, 256, 8, 16, 1, 1024, 16777216],[16, 16777216, 4, 1, 16388, 1048576, 65536, 16777216, 16384, 4096, 32776, 32776, 16, 16777216, 4, 1, 1, 256, 16, 16777216, 4, 1, 16388, 16388, 16777216],16777216⟩,
.cycle 3 11 true (1),
.cycle 0 33 false (4),
.cycle 8 6 true (1),
.cycle 0 29 false (3),
.last 14 (1,true),
.cycle 14 12 true (-1),
.cycle 0 20 true (0),
.cycle 0 21 false (3),
.cycle 0 25 false (3),
.cycle 0 14 true (0),
.cycle 1 13 true (1),
.cycle 2 12 true (1),
.cycle 0 21 true (0),
.cycle 0 31 false (4),
.cycle 0 37 false (5)
])
theorem kid05_part1434_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,0⟩)) (kid05_part1434) = true := by rfl

def kid05_part1435 : Audit := .cycle 0 14 true (0)
theorem kid05_part1435_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,1⟩)) (kid05_part1435) = true := by rfl

def kid05_part1436 : Audit := .cycle 21 1 false (1)
theorem kid05_part1436_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,2⟩)) (kid05_part1436) = true := by rfl

def kid05_part1437 : Audit := .cycle 18 1 false (0)
theorem kid05_part1437_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,3⟩)) (kid05_part1437) = true := by rfl

def kid05_part1438 : Audit := .cycle 12 4 false (0)
theorem kid05_part1438_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,4⟩)) (kid05_part1438) = true := by rfl

def kid05_part1439 : Audit := .cycle 14 3 false (0)
theorem kid05_part1439_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,false,5⟩)) (kid05_part1439) = true := by rfl

def kid05_part1440 : Audit := .cycle 0 16 true (0)
theorem kid05_part1440_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,0⟩)) (kid05_part1440) = true := by rfl

def kid05_part1441 : Audit := .split 11 (1,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 25 (2,true),
.cycle 40 1 false (8),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 6 8 true (2),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.last 17 (2,true),
.cycle 1 14 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 18 true (1),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1441_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,1⟩)) (kid05_part1441) = true := by rfl

def kid05_part1442 : Audit := .split 11 (2,true) (byMove [
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 24 1 false (2),
.cycle 21 1 false (1),
.cycle 32 1 false (2),
.cycle 8 4 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 29 1 false (7),
.cycle 30 1 false (6),
.cycle 49 1 false (7),
.cycle 8 4 true (2),
.last 13 (1,true),
.last 14 (1,true),
.cycle 0 14 true (0),
.cycle 21 1 false (1),
.cycle 0 18 true (0),
.cycle 38 1 false (6),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 0 41 true (0),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1442_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,2⟩)) (kid05_part1442) = true := by rfl

def kid05_part1443 : Audit := .cycle 0 12 true (0)
theorem kid05_part1443_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,3⟩)) (kid05_part1443) = true := by rfl

def kid05_part1444 : Audit := .cycle 7 4 true (2)
theorem kid05_part1444_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,4⟩)) (kid05_part1444) = true := by rfl

def kid05_part1445 : Audit := .cycle 8 4 true (2)
theorem kid05_part1445_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨false,true,5⟩)) (kid05_part1445) = true := by rfl

def kid05_part1446 : Audit := .split 12 (1,true) (byMove [
.cycle 22 7 false (0),
.cycle 13 13 false (1),
.last 13 (2,true),
.cycle 0 17 true (0),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 0 20 true (0),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 18 11 false (2),
.cycle 8 8 true (1),
.cycle 18 7 false (1),
.last 16 (2,true),
.last 13 (2,true),
.cycle 5 8 true (1),
.cycle 14 6 false (0),
.cycle 18 3 false (0),
.cycle 18 17 false (3),
.cycle 1 13 true (1),
.last 13 (2,true),
.cycle 0 14 true (0),
.cycle 19 9 false (1),
.cycle 18 13 false (2)
])
theorem kid05_part1446_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,0⟩)) (kid05_part1446) = true := by rfl

def kid05_part1447 : Audit := .split 12 (2,true) (byMove [
.last 18 (1,true),
.last 13 (1,true),
.cycle 16 1 false (0),
.last 15 (1,true),
.cycle 14 6 false (0),
.last 14 (1,true),
.cycle 0 20 true (0),
.last 13 (1,true),
.far false 4 ⟨0,[0, 1, 2, 3, 0, 1, 2, 3],[128, 256, 8, 4, 8, 1024, 524288, 1048576, 32768, 16, 4, 4194304, 128, 256, 8, 4, 16777216, 1024, 524288, 1048576, 32768, 16, 16777216, 4194304, 16777216],[16, 16777216, 4, 1, 4, 16384, 65536, 16777216, 16384, 4096, 8, 16777216, 16, 16777216, 4, 1, 16777216, 16384, 65536, 16777216, 16384, 4096, 16777216, 16777216, 16777216],29427712⟩,
.cycle 0 14 true (0),
.last 17 (1,true),
.cycle 8 8 true (1),
.last 18 (1,true),
.last 13 (1,true),
.cycle 13 10 true (-1),
.cycle 5 8 true (1),
.cycle 14 6 false (0),
.last 14 (1,true),
.last 18 (1,true),
.last 13 (1,true),
.cycle 2 12 true (1),
.cycle 0 14 true (0),
.last 15 (1,true),
.last 14 (1,true)
])
theorem kid05_part1447_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,1⟩)) (kid05_part1447) = true := by rfl

def kid05_part1448 : Audit := .cycle 0 20 true (0)
theorem kid05_part1448_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,2⟩)) (kid05_part1448) = true := by rfl

def kid05_part1449 : Audit := .cycle 18 1 false (0)
theorem kid05_part1449_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,3⟩)) (kid05_part1449) = true := by rfl

def kid05_part1450 : Audit := .cycle 12 4 false (0)
theorem kid05_part1450_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,4⟩)) (kid05_part1450) = true := by rfl

def kid05_part1451 : Audit := .cycle 14 3 false (0)
theorem kid05_part1451_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,false,5⟩)) (kid05_part1451) = true := by rfl

def kid05_part1452 : Audit := .cycle 0 16 true (0)
theorem kid05_part1452_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,0⟩)) (kid05_part1452) = true := by rfl

def kid05_part1453 : Audit := .split 11 (1,true) (byMove [
.cycle 1 16 true (1),
.cycle 1 12 true (1),
.last 12 (2,true),
.cycle 0 13 true (0),
.cycle 1 18 true (0),
.cycle 1 12 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.last 23 (2,true),
.cycle 3 9 true (1),
.cycle 1 15 true (1),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 14 (2,true),
.last 12 (2,true),
.cycle 1 17 true (1),
.last 20 (2,true),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 1 18 true (1),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1453_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,1⟩)) (kid05_part1453) = true := by rfl

def kid05_part1454 : Audit := .split 11 (2,true) (byMove [
.cycle 2 15 true (1),
.last 12 (1,true),
.cycle 25 1 false (1),
.cycle 0 13 true (0),
.cycle 24 5 false (2),
.cycle 2 11 true (1),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.far false 1 ⟨0,[0, 0],[2, 4, 8, 29, 12, 16, 64],[16, 64, 4, 1, 12, 4, 64],64⟩,
.cycle 3 9 true (1),
.cycle 2 14 true (1),
.cycle 8 4 true (2),
.cycle 6 6 true (2),
.last 12 (1,true),
.cycle 2 18 true (1),
.cycle 2 16 true (1),
.cycle 36 20 true (0),
.cycle 10 2 true (2),
.cycle 0 12 true (0),
.cycle 1 11 true (1),
.cycle 2 10 true (1),
.cycle 2 17 true (1),
.cycle 9 3 true (2),
.cycle 8 4 true (2)
])
theorem kid05_part1454_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,2⟩)) (kid05_part1454) = true := by rfl

def kid05_part1455 : Audit := .cycle 0 12 true (0)
theorem kid05_part1455_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,3⟩)) (kid05_part1455) = true := by rfl

def kid05_part1456 : Audit := .cycle 9 4 true (2)
theorem kid05_part1456_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,4⟩)) (kid05_part1456) = true := by rfl

def kid05_part1457 : Audit := .cycle 8 4 true (2)
theorem kid05_part1457_checked : zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some ⟨true,true,5⟩)) (kid05_part1457) = true := by rfl

def kid05_part1433 : Audit := .split 10 (5,true) (byMove [(kid05_part1434),(kid05_part1435),(kid05_part1436),(kid05_part1437),(kid05_part1438),(kid05_part1439),(kid05_part1440),(kid05_part1441),(kid05_part1442),(kid05_part1443),(kid05_part1444),(kid05_part1445),(kid05_part1446),(kid05_part1447),(kid05_part1448),(kid05_part1449),(kid05_part1450),(kid05_part1451),(kid05_part1452),(kid05_part1453),(kid05_part1454),(kid05_part1455),(kid05_part1456),(kid05_part1457)])

theorem kid05_part1433_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (kid05_part1433) = true := by

  change (zipQueryOK 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) 10 (5,true) && allMoves (fun mv => zipCheck 944 (refine (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,false,5⟩)) (5,true) (some mv)) (byMove [(kid05_part1434),(kid05_part1435),(kid05_part1436),(kid05_part1437),(kid05_part1438),(kid05_part1439),(kid05_part1440),(kid05_part1441),(kid05_part1442),(kid05_part1443),(kid05_part1444),(kid05_part1445),(kid05_part1446),(kid05_part1447),(kid05_part1448),(kid05_part1449),(kid05_part1450),(kid05_part1451),(kid05_part1452),(kid05_part1453),(kid05_part1454),(kid05_part1455),(kid05_part1456),(kid05_part1457)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1434_checked

  · exact kid05_part1440_checked

  · exact kid05_part1446_checked

  · exact kid05_part1452_checked

  · exact kid05_part1435_checked

  · exact kid05_part1441_checked

  · exact kid05_part1447_checked

  · exact kid05_part1453_checked

  · exact kid05_part1436_checked

  · exact kid05_part1442_checked

  · exact kid05_part1448_checked

  · exact kid05_part1454_checked

  · exact kid05_part1437_checked

  · exact kid05_part1443_checked

  · exact kid05_part1449_checked

  · exact kid05_part1455_checked

  · exact kid05_part1438_checked

  · exact kid05_part1444_checked

  · exact kid05_part1450_checked

  · exact kid05_part1456_checked

  · exact kid05_part1439_checked

  · exact kid05_part1445_checked

  · exact kid05_part1451_checked

  · exact kid05_part1457_checked

def kid05_part1458 : Audit := .cycle 0 10 true (0)
theorem kid05_part1458_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,0⟩)) (kid05_part1458) = true := by rfl

def kid05_part1459 : Audit := .cycle 1 9 true (1)
theorem kid05_part1459_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,1⟩)) (kid05_part1459) = true := by rfl

def kid05_part1460 : Audit := .cycle 2 8 true (1)
theorem kid05_part1460_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,2⟩)) (kid05_part1460) = true := by rfl

def kid05_part1461 : Audit := .cycle 9 4 true (3)
theorem kid05_part1461_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,3⟩)) (kid05_part1461) = true := by rfl

def kid05_part1462 : Audit := .cycle 9 1 true (3)
theorem kid05_part1462_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,4⟩)) (kid05_part1462) = true := by rfl

def kid05_part1463 : Audit := .cycle 8 2 true (2)
theorem kid05_part1463_checked : zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨true,true,5⟩)) (kid05_part1463) = true := by rfl

def kid05_part1343 : Audit := .split 9 (4,false) (byMove [(kid05_part1344),(kid05_part1345),(kid05_part1346),(kid05_part1347),(kid05_part1348),(kid05_part1349),(kid05_part1350),(kid05_part1351),(kid05_part1352),(kid05_part1353),(kid05_part1354),(kid05_part1355),(kid05_part1356),(kid05_part1357),(kid05_part1382),(kid05_part1407),(kid05_part1408),(kid05_part1433),(kid05_part1458),(kid05_part1459),(kid05_part1460),(kid05_part1461),(kid05_part1462),(kid05_part1463)])

theorem kid05_part1343_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (kid05_part1343) = true := by

  change (zipQueryOK 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) 9 (4,false) && allMoves (fun mv => zipCheck 944 (refine (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,4⟩)) (4,false) (some mv)) (byMove [(kid05_part1344),(kid05_part1345),(kid05_part1346),(kid05_part1347),(kid05_part1348),(kid05_part1349),(kid05_part1350),(kid05_part1351),(kid05_part1352),(kid05_part1353),(kid05_part1354),(kid05_part1355),(kid05_part1356),(kid05_part1357),(kid05_part1382),(kid05_part1407),(kid05_part1408),(kid05_part1433),(kid05_part1458),(kid05_part1459),(kid05_part1460),(kid05_part1461),(kid05_part1462),(kid05_part1463)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1344_checked

  · exact kid05_part1350_checked

  · exact kid05_part1356_checked

  · exact kid05_part1458_checked

  · exact kid05_part1345_checked

  · exact kid05_part1351_checked

  · exact kid05_part1357_checked

  · exact kid05_part1459_checked

  · exact kid05_part1346_checked

  · exact kid05_part1352_checked

  · exact kid05_part1382_checked

  · exact kid05_part1460_checked

  · exact kid05_part1347_checked

  · exact kid05_part1353_checked

  · exact kid05_part1407_checked

  · exact kid05_part1461_checked

  · exact kid05_part1348_checked

  · exact kid05_part1354_checked

  · exact kid05_part1408_checked

  · exact kid05_part1462_checked

  · exact kid05_part1349_checked

  · exact kid05_part1355_checked

  · exact kid05_part1433_checked

  · exact kid05_part1463_checked

def kid05_part1464 : Audit := .cycle 8 1 true (2)
theorem kid05_part1464_checked : zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some ⟨true,true,5⟩)) (kid05_part1464) = true := by rfl

def kid05 : Audit := .split 8 (5,false) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part29),(kid05_part150),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part274),(kid05_part275),(kid05_part372),(kid05_part373),(kid05_part566),(kid05_part807),(kid05_part808),(kid05_part809),(kid05_part1050),(kid05_part1315),(kid05_part1316),(kid05_part1317),(kid05_part1318),(kid05_part1343),(kid05_part1464)])

theorem check05 : zipCheck 944 (child ⟨false,false,5⟩) (kid05) = true := by

  change (zipQueryOK 944 (child ⟨false,false,5⟩) 8 (5,false) && allMoves (fun mv => zipCheck 944 (refine (child ⟨false,false,5⟩) (5,false) (some mv)) (byMove [(kid05_part1),(kid05_part2),(kid05_part3),(kid05_part4),(kid05_part29),(kid05_part150),(kid05_part247),(kid05_part248),(kid05_part249),(kid05_part274),(kid05_part275),(kid05_part372),(kid05_part373),(kid05_part566),(kid05_part807),(kid05_part808),(kid05_part809),(kid05_part1050),(kid05_part1315),(kid05_part1316),(kid05_part1317),(kid05_part1318),(kid05_part1343),(kid05_part1464)] mv))) = true

  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r

  · exact kid05_part1_checked

  · exact kid05_part247_checked

  · exact kid05_part373_checked

  · exact kid05_part1315_checked

  · exact kid05_part2_checked

  · exact kid05_part248_checked

  · exact kid05_part566_checked

  · exact kid05_part1316_checked

  · exact kid05_part3_checked

  · exact kid05_part249_checked

  · exact kid05_part807_checked

  · exact kid05_part1317_checked

  · exact kid05_part4_checked

  · exact kid05_part274_checked

  · exact kid05_part808_checked

  · exact kid05_part1318_checked

  · exact kid05_part29_checked

  · exact kid05_part275_checked

  · exact kid05_part809_checked

  · exact kid05_part1343_checked

  · exact kid05_part150_checked

  · exact kid05_part372_checked

  · exact kid05_part1050_checked

  · exact kid05_part1464_checked

end BB6.Agent11Raw39B0RE
