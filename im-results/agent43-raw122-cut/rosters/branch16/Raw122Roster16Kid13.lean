import Raw122Kid16_13
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p16_010 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_010_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (1,true) (some ⟨true,true,1⟩)) (4,false) (some ⟨false,false,4⟩)) = p16_010 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_011 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_011_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) = p16_011 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_012 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_012_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (4,false) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) = p16_012 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid16_13_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) kid16_13).map Prod.snd = [p16_010,p16_011,p16_012] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (1,true) (some ⟨true,true,1⟩)) (4,false) (some ⟨false,false,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,0⟩)) (1,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,1⟩)) (4,false) (some ⟨false,false,0⟩)) (0,true) (some ⟨false,false,0⟩))] := rfl
    _ = _ := by rw [p16_010_eq,p16_011_eq,p16_012_eq]
end BB6.Agent43Raw122Roster
