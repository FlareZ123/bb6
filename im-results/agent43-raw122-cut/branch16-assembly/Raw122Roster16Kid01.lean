import Raw122Kid16_01
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p16_001 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_001_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (1,true) (some ⟨false,true,4⟩)) = p16_001 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_002 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_002_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) = p16_002 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_003 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_003_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) = p16_003 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_004 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_004_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,5⟩)) = p16_004 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid16_01_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) kid16_01).map Prod.snd = [p16_001,p16_002,p16_003,p16_004] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) (1,true) (some ⟨false,true,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,5⟩))] := rfl
    _ = _ := by rw [p16_001_eq,p16_002_eq,p16_003_eq,p16_004_eq]
end BB6.Agent43Raw122Roster
