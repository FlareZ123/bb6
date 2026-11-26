import Raw122Kid00_01
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p00_000 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_000_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) = p00_000 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_001 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_001_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) = p00_001 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_002 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_002_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (1,true) (some ⟨false,false,4⟩)) = p00_002 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_003 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_003_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (1,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,3⟩)) = p00_003 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_004 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_004_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩)) = p00_004 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid00_01_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) kid00_01).map Prod.snd = [p00_000,p00_001,p00_002,p00_003,p00_004] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,0⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,2⟩)) (2,true) (some ⟨false,true,2⟩)) (1,true) (some ⟨false,false,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (1,true) (some ⟨false,false,1⟩)) (5,false) (some ⟨false,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨true,true,5⟩)) (1,true) (some ⟨true,false,1⟩)) (2,true) (some ⟨false,true,2⟩))] := rfl
    _ = _ := by rw [p00_000_eq,p00_001_eq,p00_002_eq,p00_003_eq,p00_004_eq]
end BB6.Agent43Raw122Roster
