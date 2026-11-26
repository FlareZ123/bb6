import Raw122Kid05_06
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p05_000 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_000_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) = p05_000 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_001 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_001_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)) = p05_001 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_002 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_002_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) = p05_002 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_003 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_003_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) = p05_003 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid05_06_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) kid05_06).map Prod.snd = [p05_000,p05_001,p05_002,p05_003] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,0⟩)) (2,true) (some ⟨true,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩))] := rfl
    _ = _ := by rw [p05_000_eq,p05_001_eq,p05_002_eq,p05_003_eq]
end BB6.Agent43Raw122Roster
