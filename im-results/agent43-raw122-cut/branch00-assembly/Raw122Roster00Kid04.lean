import Raw122Kid00_04
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p00_005 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_005_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨true,true,2⟩)) (1,true) (some ⟨false,true,1⟩)) = p00_005 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_006 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_006_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨true,true,2⟩)) (1,true) (some ⟨false,true,5⟩)) = p00_006 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_007 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_007_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨false,true,4⟩)) (1,true) (some ⟨true,true,1⟩)) = p00_007 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_008 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_008_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨false,true,4⟩)) (1,true) (some ⟨false,true,2⟩)) = p00_008 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_009 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_009_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩)) = p00_009 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid00_04_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) kid00_04).map Prod.snd = [p00_005,p00_006,p00_007,p00_008,p00_009] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨true,true,2⟩)) (1,true) (some ⟨false,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨true,true,2⟩)) (1,true) (some ⟨false,true,5⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨false,true,4⟩)) (1,true) (some ⟨true,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (5,false) (some ⟨false,true,4⟩)) (1,true) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨true,false,2⟩))] := rfl
    _ = _ := by rw [p00_005_eq,p00_006_eq,p00_007_eq,p00_008_eq,p00_009_eq]
end BB6.Agent43Raw122Roster
