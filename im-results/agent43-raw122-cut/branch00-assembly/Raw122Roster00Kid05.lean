import Raw122Kid00_05
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p00_010 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_010_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)) = p00_010 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_011 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_011_eq : (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨false,true,2⟩)) = p00_011 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_012 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_012_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,4⟩)) (1,true) (some ⟨false,true,2⟩)) = p00_012 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_013 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_013_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (4,false) (some ⟨false,true,2⟩)) = p00_013 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_014 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_014_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)) = p00_014 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_015 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_015_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩)) = p00_015 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid00_05_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) kid00_05).map Prod.snd = [p00_010,p00_011,p00_012,p00_013,p00_014,p00_015] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,2⟩)),(refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨false,true,0⟩)) (4,false) (some ⟨true,false,4⟩)) (1,true) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,0⟩)) (4,false) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨false,false,5⟩)) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,2⟩)) (2,true) (some ⟨false,true,0⟩))] := rfl
    _ = _ := by rw [p00_010_eq,p00_011_eq,p00_012_eq,p00_013_eq,p00_014_eq,p00_015_eq]
end BB6.Agent43Raw122Roster
