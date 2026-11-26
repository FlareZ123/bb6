import Raw122Kid00_12
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p00_017 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_017_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)) = p00_017 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_018 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_018_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)) = p00_018 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_019 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_019_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,2⟩)) = p00_019 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_020 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_020_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)) = p00_020 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_021 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_021_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (5,false) (some ⟨false,true,2⟩)) = p00_021 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p00_022 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem p00_022_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (2,true) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,1⟩)) = p00_022 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid00_12_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) kid00_12).map Prod.snd = [p00_017,p00_018,p00_019,p00_020,p00_021,p00_022] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨false,false,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,1⟩)) (4,false) (some ⟨false,true,5⟩)) (5,false) (some ⟨true,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,false,4⟩)) (5,false) (some ⟨true,true,4⟩)) (4,false) (some ⟨false,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨false,true,4⟩)) (4,false) (some ⟨false,false,0⟩)) (5,false) (some ⟨false,true,2⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,0⟩) (0,true) (some ⟨true,false,0⟩)) (1,true) (some ⟨true,false,5⟩)) (2,true) (some ⟨true,false,2⟩)) (4,false) (some ⟨false,true,1⟩))] := rfl
    _ = _ := by rw [p00_017_eq,p00_018_eq,p00_019_eq,p00_020_eq,p00_021_eq,p00_022_eq]
end BB6.Agent43Raw122Roster
