import Raw122Kid17_18
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p17_017 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
theorem p17_017_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)) = p17_017 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p17_018 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
theorem p17_018_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (2,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,1⟩)) = p17_018 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p17_019 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
theorem p17_019_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (2,true) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,1⟩)) = p17_019 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p17_020 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
theorem p17_020_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,true,5⟩)) (1,true) (some ⟨true,true,0⟩)) = p17_020 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid17_18_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) kid17_18).map Prod.snd = [p17_017,p17_018,p17_019,p17_020] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨true,true,2⟩)) (2,true) (some ⟨true,false,1⟩)) (1,true) (some ⟨false,false,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (2,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨true,false,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,false,4⟩)) (2,true) (some ⟨true,true,2⟩)) (4,false) (some ⟨false,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,5⟩) (5,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,true,5⟩)) (1,true) (some ⟨true,true,0⟩))] := rfl
    _ = _ := by rw [p17_017_eq,p17_018_eq,p17_019_eq,p17_020_eq]
end BB6.Agent43Raw122Roster
