import Raw122Kid16_04
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p16_005 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_005_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (2,true) (some ⟨false,true,0⟩)) = p16_005 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_006 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_006_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (2,true) (some ⟨false,true,0⟩)) = p16_006 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p16_007 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_007_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) = p16_007 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid16_04_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) kid16_04).map Prod.snd = [p16_005,p16_006,p16_007] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,1⟩)) (2,true) (some ⟨false,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,5⟩)) (2,true) (some ⟨false,true,0⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,4⟩)) (4,false) (some ⟨true,false,2⟩)) (2,true) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩))] := rfl
    _ = _ := by rw [p16_005_eq,p16_006_eq,p16_007_eq]
end BB6.Agent43Raw122Roster
