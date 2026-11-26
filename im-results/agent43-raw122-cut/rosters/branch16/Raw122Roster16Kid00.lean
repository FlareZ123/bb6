import Raw122Kid16_00
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p16_000 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem p16_000_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,0⟩)) (4,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (1,true) (some ⟨true,true,4⟩)) = p16_000 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid16_00_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,0⟩)) kid16_00).map Prod.snd = [p16_000] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,false,0⟩)) (4,false) (some ⟨true,false,0⟩)) (0,true) (some ⟨true,true,0⟩)) (1,true) (some ⟨true,true,4⟩))] := rfl
    _ = _ := by rw [p16_000_eq]
end BB6.Agent43Raw122Roster
