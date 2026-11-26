import Raw122Kid05_16
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
def p05_008 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_008_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,true,3⟩)) = p05_008 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_009 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_009_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,false,3⟩)) = p05_009 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_010 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_010_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,3⟩)) = p05_010 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_011 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_011_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,false,4⟩)) = p05_011 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_012 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_012_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,4⟩)) = p05_012 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_013 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_013_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,false,5⟩)) = p05_013 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_014 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_014_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,5⟩)) = p05_014 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_015 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_015_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,1⟩)) = p05_015 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_016 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_016_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨false,true,1⟩)) = p05_016 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_017 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_017_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,1⟩)) = p05_017 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_018 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_018_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨false,false,3⟩)) = p05_018 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
def p05_019 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
theorem p05_019_eq : (refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,4⟩)) = p05_019 := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl
theorem kid05_16_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) kid05_16).map Prod.snd = [p05_008,p05_009,p05_010,p05_011,p05_012,p05_013,p05_014,p05_015,p05_016,p05_017,p05_018,p05_019] := by
  calc
    _ = [(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,false,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,false,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,4⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨false,false,5⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,0⟩)) (0,true) (some ⟨false,true,4⟩)) (2,true) (some ⟨true,true,5⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨false,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨false,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,1⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨false,false,3⟩)),(refine (refine (refine (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,false,4⟩)) (4,false) (some ⟨true,true,1⟩)) (1,true) (some ⟨false,true,0⟩)) (2,true) (some ⟨true,true,4⟩))] := rfl
    _ = _ := by rw [p05_008_eq,p05_009_eq,p05_010_eq,p05_011_eq,p05_012_eq,p05_013_eq,p05_014_eq,p05_015_eq,p05_016_eq,p05_017_eq,p05_018_eq,p05_019_eq]
end BB6.Agent43Raw122Roster
