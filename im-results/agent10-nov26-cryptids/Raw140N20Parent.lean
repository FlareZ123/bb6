import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw140N20
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent50TNFPilot

def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨true,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,true,3⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def sourceLeaf : PartialMachine := refine parent (5,true) (some ⟨false,true,4⟩)

def tree (safe : ∀ m, compatible sourceLeaf m → NeverHalts m) : Audit :=
  .split 72 (5,true) (byMove [
  .cycle 590 84 false (-12),
  .cycle 131 201 false (2),
  .cycle 33 47 false (1),
  .cycle 318 69 false (-4),
  .cycle 130 201 false (2),
  .last 75 (5,false),
  .cycle 33 48 false (1),
  .last 314 (5,false),
  .last 217 (5,false),
  .cycle 210 69 false (-1),
  .proven sourceLeaf safe,
  .last 73 (5,false),
  .cycle 26 66 false (2),
  .cycle 30 59 false (1),
  .cycle 71 9 false (-5),
  .last 95 (5,false),
  .cycle 29 59 false (1),
  .last 75 (5,false),
  .cycle 30 45 false (1),
  .cycle 198 65 false (-1),
  .cycle 298 65 false (-4),
  .cycle 25 70 false (3),
  .last 81 (5,false),
  .last 73 (5,false)
])

theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem checked (safe : ∀ m, compatible sourceLeaf m → NeverHalts m) :
    zipCheck 400 parent (tree safe) = true := by rfl

theorem cover_of_source (h : Cover NeverHalts sourceLeaf) :
    Cover (WeightedBound 400) parent :=
  (certifiedZip 400 parent (tree h.sound) root nohalt (checked h.sound)).toCover

#print axioms checked
#print axioms cover_of_source
end BB6.Agent10Raw140N20
