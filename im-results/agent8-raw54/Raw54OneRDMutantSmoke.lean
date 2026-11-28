import Raw54OneRDBankAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54.OneRDMutantSmoke
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8Raw54.OneRDBankAudit

/-- The literal 1RD residual partial table. -/
abbrev p : PartialMachine := (refine (refine (refine (refine (refine (refine (refine (refine (refine (refine (refine (fun _ => (none : Option Transition)) (0,false) (some ⟨true,true,1⟩)) (0,true) (some ⟨false,true,5⟩)) (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨false,true,3⟩)) (2,true) (some ⟨false,true,0⟩)) (3,false) (some ⟨true,false,3⟩)) (3,true) (some ⟨false,false,4⟩)) (4,false) (some ⟨false,false,0⟩)) (4,true) (some ⟨true,true,3⟩)) (5,false) (some ⟨true,false,4⟩)) (5,true) (some ⟨false,true,4⟩))
/-- An anchored one-edge mutation of an existing FAR DFA; discovered by
    untrusted C++ and verified in source independently. -/
def bank : List FarSpec := [⟨false,7,by decide,[0,2,6,4,6,4,3,3,5,1,0,1,3,3]⟩]
def t : BankAudit := .far 0
theorem checked : bankCheck bank 1006 p t = true := by decide +kernel
theorem firstOne : p initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases b <;> decide +kernel

/-- Every ordinary table refining this one-hole parent is nonhalting
    if the checked FAR certificate is accepted. -/
theorem cover : Cover (WeightedBound 1006) p := by
  apply bankClose bank 1006 p t firstOne nohalt checked
  intro e he
  simp [bankResiduals,t] at he

#print axioms checked
#print axioms cover
end BB6.Agent8Raw54.OneRDMutantSmoke
