import TreeLift
import Box11Core
import Box12External

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48Box11Lift
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge BB6.Agent48Box12 BB6.Agent48PackedFinite BB6.Agent48TreeLift
open BB6.Agent49Box (Box Fits)
open BB6.Agent49Box6 (index decode code fromCodes partialEq_sound)

def domain := BB6.Agent48Box11.baseBox

def entry (e : Nat) : Array Nat := #[8,25,11,25,17,13,11,25,e,25,25,25]
def branchResiduals (B e : Nat) (tree : Tree) : List (Array Nat) :=
  residuals B externalCheck domain (1,true) 8 (entry e) tree

theorem branch_sound (B e : Nat) (tree : Tree) (m : Machine) (hm : Fits domain m)
    (hp : compatible (fromCodes (entry e)) m)
    (h : ∀ ds ∈ branchResiduals B e tree, compatible (fromCodes ds) m → DecidedBelow B m) :
    DecidedBelow B m :=
  residuals_sound B externalCheck (externalCheck_sound B) domain (1,true) 8 (entry e) tree (by rfl) m hm hp h

theorem entry_compatible (e : Nat) (m : Machine) (hm : Fits domain m)
    (he : e < 25) (hq : m (4,false) = decode e) :
    compatible (fromCodes (entry e)) m := by
  have hp := BB6.Agent48Box11.initial_compatible m hm
  have hr := compatible_refine BB6.Agent48Box11.initial m (4,false) hp
  rw [hq] at hr
  have hc : fromCodes (entry e) = refine BB6.Agent48Box11.initial (4,false) (decode e) := by
    have ht : (List.range 25).all (fun e =>
      BB6.Agent49Box6.partialEq (fromCodes (entry e)) (refine BB6.Agent48Box11.initial (4,false) (decode e))) = true := by decide +kernel
    exact partialEq_sound (List.all_eq_true.mp ht e (List.mem_range.mpr he))
  rw [hc]
  exact hr

theorem source_branch_sound (B e : Nat) (tree : Tree) (m : Machine)
    (hm : Fits raw10Remainder[11]! m)
    (he : e < 25) (hq : m (4,false) = decode e)
    (h : ∀ ds ∈ branchResiduals B e tree, compatible (fromCodes ds) m → DecidedBelow B m) :
    WeightedBound (B+5) m := by
  have hd := BB6.Agent48Box11.sourceMatch_sound _ BB6.Agent48Box11.sourceIndex11 m hm
  exact ordinary_weighted _ B (by omega) m (branch_sound B e tree m hd (entry_compatible e m hd he hq) h)

def mass (cs : Array Nat) : Nat :=
  (List.range 12).foldl (fun n i => if cs[i]! = 25 then n * (if i = 3 then 20 else if i = 8 then 11 else 25) else n) 1

#print axioms source_branch_sound
end BB6.Agent48Box11Lift
