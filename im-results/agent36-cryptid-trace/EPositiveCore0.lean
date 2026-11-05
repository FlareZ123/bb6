import EZeroPairs0
import Lean.Elab.Tactic.Omega
namespace BB6.Agent36PositiveDoubleZero
open CryptidBoundary
open BB6.Agent36EZeroPairs0
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192
def core (m : Nat) : List Bool := pairs (m+2) ++ [true,true]
theorem dBridge (q : Nat) (L ys : List Bool) :
    run 4 (⟨oppairs (q+2) ++ L,true,ys,3⟩ : Cfg) =
    cWalk q L ([true,false,true,true] ++ ys) := by
  simp [run,step,goL,goR,oppairs,cWalk]
theorem fourOnes (r : Nat) (ys : List Bool) :
    [true,true] ++ (List.replicate (2*r) true ++ ([true,true] ++ ys)) =
    List.replicate (2*r+4) true ++ ys := by
  calc
    _ = (List.replicate 2 true ++ List.replicate (2*r) true ++
          List.replicate 2 true) ++ ys := by simp [List.append_assoc]
    _ = List.replicate (2+2*r+2) true ++ ys := by
      rw [List.replicate_append_replicate, List.replicate_append_replicate]
    _ = _ := by rw [show 2+2*r+2=2*r+4 by omega]
#print axioms dBridge
end BB6.Agent36PositiveDoubleZero
