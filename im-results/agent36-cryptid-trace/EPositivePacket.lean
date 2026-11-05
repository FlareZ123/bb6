import EPositiveDoubleZero
import Lean.Elab.Tactic.Omega
namespace BB6.Agent36PositiveDoubleZero
open CryptidBoundary
set_option maxHeartbeats 1000000
theorem packetSimplified (q r : Nat) (ys : List Bool) :
    [false,true,true,true] ++
      (List.replicate (2*q) true ++
        ([true,false,true,true] ++
          (List.replicate (2*r+4) true ++ ys))) =
    false :: (List.replicate (2*q+4) true ++
      (false :: (List.replicate (2*r+6) true ++ ys))) := by
  have hq : [true,true,true] ++ (List.replicate (2*q) true ++ [true]) =
      List.replicate (2*q+4) true := by
    calc
      _ = (List.replicate 3 true ++ List.replicate (2*q) true) ++
        List.replicate 1 true := by simp [List.append_assoc]
      _ = List.replicate (3+2*q+1) true := by
        rw [List.replicate_append_replicate, List.replicate_append_replicate]
      _ = _ := by rw [show 3+2*q+1=2*q+4 by omega]
  have hr : [true,true] ++ List.replicate (2*r+4) true =
      List.replicate (2*r+6) true := by
    calc
      _ = List.replicate 2 true ++ List.replicate (2*r+4) true := rfl
      _ = List.replicate (2+(2*r+4)) true := List.replicate_append_replicate
      _ = _ := by rw [show 2+(2*r+4)=2*r+6 by omega]
  calc
    _ = false :: (([true,true,true] ++
        (List.replicate (2*q) true ++ [true])) ++
        (false :: (([true,true] ++
          List.replicate (2*r+4) true) ++ ys))) := by
          simp [List.append_assoc]
    _ = _ := by rw [hq,hr]
#print axioms packetSimplified
end BB6.Agent36PositiveDoubleZero
