import Lean.Elab.Tactic.Omega
import E110111Standalone

namespace BB6.Agent37E110111
open CryptidBoundary

/-- The raw concatenation of the exact sweep steps equals a uniform packet. -/
theorem longPacket_normal (q : Nat) (ys : List Bool) :
    longPacket q ys =
      [true,true,false] ++ List.replicate (2*q+6) true ++
        ([false,true,false,true,false] ++ ys) := by
  have h : 3+2*(q+1)+1 = 2*q+6 := by omega
  unfold longPacket
  calc
    [true,true] ++ ([false,true,true,true] ++
      (List.replicate (2*(q+1)) true ++
        ([true,false,true,false,true,false] ++ ys)))
      = [true,true,false] ++
        ((List.replicate 3 true ++ List.replicate (2*(q+1)) true ++
            List.replicate 1 true) ++ ([false,true,false,true,false] ++ ys)) := by
              simp [List.append_assoc]
    _ = [true,true,false] ++
        (List.replicate (2*q+6) true ++ ([false,true,false,true,false] ++ ys)) := by
              rw [← List.append_assoc, List.replicate_append_replicate,
                  List.replicate_append_replicate]
              rw [h]
              simp only [List.append_assoc]

/-- Fully normalized source-table E return on a variable alternating block. -/
theorem eLong_run_normal (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+35) (eLong m q ys) =
      ⟨[], false, List.replicate (2*m+3) true ++
         ([true,true,false] ++ List.replicate (2*q+6) true ++
           ([false,true,false,true,false] ++ ys)),5⟩ := by
  rw [eLong_run, longPacket_normal]

#print axioms longPacket_normal
#print axioms eLong_run_normal
end BB6.Agent37E110111
