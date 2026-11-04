import Lean.Elab.Tactic.Omega
import AExceptionalClosure
import A1101010111First

namespace BB6.Agent26ACodeFirst

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def packet (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,true,true] ++ ys

def tail (ys : List Bool) : List Bool :=
  [false,true,false,true,false,true,false,true,false] ++ ys

/-- Original six-state machine: the mixed 10/111 code followed by the
  new exceptional A terminal returns for the FIRST time at the exact
  stated number of primitive steps, from any synthetic F/0 section. -/
theorem full_A_code_1101010111_first_return
    (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+36))
    let start := init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ packet ys))
    run elapsed start =
      ⟨[],false,List.replicate (2*m+5) true ++ tail ys,5⟩ ∧
    ∀ t, 0<t → t<elapsed →
      ¬ BB6.CryptidE111FirstReturn.IsPhysicalReturn (run t start) := by
  have hend : ∀ (m : Nat) (ys : List Bool), 3 ≤ m →
      run (2*m+36) (CryptidBoundary.aBoundary m (packet ys)) =
        ⟨[], false, List.replicate (2*m+5) true ++ tail ys, 5⟩ := by
    intro m zs _
    exact a1101010111_run m zs
  have hno : ∀ (m : Nat) (ys : List Bool) (t : Nat),
      3 ≤ m → t < 2*m+36 →
      ¬ Physical (run t (CryptidBoundary.aBoundary m (packet ys))) := by
    intro m zs t _ ht
    exact a1101010111_first_physical m zs t ht
  exact BB6.CryptidAGenericClosure.lift_first_return
    packet tail (fun m => 2*m+36) (fun m => 2*m+5)
    hend hno k ws ys

#print axioms full_A_code_1101010111_first_return

end BB6.Agent26ACodeFirst
