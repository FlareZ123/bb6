import Lean.Elab.Tactic.Omega
import ABridgeCode
import A1101010111

namespace BB6.Agent26ACode

open CryptidBoundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 2048

def packet (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,true,true] ++ ys

def tail (ys : List Bool) : List Bool :=
  [false,true,false,true,false,true,false,true,false] ++ ys

/-- An arbitrary mixed 10/111 prefix followed by 1101010111 has an
    exact original-machine F/0 endpoint for all codewords and suffixes. -/
theorem full_A_code_1101010111 (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+36))
    let start := init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ packet ys))
    run elapsed start =
      ⟨[], false, List.replicate (2*m+5) true ++ tail ys, 5⟩ := by
  dsimp
  rw [run_add, prefix_A]
  change run
    (CryptidA.wordCost (4*k+3) ws +
      (2*(4*k+3+CryptidA.wordInc ws)+36))
    (BB6.Agent35.aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ packet ys)) = _
  rw [run_add, BB6.Agent35.a_code_return]
  change run (2*(4*k+3+CryptidA.wordInc ws)+36)
    (aBoundary (4*k+3+CryptidA.wordInc ws) (packet ys)) = _
  exact a1101010111_run (4*k+3+CryptidA.wordInc ws) ys

#print axioms full_A_code_1101010111
end BB6.Agent26ACode
