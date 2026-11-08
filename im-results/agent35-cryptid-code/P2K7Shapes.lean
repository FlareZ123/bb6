import Lean.Elab.Tactic.Omega
import ABridgeCode
import P2K4Shapes

namespace BB6.Agent35K7Shapes
open BB6.Agent35K4Shapes (marker)
set_option maxHeartbeats 10000000
set_option maxRecDepth 2048

def code (u : Nat) : List Bool := [false] ++ List.replicate (2*u+1) true
def codeTail (u : Nat) : List Bool := [false] ++ List.replicate (2*u+2) true ++ [false,false,false,true]

private theorem code_append (xs ys : List Bool) :
    CryptidA.wordCode (xs ++ ys) = CryptidA.wordCode xs ++ CryptidA.wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [CryptidA.wordCode, ih]

private theorem triple_code (r : Nat) :
    CryptidA.wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ CryptidA.wordCode (List.replicate r true) = _
    rw [ih, show 3*(r+1)=3+3*r by omega]
    rw [←List.replicate_append_replicate]
    rfl

theorem word0 (u : Nat) :
    [true,false] ++ (List.replicate (2*(3*u)+3) true ++ marker) =
      CryptidA.wordCode (code u) ++
        (false :: [true,false,true,false,true,true,true]) := by
  rw [code,code_append,triple_code]
  rw [show 2*(3*u)+3=3*(2*u+1) by omega]
  simp [marker,List.append_assoc,CryptidA.wordCode]

theorem word1 (u : Nat) :
    [true,false] ++ (List.replicate (2*(3*u+1)+3) true ++ marker) =
      CryptidA.wordCode (code u) ++
        [true,true,false,true,false,true,false,true,true,true] := by
  rw [code,code_append,triple_code]
  rw [show 2*(3*u+1)+3=3*(2*u+1)+2 by omega]
  rw [←List.replicate_append_replicate]
  simp [marker,List.append_assoc,CryptidA.wordCode]

theorem word2 (u : Nat) :
    [true,false] ++ (List.replicate (2*(3*u+2)+3) true ++ marker) =
      CryptidA.wordCode (codeTail u) := by
  rw [codeTail,code_append,code_append,triple_code]
  rw [show 2*(3*u+2)+3=3*(2*u+2)+1 by omega]
  rw [←List.replicate_append_replicate]
  simp [marker,List.append_assoc,CryptidA.wordCode]

#print axioms word0
#print axioms word1
#print axioms word2
end BB6.Agent35K7Shapes
