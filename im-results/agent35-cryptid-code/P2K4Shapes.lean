import Lean.Elab.Tactic.Omega
import ABridgeCode

namespace BB6.Agent35K4Shapes
set_option maxHeartbeats 10000000
set_option maxRecDepth 2048

def marker : List Bool := [false,true,false,true,false,true,true,true]
def code (u : Nat) : List Bool := List.replicate 4 false ++ List.replicate (2*u) true
def codeTail (u : Nat) : List Bool := List.replicate 4 false ++ List.replicate (2*u+1) true ++ [false,false,false,true]

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

private theorem pref_code :
    CryptidA.wordCode (List.replicate 4 false) =
      [true,false,true,false,true,false,true,false] := by rfl

theorem word0 (u : Nat) :
    [true,false,true,false,true,false,true,false] ++
       (List.replicate (2*(3*u)) true ++ marker) =
       CryptidA.wordCode (code u) ++
         (false :: [true,false,true,false,true,true,true]) := by
  rw [code, code_append, pref_code, triple_code]
  rw [show 2*(3*u)=3*(2*u) by omega]
  simp [marker, List.append_assoc]

theorem word1 (u : Nat) :
    [true,false,true,false,true,false,true,false] ++
       (List.replicate (2*(3*u+1)) true ++ marker) =
       CryptidA.wordCode (code u) ++
         [true,true,false,true,false,true,false,true,true,true] := by
  rw [code,code_append,pref_code,triple_code]
  rw [show 2*(3*u+1)=3*(2*u)+2 by omega]
  rw [←List.replicate_append_replicate]
  simp [marker,List.append_assoc]

theorem word2 (u : Nat) :
    [true,false,true,false,true,false,true,false] ++
       (List.replicate (2*(3*u+2)) true ++ marker) =
       CryptidA.wordCode (codeTail u) := by
  rw [codeTail,code_append,code_append,pref_code,triple_code]
  rw [show 2*(3*u+2)=3*(2*u+1)+1 by omega]
  rw [←List.replicate_append_replicate]
  simp [marker,CryptidA.wordCode,List.append_assoc]

#print axioms word0
#print axioms word1
#print axioms word2
end BB6.Agent35K4Shapes
