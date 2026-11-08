import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 5000000

namespace BB6.Agent37PacketAUniformShapes

def marker : List Bool := [false,true,false,true,false,true,true,true]

def pairs : Nat → List Bool
  | 0 => []
  | q+1 => [true,false] ++ pairs q

def wordCode : List Bool → List Bool
  | [] => []
  | false::xs => [true,false] ++ wordCode xs
  | true::xs => [true,true,true] ++ wordCode xs

def code (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

def codeTail (q r : Nat) : List Bool :=
  code q r ++ [false,false,false,true]

theorem code_append (xs ys : List Bool) :
    wordCode (xs ++ ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [wordCode, ih]

theorem false_code (q : Nat) :
    wordCode (List.replicate q false) = pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change [true,false] ++ wordCode (List.replicate q false) = _
    rw [ih]
    rfl

theorem true_code (r : Nat) :
    wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ wordCode (List.replicate r true) = _
    rw [ih, show 3*(r+1)=3+3*r by omega]
    rw [←List.replicate_append_replicate]
    rfl

theorem mixed_code (q r : Nat) :
    wordCode (code q r) = pairs q ++ List.replicate (3*r) true := by
  rw [code, code_append, false_code, true_code]

theorem residue_zero_word (q r : Nat) :
    pairs q ++ (List.replicate (3*r) true ++ marker) =
    wordCode (code q r) ++ (false :: [true,false,true,false,true,true,true]) := by
  rw [mixed_code]
  simp [marker, List.append_assoc]

theorem residue_two_word (q r : Nat) :
    pairs q ++ (List.replicate (3*r+2) true ++ marker) =
    wordCode (code q r) ++ [true,true,false,true,false,true,false,true,true,true] := by
  rw [mixed_code, show 3*r+2=3*r+2 by omega, ←List.replicate_append_replicate]
  simp [marker, List.append_assoc]

theorem residue_one_word (q r : Nat) :
    pairs q ++ (List.replicate (3*r+1) true ++ marker) =
    wordCode (codeTail q r) := by
  rw [codeTail,code_append,mixed_code]
  rw [show 3*r+1=3*r+1 by omega, ←List.replicate_append_replicate]
  simp [wordCode, marker, List.append_assoc]

#print axioms residue_zero_word
#print axioms residue_one_word
#print axioms residue_two_word

end BB6.Agent37PacketAUniformShapes
