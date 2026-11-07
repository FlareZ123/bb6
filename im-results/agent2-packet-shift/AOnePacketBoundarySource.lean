import Lean.Elab.Tactic.Omega
import ABridgeCode
import BoundaryPadding
import PacketSource

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace BB6.Agent2AOneBoundary

open CryptidBoundary CryptidA
open BB6.Agent31PacketSource BB6.BoundaryPadding

/-- A-code words ending in the source-certified six-one A terminal form. -/
def aWords (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true ++ [false,true,true]

private theorem wordCode_append (ws zs : List Bool) :
    CryptidA.wordCode (ws ++ zs) =
      CryptidA.wordCode ws ++ CryptidA.wordCode zs := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordCode,ih,List.append_assoc]

private theorem falseCode (q : Nat) :
    CryptidA.wordCode (List.replicate q false) = pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change CryptidA.wordCode (false :: List.replicate q false) =
      true :: false :: pairs q
    change true :: false :: CryptidA.wordCode (List.replicate q false) = _
    rw [ih]

private theorem trueCode (r : Nat) :
    CryptidA.wordCode (List.replicate r true) =
      List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [List.replicate_succ,CryptidA.wordCode,ih]
    rw [show 3*(r+1)=3+3*r by omega,
      ←List.replicate_append_replicate]
    rfl

private theorem aWordsCode (q r : Nat) :
    CryptidA.wordCode (aWords q r) =
      pairs q ++ (List.replicate (3*r+1) true ++
       (false :: List.replicate 6 true)) := by
  simp only [aWords,wordCode_append,falseCode,trueCode]
  have hn : List.replicate (3*r+1) true =
    List.replicate (3*r) true ++ [true] := by
    rw [←List.replicate_append_replicate]
    rfl
  rw [hn]
  simp [CryptidA.wordCode,List.append_assoc,List.replicate]

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [oppairs,pairs,List.cons_append]
    simpa only [List.cons_append,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- The exact fixed-tail A packet is an A-word input with one implicit
    trailing zero. The physical padding relation is essential here. -/
theorem packetAInput (k q r : Nat) :
    packet (3*k+3) q (3*r+1) (false::List.replicate 6 true) =
      init (List.replicate (3*k+1) true ++
        false :: CryptidA.wordCode (aWords q r)) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    rw [show 3*k+3=2+(3*k+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++
      (false :: (List.replicate (3*r+1) true ++
        (false :: List.replicate 6 true))) =
        false :: CryptidA.wordCode (aWords q r) := by
    rw [aWordsCode]
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r+1) true ++
          (false :: List.replicate 6 true)) := by
          simp [List.append_assoc]
      _ = _ := by rw [oppairsFalse]; rfl
  simp only [packet,word,init,hn,hw,List.cons_append]

def aCost (k q r : Nat) : Nat :=
  (12*k*k+41*k+32)+
   (CryptidA.wordCost (4*k+3) (aWords q r) +
     (2*((4*k+3)+CryptidA.wordInc (aWords q r))+6))

def aUnary (k q r : Nat) : Nat :=
  2*((4*k+3)+CryptidA.wordInc (aWords q r))+5

/-- Unbounded exact original-machine A return from fixed-tail
    M(3k+3,q,3r+1;0 1^6) to a pure unary physical F/0 section.
    Original-source A token words are consumed with the exact primitive
    runtime aCost, modulo one rightmost implicit blank bit. -/
theorem a_p1_boundary (k q r : Nat) :
    ObsEq (run (aCost k q r)
      (packet (3*k+3) q (3*r+1) (false::List.replicate 6 true)))
      ⟨[],false,List.replicate (aUnary k q r) true,5⟩ := by
  let ws := aWords q r
  let xs := List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws
  have hpad := source_init_pad (aCost k q r) 1 xs
  have hin : init (xs ++ List.replicate 1 false) =
      init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ (false::[]))) := by
    simp [xs,List.append_assoc]
  have hexact :
      run (aCost k q r)
        (init (List.replicate (3*k+1) true ++
          false :: (CryptidA.wordCode ws ++ (false::[])))) =
        ⟨[],false,List.replicate (aUnary k q r) true,5⟩ := by
    simpa only [aCost,aUnary,ws,List.append_nil] using
      (BB6.Agent35.full_A_code k ws [])
  rw [hin,hexact] at hpad
  rw [packetAInput]
  exact hpad

#print axioms packetAInput
#print axioms a_p1_boundary

end BB6.Agent2AOneBoundary
