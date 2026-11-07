import Lean.Elab.Tactic.Omega
import ABridgeCode
import BoundaryPadding
import PacketSource
import CryptidPairs
import BoundaryBZero

set_option maxRecDepth 4096
set_option maxHeartbeats 10000000

namespace BB6.Agent2PacketZeroBoundary

open CryptidBoundary CryptidA BB6.Agent31PacketSource
open BB6.BoundaryPadding

def aZeroWords (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

private theorem wordCode_append (ws zs : List Bool) :
    CryptidA.wordCode (ws ++ zs) =
      CryptidA.wordCode ws ++ CryptidA.wordCode zs := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordCode,ih]

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

private theorem aZeroWordsCode (q r : Nat) :
    CryptidA.wordCode (aZeroWords q r) =
      pairs q ++ List.replicate (3*r) true := by
  simp [aZeroWords,wordCode_append,falseCode,trueCode]

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [oppairs,pairs,List.cons_append]
    simpa only [List.cons_append,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem aZeroInput (k q r : Nat) :
    packet (3*k+3) q (3*r) (false::List.replicate 6 true) =
      init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aZeroWords q r) ++
          (false :: List.replicate 6 true))) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    rw [show 3*k+3=2+(3*k+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw :
      oppairs q ++ (false :: (List.replicate (3*r) true ++
        (false :: List.replicate 6 true))) =
      false :: (CryptidA.wordCode (aZeroWords q r) ++
        (false :: List.replicate 6 true)) := by
    rw [aZeroWordsCode]
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r) true ++
          (false :: List.replicate 6 true)) := by
          simp [List.append_assoc]
      _ = _ := by rw [oppairsFalse]; simp [List.append_assoc]
  simp only [packet,word,init,hn,hw,List.cons_append]

def aZeroCost (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) (aZeroWords q r) +
      (2*((4*k+3)+CryptidA.wordInc (aZeroWords q r))+6))

def aZeroUnary (k q r : Nat) : Nat :=
  2*((4*k+3)+CryptidA.wordInc (aZeroWords q r))+11

/-- All p=0 mod3 fixed-tail A packets return to pure unary F0
    in a source-certified exact primitive runtime. -/
theorem a_zero_boundary (k q r : Nat) :
    run (aZeroCost k q r)
      (packet (3*k+3) q (3*r) (false::List.replicate 6 true)) =
      ⟨[],false,List.replicate (aZeroUnary k q r) true,5⟩ := by
  rw [aZeroInput]
  have h := BB6.Agent35.full_A_code k (aZeroWords q r) (List.replicate 6 true)
  have hrep :
      List.replicate
        (2*((4*k+3)+CryptidA.wordInc (aZeroWords q r))+5) true ++
        List.replicate 6 true =
      List.replicate (aZeroUnary k q r) true := by
    rw [List.replicate_append_replicate]
    congr 1 <;> omega
  rw [show aZeroCost k q r =
    (12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) (aZeroWords q r) +
       (2*((4*k+3)+CryptidA.wordInc (aZeroWords q r))+6)) by rfl,
       h,hrep]

/-- Every E packet with p=0 and fixed tail 0 1^6 has an exact raw
    return to the canonical regular L(8k+5,1,2q+11) section. -/
theorem e_zero_boundary (k q : Nat) :
    run (12*k*k+49*k+50+4*q)
      (packet (3*k+4) q 0 (false::List.replicate 6 true)) =
      BB6.Agent2BoundaryBZero.regularSection (8*k+5) 1 (2*q+11) := by
  let ys : List Bool := List.replicate 6 true
  have hn : List.replicate (3*k+4) true =
      true::true::List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hpair (q : Nat) :
      oppairs q ++ [false] = false :: pairs q := oppairsFalse q
  have hin :
      packet (3*k+4) q 0 (false::ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false::ys))) := by
    simp only [packet,word,init,hn,List.replicate_zero,List.nil_append,
      List.cons_append]
    simp only [List.append_assoc]
    have hword : oppairs q ++ (false :: (false :: ys)) =
        false :: (pairs q ++ (false :: ys)) := by
      calc
        _ = (oppairs q ++ [false]) ++ false :: ys := by
          simp [List.append_assoc]
        _ = _ := by rw [hpair]; rfl
    rw [hword]
  have hraw := CryptidBoundary.full_E_pairs k q ys
  rw [hin,hraw]
  have hlen : List.replicate (2*q+6) true ++ ys =
      List.replicate (2*q+12) true := by
    dsimp [ys]
    rw [List.replicate_append_replicate]
    congr 1 <;> omega
  simp only [BB6.Agent2BoundaryBZero.regularSection,oppairs,ys]
  rw [hlen]
  have hh : List.replicate (2*q+12) true =
      true :: List.replicate (2*q+11) true := by
    rw [show 2*q+12=1+(2*q+11) by omega,
      ←List.replicate_append_replicate]
    rfl
  rw [hh]
  rfl

#print axioms a_zero_boundary
#print axioms e_zero_boundary

end BB6.Agent2PacketZeroBoundary
