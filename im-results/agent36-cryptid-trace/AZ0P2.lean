import Lean.Elab.Tactic.Omega
import MarkerZeroAZero
import ABridgeTwo

namespace BB6.Agent36AZ0P2
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerZeroAZero BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def twoCost (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) (aWords q r) +
      (2*(4*k+3+CryptidA.wordInc (aWords q r))+16))

def twoUnary (k q r : Nat) : Nat :=
  2*(4*k+3+CryptidA.wordInc (aWords q r))+1

private def inputWord (k q r : Nat) : List Bool :=
  List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode (aWords q r) ++ [true,true,false])

private theorem inputShape (k q r : Nat) :
    packet (3*k+3) q (3*r+2)
      (BB6.Agent2MarkerZero.marker 0) =
    init (inputWord k q r) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    rw [show 3*k+3=2+(3*k+1) by omega,
      ← List.replicate_append_replicate]
    rfl
  have hr : List.replicate (3*r+2) true =
      List.replicate (3*r) true ++ [true,true] := by
    rw [show 3*r+2=(3*r)+2 by omega,
      ← List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++
      (false :: (List.replicate (3*r+2) true ++ [false])) =
      false :: (CryptidA.wordCode (aWords q r) ++ [true,true,false]) := by
    calc
      _ = (oppairs q ++ [false]) ++
          (List.replicate (3*r) true ++ [true,true,false]) := by
            rw [hr]
            simp [List.append_assoc]
      _ = false :: (pairs q ++
          (List.replicate (3*r) true ++ [true,true,false])) := by
            rw [BB6.Agent2MarkerZero.oppairs_false]
            simp [List.append_assoc]
      _ = _ := by
            dsimp [aWords]
            rw [BB6.Agent35MarkerA.code_word]
            simp [List.append_assoc]
  simp only [packet,word,BB6.Agent2MarkerZero.marker,oppairs,
    List.replicate_zero,List.nil_append,init,inputWord,List.cons_append]
  rw [hn,hw]
  rfl

private theorem paddedShape (k q r : Nat) :
    inputWord k q r ++ [false] =
      List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aWords q r) ++
          ([true,true,false,false] ++ [])) := by
  simp [inputWord,List.append_assoc]

/-- The original source-code A/1100 theorem with one physically
    implicit rightmost zero closes the Z_0 marker's p=2 terminal,
    uniformly over the number of coded 10 and 111 tokens. -/
theorem a_two_z0_regular (k q r : Nat) :
    ObsEq
      (run (twoCost k q r)
        (packet (3*k+3) q (3*r+2)
          (BB6.Agent2MarkerZero.marker 0)))
      (regularSection (twoUnary k q r) 1 5) := by
  let xs := inputWord k q r
  have hinput : packet (3*k+3) q (3*r+2)
      (BB6.Agent2MarkerZero.marker 0) = init xs :=
    inputShape k q r
  have hp : ObsEq
      (run (twoCost k q r) (packet (3*k+3) q (3*r+2)
        (BB6.Agent2MarkerZero.marker 0)))
      (run (twoCost k q r) (init (xs ++ [false]))) := by
    rw [hinput]
    exact source_init_pad (twoCost k q r) 1 xs
  have hraw : run (twoCost k q r) (init (xs ++ [false])) =
      (⟨[],false,List.replicate (twoUnary k q r) true ++
        (false :: List.replicate 6 true),5⟩ : Cfg) := by
    rw [show xs ++ [false] =
      List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aWords q r) ++
          ([true,true,false,false] ++ [])) from paddedShape k q r]
    exact BB6.Agent35.full_A_code_double k (aWords q r) []
  have hout :
      (⟨[],false,List.replicate (twoUnary k q r) true ++
        (false :: List.replicate 6 true),5⟩ : Cfg) =
        regularSection (twoUnary k q r) 1 5 := by
    simp [regularSection,oppairs,List.replicate_succ,List.append_assoc]
  apply cfgEq_trans hp
  rw [hraw,hout]
  exact cfgEq_refl _

#print axioms a_two_z0_regular
end BB6.Agent36AZ0P2
