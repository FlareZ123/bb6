import Lean.Elab.Tactic.Omega
import AZ0P2
import FullWordPairs

namespace BB6.Agent26ZMarkerATwo
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerZeroAZero BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Exact primitive-time cost for the A/p=2 zero-marker section. -/
def twoCost (k q r m : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) (aWords q r) +
      (2*((4*k+3)+CryptidA.wordInc (aWords q r))+16+4*m))

def twoUnary (k q r : Nat) : Nat :=
  2*((4*k+3)+CryptidA.wordInc (aWords q r))+1

private def inputWord (k q r m : Nat) : List Bool :=
  List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode (aWords q r) ++
      ([true,true,false] ++ pairs m))

private theorem inputShape (k q r m : Nat) :
    packet (3*k+3) q (3*r+2)
      (BB6.Agent2MarkerZero.marker m) =
    init (inputWord k q r m) := by
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
  have hm : BB6.Agent2MarkerZero.marker m = false :: pairs m :=
    BB6.Agent2MarkerZero.oppairs_false m
  have hw : oppairs q ++
      (false :: (List.replicate (3*r+2) true ++
         BB6.Agent2MarkerZero.marker m)) =
    false :: (CryptidA.wordCode (aWords q r) ++
      ([true,true,false] ++ pairs m)) := by
    rw [hm]
    calc
      _ = (oppairs q ++ [false]) ++
          (List.replicate (3*r) true ++
            ([true,true,false] ++ pairs m)) := by
              rw [hr]
              simp [List.append_assoc]
      _ = false :: (pairs q ++
          (List.replicate (3*r) true ++
            ([true,true,false] ++ pairs m))) := by
              rw [BB6.Agent2MarkerZero.oppairs_false]
              simp [List.append_assoc]
      _ = _ := by
              dsimp only [aWords]
              rw [BB6.Agent35MarkerA.code_word]
              simp [List.append_assoc]
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

private theorem paddedShape (k q r m : Nat) :
    inputWord k q r m ++ [false] =
      List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aWords q r) ++
          ([true,true,false] ++ (pairs m ++ [false]))) := by
  simp [inputWord,List.append_assoc]

/-- Universally over all k,q,r,m, the *original six-state* run from
    M(3k+3,q,3r+2;Z_m) reaches regular L, preserving physical tape
    equivalence at the implicit rightmost blank. This closes the A/p2
    terminal for EVERY zero-marker depth, not only m=0. -/
theorem a_two_Z_regular (k q r m : Nat) :
    ObsEq
      (run (twoCost k q r m)
        (packet (3*k+3) q (3*r+2)
          (BB6.Agent2MarkerZero.marker m)))
      (regularSection (twoUnary k q r) 1 (2*m+5)) := by
  let xs := inputWord k q r m
  have hinput : packet (3*k+3) q (3*r+2)
      (BB6.Agent2MarkerZero.marker m) = init xs :=
    inputShape k q r m
  have hp : ObsEq
      (run (twoCost k q r m) (packet (3*k+3) q (3*r+2)
        (BB6.Agent2MarkerZero.marker m)))
      (run (twoCost k q r m) (init (xs ++ [false]))) := by
    rw [hinput]
    exact source_init_pad (twoCost k q r m) 1 xs
  have hraw : run (twoCost k q r m) (init (xs ++ [false])) =
      (⟨[],false,List.replicate (twoUnary k q r) true ++
        (false :: List.replicate (2*m+6) true),5⟩ : Cfg) := by
    rw [show xs ++ [false] =
      List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aWords q r) ++
          ([true,true,false] ++ (pairs m ++ [false])))
        from paddedShape k q r m]
    exact BB6.CryptidBridge.complete_A_word_two_one_pairs
      k m (aWords q r) []
  have hout :
      (⟨[],false,List.replicate (twoUnary k q r) true ++
        (false :: List.replicate (2*m+6) true),5⟩ : Cfg) =
        regularSection (twoUnary k q r) 1 (2*m+5) := by
    have ht : List.replicate (2*m+6) true =
        true :: List.replicate (2*m+5) true := by
      rw [show 2*m+6=(2*m+5)+1 by omega]
      simp [List.replicate_succ]
    simp [regularSection,oppairs,ht,List.append_assoc]
  apply cfgEq_trans hp
  rw [hraw,hout]
  exact cfgEq_refl _

#print axioms a_two_Z_regular
end BB6.Agent26ZMarkerATwo
