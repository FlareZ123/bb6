import Lean.Elab.Tactic.Omega
import MarkerZeroSource

namespace BB6.Agent2MarkerZeroAZero
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def aWords (q r : Nat) : List Bool := BB6.Agent35MarkerA.code q r
def aCost (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) (aWords q r) +
      (2*((4*k+3)+CryptidA.wordInc (aWords q r))+6))
def aUnary (k q r : Nat) : Nat :=
  2*((4*k+3)+CryptidA.wordInc (aWords q r))+5

private theorem aInput (k q r m : Nat) :
    packet (3*k+3) q (3*r) (BB6.Agent2MarkerZero.marker m) =
      init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode (aWords q r) ++
          (false :: pairs m))) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    rw [show 3*k+3=2+(3*k+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hm : BB6.Agent2MarkerZero.marker m = false :: pairs m :=
    BB6.Agent2MarkerZero.oppairs_false m
  have hw : oppairs q ++
      (false :: (List.replicate (3*r) true ++
        BB6.Agent2MarkerZero.marker m)) =
      false :: (CryptidA.wordCode (aWords q r) ++
        (false :: pairs m)) := by
    rw [hm, BB6.Agent35MarkerA.code_word]
    calc
      _ = (oppairs q ++ [false]) ++
          (List.replicate (3*r) true ++ (false :: pairs m)) := by
            simp [List.append_assoc]
      _ = _ := by
        rw [BB6.Agent2MarkerZero.oppairs_false]
        simp [List.append_assoc]
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

/-- Arbitrary A-terminal p≡0 of zero-ended marker: exact source endpoint
    with arbitrary m unconsumed rightward (10) pairs. -/
theorem aZeroRaw (k q r m : Nat) :
    run (aCost k q r)
      (packet (3*k+3) q (3*r) (BB6.Agent2MarkerZero.marker m)) =
      (⟨[],false,List.replicate (aUnary k q r) true ++ pairs m,5⟩ : Cfg) := by
  rw [aInput]
  exact BB6.Agent35.full_A_code k (aWords q r) (pairs m)

/-- The A p=0 section always returns to physically regular L. The
    output absorbs the first 10 pair into the unary prefix and treats
    only the final zero as a physically irrelevant trailing blank. -/
theorem aZeroRegular (k q r m : Nat) :
    ∃ T a markerPairs b,
      ObsEq
        (run T
          (packet (3*k+3) q (3*r) (BB6.Agent2MarkerZero.marker m)))
        (regularSection a markerPairs b) := by
  cases m with
  | zero =>
    refine ⟨aCost k q r, aUnary k q r, 0,0,?_⟩
    rw [aZeroRaw]
    change CfgEq
      (represent
        (⟨[],false,List.replicate (aUnary k q r) true,5⟩ : Cfg))
      (represent (⟨[],false,List.replicate (aUnary k q r) true,5⟩ : Cfg))
    exact cfgEq_refl _
  | succ m =>
    refine ⟨aCost k q r, aUnary k q r+1, m,0,?_⟩
    rw [aZeroRaw]
    have hh : List.replicate (aUnary k q r) true ++ pairs (m+1) =
        List.replicate (aUnary k q r+1) true ++
          BB6.Agent2MarkerZero.marker m := by
      rw [←BB6.Agent2MarkerZero.one_marker]
      have hone : List.replicate (aUnary k q r+1) true =
          List.replicate (aUnary k q r) true ++ [true] := by
        rw [show aUnary k q r+1=(aUnary k q r)+1 by omega,
          ←List.replicate_append_replicate]
        rfl
      rw [hone]
      simp [List.append_assoc]
    rw [hh]
    exact BB6.Agent2MarkerZero.regularPad (aUnary k q r+1) m

#print axioms aZeroRaw
#print axioms aZeroRegular
end BB6.Agent2MarkerZeroAZero
