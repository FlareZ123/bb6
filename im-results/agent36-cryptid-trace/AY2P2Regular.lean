import Lean.Elab.Tactic.Omega
import YSafeNormalizer
import A110101Closure

/-!
  New all-parameter original D A/ p≡2 terminal for Y_2=(01)^2 11.
  After the universal A-coded prefix, the remaining terminal is exactly
  the 8-symbol 11010111: its previously source-proved return leaves
  the regular F0 word 010101 with one physically irrelevant end blank.
-/
namespace BB6.Agent36AY2

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 13000000
set_option maxRecDepth 8192

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => [false,true] ++ xs) ih

private theorem y_two_shape (ka q r : Nat) :
    packet (3*ka+3) q (3*r+2) (marker 2) =
      init (List.replicate (3*ka+1) true ++
        false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
          [true,true,false,true,false,true,true,true])) := by
  have hn : List.replicate (3*ka+3) true =
      true :: true :: List.replicate (3*ka+1) true := by
    rw [show 3*ka+3=2+(3*ka+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hr : List.replicate (3*r+2) true =
      List.replicate (3*r) true ++ [true,true] := by
    rw [show 3*r+2=(3*r)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++
      (false :: (List.replicate (3*r+2) true ++ marker 2)) =
      false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,false,true,true,true]) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r+2) true ++ marker 2) := by
          simp [List.append_assoc]
      _ = false :: (pairs q ++
        (List.replicate (3*r+2) true ++ marker 2)) := by
          rw [oppairs_false]
          rfl
      _ = false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,false,true,true,true]) := by
          rw [BB6.Agent35MarkerA.code_word,hr]
          simp [marker,oppairs,List.append_assoc]
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

def a2Cost (ka q r : Nat) : Nat :=
  (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) (BB6.Agent35MarkerA.code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+30))
def a2N (ka q r : Nat) : Nat :=
  2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+5

/-- Exact original primitive-time formula, unrestricted k,q,r. -/
theorem a_two_y2_original (ka q r : Nat) :
    run (a2Cost ka q r)
      (packet (3*ka+3) q (3*r+2) (marker 2)) =
      (⟨[],false,List.replicate (a2N ka q r) true ++
        [false,true,false,true,false,true,false],5⟩ : Cfg) := by
  rw [y_two_shape]
  unfold a2Cost
  rw [run_add,prefix_A]
  change run
    (CryptidA.wordCost (4*ka+3) (BB6.Agent35MarkerA.code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+30))
    (BB6.Agent35.aBoundary (4*ka+3)
      (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,false,true,true,true])) = _
  rw [run_add,BB6.Agent35.a_code_return]
  change run
    (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+30)
    (BB6.Agent35.aBoundary
      ((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))
        [true,true,false,true,false,true,true,true]) = _
  exact BB6.Agent26A110101.a_eight_return
    ((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r)) []

/-- Entire Y2, A/p2 family physically returns to regular L; the lone
    final explicit zero is the infinite-tape blank equivalence. -/
theorem a_two_y2_regular (ka q r : Nat) :
    ∃ T a Q b,
      ObsEq
        (run T (packet (3*ka+3) q (3*r+2) (marker 2)))
        (regularSection a Q b) := by
  refine ⟨a2Cost ka q r,a2N ka q r,3,0,?_⟩
  rw [a_two_y2_original]
  have hp := source_pad 0 0 1 (regularSection (a2N ka q r) 3 0)
  change ObsEq
    (regularSection (a2N ka q r) 3 0)
    (⟨[],false,
      (List.replicate (a2N ka q r) true ++
        (oppairs 3 ++ List.replicate 0 true)) ++ [false],5⟩ : Cfg) at hp
  simpa [ObsEq,regularSection,run,oppairs,List.append_assoc] using
    (BB6.Padding.cfgEq_symm hp)

#print axioms a_two_y2_original
#print axioms a_two_y2_regular
end BB6.Agent36AY2
