import Lean.Elab.Tactic.Omega
import AY2P2Regular
import A110111

/-!
  A second previously unintegrated universal A/p2 Y-marker return:
    Y_1=(01)^1 11 = 0111, so 11 Y_1 = 110111.
  The exact source six-symbol terminal from A110111 yields an F/0
  regular suffix (01)^2, up to one explicit blank-zero padding.
-/
namespace BB6.Agent36AY1

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => [false,true] ++ xs) ih

private theorem shape (ka q r : Nat) :
    packet (3*ka+3) q (3*r+2) (marker 1) =
      init (List.replicate (3*ka+1) true ++
        false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
          [true,true,false,true,true,true])) := by
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
      (false :: (List.replicate (3*r+2) true ++ marker 1)) =
      false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,true,true]) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r+2) true ++ marker 1) := by
          simp [List.append_assoc]
      _ = false :: (pairs q ++
        (List.replicate (3*r+2) true ++ marker 1)) := by
          rw [oppairs_false]
          rfl
      _ = false :: (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,true,true]) := by
          rw [BB6.Agent35MarkerA.code_word,hr]
          simp [marker,oppairs,List.append_assoc]
  simp only [packet,word,init,List.cons_append]
  rw [hn,hw]
  rfl

def cost (ka q r : Nat) : Nat :=
  (12*ka*ka+41*ka+32) +
    (CryptidA.wordCost (4*ka+3) (BB6.Agent35MarkerA.code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+24))
def unary (ka q r : Nat) : Nat :=
  2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+5

theorem original (ka q r : Nat) :
    run (cost ka q r)
      (packet (3*ka+3) q (3*r+2) (marker 1)) =
      (⟨[],false,List.replicate (unary ka q r) true ++
        [false,true,false,true,false],5⟩ : Cfg) := by
  rw [shape]
  unfold cost
  rw [run_add,prefix_A]
  change run
    (CryptidA.wordCost (4*ka+3) (BB6.Agent35MarkerA.code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+24))
    (BB6.Agent35.aBoundary (4*ka+3)
      (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
        [true,true,false,true,true,true])) = _
  rw [run_add,BB6.Agent35.a_code_return]
  change run
    (2*((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+24)
    (BB6.Agent35.aBoundary
      ((4*ka+3)+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))
        [true,true,false,true,true,true]) = _
  have h := CryptidBoundary.a110111_run
    (4*ka+CryptidA.wordInc (BB6.Agent35MarkerA.code q r)) []
  simpa [unary,BB6.Agent35.aBoundary,CryptidBoundary.aBoundary,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem regular (ka q r : Nat) :
    ∃ T a Q b,
      ObsEq
        (run T (packet (3*ka+3) q (3*r+2) (marker 1)))
        (regularSection a Q b) := by
  refine ⟨cost ka q r,unary ka q r,2,0,?_⟩
  rw [original]
  have hp := source_pad 0 0 1 (regularSection (unary ka q r) 2 0)
  change ObsEq
    (regularSection (unary ka q r) 2 0)
    (⟨[],false,
      (List.replicate (unary ka q r) true ++
        (oppairs 2 ++ List.replicate 0 true)) ++ [false],5⟩ : Cfg) at hp
  simpa [ObsEq,regularSection,run,oppairs,List.append_assoc] using
    (BB6.Padding.cfgEq_symm hp)

#print axioms original
#print axioms regular
end BB6.Agent36AY1
