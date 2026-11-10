import OddCZeroToE1
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace BB429OddAlternating
open BB429OddExcursion BB429CZeroEvenReturn BB429OddCZeroToE1

private def quads : Nat → List Bool
  | 0 => []
  | q+1 => [true,false,true,true] ++ quads q

private def extras : Nat → List Bool
  | 0 => []
  | q+1 => [false,true,true,true] ++ extras q

private theorem tens_add (a b : Nat) :
    tens (a+b) = tens a ++ tens b := by
  induction a with
  | zero => simp [tens]
  | succ a ih => simp only [Nat.succ_add,tens,ih,List.cons_append]

private theorem e_transfer6 (l r : List Bool) :
    run 6 (z 4 (tens 2 ++ l) true r) =
      some (z 4 l true ([true,false,true,true] ++ r)) := by rfl

private theorem e_transfer_many (q : Nat) (l r : List Bool) :
    run (6*q) (z 4 (tens (2*q) ++ l) true r) =
      some (z 4 l true (quads q ++ r)) := by
  induction q generalizing l r with
  | zero => simp [run,tens,quads]
  | succ q ih =>
    have hword : tens (2*(q+1)) ++ l =
        tens (2*q) ++ (tens 2 ++ l) := by
      rw [show 2*(q+1)=2*q+2 by omega,tens_add]
      simp only [List.append_assoc]
    rw [show 6*(q+1)=6*q+6 by omega,run_add,hword,ih]
    simp only [Option.bind_some]
    rw [e_transfer6]
    rfl

private theorem quad_shift (q : Nat) (r : List Bool) :
    quads q ++ (true :: r) = true :: (extras q ++ r) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [quads,extras,List.append_assoc]
    rw [ih]
    rfl

private theorem e_base7 (l r : List Bool) :
    run 7 (z 4 ([true,false,false] ++ l) true (true :: r)) =
      some (z 0 ([true,false,true,true] ++ l) true r) := by rfl

private theorem a_extra8 (l r : List Bool) :
    run 8 (z 0 ([true,false,true,true] ++ l) true
      ([false,true,true,true] ++ r)) =
      some (z 0 ([true,false,true,true] ++ ones 4 ++ l) true r) := by rfl

private theorem a_extra_many (q : Nat) (l r : List Bool) :
    run (8*q) (z 0 ([true,false,true,true] ++ l) true (extras q ++ r)) =
      some (z 0 ([true,false,true,true] ++ ones (4*q) ++ l) true r) := by
  induction q generalizing l r with
  | zero => simp [run,ones,extras]
  | succ q ih =>
    rw [show 8*(q+1)=8+8*q by omega,run_add]
    change ((run 8 (z 0 ([true,false,true,true] ++ l) true
      ([false,true,true,true] ++ (extras q ++ r)))).bind (run (8*q))) = _
    rw [a_extra8]
    simp only [Option.bind_some]
    have h := ih (ones 4 ++ l) r
    simp only [List.append_assoc] at h ⊢
    rw [h]
    simp only [Option.some.injEq]
    congr 1
    have hw : ones (4*q) ++ ones 4 ++ l = ones (4*(q+1)) ++ l := by
      change (List.replicate (4*q) true ++ List.replicate 4 true) ++ l =
        List.replicate (4*(q+1)) true ++ l
      rw [List.replicate_append_replicate]
      congr 1
    simpa only [List.append_assoc] using congrArg (fun xs => [true,false,true,true] ++ xs) hw

private theorem a_finish4 (l : List Bool) :
    run 4 (z 0 l false [false,true]) =
      some (z 2 ([true,false,true,true] ++ l) false []) := by rfl

private theorem a_finish (m : Nat) (l : List Bool) :
    run (2*m+8) (z 0 ([true,false,true,true] ++ l) true
      (tens m ++ [false,true])) =
      some (z 2 ([true,false] ++ ones (2*m+6) ++ l) false []) := by
  have h2 : run 2 (z 0 ([true,false,true,true] ++ l) true
      (tens m ++ [false,true])) =
      some (z 0 ([true,true] ++ l) false (tens (m+1) ++ [false,true])) := by
    rfl
  have hp := a_right_pairs_exact (m+1) ([true,true] ++ l) [false,true]
  rw [show 2*m+8=2+(2*(m+1)+4) by omega,run_add,h2]
  simp only [Option.bind_some]
  rw [run_add,hp]
  simp only [Option.bind_some]
  rw [a_finish4]
  simp only [Option.some.injEq]
  congr 1
  change [true,false,true,true] ++ (ones (2*(m+1)) ++ ([true,true] ++ l)) =
    [true,false] ++ (ones (2*m+6) ++ l)
  have h : ones 2 ++ ones (2*(m+1)) ++ ones 2 = ones (2*m+6) := by
    change (List.replicate 2 true ++ List.replicate (2*(m+1)) true) ++
      List.replicate 2 true = List.replicate (2*m+6) true
    rw [List.replicate_append_replicate,List.replicate_append_replicate]
    congr 1
    omega
  simpa [ones,List.append_assoc] using congrArg (fun xs => [true,false] ++ (xs ++ l)) h

/-- Arbitrarily many *odd-numbered alternating pairs* before a zero.
    All natural m,q and all untouched finite left suffixes are covered. -/
theorem odd_alternating_root (m q : Nat) (tail : List Bool) :
    run (4*m+14*q+21)
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) =
    some (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail)
      false []) := by
  have hs := odd_C0_to_E1 m (tens (2*q+1) ++ [false] ++ tail)
  have ht : 4*m+14*q+21 = (2*m+6)+((6*q)+(7+((8*q)+(2*m+8)))) := by omega
  rw [ht,run_add]
  have hinit : ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail =
      ones (2*m+1) ++ (false :: (tens (2*q+1) ++ [false] ++ tail)) := by
    simp [List.append_assoc]
  rw [hinit,hs]
  simp only [Option.bind_some]
  rw [run_add]
  have hleft : tens (2*q+1) ++ [false] ++ tail =
      tens (2*q) ++ (tens 1 ++ [false] ++ tail) := by
    rw [show 2*q+1=2*q+1 by omega,tens_add]
    simp only [List.append_assoc]
  rw [hleft,e_transfer_many]
  simp only [Option.bind_some]
  rw [run_add]
  have hr : quads q ++ (true :: tens m ++ [false,true]) =
       true :: (extras q ++ (tens m ++ [false,true])) := by
    simpa [List.append_assoc] using quad_shift q (tens m ++ [false,true])
  rw [hr]
  have hb : tens 1 ++ [false] ++ tail = [true,false,false] ++ tail := by rfl
  rw [hb,e_base7]
  simp only [Option.bind_some]
  rw [run_add,a_extra_many]
  simp only [Option.bind_some]
  change run (2*m+8) (z 0 ([true,false,true,true] ++ (ones (4*q) ++ tail))
    true (tens m ++ [false,true])) = _
  rw [a_finish]
  simp only [Option.some.injEq]
  congr 1
  have hw : ones (2*m+6) ++ (ones (4*q) ++ tail) =
      ones (2*m+4*q+6) ++ tail := by
    change List.replicate (2*m+6) true ++ (List.replicate (4*q) true ++ tail) =
      List.replicate (2*m+4*q+6) true ++ tail
    rw [← List.append_assoc, List.replicate_append_replicate]
    have hn : 2*m+6+4*q = 2*m+4*q+6 := by omega
    rw [hn]
  simpa [List.append_assoc] using congrArg (fun xs => [true,false] ++ xs) hw

#print axioms odd_alternating_root
end BB429OddAlternating
