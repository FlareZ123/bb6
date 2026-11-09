import CZeroToJunc0
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low2Stage
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429CZeroToJunc0

/-- Canonical entire-tape source section after the first v physical bubbles
    of J(v+1,2v), with the head at physical coordinate 2v. -/
def stage (v : Nat) : Zipper :=
  z 0 (ones (4*v) ++ (true::false::ones 6)) true [true,false,true]

private theorem ones_add (m n : Nat) :
    ones (m+n) = ones m ++ ones n := by simp [ones]

private theorem tens_tail_pair (n : Nat) :
    tens n ++ [true,false] = tens (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change true::false::(tens n ++ [true,false]) =
        true::false::tens (n+1)
      rw [ih]

private theorem af_tail_two (left right : List Bool) :
    run 2 (z 0 (true::false::left) true right) =
      some (z 0 left false (true::false::right)) := by rfl

private theorem ar_pair (left right : List Bool) :
    run 2 (z 0 left false (true::false::right)) =
      some (z 0 (true::true::left) false right) := by rfl

/-- An arbitrary-length A/0,B/1 rightward sweep, with the full source tape. -/
theorem ar_pairs_exact (j : Nat) (left right : List Bool) :
    run (2*j) (z 0 left false (tens j ++ right)) =
      some (z 0 (ones (2*j) ++ left) false right) := by
  induction j generalizing left with
  | zero => rfl
  | succ j ih =>
      have hf : run 2 (z 0 left false (tens (j+1) ++ right)) =
          some (z 0 (true::true::left) false (tens j ++ right)) := by
        exact ar_pair left (tens j ++ right)
      rw [show 2*(j+1)=2+2*j by omega,run_add,hf]
      simp only [Option.bind_some]
      rw [ih (true::true::left)]
      have hw : ones (2*j) ++ (true::true::left) =
          ones (2*(j+1)) ++ left := by
        calc
          ones (2*j) ++ (true::true::left) =
              (ones (2*j) ++ ones 2) ++ left := by simp [ones,List.append_assoc]
          _ = ones (2*j+2) ++ left := by rw [← ones_add]
          _ = ones (2*(j+1)) ++ left := by rw [show 2*j+2=2*(j+1) by omega]
      rw [hw]
      rw [show 2+2*j=2*(j+1) by omega]

private theorem ar_tail_two (left : List Bool) :
    run 2 (z 0 left false [true]) =
      some (z 0 (true::true::left) false []) := by rfl

private theorem a0_to_c0_two (left : List Bool) :
    run 2 (z 0 left false []) =
      some (z 2 (true::true::left) false []) := by rfl

/-- A uniform first fresh C/0: from the entire full-tape bubble checkpoint
    for every v, the head traverses 8v+10 original instructions. -/
theorem stage_to_C0 (v : Nat) :
    run (8*v+10) (stage v) =
      some (z 2 (ones (4*v+14)) false []) := by
  have hAF : run (4*v) (stage v) =
      some (z 0 (true::false::ones 6) true
        (tens (2*v) ++ [true,false,true])) := by
    simpa [stage,ones,show 2*(2*v)=4*v by omega] using
      (af_pairs (2*v) (true::false::ones 6) [true,false,true])
  have hAFtail : run 2
      (z 0 (true::false::ones 6) true
        (tens (2*v) ++ [true,false,true])) =
      some (z 0 (ones 6) false
        (tens (2*v+1) ++ [true,false,true])) := by
    change run 2 (z 0 (true::false::ones 6) true
      (tens (2*v) ++ [true,false,true])) =
      some (z 0 (ones 6) false
        (true::false::(tens (2*v) ++ [true,false,true])))
    exact af_tail_two (ones 6) _
  have hright : tens (2*v+1) ++ [true,false,true] =
      tens (2*v+2) ++ [true] := by
    calc
      tens (2*v+1) ++ [true,false,true] =
          (tens (2*v+1) ++ [true,false]) ++ [true] := by simp [List.append_assoc]
      _ = tens ((2*v+1)+1) ++ [true] := by rw [tens_tail_pair]
      _ = tens (2*v+2) ++ [true] := by rw [show (2*v+1)+1=2*v+2 by omega]
  have hAR : run (4*v+4) (z 0 (ones 6) false
          (tens (2*v+1) ++ [true,false,true])) =
      some (z 0 (ones (4*v+4) ++ ones 6) false [true]) := by
    rw [hright]
    simpa [show 2*(2*v+2)=4*v+4 by omega] using
      (ar_pairs_exact (2*v+2) (ones 6) [true])
  have htail : run 2 (z 0 (ones (4*v+4) ++ ones 6) false [true]) =
      some (z 0 (ones (4*v+6) ++ ones 6) false []) := by
    have hwords : ones (4*v+6) ++ ones 6 =
        true::true::(ones (4*v+4) ++ ones 6) := by
      rw [show 4*v+6=2+(4*v+4) by omega,ones_add]
      rfl
    rw [hwords]
    exact ar_tail_two _
  have hC : run 2 (z 0 (ones (4*v+6) ++ ones 6) false []) =
      some (z 2 (ones (4*v+14)) false []) := by
    have hwords : true::true::(ones (4*v+6) ++ ones 6) =
        ones (4*v+14) := by
      simp [ones,show 4*v+14=2+(4*v+6)+6 by omega,
        ←List.replicate_append_replicate,List.append_assoc]
    simpa [hwords] using a0_to_c0_two (ones (4*v+6) ++ ones 6)
  rw [show 8*v+10 = 4*v+(2+((4*v+4)+(2+2))) by omega,run_add,hAF]
  simp only [Option.bind_some]
  rw [run_add,hAFtail]
  simp only [Option.bind_some]
  rw [run_add,hAR]
  simp only [Option.bind_some]
  rw [run_add,htail]
  simp only [Option.bind_some]
  exact hC

private theorem run_compose (m n : Nat) (a b c : Zipper)
    (h1 : run m a = some b) (h2 : run n b = some c) :
    run (m+n) a = some c := by
  rw [run_add, h1]
  exact h2

/-- Entire symbolic low-J deficit-two return, uniformly in every v. -/
theorem stage_to_junc (v : Nat) :
    run (20*v+79) (stage v) = some (junc 0 0 (4*v+12)) := by
  have hwords : 2*(2*v+6)+2=4*v+14 := by omega
  have htarget : 2*(2*v+6)=4*v+12 := by omega
  have hnext : run (6*(2*v+6)+33)
      (z 2 (ones (4*v+14)) false []) = some (junc 0 0 (4*v+12)) := by
    simpa only [hwords,htarget] using (even_C0_to_junc0 (2*v+6))
  have hfull := run_compose (8*v+10) (6*(2*v+6)+33)
    (stage v) (z 2 (ones (4*v+14)) false [])
    (junc 0 0 (4*v+12)) (stage_to_C0 v) hnext
  have ht : (8*v+10)+(6*(2*v+6)+33) = 20*v+79 := by omega
  simpa only [ht] using hfull

#print axioms ar_pairs_exact
#print axioms stage_to_C0
#print axioms stage_to_junc
end BB429Low2Stage
