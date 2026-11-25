import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39RCCounter38
namespace M38

namespace MInit

-- 1RB0RC_1RC---_0RD0LE_1LD0RA_1LE0LF_0LA0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false]) ++ (L),(R)⟩ = some ⟨3,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true]),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false,false,false] [true,true,true] 3 local0 n (([false,false,false,false,false,true,true])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨3,([false,false,false,false,false,true,true]),(rep [true,true,true] (n))⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true])) ([]) [true,true] true n

theorem epoch (n : Nat) : run0 table (13+3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 3*n+13=13+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (13+3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD0LE_1LD0RA_1LE0LF_0LA0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,false])⟩ = some ⟨3,([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) := by
  calc
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([true,true])) [false,false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([false,true,true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,false,true,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,false,true,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,true,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,true,true])) [false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (8+3*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+3*n+7=8+3*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false]) = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false]) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,false])) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,false])) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,false])) [true,true] false n

theorem eq1l (n : Nat) : (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,true,true])) [false,false] false n

theorem canon (n : Nat) : run0 table (8+3*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false])⟩ = some ⟨3,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ := by
  simpa only [eq0r n, eq1l n] using epoch n

end MFinish


namespace MReset

-- 1RB0RC_1RC---_0RD0LE_1LD0RA_1LE0LF_0LA0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([false,true,true,true]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,true])⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([false,false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨4,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false])⟩ = some ⟨4,([false,false,false,false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local3 n (([true,true])) (([false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨4,([false,false,false,false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false]) = (rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true])) (([false])) [true,true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true])) (([true,false])) [true,true] true n
    _ = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true])) (([true,true,false])) [true,true] true n
    _ = ([true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([true,true,true,false])) [true,true] true n
    _ = ([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,true,true,false])) [true,true] true n
    _ = (rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,true,true,true,false])) [true,true] true n

theorem epoch (n : Nat) : run0 table (18+6*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false])⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+7+3*n+10=18+6*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true]) = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true]) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true])) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true])) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true])) [true,true] false n

theorem canon (n : Nat) : run0 table (18+6*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true])⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false])⟩ := by
  simpa only [eq0r n] using epoch n

end MReset


namespace MCarry

-- 1RB0RC_1RC---_0RD0LE_1LD0RA_1LE0LF_0LA0RF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([true,true,true]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 4 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true]) ++ (R)⟩ = some ⟨4,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false,true,true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨4,([false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨4,([false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨4,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false,true,true]) ++ (R)⟩ = some ⟨4,([false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [false,false,false] [] [false,false,false] [true,true,true] 3 local3 n (([true,true])) (([false,true,true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 7 ⟨4,([false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R) = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by
  calc
    _ = ([true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true]) ++ (R)) [true,true] true n
    _ = ([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true]) ++ (R)) [true,true] true n
    _ = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true]) ++ (R)) [true,true] true n

theorem epoch (n : Nat) (R : List Bool) : run0 table (12+6*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 1+3*n+4+3*n+7=12+6*n by omega] at H
  exact H

theorem eq0r (n : Nat) (R : List Bool) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R) = (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true]) ++ (R)) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,true,true,true]) ++ (R)) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,true,true,true]) ++ (R)) [true,true] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (12+6*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  simpa only [eq0r n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true,true]
abbrev Z : List Bool := [true,true,true]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩
def carryCost (n : Nat) : Nat := 6+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 6+6*n.succ = 12+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (13+3*n) + partialCost carryCost 2 n + (18+6*n) + fillCost carryCost (n+2) + (8+3*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fillFrom table Q A Z carryCost carry 2 n [true]
  have h3 := MReset.canon n
  have h4 := fill table Q A Z carryCost carry (n+2) [false]
  have h5 := MFinish.canon n
  rw [Nat.add_comm 2 n,rep_add A n 2] at h2
  rw [rep_add Z n 2,rep_add A n 2] at h4
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2 h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M38
namespace M176

namespace MInit

-- 1RB0RC_1RC---_0RD0LF_1LD0RA_0LA0RE_1LF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem local0 (L R : List Bool) : run0 table 3 ⟨3,([false,false,false]) ++ (L),(R)⟩ = some ⟨3,(L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase0 (n : Nat) : run0 table (3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨3,([false,false,false,false,false,true,true]),(rep [true,true,true] (n))⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 3 [] [] [false,false,false] [true,true,true] 3 local0 n (([false,false,false,false,false,true,true])) ([])

theorem phase1 (n : Nat) : run0 table 13 ⟨3,([false,false,false,false,false,true,true]),(rep [true,true,true] (n))⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n))⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([false,true,true,false,true,true,true]) ++ (rep [true,true,true] (n)) = ([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by
  calc
    _ = ([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true])) ([]) [true,true] true n

theorem epoch (n : Nat) : run0 table (13+3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by
  have H := (join0 (phase0 n) (phase1 n))
  rw [finalR n] at H
  rw [show 3*n+13=13+3*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (13+3*n) ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ = some ⟨1,([false,true]),([false,true,true,false,true,true]) ++ (rep [true,true,true] (n)) ++ ([true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB0RC_1RC---_0RD0LF_1LD0RA_0LA0RE_1LF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([false,true,true,false]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,false])⟩ = some ⟨3,([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]) = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) := by
  calc
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([true,true])) [false,false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([false,true,true])) [false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,false,true,true])) [false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,false,true,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,true,true])) [false,false] false n
    _ = (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,true,true])) [false,false] false n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (8+3*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false])⟩ = some ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 1+3*n+7=8+3*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,false]) = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false]) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,false])) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,false])) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,false])) [true,true] false n

theorem eq1l (n : Nat) : (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true,true]) = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by
  calc
    _ = ([false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,true,true])) [false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,true,true])) [false,false] false n

theorem canon (n : Nat) : run0 table (8+3*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,false])⟩ = some ⟨3,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩ := by
  simpa only [eq0r n, eq1l n] using epoch n

end MFinish


namespace MReset

-- 1RB0RC_1RC---_0RD0LF_1LD0RA_0LA0RE_1LF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([false,true,true,true]))

theorem phase2 (n : Nat) : run0 table 7 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,false,true,true,true])⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false])⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false,false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false,false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) : run0 table (3*n) ⟨5,([false,false,false,false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false])⟩ = some ⟨5,([false,false,false,false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false,false,false,false] [] [false,false,false] [true,true,true] 3 local3 n (([true,true])) (([false]))

theorem phase4 (n : Nat) : run0 table 10 ⟨5,([false,false,false,false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false])⟩ = some ⟨1,([false,true]),([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false])⟩ := by rfl

theorem finalL (n : Nat) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) : ([true,true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false]) = (rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false]) := by
  calc
    _ = ([true,true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true,true])) (([false])) [true,true] true n
    _ = ([true,true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true,true])) (([true,false])) [true,true] true n
    _ = ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true,true])) (([true,true,false])) [true,true] true n
    _ = ([true,true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([true,true,true,false])) [true,true] true n
    _ = ([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,true,true,true,false])) [true,true] true n
    _ = (rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,true,true,true,false])) [true,true] true n

theorem epoch (n : Nat) : run0 table (18+6*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true])⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false])⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n) (phase1 n)) (phase2 n)) (phase3 n)) (phase4 n))
  rw [finalR n] at H
  rw [show 1+3*n+7+3*n+10=18+6*n by omega] at H
  exact H

theorem eq0r (n : Nat) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([false,true,true,true]) = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true]) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([false,true,true,true])) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,false,true,true,true])) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true,true])) [true,true] false n

theorem canon (n : Nat) : run0 table (18+6*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,false,true,true,true])⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,true,true,true,false])⟩ := by
  simpa only [eq0r n] using epoch n

end MReset


namespace MCarry

-- 1RB0RC_1RC---_0RD0LF_1LD0RA_0LA0RE_1LF0LE

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 1 ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 3 ⟨2,([false]) ++ (L),([true,true]) ++ ([false,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ ([false,false,false]) ++ (L),([true,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨2,([false,true,true]),([true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 2 [false] [true,true] [false,true,true] [false,false,false] 3 local1 n (([true,true])) (([true,true,true]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 4 ⟨2,([false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([true,true,true,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false,true,true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 3 ⟨5,([false,false,false]) ++ ([false,false,false]) ++ (L),(R)⟩ = some ⟨5,([false,false,false]) ++ (L),([true,true,true]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (3*n) ⟨5,([false,false,false]) ++ (rep [false,false,false] (n)) ++ ([true,true]),([false,true,true]) ++ (R)⟩ = some ⟨5,([false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 5 [false,false,false] [] [false,false,false] [true,true,true] 3 local3 n (([true,true])) (([false,true,true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 7 ⟨5,([false,false,false,true,true]),(rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([false,true]) = ([false,true]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([true,true,true]) ++ (rep [true,true,true] (n)) ++ ([false,true,true]) ++ (R) = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by
  calc
    _ = ([true,true]) ++ (rep [true,true,true] (n)) ++ ([true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true,true])) (([false,true,true]) ++ (R)) [true,true] true n
    _ = ([true]) ++ (rep [true,true,true] (n)) ++ ([true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([true])) (([true,false,true,true]) ++ (R)) [true,true] true n
    _ = (rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,false,true,true]) ++ (R)) [true,true] true n

theorem epoch (n : Nat) (R : List Bool) : run0 table (12+6*n) ⟨1,([false,true]),([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 1+3*n+4+3*n+7=12+6*n by omega] at H
  exact H

theorem eq0r (n : Nat) (R : List Bool) : ([false,true,true]) ++ (rep [false,true,true] (n)) ++ ([true,true,true]) ++ (R) = (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R) := by
  calc
    _ = ([false,true]) ++ (rep [true,false,true] (n)) ++ ([true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true])) (([true,true,true]) ++ (R)) [false,true] true n
    _ = ([false]) ++ (rep [true,true,false] (n)) ++ ([true,true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([true,true,true,true]) ++ (R)) [true,false] true n
    _ = (rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([true,true,true,true,true]) ++ (R)) [true,true] false n

theorem canon (n : Nat) (R : List Bool) : run0 table (12+6*n) ⟨1,([false,true]),(rep [false,true,true] (n)) ++ ([false,true,true,true,true,true]) ++ (R)⟩ = some ⟨1,([false,true]),(rep [true,true,true] (n)) ++ ([true,true,true,false,true,true]) ++ (R)⟩ := by
  simpa only [eq0r n R] using epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,true,true]
abbrev Z : List Bool := [true,true,true]
def Q (R : List Bool) : Z0 := ⟨1,[false,true],(R)⟩
def family (n : Nat) : Z0 := ⟨3,(rep [false,false,false] (n)) ++ ([false,false,false,false,false,true,true]),[]⟩
def carryCost (n : Nat) : Nat := 6+6*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 6+6*n.succ = 12+6*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (13+3*n) + partialCost carryCost 2 n + (18+6*n) + fillCost carryCost (n+2) + (8+3*n)

theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fillFrom table Q A Z carryCost carry 2 n [true]
  have h3 := MReset.canon n
  have h4 := fill table Q A Z carryCost carry (n+2) [false]
  have h5 := MFinish.canon n
  rw [Nat.add_comm 2 n,rep_add A n 2] at h2
  rw [rep_add Z n 2,rep_add A n 2] at h4
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2 h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h


theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M176

end BB6.Agent11Raw39RCCounter38
