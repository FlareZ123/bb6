import Raw39CounterCarry
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11CounterCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace BB6.Agent11Raw39B1RCCounter2124
namespace M2124

namespace MInit

-- 1RB1RC_1RC---_0RD1RF_1LD0RA_1LC0LE_1LE1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 10 ⟨5,([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 6 ⟨4,([true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([false,false,false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (6*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([true])⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,false,false,false,false,false] 6 local1 n (([false,false])) (([true]))

theorem phase2 (n : Nat) : run0 table 5 ⟨4,([true,true,true,true,true,true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([true])⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),([false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true])⟩ := by rfl

theorem finalL (n : Nat) : ([true,true,true,true,true,true,false,false]) = ([true,true,true,true,true,true,false,false]) := by
  rfl

theorem finalR (n : Nat) : ([false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]) = (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by
  calc
    _ = ([false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([true])) [false,false,false,false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,true])) [false,false,false,false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,true])) [false,false,false,false,false] false n
    _ = ([false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,true])) [false,false,false,false,false] false n
    _ = (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,true]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,true])) [false,false,false,false,false] false n

theorem epoch (n : Nat) : run0 table (15+6*n) ⟨5,([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,true])⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalR n] at H
  rw [show 10+6*n+5=15+6*n by omega] at H
  exact H

theorem canon (n : Nat) : run0 table (15+6*n) ⟨5,([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,true])⟩ := by
  exact epoch n

end MInit


namespace MFinish

-- 1RB1RC_1RC---_0RD1RF_1LD0RA_1LC0LE_1LE1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) : run0 table 35 ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨0,([false,false,false]),([false,false,false,false,true]) ++ (rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨0,([false]) ++ (L),([false,false,false,false,true]) ++ ([false,false,false,false,false,true]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([false,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) : run0 table (18*n) ⟨0,([false,false,false]),([false,false,false,false,true]) ++ (rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false,true,false,false,false,false,false,true])⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,false,false,false,true] [false,false,false,false,false,true] [true,true,true,true,true,true] 18 local1 n (([false,false])) (([false,false,false,false,false,true]))

theorem phase2 (n : Nat) : run0 table 44 ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false,true,false,false,false,false,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩ := by rfl

theorem finalL (n : Nat) : ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]) = ([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,false,false]) := by
  calc
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])) (([false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true])) (([true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true])) (([true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true])) (([true,true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true])) (([true,true,true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,false,false]) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true])) (([true,true,true,true,true,false,false])) [true,true,true,true,true] true n

theorem finalR (n : Nat) : ([] : List Bool) = [] := by
  rfl

theorem epoch (n : Nat) : run0 table (79+18*n) ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,false,false]),[]⟩ := by
  have H := (join0 (join0 (phase0 n) (phase1 n)) (phase2 n))
  rw [finalL n] at H
  rw [show 35+18*n+44=79+18*n by omega] at H
  exact H

theorem eq1l (n : Nat) : ([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,true,false,false]) = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]) := by
  calc
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true])) (([true,true,true,true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true])) (([true,true,true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true])) (([true,true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true])) (([true,true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([true,false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true])) (([true,false,false])) [true,true,true,true,true] true n
    _ = ([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]) := by symm; simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true])) (([false,false])) [true,true,true,true,true] true n

theorem canon (n : Nat) : run0 table (79+18*n) ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true])⟩ = some ⟨5,([false,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩ := by
  simpa only [eq1l n] using epoch n

end MFinish


namespace MCarry

-- 1RB1RC_1RC---_0RD1RF_1LD0RA_1LC0LE_1LE1RA

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem phase0 (n : Nat) (R : List Bool) : run0 table 35 ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨0,([false,false,false]),([false,false,false,false,true]) ++ (rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ := by rfl

theorem local1 (L R : List Bool) : run0 table 18 ⟨0,([false]) ++ (L),([false,false,false,false,true]) ++ ([false,false,false,false,false,true]) ++ (R)⟩ = some ⟨0,([false]) ++ ([true,true,true,true,true,true]) ++ (L),([false,false,false,false,true]) ++ (R)⟩ := by rfl

theorem phase1 (n : Nat) (R : List Bool) : run0 table (18*n) ⟨0,([false,false,false]),([false,false,false,false,true]) ++ (rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepR table 0 [false] [false,false,false,false,true] [false,false,false,false,false,true] [true,true,true,true,true,true] 18 local1 n (([false,false])) (([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R))

theorem phase2 (n : Nat) (R : List Bool) : run0 table 54 ⟨0,([false]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([false,false,false,false,true,false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([true]) ++ (R)⟩ := by rfl

theorem local3 (L R : List Bool) : run0 table 6 ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ ([true,true,true,true,true,true]) ++ (L),(R)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (L),([false,false,false,false,false,false]) ++ (R)⟩ := by rfl

theorem phase3 (n : Nat) (R : List Bool) : run0 table (6*n) ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),([true]) ++ (R)⟩ = some ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by
  simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using sweepL table 4 [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,false,false,false,false,false] 6 local3 n (([false,false])) (([true]) ++ (R))

theorem phase4 (n : Nat) (R : List Bool) : run0 table 11 ⟨4,([true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([true]) ++ (R)⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),([false,false,false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]) ++ (R)⟩ := by rfl

theorem finalL (n : Nat) (R : List Bool) : ([true,true,true,true,true,true,false,false]) = ([true,true,true,true,true,true,false,false]) := by
  rfl

theorem finalR (n : Nat) (R : List Bool) : ([false,false,false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([true]) ++ (R) = (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,false,false,true]) ++ (R) := by
  calc
    _ = ([false,false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false,false,false])) (([true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false,false])) (([false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false,false])) (([false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false,false])) (([false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false,false])) (([false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false,false])) (([false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false,false])) (([false,false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false,false])) (([false,false,false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false,false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false,false])) (([false,false,false,false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = ([false]) ++ (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut (([false])) (([false,false,false,false,false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n
    _ = (rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,false,false,true]) ++ (R) := by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using moveCut ([]) (([false,false,false,false,false,false,false,false,false,false,true]) ++ (R)) [false,false,false,false,false] false n

theorem epoch (n : Nat) (R : List Bool) : run0 table (100+24*n) ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,false,false,true]) ++ (R)⟩ := by
  have H := (join0 (join0 (join0 (join0 (phase0 n R) (phase1 n R)) (phase2 n R)) (phase3 n R)) (phase4 n R))
  rw [finalR n R] at H
  rw [show 35+18*n+54+6*n+11=100+24*n by omega] at H
  exact H

theorem canon (n : Nat) (R : List Bool) : run0 table (100+24*n) ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,true] (n)) ++ ([false,false,false,false,false,true,false,false,false,false,false,false]) ++ (R)⟩ = some ⟨4,([true,true,true,true,true,true,false,false]),(rep [false,false,false,false,false,false] (n)) ++ ([false,false,false,false,false,false,false,false,false,false,false,true]) ++ (R)⟩ := by
  exact epoch n R

end MCarry


abbrev table := MInit.table
abbrev A : List Bool := [false,false,false,false,false,true]
abbrev Z : List Bool := [false,false,false,false,false,false]
def Q (R : List Bool) : Z0 := ⟨4,[true,true,true,true,true,true,false,false],(R)⟩
def family (n : Nat) : Z0 := ⟨5,([false,true,true,false,true,true,true,true,true,true,true]) ++ (rep [true,true,true,true,true,true] (n)) ++ ([false,false]),[]⟩
def carryCost (n : Nat) : Nat := 76+24*n

theorem carry (n : Nat) (R : List Bool) : run0 table (carryCost n) (Q (rep A n ++ Z ++ R)) = some (Q (rep Z n ++ A ++ R)) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h := MCarry.canon n R
    rw [show MCarry.table = table from rfl] at h
    unfold carryCost
    rw [show 76+24*n.succ = 100+24*n by omega]
    rw [rep_succ_snoc A n,rep_succ_snoc Z n]
    simpa only [table,Q,A,Z,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem entry : run0 table 52 ⟨0,[],[]⟩ = some (family 0) := by rfl


def cost (n : Nat) : Nat := (15+6*n) + fillCost carryCost (n+0) + (79+18*n)
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := by
  have h1 := MInit.canon n
  have h2 := fill table Q A Z carryCost carry (n+0) [false,false,false,false,false,true]
  have h3 := MFinish.canon n
  rw [rep_add Z n 0,rep_add A n 0] at h2
  simp only [Q,A,Z,rep,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] at h2
  have h := join0 (join0 h1 h2) h3
  simpa only [cost,family,rep,rep_succ_snoc,List.append_assoc,List.nil_append,List.append_nil,List.cons_append] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 52 cost entry (by intro n; unfold cost; omega) growth m hm

#print axioms growth
#print axioms never
end M2124

end BB6.Agent11Raw39B1RCCounter2124
